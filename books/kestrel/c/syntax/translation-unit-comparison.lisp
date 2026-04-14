; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-trees")
(include-book "hash-conditional-evaluation")

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ translation-unit-comparison
  :parents (syntax-for-tools)
  :short "Comparison between translation units,
          taking macros into account."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our disambiguator tries to preserve
     the @('#include') and relative directives
     that are preserved by our preprocessor.
     It does so using a technique similar to the one used by the preprocessor;
     the latter is described in @(see preservable-inclusions).
     The technique used in the disambiguator
     involves the comparison of the results of
     disambiguating an included translation unit
     first in the context of the including translation unit
     and then in a fresh context (i.e. stand-alone).
     But the comparison must take into account the macro table,
     for the same reasons explained in @(see preservable-inclusions).
     Here we introduce the code to perform this comparison,
     which is similar to @(tsee compare-pfiles),
     but it operates on translation units.")
   (xdoc::p
    "This comparison is more general than the disambiguator.
     It will be used soon in the validator as well,
     and it may be used in at least certain transformations."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines compare-trans-items-and-components
  :short "Compare translation items and related components,
          taking macros into account."

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define compare-trans-items ((item1 trans-itemp)
                               (item2 trans-itemp)
                               (macros macro-tablep)
                               (ienv ienvp))
    :returns (yes/no booleanp)
    :parents (translation-unit-comparison compare-trans-items-and-components)
    :short "Compare two translation items, taking macros into account."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two translation items must be of the same kind.
       And they must be be identical in all cases
       except when they are conditional translation items,
       which needs a more relaxed check.
       The initial @('#if') or @('#ifdef') or @('#ifndef') must be identical.
       We evaluate the condition:
       if satisfied, the items under that condition must compare equal;
       if not satified, they are skipped in the comparison,
       so we allow them to differ.
       Then we compare the @('#elif')s (if any) via a separate function,
       which also tells us, via the @('donep') result,
       whether a satisfied condition was found or not.
       We use this information to compare the final @('#else')s if present:
       if no previous condition was satisfied,
       the @('#else') is satisfied,
       in which case its translation items must compare equal;
       otherwise, they are skipped.
       Note that the presence vs. absence of the @('#else') itself must match,
       regardless of whether a previous condition was selected or not:
       that is, either both have @('#else') or neither does;
       if they both do, the items must compare equal or not
       based on the truth of the default @('#else') condition."))
    (and (equal (trans-item-kind item1)
                (trans-item-kind item2))
         (if (trans-item-case item1 :cond)
             (b* (((trans-item-cond item1) item1)
                  ((trans-item-cond item2) item2)
                  ((unless (equal item1.if/ifdef/ifndef
                                  item2.if/ifdef/ifndef))
                   nil)
                  (condp
                   (hash-if/ifdef/ifndef-case
                    item1.if/ifdef/ifndef
                    :if (b* (((mv erp intval)
                              (eval-hash-if/elif-expr
                               item1.if/ifdef/ifndef.expr macros ienv))
                             ((when erp)
                              (raise "Internal error: evaluation of ~x0 fails."
                                     item1.if/ifdef/ifndef.expr)))
                          (/= intval 0))
                    :ifdef (b* ((name
                                 (ident->unwrap item1.if/ifdef/ifndef.name))
                                ((unless (stringp name))
                                 (raise "Internal error: ~
                                         malformed identifier ~x0."
                                        item1.if/ifdef/ifndef.name)))
                             (and (macro-lookup name macros) t))
                    :ifndef (b* ((name
                                  (ident->unwrap item1.if/ifdef/ifndef.name))
                                 ((unless (stringp name))
                                  (raise "Internal error: ~
                                          malformed identifier ~x0."
                                         item1.if/ifdef/ifndef.name)))
                              (not (macro-lookup name macros)))))
                  ((when (and condp
                              (not (equal item1.items item2.items))))
                   nil)
                  ((mv yes/no donep)
                   (compare-hash-elif-lists item1.elifs
                                            item2.elifs
                                            condp
                                            macros
                                            ienv))
                  ((unless yes/no) nil))
               (hash-else-option-case
                item1.else
                :none (hash-else-option-case item2.else :none)
                :some (and (hash-else-option-case item2.else :some)
                           (b* ((item2.else.val
                                 (hash-else-option-some->val item2.else)))
                             (if donep ; #else not selected
                                 t
                               (compare-trans-item-lists
                                (hash-else->items item1.else.val)
                                (hash-else->items item2.else.val)
                                macros
                                ienv))))))
           (equal (trans-item-fix item1)
                  (trans-item-fix item2))))
    :no-function nil
    :measure (trans-item-count item1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define compare-trans-item-lists ((items1 trans-item-listp)
                                    (items2 trans-item-listp)
                                    (macros macro-tablep)
                                    (ienv ienvp))
    :returns (yes/no booleanp)
    :parents (translation-unit-comparison compare-trans-items-and-components)
    :short "Compare two lists of translation items, taking macros into account."
    :long
    (xdoc::topstring
     (xdoc::p
      "We compare the two lists element-wise.
       They must have the same length,
       and corresponding elements must compare equal."))
    (if (endp items1)
        (endp items2)
      (and (consp items2)
           (compare-trans-items (car items1) (car items2) macros ienv)
           (compare-trans-item-lists (cdr items1) (cdr items2) macros ienv)))
    :measure (trans-item-list-count items1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define compare-hash-elifs ((elif1 hash-elifp)
                              (elif2 hash-elifp)
                              (donep booleanp)
                              (macros macro-tablep)
                              (ienv ienvp))
    :returns (mv (yes/no booleanp) (new-donep booleanp))
    :parents (translation-unit-comparison compare-trans-items-and-components)
    :short "Compare two @('#elif')s, taking macros into account."
    :long
    (xdoc::topstring
     (xdoc::p
      "The two expressions must be identical.
       Unless the input @('donep') flag is @('t'),
       which means that a previous condition was satisfied,
       we evaluate the condition,
       and return a possibly updated @('donep') as result.
       Based on whether this @('#elif') is selected or not,
       we either compare its items or we skip them."))
    (b* (((hash-elif elif1) elif1)
         ((hash-elif elif2) elif2)
         ((unless (equal elif1.expr elif2.expr)) (mv nil nil))
         ((when donep) (mv t t))
         ((mv erp intval) (eval-hash-if/elif-expr elif1.expr macros ienv))
         ((when erp)
          (raise "Internal error: evaluation of ~x0 fails." elif1.expr)
          (mv nil nil))
         (condp (/= intval 0)))
      (if condp
          (mv (compare-trans-item-lists elif1.items elif2.items macros ienv) t)
        (mv t nil)))
    :no-function nil
    :measure (hash-elif-count elif1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define compare-hash-elif-lists ((elifs1 hash-elif-listp)
                                   (elifs2 hash-elif-listp)
                                   (donep booleanp)
                                   (macros macro-tablep)
                                   (ienv ienvp))
    :returns (mv (yes/no booleanp) (new-donep booleanp))
    :parents (translation-unit-comparison compare-trans-items-and-components)
    :short "Compare two lists of @('#elif')s, taking macros into account."
    :long
    (xdoc::topstring
     (xdoc::p
      "We compare the two lists element-wise.
       The @('donep') flag, which must be common to both,
       is threaded through."))
    (b* (((when (endp elifs1)) (mv (endp elifs2) (bool-fix donep)))
         ((unless (consp elifs2)) (mv nil nil))
         ((mv yes/no donep) (compare-hash-elifs (car elifs1)
                                                (car elifs2)
                                                donep
                                                macros
                                                ienv))
         ((unless yes/no) (mv nil nil)))
      (compare-hash-elif-lists (cdr elifs1) (cdr elifs2) donep macros ienv))
    :measure (hash-elif-list-count elifs1))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ///

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deffixequiv-mutual compare-trans-items-and-components))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compare-trans-units ((tunit1 trans-unitp)
                             (tunit2 trans-unitp)
                             (macros macro-tablep)
                             (ienv ienvp))
  :returns (yes/no booleanp)
  :short "Compare two translation units."
  :long
  (xdoc::topstring
   (xdoc::p
    "We compare their translation items."))
  (compare-trans-item-lists (trans-unit->items tunit1)
                            (trans-unit->items tunit2)
                            macros
                            ienv))
