;; Author: Grant Jurgensen (grant@kestrel.edu)

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/terms-light/expr-calls-fn" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "kestrel/utilities/magic-macroexpand" :dir :system)
(include-book "kestrel/utilities/fake-worlds" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))


(local
 (defthm pseudo-termp-of-if-condition
   (implies (and (pseudo-termp term)
                 (eq 'if (ffn-symb term)))
            (pseudo-termp (farg1 term)))))

(local
 (defthm pseudo-termp-of-if-then-branch
   (implies (and (pseudo-termp term)
                 (eq 'if (ffn-symb term)))
            (pseudo-termp (farg2 term)))))

(local
 (defthm pseudo-termp-of-if-else-branch
   (implies (and (pseudo-termp term)
                 (eq 'if (ffn-symb term)))
            (pseudo-termp (farg3 term)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Variant on translated terms

(define find-a-base-case-translated-aux
  ((term pseudo-termp)
   (fns symbol-listp)
   (prefer-then booleanp))
  :returns (mv (erp "@('nil') when a base-case is found.")
               (all-base booleanp
                         "@('t') when @('term') is a base-case.")
               (largest pseudo-termp
                        "If @('(or erp all-base)'), then this is nil. Otherwise,
                         it is the largest (proper) subterm which is a
                         base-case."
                        :hyp :guard))
  :short "Find a base-case within a translated term."
  :long
  (xdoc::topstring
   (xdoc::p
    "If none of @('fns') appear in @('term'), @('term') is a base-case of itself.
     If @('term') is an @('if') call, then all base-cases of the ``then'' and
     ``else'' branches are base-cases of @('term').")
   (xdoc::p
    "A term may have many base-cases. We bias our search toward larger
     base-cases, and toward ``then'' branches if @('prefer-then'), and ``else''
     branches otherwise.")
   (xdoc::p
    "If @('term') is a base-case, we return it. If either of its branches are
     base-cases, we return one of those, with the aforementioned biases.
     Otherwise, we pick the largest base-case in the biased branch."))
  (b* (((unless (consp term)) (mv nil t nil))
       ((unless (eq 'if (ffn-symb term)))
        (if (expr-calls-some-fn fns term)
            (mv t nil nil)
          (mv nil t nil)))
       ((mv erp-then all-base-then largest-then)
        (find-a-base-case-translated-aux (farg2 term) fns prefer-then))
       ((mv erp-else all-base-else largest-else)
        (find-a-base-case-translated-aux (farg3 term) fns prefer-then)))
    (cond (erp-then
           (if erp-else
               (mv erp-else nil nil)
             (mv nil nil (if all-base-else
                             (farg3 term)
                           largest-else))))
          (erp-else
           (mv nil nil (if all-base-then
                           (farg2 term)
                         largest-then)))
          (all-base-then
           (if all-base-else
               (if (not (expr-calls-some-fn fns (farg1 term)))
                   (mv nil t nil)
                 (mv nil nil (if prefer-then
                                 (farg2 term)
                               (farg3 term))))
             (mv nil nil (farg2 term))))
          (all-base-else
           (mv nil nil (farg3 term)))
          (prefer-then (mv nil nil largest-then))
          (t (mv nil nil largest-else)))))

(define find-a-base-case-translated
  ((term pseudo-termp)
   (fns symbol-listp)
   (prefer-then booleanp))
  :returns (base-case "Either a @(tsee pseudo-termp) representing the base-case,
                       or a hard error. A hard error should not occur if
                       @('term') is the translated body of a valid function, and
                       @('fns') includes only symbols corresponding to the
                       function or functions defined in mutual recursion with the
                       function.")
  :short "Find a base-case within a translated term."
  (mv-let (erp all-base largest)
          (find-a-base-case-translated-aux term fns prefer-then)
          (cond (erp (hard-error 'find-a-base-case-translated
                                 "Cannot find a base case!"
                                 nil))
                (all-base term)
                (t largest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Variant on untranslated terms

(define untranslated-expr-calls-some-fn
  ((fns symbol-listp)
   term
   (wrld plist-worldp))
  :mode :program
  (expr-calls-some-fn fns (translate-term term 'top wrld)))

(define find-a-base-case-aux
  (term
   (fns symbol-listp)
   (prefer-then booleanp)
   (wrld plist-worldp)
   state)
  :returns (mv (erp "@('nil') when a base-case is found.")
               (all-base "A @(tsee booleanp). @('t') when @('term') is a
                          base-case.")
               (largest "A@(tsee pseudo-termp). If @('(or erp all-base)'), then
                         this is nil. Otherwise, it is the largest (proper)
                         subterm which is a base-case."))
  :mode :program
  :short "Find a base-case within an untranslated term."
  :long
  (xdoc::topstring
   (xdoc::p
    "If none of @('fns') appear in @('term'), @('term') is a base-case of itself.
     If @('term') macro-expands to an @('if') call, then all base-cases of the
     ``then'' and ``else'' branches are base-cases of @('term').")
   (xdoc::p
    "A term may have many base-cases. We bias our search toward larger
     base-cases, and toward ``then'' branches if @('prefer-then'), and ``else''
     branches otherwise.")
   (xdoc::p
    "If @('term') is a base-case, we return it. If either of its branches are
     base-cases, we return one of those, with the aforementioned biases.
     Otherwise, we pick the largest base-case in the biased branch."))
  (b* (((unless (consp term)) (mv nil t nil))
       ((mv erp term) (magic-macroexpand term 'find-a-base-case wrld state))
       ((when erp) (mv erp nil nil))
       ((unless (consp term)) (mv nil t nil))
       ((unless (eq 'if (ffn-symb term)))
        (if (untranslated-expr-calls-some-fn fns term wrld)
            (mv t nil nil)
          (mv nil t nil)))
       ((mv erp-then all-base-then largest-then)
        (find-a-base-case-aux (farg2 term) fns prefer-then wrld state))
       ((mv erp-else all-base-else largest-else)
        (find-a-base-case-aux (farg3 term) fns prefer-then wrld state)))
    (cond (erp-then
           (if erp-else
               (mv erp-else nil nil)
             (mv nil nil (if all-base-else
                             (farg3 term)
                           largest-else))))
          (erp-else
           (mv nil nil (if all-base-then
                           (farg2 term)
                         largest-then)))
          (all-base-then
           (if all-base-else
               (if (not (untranslated-expr-calls-some-fn fns (farg1 term) wrld))
                   (mv nil t nil)
                 (mv nil nil (if prefer-then
                                 (farg2 term)
                               (farg3 term))))
             (mv nil nil (farg2 term))))
          (all-base-else
           (mv nil nil (farg3 term)))
          (prefer-then (mv nil nil largest-then))
          (t (mv nil nil largest-else)))))

(define find-a-base-case
  (term
   (fns symbol-listp)
   (fake-fns (and (symbol-alistp fake-fns)
                  (nat-listp (strip-cdrs fake-fns))))
   (prefer-then booleanp)
   state)
  :returns (base-case "Either a @(tsee pseudo-termp) representing the base-case,
                       or a hard error. A hard error should not occur if
                       @('term') is the body of a valid function, and @('fns')
                       includes only symbols corresponding to the function or
                       functions defined in mutual recursion with the function.")
  :mode :program
  (mv-let (erp all-base largest)
          (find-a-base-case-aux term
                                (append fns (strip-cars fake-fns))
                                prefer-then
                                (add-fake-fns-to-world fake-fns (w state))
                                state)
          (cond (erp (hard-error 'find-a-base-case "Cannot find a base case!" nil))
                (all-base term)
                (t largest))))
