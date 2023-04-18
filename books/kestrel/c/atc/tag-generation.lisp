; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "tag-tables")
(include-book "types-to-recognizers")

(include-book "symbolic-execution-rules/syntaxp")

(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)

(local (include-book "kestrel/std/system/good-atom-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-tag-generation
  :parents (atc-event-and-code-generation)
  :short "Generation of C tag declarations (currently just structures)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-member-read-thms ((tag identp)
                                      (recognizer symbolp)
                                      (fixer symbolp)
                                      (fixer-recognizer-thm symbolp)
                                      (not-error-thm symbolp)
                                      (meminfo defstruct-member-infop)
                                      (names-to-avoid symbol-listp)
                                      (wrld plist-worldp))
  :returns (mv (local-events pseudo-event-form-listp)
               (member-read-thms symbol-listp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorems to rewrite
          the execution of certain pure expressions to structure reads,
          for a member of a structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This class of theorems are the structure counterpart of
     the ones that rewrite @(tsee exec-arrsub) to array readers,
     generated in @(see atc-exec-arrsub-rules-generation).")
   (xdoc::p
    "For a scalar member (which must have integer type),
     we generate two theorems that
     rewrite calls of @(tsee exec-member) and @(tsee exec-memberp)
     to calls of the reader.")
   (xdoc::p
    "For an array member (which must have integer element type),
     we generate 20 theorems,
     for each integer index type (10)
     and for each of @(tsee exec-member) and @(tsee exec-memberp).
     The theorems rewrite calls of
     @('exec-arrsub-of-member') or @('exec-arrsub-of-memberp')
     (see @(see atc-exec-expr-pure-rules))
     to calls of the readers.
     The generation of these theorems relies on the fact that
     the order of the readers and the checkers matches the order of
     the types in @(tsee *nonchar-integer-types*).
     Note that the @(tsee defstruct-member-info)
     contains 11 readers and 11 checkers,
     where the first reader and checker operate on ACL2 integers,
     while the other 10 readers and 10 checkers operate on C integers.
     We iterate through the 10 readers and checkers on C integers,
     while using the reader and checker on ACL2 integers at each iteration.")
   (xdoc::p
    "If the structure type has a flexible array member,
     we avoid generating theorems for accessing members by structure value,
     because in ATC-generated code we only allow access by pointer."))
  (b* ((memtype (defstruct-member-info->memtype meminfo))
       (memname (member-type->name memtype))
       (type (member-type->type memtype))
       (length (defstruct-member-info->length meminfo))
       (reader (defstruct-member-info->reader meminfo))
       (reader-element (defstruct-member-info->reader-element meminfo))
       (readers (defstruct-member-info->readers meminfo))
       (checker (defstruct-member-info->checker meminfo))
       (checkers (defstruct-member-info->checkers meminfo))
       ((when (type-nonchar-integerp type))
        (b* ((thm-member-name (pack 'exec-member-read-when-
                                    recognizer
                                    '-and-
                                    (ident->name memname)))
             ((mv thm-member-name names-to-avoid)
              (fresh-logical-name-with-$s-suffix thm-member-name
                                                 nil
                                                 names-to-avoid
                                                 wrld))
             (thm-memberp-name (pack 'exec-memberp-read-when-
                                     recognizer
                                     '-and-
                                     (ident->name memname)))
             ((mv thm-memberp-name names-to-avoid)
              (fresh-logical-name-with-$s-suffix thm-memberp-name
                                                 nil
                                                 names-to-avoid
                                                 wrld))
             (formula-member
              `(implies (and ,(atc-syntaxp-hyp-for-expr-pure 'struct)
                             (,recognizer struct))
                        (equal (exec-member (expr-value struct objdes)
                                            (ident ,(ident->name memname)))
                               (expr-value (,reader struct)
                                           (if (objdesign-option-fix objdes)
                                               (objdesign-member
                                                (objdesign-option-fix objdes)
                                                (ident ,(ident->name memname)))
                                             nil)))))
             (formula-memberp
              `(implies (and ,(atc-syntaxp-hyp-for-expr-pure 'ptr)
                             (valuep ptr)
                             (value-case ptr :pointer)
                             (value-pointer-validp ptr)
                             (equal (value-pointer->reftype ptr)
                                    (type-struct (ident ,(ident->name tag))))
                             (equal struct
                                    (read-object (value-pointer->designator ptr)
                                                 compst))
                             (,recognizer struct))
                        (equal (exec-memberp (expr-value ptr objdes)
                                             (ident ,(ident->name memname))
                                             compst)
                               (expr-value (,reader struct)
                                           (objdesign-member
                                            (value-pointer->designator ptr)
                                            (ident ,(ident->name memname)))))))
             (value-kind-when-typep (pack 'value-kind-when-
                                          (integer-type-to-fixtype type)
                                          'p))
             (valuep-when-typep (pack 'valuep-when-
                                      (integer-type-to-fixtype type)
                                      'p))
             (hints `(("Goal"
                       :in-theory
                       '(exec-member
                         exec-memberp
                         not-errorp-when-valuep
                         value-resultp-when-valuep
                         value-result-fix-when-value-resultp
                         ,recognizer
                         ,reader
                         ,not-error-thm
                         ,fixer-recognizer-thm
                         value-struct-read
                         ,value-kind-when-typep
                         (:e ident)
                         expr-value->value-of-expr-value
                         expr-value->object-of-expr-value
                         value-fix-when-valuep
                         not-errorp-when-valuep
                         ,valuep-when-typep
                         (:e c::objdesign-option-fix)
                         apconvert-expr-value-when-not-value-array
                         expr-valuep-of-expr-value
                         not-errorp-when-expr-valuep))))
             ((mv event-member &)
              (evmac-generate-defthm thm-member-name
                                     :formula formula-member
                                     :hints hints
                                     :enable nil))
             ((mv event-memberp &)
              (evmac-generate-defthm thm-memberp-name
                                     :formula formula-memberp
                                     :hints hints
                                     :enable nil)))
          (mv (list event-member event-memberp)
              (list thm-member-name thm-memberp-name)
              names-to-avoid)))
       ((unless (type-case type :array))
        (prog2$
         (raise "Internal error: member type ~x0." type)
         (mv nil nil nil)))
       (elemtype (type-array->of type))
       ((unless (type-nonchar-integerp elemtype))
        (prog2$
         (raise "Internal error: array member element type ~x0." elemtype)
         (mv nil nil nil)))
       (thm-member-name (pack 'exec-member-read-when-
                              recognizer
                              '-and-
                              (ident->name memname)
                              '-element))
       ((mv thm-member-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix thm-member-name
                                           nil
                                           names-to-avoid
                                           wrld))
       (thm-memberp-name (pack 'exec-memberp-read-when-
                               recognizer
                               '-and-
                               (ident->name memname)
                               '-element))
       ((mv thm-memberp-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix thm-memberp-name
                                           nil
                                           names-to-avoid
                                           wrld))
       (formula-member
        `(implies
          (and (,recognizer struct)
               (cintegerp index)
               (,checker index ,@(and length (list 'struct)))
               (objdesignp objdes-struct)
               (equal (read-object objdes-struct compst) struct))
          (equal (exec-arrsub-of-member (expr-value struct objdes-struct)
                                        (ident ,(ident->name memname))
                                        (expr-value index objdes-index)
                                        compst)
                 (expr-value (,reader-element index struct)
                             (objdesign-element
                              (objdesign-member objdes-struct
                                                (ident ,(ident->name memname)))
                              (value-integer->get index))))))
       (formula-memberp
        `(implies
          (and (valuep ptr)
               (value-case ptr :pointer)
               (value-pointer-validp ptr)
               (equal (value-pointer->reftype ptr)
                      (type-struct (ident ,(ident->name tag))))
               (equal struct
                      (read-object (value-pointer->designator ptr) compst))
               (,recognizer struct)
               (cintegerp index)
               (,checker index ,@(and length (list 'struct))))
          (equal (exec-arrsub-of-memberp (expr-value ptr objdes-ptr)
                                         (ident ,(ident->name memname))
                                         (expr-value index objdes-index)
                                         compst)
                 (expr-value (,reader-element index struct)
                             (objdesign-element
                              (objdesign-member
                               (value-pointer->designator ptr)
                               (ident ,(ident->name memname)))
                              (value-integer->get index))))))
       (elemfixtype (integer-type-to-fixtype elemtype))
       (valuep-when-elemtype-arrayp
        (pack 'valuep-when- elemfixtype '-arrayp))
       (value-kind-when-elemtype-arrayp
        (pack 'value-kind-when- elemfixtype '-arrayp))
       (value-array->elemtype-when-elemtype-arrayp
        (pack 'value-array->elemtype-when- elemfixtype '-arrayp))
       (value-array-read-when-elemtype-arrayp
        (pack 'value-array-read-when- elemfixtype '-arrayp))
       (apconvert-expr-value-when-elemtype-arrayp
        (pack 'apconvert-expr-value-when- elemfixtype '-arrayp))
       (elemfixtype-array-index-okp (pack elemfixtype '-array-index-okp))
       (type-elemfixtype (pack 'type- elemfixtype))
       (elemfixtypep-of-elemfixtype-array-read
        (pack elemfixtype 'p-of- elemfixtype '-array-read))
       (valuep-when-elemfixtypep (pack 'valuep-when- elemfixtype 'p))
       (theory-member
        `(exec-arrsub-of-member
          apconvert-expr-value-when-not-value-array-alt
          expr-value->value-of-expr-value
          expr-value->object-of-expr-value
          value-fix-when-valuep
          ,recognizer
          expr-value-fix-when-expr-valuep
          expr-valuep-of-expr-value
          not-errorp-when-expr-valuep
          value-struct-read
          (:e ident)
          not-errorp-when-valuep
          ,valuep-when-elemtype-arrayp
          ,apconvert-expr-value-when-elemtype-arrayp
          objdesign-option-fix
          not-nil-when-objdesignp
          objdesign-fix-when-objdesignp
          return-type-of-objdesign-member
          return-type-of-value-pointer
          value-pointer-validp-of-value-pointer
          return-type-of-pointer-valid
          value-pointer->designator-of-value-pointer
          pointer-valid->get-of-pointer-valid
          read-object-of-objdesign-member
          ,value-kind-when-elemtype-arrayp
          value-pointer->reftype-of-value-pointer
          ,value-array->elemtype-when-elemtype-arrayp
          (:e type-fix)
          (:e ,type-elemfixtype)
          value-kind-not-array-when-cintegerp
          valuep-when-cintegerp
          value-integerp-when-cintegerp
          value-integer->get-when-cintegerp
          ,checker
          integer-range-p
          ,value-array-read-when-elemtype-arrayp
          ,elemfixtype-array-index-okp
          ,elemfixtypep-of-elemfixtype-array-read
          ,valuep-when-elemfixtypep
          ,reader-element
          ,reader
          ,fixer
          ,@(and length (list length))))
       (theory-memberp
        `(exec-arrsub-of-memberp
          apconvert-expr-value-when-not-value-array-alt
          expr-value->value-of-expr-value
          value-fix-when-valuep
          ,recognizer
          expr-value-fix-when-expr-valuep
          expr-valuep-of-expr-value
          not-errorp-when-expr-valuep
          value-struct-read
          (:e ident)
          not-errorp-when-valuep
          ,valuep-when-elemtype-arrayp
          ,apconvert-expr-value-when-elemtype-arrayp
          objdesign-fix-when-objdesignp
          return-type-of-objdesign-member
          return-type-of-value-pointer
          value-pointer-validp-of-value-pointer
          return-type-of-pointer-valid
          value-pointer->designator-of-value-pointer
          pointer-valid->get-of-pointer-valid
          read-object-of-objdesign-member
          ,value-kind-when-elemtype-arrayp
          value-pointer->reftype-of-value-pointer
          ,value-array->elemtype-when-elemtype-arrayp
          (:e type-fix)
          (:e ,type-elemfixtype)
          value-kind-not-array-when-cintegerp
          valuep-when-cintegerp
          value-integerp-when-cintegerp
          value-integer->get-when-cintegerp
          ,checker
          integer-range-p
          ,value-array-read-when-elemtype-arrayp
          ,elemfixtype-array-index-okp
          ,elemfixtypep-of-elemfixtype-array-read
          ,valuep-when-elemfixtypep
          ,reader-element
          ,reader
          ,fixer
          ,@(and length (list length))))
       ((mv event-member &)
        (evmac-generate-defthm thm-member-name
                               :formula formula-member
                               :hints `(("Goal" :in-theory ',theory-member))
                               :enable nil))
       ((mv event-memberp &)
        (evmac-generate-defthm thm-memberp-name
                               :formula formula-memberp
                               :hints `(("Goal" :in-theory ',theory-memberp))
                               :enable nil))
       ((mv more-events
            member-read-thms
            names-to-avoid)
        (atc-gen-tag-member-read-thms-aux tag
                                          recognizer
                                          fixer-recognizer-thm
                                          memname
                                          elemtype
                                          *nonchar-integer-types*
                                          (car readers)
                                          (car checkers)
                                          (cdr readers)
                                          (cdr checkers)
                                          length
                                          thm-member-name
                                          thm-memberp-name
                                          names-to-avoid
                                          wrld)))
    (mv (list* event-member event-memberp more-events)
        member-read-thms
        names-to-avoid))

  :prepwork
  ((define atc-gen-tag-member-read-thms-aux ((tag identp)
                                             (recognizer symbolp)
                                             (fixer-recognizer-thm symbolp)
                                             (memname identp)
                                             (elemtype typep)
                                             (indextypes type-listp)
                                             (reader-acl2int symbolp)
                                             (checker-acl2int symbolp)
                                             (readers symbol-listp)
                                             (checkers symbol-listp)
                                             (length symbolp)
                                             (reader-member-thm symbolp)
                                             (reader-memberp-thm symbolp)
                                             (names-to-avoid symbol-listp)
                                             (wrld plist-worldp))
     :guard (and (type-nonchar-integerp elemtype)
                 (type-nonchar-integer-listp indextypes))
     :returns (mv (local-events pseudo-event-form-listp)
                  (member-read-thms symbol-listp)
                  (updated-names-to-avoid symbol-listp
                                          :hyp (symbol-listp names-to-avoid)))
     :parents nil
     (b* (((when (endp indextypes)) (mv nil nil nil))
          (indextype (car indextypes))
          (reader (car readers))
          (checker (car checkers))
          (indexfixtype (integer-type-to-fixtype indextype))
          (indextypep (pack indexfixtype 'p))
          (thm-member-name (pack 'exec-member-read-when-
                                 recognizer
                                 '-and-
                                 (ident->name memname)
                                 '-
                                 indexfixtype))
          ((mv thm-member-name names-to-avoid)
           (fresh-logical-name-with-$s-suffix thm-member-name
                                              nil
                                              names-to-avoid
                                              wrld))
          (thm-memberp-name (pack 'exec-memberp-read-when-
                                  recognizer
                                  '-and-
                                  (ident->name memname)
                                  '-
                                  indexfixtype))
          ((mv thm-memberp-name names-to-avoid)
           (fresh-logical-name-with-$s-suffix thm-memberp-name
                                              nil
                                              names-to-avoid
                                              wrld))
          (check-hyp (if length
                         `(,checker index struct)
                       `(,checker index)))
          (formula-member
           `(implies (and ,(atc-syntaxp-hyp-for-expr-pure 'struct)
                          (,recognizer struct)
                          (,indextypep index)
                          ,check-hyp
                          (objdesignp objdes-struct)
                          (equal (read-object objdes-struct compst) struct))
                     (equal (exec-arrsub-of-member
                             (expr-value struct objdes-struct)
                             (ident ,(ident->name memname))
                             (expr-value index objdes-index)
                             compst)
                            (expr-value (,reader index struct)
                                        (objdesign-element
                                         (objdesign-member
                                          objdes-struct
                                          (ident ,(ident->name memname)))
                                         (value-integer->get index))))))
          (formula-memberp
           `(implies (and ,(atc-syntaxp-hyp-for-expr-pure 'ptr)
                          (valuep ptr)
                          (value-case ptr :pointer)
                          (value-pointer-validp ptr)
                          (equal (value-pointer->reftype ptr)
                                 (type-struct (ident ,(ident->name tag))))
                          (equal struct
                                 (read-object (value-pointer->designator ptr)
                                              compst))
                          (,recognizer struct)
                          (,indextypep index)
                          ,check-hyp)
                     (equal (exec-arrsub-of-memberp
                             (expr-value ptr objdes-ptr)
                             (ident ,(ident->name memname))
                             (expr-value index objdes-index)
                             compst)
                            (expr-value (,reader index struct)
                                        (objdesign-element
                                         (objdesign-member
                                          (value-pointer->designator ptr)
                                          (ident ,(ident->name memname)))
                                         (value-integer->get index))))))
          (reader-alt-def (packn-pos (list reader '-alt-def) reader))
          (checker-alt-def (packn-pos (list checker '-alt-def) checker))
          (hints-member `(("Goal"
                           :in-theory '(,reader-member-thm
                                        ,reader-alt-def
                                        ,checker-alt-def
                                        cintegerp))))
          (hints-memberp `(("Goal"
                            :in-theory '(,reader-memberp-thm
                                         ,reader-alt-def
                                         ,checker-alt-def
                                         cintegerp))))
          ((mv event-member &)
           (evmac-generate-defthm thm-member-name
                                  :formula formula-member
                                  :hints hints-member
                                  :enable nil))
          ((mv event-memberp &)
           (evmac-generate-defthm thm-memberp-name
                                  :formula formula-memberp
                                  :hints hints-memberp
                                  :enable nil))
          ((mv events thm-names names-to-avoid)
           (atc-gen-tag-member-read-thms-aux tag
                                             recognizer
                                             fixer-recognizer-thm
                                             memname
                                             elemtype
                                             (cdr indextypes)
                                             reader-acl2int
                                             checker-acl2int
                                             (cdr readers)
                                             (cdr checkers)
                                             length
                                             reader-member-thm
                                             reader-memberp-thm
                                             names-to-avoid
                                             wrld)))
       (mv (append (and (not length)
                        (list event-member))
                   (list event-memberp)
                   events)
           (append (and (not length)
                        (list thm-member-name))
                   (list thm-memberp-name)
                   thm-names)
           names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-member-read-all-thms ((tag identp)
                                          (recognizer symbolp)
                                          (fixer symbolp)
                                          (fixer-recognizer-thm symbolp)
                                          (not-error-thm symbolp)
                                          (meminfos defstruct-member-info-listp)
                                          (names-to-avoid symbol-listp)
                                          (wrld plist-worldp))
  :returns (mv (local-events pseudo-event-form-listp)
               (member-read-thms symbol-listp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorems to rewrite
          the execution of certain pure expressions to structure reads,
          for all the members of a structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This relies on @('readers') to be in the same order as @('members')."))
  (b* (((when (endp meminfos)) (mv nil nil names-to-avoid))
       ((mv events thms names-to-avoid)
        (atc-gen-tag-member-read-thms tag
                                      recognizer
                                      fixer
                                      fixer-recognizer-thm
                                      not-error-thm
                                      (car meminfos)
                                      names-to-avoid
                                      wrld))
       ((mv more-events more-thms names-to-avoid)
        (atc-gen-tag-member-read-all-thms tag
                                          recognizer
                                          fixer
                                          fixer-recognizer-thm
                                          not-error-thm
                                          (cdr meminfos)
                                          names-to-avoid
                                          wrld)))
    (mv (append events more-events)
        (append thms more-thms)
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-member-write-thms ((tag identp)
                                       (recognizer symbolp)
                                       (fixer symbolp)
                                       (fixer-recognizer-thm symbolp)
                                       (not-error-thm symbolp)
                                       (type-of-value-thm symbolp)
                                       (meminfo defstruct-member-infop)
                                       (names-to-avoid symbol-listp)
                                       (wrld plist-worldp))
  :returns (mv (local-events pseudo-event-form-listp)
               (member-write-thms symbol-listp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorems to rewrite
          the execution of certain assignment expressions to structure writes,
          for a member of a structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This class of theorems are the structure counterpart of
     the ones that rewrite @(tsee exec-expr-asg)
     that have @(':arrsub') left expressions
     to array writers,
     in @(see atc-exec-expr-asg-arrsub-rules-generation).")
   (xdoc::p
    "For a scalar member (which must have integer type),
     we generate two theorems that
     rewrite calls of @(tsee exec-expr-asg),
     where the assignee is a @(':member') or @(':memberp') expression,
     to calls of the writer.")
   (xdoc::p
    "For an array member (which must have integer element type),
     we generate 10 theorems, one for each integer index type.
     The theorem rewrites certain calls of @(tsee exec-expr-asg)
     to calls of the writers.
     The generation of these theorems relies on the fact that
     the order of the writers and the checkers matches the order of
     the types in @(tsee *nonchar-integer-types*).
     Note that the @(tsee defstruct-member-info)
     contains 11 writers and 11 checkers,
     where the first writer and checker operate on ACL2 integers,
     while the other 10 writers and 10 checkers operate on C integers.
     We iterate through the 10 writers and checkers on C integers,
     while using the writer and checker on ACL2 integers at each iteration.")
   (xdoc::p
    "If the structure type has a flexible array member,
     we avoid generating theorems for accessing members by structure value,
     because in ATC-generated code we only allow access by pointer."))
  (b* ((memtype (defstruct-member-info->memtype meminfo))
       (memname (member-type->name memtype))
       (type (member-type->type memtype))
       (length (defstruct-member-info->length meminfo))
       (reader (defstruct-member-info->reader meminfo))
       (reader-element (defstruct-member-info->reader-element meminfo))
       (writer (defstruct-member-info->writer meminfo))
       (writer-element (defstruct-member-info->writer-element meminfo))
       (writers (defstruct-member-info->writers meminfo))
       (checker (defstruct-member-info->checker meminfo))
       (checkers (defstruct-member-info->checkers meminfo))
       ((when (type-nonchar-integerp type))
        (b* ((thm-member-name (pack 'exec-member-write-when-
                                    recognizer
                                    '-and-
                                    (ident->name memname)))
             ((mv thm-member-name names-to-avoid)
              (fresh-logical-name-with-$s-suffix thm-member-name
                                                 nil
                                                 names-to-avoid
                                                 wrld))
             (thm-memberp-name (pack 'exec-memberp-write-when-
                                     recognizer
                                     '-and-
                                     (ident->name memname)))
             ((mv thm-memberp-name names-to-avoid)
              (fresh-logical-name-with-$s-suffix thm-memberp-name
                                                 nil
                                                 names-to-avoid
                                                 wrld))
             (typep (type-to-recognizer type wrld))
             ((unless typep)
              (raise "Internal error: unsupported member type ~x0." type)
              (mv nil nil nil))
             (formula-member
              `(implies (and (syntaxp (quotep e))
                             (equal (expr-kind e) :binary)
                             (equal (binop-kind (expr-binary->op e)) :asg)
                             (equal left (expr-binary->arg1 e))
                             (equal right (expr-binary->arg2 e))
                             (equal (expr-kind left) :member)
                             (equal target (expr-member->target left))
                             (equal member (expr-member->name left))
                             (equal (expr-kind target) :ident)
                             (equal member (ident ,(ident->name memname)))
                             (not (zp limit))
                             (equal var (expr-ident->get target))
                             (equal struct (read-var var compst))
                             (,recognizer struct)
                             (equal eval (exec-expr-pure right compst))
                             (expr-valuep eval)
                             (equal val (expr-value->value eval))
                             (,typep val))
                        (equal (exec-expr-asg e compst fenv limit)
                               (write-var var
                                          (,writer val struct)
                                          compst))))
             (formula-memberp
              `(implies (and (syntaxp (quotep e))
                             (equal (expr-kind e) :binary)
                             (equal (binop-kind (expr-binary->op e)) :asg)
                             (equal left (expr-binary->arg1 e))
                             (equal right (expr-binary->arg2 e))
                             (equal (expr-kind left) :memberp)
                             (equal target (expr-memberp->target left))
                             (equal member (expr-memberp->name left))
                             (equal (expr-kind target) :ident)
                             (equal member (ident ,(ident->name memname)))
                             (not (zp limit))
                             (equal ptr (read-var (expr-ident->get target)
                                                  compst))
                             (valuep ptr)
                             (value-case ptr :pointer)
                             (value-pointer-validp ptr)
                             (equal (value-pointer->reftype ptr)
                                    (type-struct (ident ,(ident->name tag))))
                             (equal struct
                                    (read-object (value-pointer->designator ptr)
                                                 compst))
                             (,recognizer struct)
                             (equal eval (exec-expr-pure right compst))
                             (expr-valuep eval)
                             (equal val (expr-value->value eval))
                             (,typep val))
                        (equal (exec-expr-asg e compst fenv limit)
                               (write-object (value-pointer->designator ptr)
                                             (,writer val struct)
                                             compst))))
             (writer-return-thm
              (defstruct-member-info->writer-return-thm meminfo))
             (hints-member
              `(("Goal"
                 :in-theory
                 '(exec-expr-asg
                   not-errorp-when-valuep
                   valuep-when-ucharp
                   valuep-when-scharp
                   valuep-when-ushortp
                   valuep-when-sshortp
                   valuep-when-uintp
                   valuep-when-sintp
                   valuep-when-ulongp
                   valuep-when-slongp
                   valuep-when-ullongp
                   valuep-when-sllongp
                   consp-when-ucharp
                   consp-when-scharp
                   consp-when-ushortp
                   consp-when-sshortp
                   consp-when-uintp
                   consp-when-sintp
                   consp-when-ulongp
                   consp-when-slongp
                   consp-when-ullongp
                   consp-when-sllongp
                   uchar-fix-when-ucharp
                   schar-fix-when-scharp
                   ushort-fix-when-ushortp
                   sshort-fix-when-sshortp
                   uint-fix-when-uintp
                   sint-fix-when-sintp
                   ulong-fix-when-ulongp
                   slong-fix-when-slongp
                   ullong-fix-when-ullongp
                   sllong-fix-when-sllongp
                   ,writer
                   ,not-error-thm
                   ,recognizer
                   ,fixer-recognizer-thm
                   ,type-of-value-thm
                   not-errorp-when-expr-valuep
                   apconvert-expr-value-when-not-value-array-alt
                   value-kind-when-ucharp
                   value-kind-when-scharp
                   value-kind-when-ushortp
                   value-kind-when-sshortp
                   value-kind-when-uintp
                   value-kind-when-sintp
                   value-kind-when-ulongp
                   value-kind-when-slongp
                   value-kind-when-ullongp
                   value-kind-when-sllongp
                   expr-value-fix-when-expr-valuep
                   exec-ident
                   exec-member
                   read-object-of-objdesign-of-var-to-read-var
                   write-object-of-objdesign-of-var-to-write-var
                   write-object
                   value-struct-read
                   acl2::mv-nth-of-cons
                   expr-fix-when-exprp
                   exprp-of-expr-binary->arg1
                   exprp-of-expr-member->target
                   expr-valuep-of-expr-value
                   expr-value->value-of-expr-value
                   expr-value->object-of-expr-value
                   value-fix-when-valuep
                   objdesign-option-fix
                   objdesign-fix-when-objdesignp
                   return-type-of-objdesign-member
                   objdesign-of-var-when-valuep-of-read-var
                   objdesignp-of-objdesign-of-var-when-valuep-of-read-var
                   objdesign-member->super-of-objdesign-member
                   objdesign-member->name-of-objdesign-member
                   (:e zp)
                   (:e ident)
                   (:e ident-fix)
                   (:t objdesign-member))
                 :expand
                 ((exec-expr-pure (expr-binary->arg1 e)
                                  compst)
                  (exec-expr-pure (expr-member->target (expr-binary->arg1 e))
                                  compst))
                 :use
                 (:instance
                  ,writer-return-thm
                  (val (expr-value->value
                        (exec-expr-pure (expr-binary->arg2 e) compst)))
                  (struct (b* ((left (expr-binary->arg1 e))
                               (target (expr-member->target left))
                               (var (expr-ident->get target))
                               (struct (read-var var compst)))
                            struct))))))
             (hints-memberp
              `(("Goal"
                 :in-theory
                 '(exec-expr-asg
                   not-errorp-when-valuep
                   valuep-when-ucharp
                   valuep-when-scharp
                   valuep-when-ushortp
                   valuep-when-sshortp
                   valuep-when-uintp
                   valuep-when-sintp
                   valuep-when-ulongp
                   valuep-when-slongp
                   valuep-when-ullongp
                   valuep-when-sllongp
                   consp-when-ucharp
                   consp-when-scharp
                   consp-when-ushortp
                   consp-when-sshortp
                   consp-when-uintp
                   consp-when-sintp
                   consp-when-ulongp
                   consp-when-slongp
                   consp-when-ullongp
                   consp-when-sllongp
                   uchar-fix-when-ucharp
                   schar-fix-when-scharp
                   ushort-fix-when-ushortp
                   sshort-fix-when-sshortp
                   uint-fix-when-uintp
                   sint-fix-when-sintp
                   ulong-fix-when-ulongp
                   slong-fix-when-slongp
                   ullong-fix-when-ullongp
                   sllong-fix-when-sllongp
                   ,writer
                   ,not-error-thm
                   ,recognizer
                   ,fixer-recognizer-thm
                   ,type-of-value-thm
                   not-errorp-when-expr-valuep
                   apconvert-expr-value-when-not-value-array-alt
                   value-kind-when-ucharp
                   value-kind-when-scharp
                   value-kind-when-ushortp
                   value-kind-when-sshortp
                   value-kind-when-uintp
                   value-kind-when-sintp
                   value-kind-when-ulongp
                   value-kind-when-slongp
                   value-kind-when-ullongp
                   value-kind-when-sllongp
                   expr-value-fix-when-expr-valuep
                   exec-ident
                   exec-memberp
                   read-object-of-objdesign-of-var-to-read-var
                   value-struct-read
                   acl2::mv-nth-of-cons
                   expr-fix-when-exprp
                   exprp-of-expr-binary->arg1
                   exprp-of-expr-memberp->target
                   expr-valuep-of-expr-value
                   expr-value->value-of-expr-value
                   expr-value->object-of-expr-value
                   value-fix-when-valuep
                   objdesign-of-var-when-valuep-of-read-var
                   objdesign-option-fix
                   objdesign-fix-when-objdesignp
                   return-type-of-objdesign-member
                   objdesignp-of-value-pointer->designator
                   objdesign-member->super-of-objdesign-member
                   objdesign-member->name-of-objdesign-member
                   (:e zp)
                   (:e ident)
                   (:e ident-fix)
                   (:t objdesign-member))
                 :expand
                 ((exec-expr-pure (expr-binary->arg1 e) compst)
                  (exec-expr-pure (expr-memberp->target (expr-binary->arg1 e))
                                  compst)
                  (:free (x y z w) (write-object (objdesign-member x y) z w))
                  (:free (x y) (read-object (objdesign-member->super x) y)))
                 :use
                 (:instance
                  ,writer-return-thm
                  (val (expr-value->value
                        (exec-expr-pure (expr-binary->arg2 e) compst)))
                  (struct (b* ((left (expr-binary->arg1 e))
                               (target (expr-memberp->target left))
                               (ptr (read-var (expr-ident->get target)
                                              compst))
                               (struct (read-object
                                        (value-pointer->designator ptr)
                                        compst)))
                            struct))))))
             ((mv event-member &)
              (evmac-generate-defthm thm-member-name
                                     :formula formula-member
                                     :hints hints-member
                                     :enable nil))
             ((mv event-memberp &)
              (evmac-generate-defthm thm-memberp-name
                                     :formula formula-memberp
                                     :hints hints-memberp
                                     :enable nil)))
          (mv (list event-member event-memberp)
              (list thm-member-name thm-memberp-name)
              names-to-avoid)))
       ((unless (type-case type :array))
        (prog2$
         (raise "Internal error: member type ~x0." type)
         (mv nil nil nil)))
       (elemtype (type-array->of type))
       ((unless (type-nonchar-integerp elemtype))
        (prog2$
         (raise "Internal error: array member element type ~x0." elemtype)
         (mv nil nil nil)))
       (writer-return-thms (defstruct-member-info->writer-return-thms meminfo))
       (writer-return-thm (car writer-return-thms))
       (thm-member-name (pack 'exec-member-write-when-
                              recognizer
                              '-and-
                              (ident->name memname)
                              '-element))
       ((mv thm-member-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix thm-member-name
                                           nil
                                           names-to-avoid
                                           wrld))
       (thm-memberp-name (pack 'exec-memberp-write-when-
                               recognizer
                               '-and-
                               (ident->name memname)
                               '-element))
       ((mv thm-memberp-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix thm-memberp-name
                                           nil
                                           names-to-avoid
                                           wrld))
       (elemfixtype (integer-type-to-fixtype elemtype))
       (elemfixtypep (pack elemfixtype 'p))
       (valuep-when-elemtype-arrayp (pack 'valuep-when- elemfixtype '-arrayp))
       (value-kind-when-elemfixtype-arrayp
        (pack 'value-kind-when- elemfixtype '-arrayp))
       (value-kind-when-elemfixtypep (pack 'value-kind-when- elemfixtypep))
       (value-array-write-when-elemfixtype-arrayp
        (pack 'value-array-write-when- elemfixtype '-arrayp))
       (elemfixtype-array-index-okp (pack elemfixtype '-array-index-okp))
       (elemfixtype-arrayp-of-elemfixtype-array-write
        (pack elemfixtype '-arrayp-of- elemfixtype '-array-write))
       (elemfixtype-array-fix-when-elemfixtype-arrayp
        (pack elemfixtype '-array-fix-when- elemfixtype '-arrayp))
       (elemfixtype-array-length-of-elemfixtype-array-write
        (pack elemfixtype '-array-length-of- elemfixtype '-array-write))
       (type-of-value-when-elemfixtype-arrayp
        (pack 'type-of-value-when- elemfixtype '-arrayp))
       (value-array->length-when-elemfixtype-arrayp
        (pack 'value-array->length-when- elemfixtype '-arrayp))
       (formula-member
        `(implies
          (and (equal (expr-kind e) :binary)
               (equal (binop-kind (expr-binary->op e)) :asg)
               (equal left (expr-binary->arg1 e))
               (equal right (expr-binary->arg2 e))
               (equal (expr-kind left) :arrsub)
               (equal array (expr-arrsub->arr left))
               (equal index (expr-arrsub->sub left))
               (equal (expr-kind array) :member)
               (equal target (expr-member->target array))
               (equal member (expr-member->name array))
               (equal (expr-kind target) :ident)
               (equal member (ident ,(ident->name memname)))
               (not (zp limit))
               (equal var (expr-ident->get target))
               (equal struct (read-var var compst))
               (,recognizer struct)
               (equal eidx (exec-expr-pure index compst))
               (expr-valuep eidx)
               (equal eidx1 (apconvert-expr-value eidx))
               (expr-valuep eidx1)
               (equal idx (expr-value->value eidx1))
               (cintegerp idx)
               (,checker idx ,@(and length (list 'struct)))
               (equal eval (exec-expr-pure right compst))
               (expr-valuep eval)
               (equal val (expr-value->value eval))
               (,elemfixtypep val))
          (equal (exec-expr-asg e compst fenv limit)
                 (write-var var
                            (,writer-element idx val struct)
                            compst))))
       (formula-memberp
        `(implies
          (and (equal (expr-kind e) :binary)
               (equal (binop-kind (expr-binary->op e)) :asg)
               (equal left (expr-binary->arg1 e))
               (equal right (expr-binary->arg2 e))
               (equal (expr-kind left) :arrsub)
               (equal array (expr-arrsub->arr left))
               (equal index (expr-arrsub->sub left))
               (equal (expr-kind array) :memberp)
               (equal target (expr-memberp->target array))
               (equal member (expr-memberp->name array))
               (equal (expr-kind target) :ident)
               (equal member (ident ,(ident->name memname)))
               (not (zp limit))
               (equal ptr (read-var (expr-ident->get target)
                                    compst))
               (valuep ptr)
               (value-case ptr :pointer)
               (value-pointer-validp ptr)
               (equal (value-pointer->reftype ptr)
                      (type-struct (ident ,(ident->name tag))))
               (equal struct
                      (read-object (value-pointer->designator ptr)
                                   compst))
               (,recognizer struct)
               (equal eidx (exec-expr-pure index compst))
               (expr-valuep eidx)
               (equal eidx1 (apconvert-expr-value eidx))
               (expr-valuep eidx1)
               (equal idx (expr-value->value eidx1))
               (cintegerp idx)
               (,checker idx ,@(and length (list 'struct)))
               (equal eval (exec-expr-pure right compst))
               (expr-valuep eval)
               (equal eval1 (apconvert-expr-value eval))
               (expr-valuep eval1)
               (equal val (expr-value->value eval1))
               (,elemfixtypep val))
          (equal (exec-expr-asg e compst fenv limit)
                 (write-object (value-pointer->designator ptr)
                               (,writer-element idx val struct)
                               compst))))
       (theory-member
        `(exec-expr-asg
          expr-fix-when-exprp
          exprp-of-expr-member->target
          exprp-of-expr-arrsub->sub
          exec-ident
          read-object-of-objdesign-of-var-to-read-var
          apconvert-expr-value-when-not-value-array-alt
          ,recognizer
          objdesign-of-var-when-valuep-of-read-var
          expr-value->value-of-expr-value
          expr-value-fix-when-expr-valuep
          expr-valuep-of-expr-value
          value-fix-when-valuep
          expr-value->object-of-expr-value
          objdesign-option-fix
          objdesign-fix-when-objdesignp
          objdesignp-of-objdesign-of-var-when-valuep-of-read-var
          value-struct-read
          not-errorp-when-valuep
          ,valuep-when-elemtype-arrayp
          (:e ident)
          ,value-kind-when-elemfixtype-arrayp
          not-errorp-when-expr-valuep
          ,checker
          integer-range-p
          value-integer->get-when-cintegerp
          ,value-kind-when-elemfixtypep
          return-type-of-objdesign-element
          return-type-of-objdesign-member
          objdesign-element->super-of-objdesign-element
          objdesign-element->index-of-objdesign-element
          objdesign-member->super-of-objdesign-member
          objdesign-member->name-of-objdesign-member
          read-object-of-objdesign-member
          nfix
          ,value-array-write-when-elemfixtype-arrayp
          ,elemfixtype-array-index-okp
          ,elemfixtype-arrayp-of-elemfixtype-array-write
          ,writer-element
          ,writer
          value-integerp-when-cintegerp
          write-object-of-objdesign-of-var-to-write-var
          (:e ident-fix)
          ,elemfixtype-array-fix-when-elemfixtype-arrayp
          ,reader
          ,reader-element
          ,fixer
          ,elemfixtype-array-length-of-elemfixtype-array-write
          value-struct-write
          return-type-of-value-struct
          not-errorp-when-member-value-listp
          member-value-listp-of-value-struct-write-aux
          ,type-of-value-when-elemfixtype-arrayp
          ,value-array->length-when-elemfixtype-arrayp
          write-object
          exec-expr-pure
          ,@(and length (list length))))
       (theory-memberp
        `(exec-expr-asg
          ,recognizer
          value-struct-read
          not-errorp-when-valuep
          ,valuep-when-elemtype-arrayp
          (:e ident)
          ,value-kind-when-elemfixtype-arrayp
          not-errorp-when-expr-valuep
          ,checker
          integer-range-p
          value-integer->get-when-cintegerp
          ,value-array-write-when-elemfixtype-arrayp
          ,elemfixtype-array-index-okp
          ,elemfixtype-arrayp-of-elemfixtype-array-write
          ,writer-element
          ,writer
          value-integerp-when-cintegerp
          ,elemfixtype-array-fix-when-elemfixtype-arrayp
          ,reader
          ,fixer
          ,elemfixtype-array-length-of-elemfixtype-array-write
          value-struct-write
          return-type-of-value-struct
          not-errorp-when-member-value-listp
          member-value-listp-of-value-struct-write-aux
          ,type-of-value-when-elemfixtype-arrayp
          ,value-array->length-when-elemfixtype-arrayp
          ,type-of-value-thm
          ,@(and length (list length))))
       ((mv event-member &)
        (evmac-generate-defthm thm-member-name
                               :formula formula-member
                               :hints `(("Goal" :in-theory ',theory-member))
                               :enable nil))
       ((mv event-memberp &)
        (evmac-generate-defthm thm-memberp-name
                               :formula formula-memberp
                               :hints `(("Goal" :in-theory ',theory-memberp))
                               :enable nil))
       ((mv more-events
            member-write-thms
            names-to-avoid)
        (atc-gen-tag-member-write-thms-aux tag
                                           recognizer
                                           fixer-recognizer-thm
                                           memname
                                           elemtype
                                           *nonchar-integer-types*
                                           (car writers)
                                           (car checkers)
                                           (cdr writers)
                                           (cdr checkers)
                                           writer-return-thm
                                           not-error-thm
                                           type-of-value-thm
                                           length
                                           thm-member-name
                                           thm-memberp-name
                                           names-to-avoid
                                           wrld)))
    (mv (list* event-member event-memberp more-events)
        member-write-thms
        names-to-avoid))

  :prepwork
  ((define atc-gen-tag-member-write-thms-aux ((tag identp)
                                              (recognizer symbolp)
                                              (fixer-recognizer-thm symbolp)
                                              (memname identp)
                                              (elemtype typep)
                                              (indextypes type-listp)
                                              (writer-acl2int symbolp)
                                              (checker-acl2int symbolp)
                                              (writers symbol-listp)
                                              (checkers symbol-listp)
                                              (writer-return-thm symbolp)
                                              (not-error-thm symbolp)
                                              (type-of-value-thm symbolp)
                                              (length symbolp)
                                              (writer-member-thm symbolp)
                                              (writer-memberp-thm symbolp)
                                              (names-to-avoid symbol-listp)
                                              (wrld plist-worldp))
     :guard (and (type-nonchar-integerp elemtype)
                 (type-nonchar-integer-listp indextypes))
     :returns (mv (local-events pseudo-event-form-listp)
                  (member-write-thms symbol-listp)
                  (updated-names-to-avoid symbol-listp
                                          :hyp (symbol-listp names-to-avoid)))
     :parents nil
     (b* (((when (endp indextypes)) (mv nil nil nil))
          (indextype (car indextypes))
          (writer (car writers))
          (checker (car checkers))
          (indexfixtype (integer-type-to-fixtype indextype))
          (elemfixtype (integer-type-to-fixtype elemtype))
          (indextypep (pack indexfixtype 'p))
          (elemtypep (pack elemfixtype 'p))
          (thm-member-name (pack 'exec-member-write-when-
                                 recognizer
                                 '-and-
                                 (ident->name memname)
                                 '-
                                 indexfixtype))
          ((mv thm-member-name names-to-avoid)
           (fresh-logical-name-with-$s-suffix thm-member-name
                                              nil
                                              names-to-avoid
                                              wrld))
          (thm-memberp-name (pack 'exec-memberp-write-when-
                                  recognizer
                                  '-and-
                                  (ident->name memname)
                                  '-
                                  indexfixtype))
          ((mv thm-memberp-name names-to-avoid)
           (fresh-logical-name-with-$s-suffix thm-memberp-name
                                              nil
                                              names-to-avoid
                                              wrld))
          (check-hyp (if length
                         `(,checker idx struct)
                       `(,checker idx)))
          (formula-member
           `(implies (and (syntaxp (quotep e))
                          (equal (expr-kind e) :binary)
                          (equal (binop-kind (expr-binary->op e)) :asg)
                          (equal left (expr-binary->arg1 e))
                          (equal right (expr-binary->arg2 e))
                          (equal (expr-kind left) :arrsub)
                          (equal array (expr-arrsub->arr left))
                          (equal index (expr-arrsub->sub left))
                          (equal (expr-kind array) :member)
                          (equal target (expr-member->target array))
                          (equal member (expr-member->name array))
                          (equal (expr-kind target) :ident)
                          (equal member (ident ,(ident->name memname)))
                          (not (zp limit))
                          (equal var (expr-ident->get target))
                          (equal struct (read-var var compst))
                          (,recognizer struct)
                          (equal eidx (exec-expr-pure index compst))
                          (expr-valuep eidx)
                          (equal eidx1 (apconvert-expr-value eidx))
                          (expr-valuep eidx1)
                          (equal idx (expr-value->value eidx1))
                          (,indextypep idx)
                          ,check-hyp
                          (equal eval (exec-expr-pure right compst))
                          (expr-valuep eval)
                          (equal val (expr-value->value eval))
                          (,elemtypep val))
                     (equal (exec-expr-asg e compst fenv limit)
                            (write-var var
                                       (,writer idx val struct)
                                       compst))))
          (formula-memberp
           `(implies (and (syntaxp (quotep e))
                          (equal (expr-kind e) :binary)
                          (equal (binop-kind (expr-binary->op e)) :asg)
                          (equal left (expr-binary->arg1 e))
                          (equal right (expr-binary->arg2 e))
                          (equal (expr-kind left) :arrsub)
                          (equal array (expr-arrsub->arr left))
                          (equal index (expr-arrsub->sub left))
                          (equal (expr-kind array) :memberp)
                          (equal target (expr-memberp->target array))
                          (equal member (expr-memberp->name array))
                          (equal (expr-kind target) :ident)
                          (equal member (ident ,(ident->name memname)))
                          (not (zp limit))
                          (equal ptr (read-var (expr-ident->get target)
                                               compst))
                          (valuep ptr)
                          (value-case ptr :pointer)
                          (value-pointer-validp ptr)
                          (equal (value-pointer->reftype ptr)
                                 (type-struct (ident ,(ident->name tag))))
                          (equal struct
                                 (read-object (value-pointer->designator ptr)
                                              compst))
                          (,recognizer struct)
                          (equal eidx (exec-expr-pure index compst))
                          (expr-valuep eidx)
                          (equal eidx1 (apconvert-expr-value eidx))
                          (expr-valuep eidx1)
                          (equal idx (expr-value->value eidx1))
                          (,indextypep idx)
                          ,check-hyp
                          (equal eval (exec-expr-pure right compst))
                          (expr-valuep eval)
                          (equal eval1 (apconvert-expr-value eval))
                          (expr-valuep eval1)
                          (equal val (expr-value->value eval1))
                          (,elemtypep val))
                     (equal (exec-expr-asg e compst fenv limit)
                            (write-object (value-pointer->designator ptr)
                                          (,writer idx val struct)
                                          compst))))
          (writer-alt-def (packn-pos (list writer '-alt-def) writer))
          (checker-alt-def (packn-pos (list checker '-alt-def) checker))
          (hints-member `(("Goal" :in-theory '(,writer-member-thm
                                               ,writer-alt-def
                                               ,checker-alt-def
                                               cintegerp))))
          (hints-memberp `(("Goal" :in-theory '(,writer-memberp-thm
                                                ,writer-alt-def
                                                ,checker-alt-def
                                                cintegerp))))
          ((mv event-member &)
           (evmac-generate-defthm thm-member-name
                                  :formula formula-member
                                  :hints hints-member
                                  :enable nil))
          ((mv event-memberp &)
           (evmac-generate-defthm thm-memberp-name
                                  :formula formula-memberp
                                  :hints hints-memberp
                                  :enable nil))
          ((mv events thm-names names-to-avoid)
           (atc-gen-tag-member-write-thms-aux tag
                                              recognizer
                                              fixer-recognizer-thm
                                              memname
                                              elemtype
                                              (cdr indextypes)
                                              writer-acl2int
                                              checker-acl2int
                                              (cdr writers)
                                              (cdr checkers)
                                              writer-return-thm
                                              not-error-thm
                                              type-of-value-thm
                                              length
                                              writer-member-thm
                                              writer-memberp-thm
                                              names-to-avoid
                                              wrld)))
       (mv (append (and (not length)
                        (list event-member))
                   (list event-memberp)
                   events)
           (append (and (not length)
                        (list thm-member-name))
                   (list thm-memberp-name)
                   thm-names)
           names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-member-write-all-thms
  ((tag identp)
   (recognizer symbolp)
   (fixer symbolp)
   (fixer-recognizer-thm symbolp)
   (not-error-thm symbolp)
   (type-of-value-thm symbolp)
   (meminfos defstruct-member-info-listp)
   (names-to-avoid symbol-listp)
   (wrld plist-worldp))
  :returns (mv (local-events pseudo-event-form-listp)
               (member-write-thms symbol-listp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorems to rewrite @(tsee exec-expr-asg)
          with a @(':memberp') left expression
          to a structure writer,
          for all the members of a structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This relies on @('writers') and @('writer-return-thms')
     to be in the same order as @('members')."))
  (b* (((when (endp meminfos)) (mv nil nil names-to-avoid))
       ((mv events thms names-to-avoid)
        (atc-gen-tag-member-write-thms tag
                                       recognizer
                                       fixer
                                       fixer-recognizer-thm
                                       not-error-thm
                                       type-of-value-thm
                                       (car meminfos)
                                       names-to-avoid
                                       wrld))
       ((mv more-events more-thms names-to-avoid)
        (atc-gen-tag-member-write-all-thms tag
                                           recognizer
                                           fixer
                                           fixer-recognizer-thm
                                           not-error-thm
                                           type-of-value-thm
                                           (cdr meminfos)
                                           names-to-avoid
                                           wrld)))
    (mv (append events more-events)
        (append thms more-thms)
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-struct-declon-list ((meminfos member-type-listp))
  :returns (declons struct-declon-listp)
  :short "Generate a list of C structure declarations
          from a list of member types."
  (b* (((when (endp meminfos)) nil)
       (meminfo (car meminfos))
       ((member-type meminfo) meminfo)
       ((mv tyspec declor) (ident+type-to-tyspec+declor meminfo.name
                                                        meminfo.type))
       (declon (make-struct-declon :tyspec tyspec :declor declor))
       (declons (atc-gen-struct-declon-list (cdr meminfos))))
    (cons declon declons)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tag-declon ((tag stringp)
                            (info defstruct-infop)
                            (prec-tags atc-string-taginfo-alistp)
                            (proofs booleanp)
                            (names-to-avoid symbol-listp)
                            (wrld plist-worldp))
  :returns (mv (declon tag-declonp)
               (local-events pseudo-event-form-listp)
               (updated-prec-tags
                atc-string-taginfo-alistp
                :hyp (and (stringp tag)
                          (atc-string-taginfo-alistp prec-tags))
                :hints (("Goal" :in-theory (enable acons))))
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate a C structure type declaration,
          with accompanying theorems."
  (b* ((meminfos (defstruct-info->members info))
       (memtypes (defstruct-member-info-list->memtype-list meminfos))
       (tag-ident (defstruct-info->tag info))
       (recognizer (defstruct-info->recognizer info))
       (fixer (defstruct-info->fixer info))
       (fixer-recognizer-thm (defstruct-info->fixer-recognizer-thm info))
       (not-error-thm (defstruct-info->not-error-thm info))
       (type-of-value-thm (defstruct-info->type-of-value-thm info))
       (struct-declons (atc-gen-struct-declon-list memtypes))
       ((mv read-thm-events read-thm-names names-to-avoid)
        (if proofs
            (atc-gen-tag-member-read-all-thms tag-ident
                                              recognizer
                                              fixer
                                              fixer-recognizer-thm
                                              not-error-thm
                                              meminfos
                                              names-to-avoid
                                              wrld)
          (mv nil nil names-to-avoid)))
       ((mv write-thm-events write-thm-names names-to-avoid)
        (if proofs
            (atc-gen-tag-member-write-all-thms tag-ident
                                               recognizer
                                               fixer
                                               fixer-recognizer-thm
                                               not-error-thm
                                               type-of-value-thm
                                               meminfos
                                               names-to-avoid
                                               wrld)
          (mv nil nil names-to-avoid)))
       (thm-events (append read-thm-events write-thm-events))
       (info (make-atc-tag-info :defstruct info
                                :member-read-thms read-thm-names
                                :member-write-thms write-thm-names))
       (prec-tags (acons tag info prec-tags)))
    (mv (make-tag-declon-struct :tag tag-ident :members struct-declons)
        thm-events
        prec-tags
        names-to-avoid)))
