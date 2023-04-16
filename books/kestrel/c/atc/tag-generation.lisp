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
       (readers (defstruct-member-info->readers meminfo))
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
         (mv nil nil nil))))
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
                                      names-to-avoid
                                      wrld))

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
          (elemfixtype (integer-type-to-fixtype elemtype))
          (indextypep (pack indexfixtype 'p))
          (array-reader (pack elemfixtype '-array-integer-read-alt-def))
          (array-checker (pack elemfixtype '-array-integer-index-okp))
          (not-error-array-thm (pack 'not-errorp-when- elemfixtype '-arrayp))
          (kind-array-thm (pack 'value-kind-when- elemfixtype '-arrayp))
          (valuep-when-indextype (pack 'valuep-when- indextypep))
          (type-thm (pack 'integer-from- indexfixtype))
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
          (hints `(("Goal"
                    :in-theory
                    '(exec-arrsub-of-member
                      exec-arrsub-of-memberp
                      value-struct-read
                      value-integer->get
                      value-schar->get-to-integer-from-schar
                      value-uchar->get-to-integer-from-uchar
                      value-sshort->get-to-integer-from-sshort
                      value-ushort->get-to-integer-from-ushort
                      value-sint->get-to-integer-from-sint
                      value-uint->get-to-integer-from-uint
                      value-slong->get-to-integer-from-slong
                      value-ulong->get-to-integer-from-ulong
                      value-sllong->get-to-integer-from-sllong
                      value-ullong->get-to-integer-from-ullong
                      value-kind-when-scharp
                      value-kind-when-ucharp
                      value-kind-when-sshortp
                      value-kind-when-ushortp
                      value-kind-when-sintp
                      value-kind-when-uintp
                      value-kind-when-slongp
                      value-kind-when-ulongp
                      value-kind-when-sllongp
                      value-kind-when-ullongp
                      value-array->elemtype-when-uchar-arrayp
                      value-array->elemtype-when-schar-arrayp
                      value-array->elemtype-when-ushort-arrayp
                      value-array->elemtype-when-sshort-arrayp
                      value-array->elemtype-when-uint-arrayp
                      value-array->elemtype-when-sint-arrayp
                      value-array->elemtype-when-ulong-arrayp
                      value-array->elemtype-when-slong-arrayp
                      value-array->elemtype-when-ullong-arrayp
                      value-array->elemtype-when-sllong-arrayp
                      ifix
                      integer-range-p
                      not-errorp-when-valuep
                      value-fix-when-valuep
                      value-result-fix-when-value-resultp
                      value-resultp-when-valuep
                      value-integerp
                      value-unsigned-integerp-alt-def
                      value-signed-integerp-alt-def
                      (:e ident)
                      ,@*integer-value-disjoint-rules*
                      ,recognizer
                      ,fixer-recognizer-thm
                      ,checker
                      ,checker-acl2int
                      ,reader
                      ,reader-acl2int
                      ,array-reader
                      ,array-checker
                      ,not-error-array-thm
                      ,kind-array-thm
                      ,valuep-when-indextype
                      (:t ,type-thm)
                      ,@(and length
                             (list length
                                   'value-struct-read))
                      expr-value->value-of-expr-value
                      expr-value->object-of-expr-value
                      ,@*atc-array-read-rules*
                      apconvert-expr-value-when-not-value-array
                      apconvert-expr-value-when-uchar-arrayp
                      apconvert-expr-value-when-schar-arrayp
                      apconvert-expr-value-when-ushort-arrayp
                      apconvert-expr-value-when-sshort-arrayp
                      apconvert-expr-value-when-uint-arrayp
                      apconvert-expr-value-when-sint-arrayp
                      apconvert-expr-value-when-ulong-arrayp
                      apconvert-expr-value-when-slong-arrayp
                      apconvert-expr-value-when-ullong-arrayp
                      apconvert-expr-value-when-sllong-arrayp
                      expr-valuep-of-expr-value
                      not-errorp-when-expr-valuep
                      objdesign-option-fix
                      objdesign-fix-when-objdesignp
                      return-type-of-objdesign-member
                      return-type-of-value-pointer
                      value-pointer->designator-of-value-pointer
                      value-pointer-validp-of-value-pointer
                      return-type-of-pointer-valid
                      pointer-valid->get-of-pointer-valid
                      value-pointer->designator-of-value-pointer
                      value-pointer->reftype-of-value-pointer
                      read-object-of-objdesign-member
                      (:e objdesignp)
                      (:e type-fix)
                      (:e type-uchar)
                      (:e type-schar)
                      (:e type-ushort)
                      (:e type-sshort)
                      (:e type-uint)
                      (:e type-sint)
                      (:e type-ulong)
                      (:e type-slong)
                      (:e type-ullong)
                      (:e type-sllong)
                      (:t objdesign-member)))))
          ((mv event-member &)
           (evmac-generate-defthm thm-member-name
                                  :formula formula-member
                                  :hints hints
                                  :enable nil))
          ((mv event-memberp &)
           (evmac-generate-defthm thm-memberp-name
                                  :formula formula-memberp
                                  :hints hints
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
                                      fixer-recognizer-thm
                                      not-error-thm
                                      (car meminfos)
                                      names-to-avoid
                                      wrld))
       ((mv more-events more-thms names-to-avoid)
        (atc-gen-tag-member-read-all-thms tag
                                          recognizer
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
       (writer (defstruct-member-info->writer meminfo))
       (writers (defstruct-member-info->writers meminfo))
       (writer-return-thm (if (type-integerp type)
                              (defstruct-member-info->writer-return-thm meminfo)
                            (car
                             (defstruct-member-info->writer-return-thms
                               meminfo))))
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
         (mv nil nil nil))))
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
                                       names-to-avoid
                                       wrld))

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
          (integer-from-indextype (pack 'integer-from- indexfixtype))
          (array-writer (pack elemfixtype '-array-integer-write-alt-def))
          (array-checker (pack elemfixtype '-array-integer-index-okp))
          (not-error-array-thm (pack 'not-errorp-when- elemfixtype '-arrayp))
          (kind-array-thm (pack 'value-kind-when- elemfixtype '-arrayp))
          (valuep-when-indextypep (pack 'valuep-when- indextypep))
          (valuep-when-elemtypep (pack 'valuep-when- elemtypep))
          (value-kind-when-indextypep (pack 'value-kind-when- indextypep))
          (value-kind-when-elemtypep (pack 'value-kind-when- elemtypep))
          (type-thm (pack 'integer-from- indexfixtype))
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
          (arrayp-of-arrary-write
           (pack elemfixtype '-arrayp-of- elemfixtype '-array-integer-write))
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
          (hints-member
           `(("Goal"
              :in-theory
              '(exec-expr-asg
                value-integer->get
                value-schar->get-to-integer-from-schar
                value-uchar->get-to-integer-from-uchar
                value-sshort->get-to-integer-from-sshort
                value-ushort->get-to-integer-from-ushort
                value-sint->get-to-integer-from-sint
                value-uint->get-to-integer-from-uint
                value-slong->get-to-integer-from-slong
                value-ulong->get-to-integer-from-ulong
                value-sllong->get-to-integer-from-sllong
                value-ullong->get-to-integer-from-ullong
                value-kind-when-scharp
                value-kind-when-ucharp
                value-kind-when-sshortp
                value-kind-when-ushortp
                value-kind-when-sintp
                value-kind-when-uintp
                value-kind-when-slongp
                value-kind-when-ulongp
                value-kind-when-sllongp
                value-kind-when-ullongp
                value-struct-read
                value-struct-write
                not-errorp-when-valuep
                value-integerp
                value-unsigned-integerp-alt-def
                value-signed-integerp-alt-def
                value-fix-when-valuep
                ifix
                integer-range-p
                (:e ident)
                (:compound-recognizer consp-when-ucharp)
                ,recognizer
                ,fixer-recognizer-thm
                ,not-error-thm
                ,type-of-value-thm
                ,kind-array-thm
                ,checker
                ,checker-acl2int
                ,writer
                ,writer-acl2int
                ,not-error-array-thm
                ,array-writer
                ,array-checker
                ,valuep-when-elemtypep
                ,valuep-when-indextypep
                ,@*integer-value-disjoint-rules*
                (:t ,type-thm)
                ,@(and length (list length))
                not-errorp-when-expr-valuep
                apconvert-expr-value-when-not-value-array-alt
                ,value-kind-when-elemtypep
                ,value-kind-when-indextypep
                expr-value-fix-when-expr-valuep
                exec-ident
                expr-fix-when-exprp
                exprp-of-expr-member->target
                not-errorp-when-expr-valuep
                expr-valuep-of-expr-value
                expr-value->value-of-expr-value
                expr-value->object-of-expr-value
                read-object-of-objdesign-of-var-to-read-var
                objdesign-of-var-when-valuep-of-read-var
                objdesignp-of-objdesign-of-var-when-valuep-of-read-var
                objdesign-option-fix
                objdesign-fix-when-objdesignp
                write-object-of-objdesign-of-var-to-write-var
                objdesign-member->super-of-objdesign-member
                objdesign-member->name-of-objdesign-member
                objdesign-element->super-of-objdesign-element
                objdesign-element->index-of-objdesign-element
                return-type-of-objdesign-member
                return-type-of-objdesign-element
                read-object
                nfix
                (:e ident-fix))
              :expand
              ((exec-expr-pure (expr-member->target
                                (expr-arrsub->arr (expr-binary->arg1 e)))
                               compst)
               (:free (x y z w) (write-object (objdesign-member x y) z w))
               (:free (x y z w) (write-object (objdesign-element x y) z w)))
              :use
              ((:instance
                ,writer-return-thm
                (index
                 (,integer-from-indextype
                  (expr-value->value
                   (apconvert-expr-value
                    (exec-expr-pure (expr-arrsub->sub (expr-binary->arg1 e))
                                    compst)))))
                (val
                 (expr-value->value
                  (apconvert-expr-value
                   (exec-expr-pure (expr-binary->arg2 e) compst))))
                (struct
                 (read-var
                  (expr-ident->get
                   (expr-member->target
                    (expr-arrsub->arr (expr-binary->arg1 e))))
                  compst)))
               (:instance
                ,arrayp-of-arrary-write
                (array
                 (value-struct-read-aux
                  (ident ,(ident->name memname))
                  (value-struct->members
                   (read-var
                    (expr-ident->get
                     (expr-member->target
                      (expr-arrsub->arr (expr-binary->arg1 e))))
                    compst))))
                (index
                 (,integer-from-indextype
                  (expr-value->value
                   (apconvert-expr-value
                    (exec-expr-pure
                     (expr-arrsub->sub (expr-binary->arg1 e))
                     compst)))))
                (element
                 (expr-value->value
                  (apconvert-expr-value
                   (exec-expr-pure (expr-binary->arg2 e) compst)))))))))
          (hints-memberp
           `(("Goal"
              :in-theory
              '(exec-expr-asg
                value-integer->get
                value-schar->get-to-integer-from-schar
                value-uchar->get-to-integer-from-uchar
                value-sshort->get-to-integer-from-sshort
                value-ushort->get-to-integer-from-ushort
                value-sint->get-to-integer-from-sint
                value-uint->get-to-integer-from-uint
                value-slong->get-to-integer-from-slong
                value-ulong->get-to-integer-from-ulong
                value-sllong->get-to-integer-from-sllong
                value-ullong->get-to-integer-from-ullong
                value-kind-when-scharp
                value-kind-when-ucharp
                value-kind-when-sshortp
                value-kind-when-ushortp
                value-kind-when-sintp
                value-kind-when-uintp
                value-kind-when-slongp
                value-kind-when-ulongp
                value-kind-when-sllongp
                value-kind-when-ullongp
                value-struct-read
                value-struct-write
                not-errorp-when-valuep
                value-integerp
                value-unsigned-integerp-alt-def
                value-signed-integerp-alt-def
                value-fix-when-valuep
                ifix
                integer-range-p
                (:e ident)
                (:compound-recognizer consp-when-ucharp)
                ,recognizer
                ,fixer-recognizer-thm
                ,not-error-thm
                ,type-of-value-thm
                ,kind-array-thm
                ,checker
                ,checker-acl2int
                ,writer
                ,writer-acl2int
                ,not-error-array-thm
                ,array-writer
                ,array-checker
                ,valuep-when-elemtypep
                ,valuep-when-indextypep
                ,@*integer-value-disjoint-rules*
                (:t ,type-thm)
                ,@(and length (list length))
                not-errorp-when-expr-valuep
                apconvert-expr-value-when-not-value-array-alt
                ,value-kind-when-elemtypep
                ,value-kind-when-indextypep
                expr-value-fix-when-expr-valuep)
              :use
              ((:instance
                ,writer-return-thm
                (index
                 (,integer-from-indextype
                  (expr-value->value
                   (apconvert-expr-value
                    (exec-expr-pure (expr-arrsub->sub (expr-binary->arg1 e))
                                    compst)))))
                (val
                 (expr-value->value
                  (apconvert-expr-value
                   (exec-expr-pure (expr-binary->arg2 e) compst))))
                (struct
                 (read-object
                  (value-pointer->designator
                   (read-var
                    (expr-ident->get
                     (expr-memberp->target
                      (expr-arrsub->arr (expr-binary->arg1 e))))
                    compst))
                  compst)))
               (:instance
                ,arrayp-of-arrary-write
                (array
                 (value-struct-read-aux
                  (ident ,(ident->name memname))
                  (value-struct->members
                   (read-object
                    (value-pointer->designator
                     (read-var
                      (expr-ident->get
                       (expr-memberp->target
                        (expr-arrsub->arr (expr-binary->arg1 e))))
                      compst))
                    compst))))
                (index
                 (,integer-from-indextype
                  (expr-value->value
                   (apconvert-expr-value
                    (exec-expr-pure
                     (expr-arrsub->sub (expr-binary->arg1 e))
                     compst)))))
                (element
                 (expr-value->value
                  (apconvert-expr-value
                   (exec-expr-pure (expr-binary->arg2 e) compst)))))))))
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
                                       fixer-recognizer-thm
                                       not-error-thm
                                       type-of-value-thm
                                       (car meminfos)
                                       names-to-avoid
                                       wrld))
       ((mv more-events more-thms names-to-avoid)
        (atc-gen-tag-member-write-all-thms tag
                                           recognizer
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
       (fixer-recognizer-thm (defstruct-info->fixer-recognizer-thm info))
       (not-error-thm (defstruct-info->not-error-thm info))
       (type-of-value-thm (defstruct-info->type-of-value-thm info))
       (struct-declons (atc-gen-struct-declon-list memtypes))
       ((mv read-thm-events read-thm-names names-to-avoid)
        (if proofs
            (atc-gen-tag-member-read-all-thms tag-ident
                                              recognizer
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
