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

(include-book "term-checkers-common")
(include-book "function-tables")
(include-book "tag-tables")

(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/irecursivep-plus" :dir :system)

(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))

(local (include-book "projects/apply/loop" :dir :system))
(local (in-theory (disable acl2::loop-book-theory)))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ term-checkers-atc
  :parents (atc-event-and-code-generation)
  :short "Checkers of ACL2 terms that represent C constructs, used by ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "These extend the ones in @(see term-checkers-common)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-sint-from-boolean ((term pseudo-termp))
  :returns (mv erp
               (yes/no booleanp)
               (arg pseudo-termp))
  :short "Check if a term may represent a conversion
          from an ACL2 boolean to a C @('int') value."
  (b* (((reterr) nil nil)
       ((acl2::fun (no)) (retok nil nil))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless (and okp
                     (eq fn 'sint-from-boolean)))
        (no))
       ((unless (list-lenp 1 args))
        (reterr (raise "Internal error: ~x0 not applied to 1 argument." fn))))
    (retok t (first args)))
  ///

  (defret pseudo-term-count-of-atc-check-sint-from-boolean
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-boolean-from-type ((term pseudo-termp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (arg pseudo-termp)
               (in-type typep))
  :short "Check if a term may represent a conversion
          from a C integer value to an ACL2 boolean."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also return the input C type of the conversion.
     The output type is known (boolean), and it is in fact an ACL2 type."))
  (b* (((reterr) nil nil nil (irr-type))
       ((acl2::fun (no)) (retok nil nil nil (irr-type)))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless okp) (no))
       ((mv okp boolean from type) (atc-check-symbol-3part fn))
       (in-type (fixtype-to-integer-type type))
       ((unless (and okp
                     (eq boolean 'boolean)
                     (eq from 'from)
                     in-type))
        (no))
       ((unless (equal (symbol-package-name fn) "C"))
        (reterr (msg "Invalid function ~x0 encountered: ~
                      it has the form of a conversion to boolean from integer, ~
                      but it is not in the \"C\" package."
                     fn)))
       ((unless (list-lenp 1 args))
        (reterr (raise "Internal error: ~x0 not applied to 1 argument." fn))))
    (retok t fn (first args) in-type))
  ///

  (defret pseudo-term-count-of-atc-check-boolean-from-type
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-condexpr ((term pseudo-termp))
  :returns (mv erp
               (yes/no booleanp)
               (test pseudo-termp)
               (then pseudo-termp)
               (else pseudo-termp))
  :short "Check if a term may represent a C conditional expression."
  (b* (((reterr) nil nil nil nil)
       ((acl2::fun (no)) (retok nil nil nil nil))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless (and okp
                     (eq fn 'condexpr)))
        (no))
       ((unless (list-lenp 1 args))
        (reterr (raise "Internal error: ~x0 not applied to 1 argument." fn)))
       (arg (first args))
       ((mv okp test then else) (fty-check-if-call arg))
       ((when (not okp))
        (reterr (msg "The function CONDEXPR is not applied to an IF, ~
                      but instead to the term ~x0."
                     arg))))
    (retok t test then else))
  ///

  (defret pseudo-term-count-of-atc-check-condexpr.test
    (implies yes/no
             (< (pseudo-term-count test)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-condexpr.then
    (implies yes/no
             (< (pseudo-term-count then)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-condexpr.else
    (implies yes/no
             (< (pseudo-term-count else)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-integer-read ((term pseudo-termp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (arg pseudo-termp)
               (type typep))
  :short "Check if a term may represent a read of an integer by pointer."
  (b* (((reterr) nil nil nil (irr-type))
       ((acl2::fun (no)) (retok nil nil nil (irr-type)))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless okp) (no))
       ((mv okp fixtype read) (atc-check-symbol-2part fn))
       (type (fixtype-to-integer-type fixtype))
       ((unless (and okp
                     (eq read 'read)
                     type))
        (no))
       ((unless (equal (symbol-package-name fn) "C"))
        (reterr (msg "Invalid function ~x0 encountered: ~
                      it has the form of a read of an integer by pointer, ~
                      but it is not in the \"C\" package."
                     fn)))
       ((unless (list-lenp 1 args))
        (reterr (raise "Internal error: ~x0 not applied to 1 argument." fn)))
       (arg (first args)))
    (retok t fn arg type))
  ///

  (defret pseudo-term-count-of-atc-check-integer-read
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret type-nonchar-integerp-of-atc-check-integer-read
    (implies yes/no
             (type-nonchar-integerp type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-integer-write ((val pseudo-termp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (arg pseudo-termp)
               (type typep))
  :short "Check if a term may represent a write of an integer by pointer."
  :long
  (xdoc::topstring
   (xdoc::p
    "A write of an integer by pointer is represented by
     a @(tsee let) of the form")
   (xdoc::codeblock
    "(let ((<var> (<type>-write <int>))) ...)")
   (xdoc::p
    "where @('<var>') is a variable of pointer-to-integer type
     and @('<int>') is a term that yields the integer to write.")
   (xdoc::p
    "This ACL2 function takes as argument the value term of the @(tsee let),
     i.e. @('(<type>-write <int>)'),
     and checks if it has the expected form,
     returning, if successful,
     the function @('<type>-write'),
     the argument @('<int>'),
     and the integer type."))
  (b* (((reterr) nil nil nil (irr-type))
       ((acl2::fun (no)) (retok nil nil nil (irr-type)))
       ((mv okp fn args) (fty-check-fn-call val))
       ((unless okp) (no))
       ((mv okp fixtype write) (atc-check-symbol-2part fn))
       (type (fixtype-to-integer-type fixtype))
       ((unless (and okp
                     (eq write 'write)
                     type))
        (no))
       ((unless (equal (symbol-package-name fn) "C"))
        (reterr (msg "Invalid function ~x0 encountered: ~
                      it has the form of a write of an integer by pointer, ~
                      but it is not in the \"C\" package."
                     fn)))
       ((unless (list-lenp 1 args))
        (reterr (raise "Internal error: ~x0 not applied to 1 argument." fn)))
       (arg (first args)))
    (retok t fn arg type))
  ///

  (defret pseudo-term-count-of-atc-check-integer-write
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count val)))
    :rule-classes :linear)

  (defret type-nonchar-integerp-of-atc-check-integer-write
    (implies yes/no
             (type-nonchar-integerp type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-array-read ((term pseudo-termp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (arr pseudo-termp)
               (sub pseudo-termp)
               (elem-type typep))
  :short "Check if a term may represent an array read."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C array read operations,
     we return the two argument terms.")
   (xdoc::p
    "We also return the element type of the array.")
   (xdoc::p
    "If the term does not have the form explained above,
     we return an indication of failure."))
  (b* (((reterr) nil nil nil nil (irr-type))
       ((acl2::fun (no)) (retok nil nil nil nil (irr-type)))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless okp) (no))
       ((mv okp fixtype array read) (atc-check-symbol-3part fn))
       (elem-type (fixtype-to-integer-type fixtype))
       ((unless (and okp
                     elem-type
                     (eq array 'array)
                     (eq read 'read)))
        (no))
       ((unless (equal (symbol-package-name fn) "C"))
        (reterr (msg "Invalid function ~x0 encountered: ~
                      it has the form of an array read, ~
                      but it is not in the \"C\" package."
                     fn)))
       ((unless (list-lenp 2 args))
        (reterr (raise "Internal error: ~x0 not applied to 2 arguments." fn)))
       (arr (first args))
       (sub (second args)))
    (retok t fn arr sub elem-type))
  ///

  (defret pseudo-term-count-of-atc-check-array-read-arr
    (implies yes/no
             (< (pseudo-term-count arr)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-array-read-sub
    (implies yes/no
             (< (pseudo-term-count sub)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret type-nonchar-integerp-of-atc-check-array-read
    (implies yes/no
             (type-nonchar-integerp elem-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-array-write ((var symbolp) (val pseudo-termp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (sub pseudo-termp)
               (elem pseudo-termp)
               (elem-type typep))
  :short "Check if a @(tsee let) binding may represent an array write."
  :long
  (xdoc::topstring
   (xdoc::p
    "An array write, i.e. an assignment to an array element,
     is represented by a @(tsee let) binding of the form")
   (xdoc::codeblock
    "(let ((<arr> (<type>-array-write <arr> <sub> <elem>))) ...)")
   (xdoc::p
    "where @('<arr>') is a variable of pointer type to an integer type,
     which must occur identically as
     both the @(tsee let) variable
     and as the first argument of @('<type>-array-write'),
     @('<sub>') is an expression that yields the index of the element to write,
     @('<elem>') is an expression that yields the element to write,
     and @('...') represents the code that follows the array assignment.
     This function takes as arguments
     the variable and value of a @(tsee let) binder,
     and checks if they have the form described above.
     If they do, the components are returned for further processing.
     We also return the types of the index and element
     as gathered from the name of the array write function."))
  (b* (((reterr) nil nil nil nil (irr-type))
       ((acl2::fun (no)) (retok nil nil nil nil (irr-type)))
       ((mv okp fn args) (fty-check-fn-call val))
       ((unless okp) (no))
       ((mv okp fixtype array write) (atc-check-symbol-3part fn))
       (elem-type (fixtype-to-integer-type fixtype))
       ((unless (and okp
                     elem-type
                     (eq array 'array)
                     (eq write 'write)))
        (no))
       ((unless (equal (symbol-package-name fn) "C"))
        (reterr (msg "Invalid function ~x0 encountered: ~
                      it has the form of an array write, ~
                      but it is not in the \"C\" package."
                     fn)))
       ((unless (list-lenp 3 args))
        (reterr (raise "Internal error: ~x0 not applied to 3 arguments." fn)))
       ((unless (equal (first args) var))
        (reterr
         (raise "Internal error: ~x0 is not applied to the variable ~x1."
                fn var)))
       (sub (second args))
       (elem (third args)))
    (retok t fn sub elem elem-type))
  ///

  (defret pseudo-term-count-of-atc-check-array-write-sub
    (implies yes/no
             (< (pseudo-term-count sub)
                (pseudo-term-count val)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-array-write-elem
    (implies yes/no
             (< (pseudo-term-count elem)
                (pseudo-term-count val)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-struct-read-scalar ((term pseudo-termp)
                                      (prec-tags atc-string-taginfo-alistp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (arg pseudo-termp)
               (tag identp)
               (member identp)
               (mem-type typep))
  :short "Check if a term may represent a structure read
          of a scalar member."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C structure read operations for scalar members,
     we return the argument term, the tag name, and the name of the member.
     The C structure type of the reader must be in the preceding tags;
     we consult the alist to retrieve the relevant information.")
   (xdoc::p
    "We also return the type of the member.")
   (xdoc::p
    "If the term does not have the form explained above,
     we return an indication of failure."))
  (b* (((reterr) nil nil nil (irr-ident) (irr-ident) (irr-type))
       ((acl2::fun (no)) (retok nil nil nil (irr-ident) (irr-ident) (irr-type)))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless okp) (no))
       ((mv okp struct tag read member) (atc-check-symbol-4part fn))
       ((unless (and okp
                     (equal (symbol-name struct) "STRUCT")
                     (equal (symbol-name read) "READ")))
        (no))
       (tag (symbol-name tag))
       (info (cdr (assoc-equal tag prec-tags)))
       ((unless info) (no))
       (info (atc-tag-info->defstruct info))
       ((unless (member-eq fn (defstruct-info->reader-list info)))
        (reterr (msg "Invalid function ~x0 encountered: ~
                      it has the form of a structure read ~
                      for the structure type ~x1, ~
                      but it is not among the readers ~
                      associated to that structure type."
                     fn tag)))
       (tag (defstruct-info->tag info))
       (members (defstruct-member-info-list->memtype-list
                  (defstruct-info->members info)))
       (member (symbol-name member))
       ((unless (paident-stringp member))
        (reterr (raise "Internal error: ~x0 is not a portable ASCII identifier."
                       member)))
       (member (ident member))
       (mem-type (member-type-lookup member members))
       ((unless mem-type)
        (reterr (raise "Internal error: type of ~x0 not found." member)))
       ((unless (type-nonchar-integerp mem-type))
        (reterr (raise "Internal error: scalar member ~x0 has type ~x1."
                       member mem-type)))
       ((unless (list-lenp 1 args))
        (reterr (raise "Internal error: ~x0 not applied to 1 argument." fn)))
       (arg (car args)))
    (retok t fn arg tag member mem-type))
  ///

  (defret pseudo-term-count-of-atc-check-struct-read-scalar
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret type-nonchar-integerp-of-atc-check-struct-read-scalar
    (implies yes/no
             (type-nonchar-integerp mem-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-struct-read-array ((term pseudo-termp)
                                     (prec-tags atc-string-taginfo-alistp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (index pseudo-termp)
               (struct pseudo-termp)
               (tag identp)
               (member identp)
               (elem-type typep)
               (flexiblep booleanp))
  :short "Check if a term may represent a structure read
          of an element of an array member."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of the ACL2 function
     that represent the C structure read operation
     for elements of array members,
     we return the reader, the argument terms (index and structure),
     the tag name, and the name of the member.
     The C structure type of the reader must be in the preceding tags;
     we consult the alist to retrieve the relevant information.")
   (xdoc::p
    "We also return the type of the array element.")
   (xdoc::p
    "If the term does not have the right form,
     we return an indication of failure."))
  (b* (((reterr) nil nil nil nil (irr-ident) (irr-ident) (irr-type) nil)
       ((acl2::fun (no))
        (retok nil nil nil nil (irr-ident) (irr-ident) (irr-type) nil))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless okp) (no))
       ((mv okp struct tag read member element) (atc-check-symbol-5part fn))
       ((unless (and okp
                     (equal (symbol-name struct) "STRUCT")
                     (equal (symbol-name read) "READ")
                     (equal (symbol-name element) "ELEMENT")))
        (no))
       (tag (symbol-name tag))
       (info (cdr (assoc-equal tag prec-tags)))
       ((unless info) (no))
       (info (atc-tag-info->defstruct info))
       ((unless (member-eq fn (defstruct-info->reader-element-list info)))
        (reterr (msg "Invalid function ~x0 encountered: ~
                      it has the form of a structure read ~
                      for the structure type ~x1, ~
                      but it is not among the readers ~
                      associated to that structure type."
                     fn tag)))
       (tag (defstruct-info->tag info))
       (members (defstruct-member-info-list->memtype-list
                  (defstruct-info->members info)))
       (member (symbol-name member))
       ((unless (paident-stringp member))
        (reterr (raise "Internal error: ~x0 is not a portable ASCII identifier."
                       member)))
       (member (ident member))
       (mem-type (member-type-lookup member members))
       ((unless mem-type)
        (reterr (raise "Internal error: type of ~x0 not found." member)))
       ((unless (type-case mem-type :array))
        (reterr (raise "Internal error: type of ~x0 is not array." member)))
       (elem-type (type-array->of mem-type))
       (flexiblep (not (type-array->size mem-type)))
       ((unless (list-lenp 2 args))
        (reterr (raise "Internal error: ~x0 not applied to 2 arguments." fn)))
       (index (first args))
       (struct (second args)))
    (retok t fn index struct tag member elem-type flexiblep))
  ///

  (defret pseudo-term-count-of-atc-check-struct-read-array-index
    (implies yes/no
             (< (pseudo-term-count index)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-struct-read-array-struct
    (implies yes/no
             (< (pseudo-term-count struct)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-struct-write-scalar ((var symbolp)
                                       (val pseudo-termp)
                                       (prec-tags atc-string-taginfo-alistp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (mem pseudo-termp)
               (tag identp)
               (member identp)
               (mem-type typep))
  :short "Check if a @(tsee let) binding may represent a structure write
          of a scalar member."
  :long
  (xdoc::topstring
   (xdoc::p
    "A structure write of a scalar member,
     i.e. an assignment to a scalar structure member
     via a pointer to the structure,
     is represented by a @(tsee let) binding of the form")
   (xdoc::codeblock
    "(let ((<struct> (struct-<tag>-write-<member> <mem> <struct>))) ...)")
   (xdoc::p
    "where @('<struct>') is a variable of pointer type to a structure type,
     which must occur identically as
     both the @(tsee let) variable
     and as the last argument of @('struct-<tag>-write-<member>'),
     @('<mem>') is an expression that yields the member value to write,
     and @('...') represents the code that follows the assignment.
     This function takes as arguments
     the variable and value of a @(tsee let) binder,
     and checks if they have the form described above.
     If they do, the member argument is returned for further processing.
     We also return the tag, the member name, and the member type.")
   (xdoc::p
    "Similarly to @(tsee atc-check-struct-read-scalar),
     we consult the @('prec-tags') alist,
     which must contain the C structure type associated to the writer."))
  (b* (((reterr) nil nil nil (irr-ident) (irr-ident) (irr-type))
       ((acl2::fun (no)) (retok nil nil nil (irr-ident) (irr-ident) (irr-type)))
       ((mv okp fn args) (fty-check-fn-call val))
       ((unless okp) (no))
       ((mv okp struct tag write member) (atc-check-symbol-4part fn))
       ((unless (and okp
                     (equal (symbol-name struct) "STRUCT")
                     (equal (symbol-name write) "WRITE")))
        (no))
       (tag (symbol-name tag))
       (info (cdr (assoc-equal tag prec-tags)))
       ((unless info)
        (reterr (raise "Internal error: no structure with tag ~x0." tag)))
       (info (atc-tag-info->defstruct info))
       ((unless (member-eq fn (defstruct-info->writer-list info)))
        (reterr (raise "Internal error: no member writer ~x0." fn)))
       (members (defstruct-member-info-list->memtype-list
                  (defstruct-info->members info)))
       (tag (defstruct-info->tag info))
       (member (symbol-name member))
       (member (ident member))
       (mem-type (member-type-lookup member members))
       ((unless mem-type)
        (reterr (raise "Internal error: no member type for ~x0." member)))
       ((unless (list-lenp 2 args))
        (reterr (raise "Internal error: ~x0 not applied to 2 arguments." fn)))
       (mem (first args))
       ((unless (equal (second args) var))
        (reterr (raise "Internal error: ~x0 is not applied to the variable ~x1."
                       fn var))))
    (retok t fn mem tag member mem-type))
  ///

  (defret pseudo-term-count-of-atc-check-struct-write-scalar
    (implies yes/no
             (< (pseudo-term-count mem)
                (pseudo-term-count val)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-struct-write-array ((var symbolp)
                                      (val pseudo-termp)
                                      (prec-tags atc-string-taginfo-alistp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (index pseudo-termp)
               (elem pseudo-termp)
               (tag identp)
               (member identp)
               (elem-type typep)
               (flexiblep booleanp))
  :short "Check if a @(tsee let) binding may represent a structure write
          of an element of an array member."
  :long
  (xdoc::topstring
   (xdoc::p
    "A structure write of an element of an array member,
     i.e. an assignment to an element of an array structure member
     via a pointer to the structure,
     is represented by a @(tsee let) binding of the form")
   (xdoc::codeblock
    "(let ((<struct>
            (struct-<tag>-write-<member>-element <index> <elem> <struct>)))
       ...)")
   (xdoc::p
    "where @('<struct>') is a variable of structure type
     or of pointer type to a structure type,
     which must occur identically as
     both the @(tsee let) variable
     and as the last argument of @('struct-<tag>-write-<member>-element'),
     @('<index>') is an expression that yields an integer used as array index,
     @('<elem>') is an expression that yields the member element value to write,
     and @('...') represents the code that follows the assignment.
     This function takes as arguments
     the variable and value of a @(tsee let) binder,
     and checks if they have the form described above.
     If they do, the index and member argument
     are returned for further processing.
     We also return the tag, the member name, and the member type.")
   (xdoc::p
    "Similarly to @(tsee atc-check-struct-read-array),
     we consult the @('prec-tags') alist,
     which must contain the C structure type associated to the writer."))
  (b* (((reterr) nil nil nil nil (irr-ident) (irr-ident) (irr-type) nil)
       ((acl2::fun (no))
        (retok nil nil nil nil (irr-ident) (irr-ident) (irr-type) nil))
       ((mv okp fn args) (fty-check-fn-call val))
       ((unless okp) (no))
       ((mv okp struct tag write member element) (atc-check-symbol-5part fn))
       ((unless (and okp
                     (equal (symbol-name struct) "STRUCT")
                     (equal (symbol-name write) "WRITE")
                     (equal (symbol-name element) "ELEMENT")))
        (no))
       (tag (symbol-name tag))
       (info (cdr (assoc-equal tag prec-tags)))
       ((unless info)
        (reterr (raise "Internal error: no structure with tag ~x0." tag)))
       (info (atc-tag-info->defstruct info))
       ((unless (member-eq fn (defstruct-info->writer-element-list info)))
        (reterr (raise "Internal error: no member writer ~x0." fn)))
       (members (defstruct-member-info-list->memtype-list
                  (defstruct-info->members info)))
       (tag (defstruct-info->tag info))
       (member (symbol-name member))
       (member (ident member))
       (mem-type (member-type-lookup member members))
       ((unless mem-type)
        (reterr (raise "Internal error: no member type for ~x0." member)))
       ((unless (type-case mem-type :array))
        (reterr (raise "Internal error: type of ~x0 is not array." member)))
       (elem-type (type-array->of mem-type))
       (flexiblep (not (type-array->size mem-type)))
       ((unless (list-lenp 3 args))
        (reterr (raise "Internal error: ~x0 not applied to 3 arguments." fn)))
       (index (first args))
       (mem (second args))
       ((unless (equal (third args) var))
        (reterr (raise "Internal error: ~x0 is not applied to the variable ~x1."
                       fn var))))
    (retok t fn index mem tag member elem-type flexiblep))
  ///

  (defret pseudo-term-count-of-atc-check-struct-write-array-index
    (implies yes/no
             (< (pseudo-term-count index)
                (pseudo-term-count val)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-struct-write-array-elem
    (implies yes/no
             (< (pseudo-term-count elem)
                (pseudo-term-count val)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-cfun-call ((term pseudo-termp)
                             (var-term-alist symbol-pseudoterm-alistp)
                             (prec-fns atc-symbol-fninfo-alistp)
                             (wrld plist-worldp))
  :returns (mv erp
               (yes/no booleanp)
               (fn symbolp)
               (args pseudo-term-listp)
               (in-types type-listp)
               (out-type typep)
               (affect symbol-listp)
               (limit pseudo-termp)
               (fn-guard symbolp))
  :short "Check if a term may represent a call to a C function,
          and in that case check the requirements on the call arguments."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check is successful, we return
     the called function along with the arguments.
     We also return the input and output types of the function,
     the variables affected by the function,
     the limit sufficient to execute the function,
     and the local function that encapsulates the function's guard.")
   (xdoc::p
    "We also check each actual argument
     for a formal parameter of array or pointer type,
     or for a formal parameter that represents an external object,
     is identical to the formal,
     as required in the ATC user documentation.")
   (xdoc::p
    "The limit retrieved from the function table
     refers to the formal parameters.
     We must instantiate it to the actual parameters
     in order to obtain an appropriate limit for the call,
     but we also need to substitute all the bindings
     in order to obtain the real arguments of the call
     from the point of view of the top level of
     where this call term occurs."))
  (b* (((reterr) nil nil nil nil (irr-type) nil nil nil)
       ((acl2::fun (no)) (retok nil nil nil nil (irr-type) nil nil nil))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       ((when (irecursivep+ term.fn wrld)) (no))
       (fn+info (assoc-eq term.fn (atc-symbol-fninfo-alist-fix prec-fns)))
       ((unless (consp fn+info)) (no))
       (info (cdr fn+info))
       (in-types (atc-fn-info->in-types info))
       (out-type (atc-fn-info->out-type info))
       (affect (atc-fn-info->affect info))
       (extobjs (atc-fn-info->extobjs info))
       ((when (null out-type)) (no))
       (limit (atc-fn-info->limit info))
       (limit (fty-fsublis-var var-term-alist limit))
       (fn-guard (atc-fn-info->guard info))
       ((erp) (atc-check-cfun-call-args term.fn
                                        (formals+ term.fn wrld)
                                        term.args
                                        in-types
                                        extobjs)))
    (retok t term.fn term.args in-types out-type affect limit fn-guard))

  :prepwork
  ((define atc-check-cfun-call-args ((fn symbolp)
                                     (formals symbol-listp)
                                     (actuals pseudo-term-listp)
                                     (in-types type-listp)
                                     (extobjs symbol-listp))
     :returns erp
     :parents nil
     (b* (((reterr))
          ((when (endp formals))
           (cond ((consp actuals)
                  (reterr
                   (raise "Internal error: extra actuals ~x0." actuals)))
                 ((consp in-types)
                  (reterr
                   (raise "Internal error: extra types ~x0." in-types)))
                 (t (retok))))
          ((when (or (endp actuals)
                     (endp in-types)))
           (reterr (raise "Internal error: extra formals ~x0." formals)))
          (formal (car formals))
          (actual (car actuals))
          (in-type (car in-types))
          ((when (and (not (type-case in-type :pointer))
                      (not (type-case in-type :array))
                      (not (member-eq formal extobjs))))
           (atc-check-cfun-call-args fn
                                     (cdr formals)
                                     (cdr actuals)
                                     (cdr in-types)
                                     extobjs))
          ((unless (eq formal actual))
           (reterr
            (msg "Since the formal parameter ~x0 of ~x1 ~
                  has array or pointer type, ~
                  or represents an external object, ~
                  the actual argument passed to the call must be ~
                  identical to the formal parameters, ~
                  but it is ~x2 instead."
                 formal fn actual))))
       (atc-check-cfun-call-args fn
                                 (cdr formals)
                                 (cdr actuals)
                                 (cdr in-types)
                                 extobjs))))

  ///

  (defret pseudo-term-count-of-atc-check-cfun-call
    (implies yes/no
             (< (pseudo-term-list-count args)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-loop-call ((term pseudo-termp)
                             (var-term-alist symbol-pseudoterm-alistp)
                             (prec-fns atc-symbol-fninfo-alistp))
  :returns (mv (yes/no booleanp)
               (fn symbolp)
               (args pseudo-term-listp)
               (in-types type-listp)
               (affect symbol-listp)
               (loop stmtp)
               (limit pseudo-termp))
  :short "Check if a term may represent a C loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check whether this is a call of
     a function that has been previously processed
     (i.e. it is in the @('prec-fns') alist)
     and is recursive
     (indicated by the presence of the loop statement in its information).
     If the checks succeed, we return
     the function symbol,
     its arguments,
     the argument types,
     the variables affected by the loop,
     the associated loop statement,
     and the limit sufficient to execute the function call.")
   (xdoc::p
    "The limit retrieved from the function table
     refers to the formal parameters.
     We must instantiate it to the actual parameters
     in order to obtain an appropriate limit for the call,
     but we also need to substitute all the bindings
     in order to obtain the real arguments of the call
     from the point of view of the top level of
     where this call term occurs."))
  (b* (((acl2::fun (no)) (mv nil nil nil nil nil (irr-stmt) nil))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       (fn+info (assoc-eq term.fn (atc-symbol-fninfo-alist-fix prec-fns)))
       ((unless (consp fn+info)) (no))
       (info (cdr fn+info))
       (loop (atc-fn-info->loop? info))
       ((unless (stmtp loop)) (no))
       (in-types (atc-fn-info->in-types info))
       (affect (atc-fn-info->affect info))
       (limit (atc-fn-info->limit info))
       (limit (fty-fsublis-var var-term-alist limit)))
    (mv t term.fn term.args in-types affect loop limit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-let ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (var symbolp)
               (val pseudo-termp)
               (body pseudo-termp)
               (wrapper? symbolp))
  :short "Check if a term may be a @(tsee let) statement term."
  :long
  (xdoc::topstring
   (xdoc::p
    "The forms of these terms are described in the user documentation.")
   (xdoc::p
    "Here we recognize and decompose statement terms that are @(tsee let)s.
     In translated form, @('(let ((var val)) body)')
     is @('((lambda (var) body) val)').
     However, if @('body') has other free variables in addition to @('var'),
     those appear as both formal parameters and actual arguments, e.g.
     @('((lambda (var x y) rest<var,x,y>) val x y)'):
     this is because ACL2 translated terms have all closed lambda expressions,
     so ACL2 adds formal parameters and actual arguments to make that happen.
     Here, we must remove them in order to get the ``true'' @(tsee let).
     This is done via a system utility.")
   (xdoc::p
    "We also return the @(tsee declar) or @(tsee assign) wrapper,
     if present; @('nil') if absent."))
  (b* (((acl2::fun (no)) (mv nil nil nil nil nil))
       ((mv okp formals body actuals) (fty-check-lambda-call term))
       ((when (not okp)) (no))
       ((mv formals actuals) (fty-remove-equal-formals-actuals formals actuals))
       ((unless (and (list-lenp 1 formals) (list-lenp 1 actuals))) (no))
       (var (first formals))
       (possibly-wrapped-val (first actuals))
       ((unless (pseudo-term-case possibly-wrapped-val :fncall))
        (mv t var possibly-wrapped-val body nil))
       ((pseudo-term-fncall possibly-wrapped-val) possibly-wrapped-val)
       ((unless (member-eq possibly-wrapped-val.fn '(declar assign)))
        (mv t var possibly-wrapped-val body nil))
       ((unless (list-lenp 1 possibly-wrapped-val.args)) (no)))
    (mv t var (first possibly-wrapped-val.args) body possibly-wrapped-val.fn))
  :guard-hints
  (("Goal" :in-theory (enable len-of-fty-check-lambda-calls.formals-is-args)))
  ///

  (defret pseudo-term-count-of-atc-check-let-val
    (implies yes/no
             (< (pseudo-term-count val)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-let-body
    (implies yes/no
             (< (pseudo-term-count body)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-let
    (implies yes/no
             (< (+ (pseudo-term-count val)
                   (pseudo-term-count body))
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-declar/assign-n ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (wrapper symbolp)
               (n natp)
               (wrapped pseudo-termp))
  :short "Check if a term is a call of @('declar<n>') or @('assign<n>')."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the macros described in @(see atc-let-designations).
     These macros expand to")
   (xdoc::codeblock
    "(mv-let (*0 *1 *2 ... *<n>)"
    "  <wrapped>"
    "  (mv (<wrapper> *0) *1 *2 ... *<n>))")
   (xdoc::p
    "which in translated terms looks like")
   (xdoc::codeblock
    "((lambda (mv)"
    "         ((lambda (*0 *1 *2 ... *<n>)"
    "                  (cons ((<wrapper> *0) (cons *1 ... (cons *<n> 'nil)))))"
    "          (mv-nth '0 mv)"
    "          (mv-nth '1 mv)"
    "          ..."
    "          (mv-nth '<n> mv)))"
    " <wrapped>)")
   (xdoc::p
    "So here we attempt to recognize this for of translated terms.
     If successful, we return @('<wrapper>'), @('<n>'), and @('<wrapped>')."))
  (b* (((mv okp mv-var vars indices hides wrapped body)
        (fty-check-mv-let-call term))
       ((unless okp) (mv nil nil 0 nil))
       ((unless (eq mv-var 'mv)) (mv nil nil 0 nil))
       (n+1 (len vars))
       ((unless (>= n+1 2)) (mv nil nil 0 nil))
       (n (1- n+1))
       ((unless (equal vars
                       (loop$ for i of-type integer from 0 to n
                              collect (pack '* i))))
        (mv nil nil 0 nil))
       ((unless (equal indices
                       (loop$ for i of-type integer from 0 to n
                              collect i)))
        (mv nil nil 0 nil))
       ((unless (equal hides (repeat n+1 nil)))
        (mv nil nil 0 nil))
       ((mv okp terms) (fty-check-list-call body))
       ((unless okp) (mv nil nil 0 nil))
       ((unless (equal (len terms) n+1)) (mv nil nil 0 nil))
       ((cons term terms) terms)
       ((unless (pseudo-term-case term :fncall)) (mv nil nil 0 nil))
       (wrapper (pseudo-term-fncall->fn term))
       ((unless (member-eq wrapper '(declar assign))) (mv nil nil 0 nil))
       ((unless (equal (pseudo-term-fncall->args term) (list '*0)))
        (mv nil nil 0 nil))
       ((unless (equal terms
                       (loop$ for i of-type integer from 1 to n
                              collect (pack '* i))))
        (mv nil nil 0 nil)))
    (mv t wrapper n wrapped))
  :guard-hints (("Goal" :in-theory (enable fix)))
  :prepwork ((local (in-theory (enable acl2::loop-book-theory))))
  ///

  (defret pseudo-term-count-of-atc-check-declar/assign-n-wrapped
    (implies yes/no
             (< (pseudo-term-count wrapped)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-mv-let ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (var? symbolp)
               (vars symbol-listp)
               (indices nat-listp)
               (val pseudo-termp)
               (body pseudo-termp)
               (wrapper? symbolp))
  :short "Check if a term may be an @(tsee mv-let) statement term."
  :long
  (xdoc::topstring
   (xdoc::p
    "The forms of these terms are described in the user documentation.")
   (xdoc::p
    "First, we check if the term is an @(tsee mv-let),
     obtaining variables, indices, value term, and body term.
     Then we check whether the value term is
     a @('declar<n>') or an @('assign<n>'):
     in this case, we return the first variable
     separately from the other variables,
     and we also return
     the corresponding @(tsee declar) or @(tsee assign) wrapper.
     Otherwise, we return all the variables together,
     with @('nil') as the @('var?') and @('wrapper?') results."))
  (b* (((mv okp & vars indices & val body) (fty-check-mv-let-call term))
       ((when (not okp)) (mv nil nil nil nil nil nil nil))
       ((mv okp wrapper & wrapped) (atc-check-declar/assign-n val))
       ((when (not okp)) (mv t nil vars indices val body nil)))
    (mv t (car vars) (cdr vars) indices wrapped body wrapper))

  :prepwork
  ((defrulel verify-guards-lemma
     (implies (symbol-listp x)
              (iff (consp x) x))))

  ///

  (defret pseudo-term-count-of-atc-check-mv-let-val
    (implies yes/no
             (< (pseudo-term-count val)
                (pseudo-term-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atc-check-mv-let-body
    (implies yes/no
             (< (pseudo-term-count body)
                (pseudo-term-count term)))
    :rule-classes :linear))
