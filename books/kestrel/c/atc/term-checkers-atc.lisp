; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "term-checkers-common")
(include-book "function-tables")
(include-book "tag-tables")

(include-book "kestrel/std/system/irecursivep-plus" :dir :system)

(local (include-book "projects/apply/loop" :dir :system))
(local (in-theory (disable acl2::loop-book-theory)))

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
  :returns (mv (yes/no booleanp)
               (arg pseudo-termp))
  :short "Check if a term may represent a conversion
          from an ACL2 boolean to a C @('int') value."
  (b* (((acl2::fun (no)) (mv nil nil))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless (and okp
                     (eq fn 'c::sint-from-boolean)
                     (list-lenp 1 args)))
        (no)))
    (mv t (first args)))
  ///

  (defret pseudo-term-count-of-atc-check-sint-from-boolean
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-boolean-from-type ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (arg pseudo-termp)
               (in-type typep))
  :short "Check if a term may represent a conversion
          from a C integer value to an ACL2 boolean."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also return the input C type of the conversion.
     The output type is known (boolean), and it is in fact an ACL2 type."))
  (b* (((acl2::fun (no)) (mv nil nil (irr-type)))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless okp) (no))
       ((mv okp boolean from type) (atc-check-symbol-3part fn))
       ((unless (and okp
                     (eq boolean 'boolean)
                     (eq from 'from)))
        (no))
       (in-type (fixtype-to-integer-type type))
       ((when (not in-type)) (no))
       ((unless (list-lenp 1 args)) (no)))
    (mv t (first args) in-type))
  ///

  (defret pseudo-term-count-of-atc-check-boolean-from-type
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-condexpr ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (test pseudo-termp)
               (then pseudo-termp)
               (else pseudo-termp))
  :short "Check if a term may represent a C conditional expression."
  (b* (((acl2::fun (no)) (mv nil nil nil nil))
       ((mv okp fn args) (fty-check-fn-call term))
       ((unless (and okp
                     (eq fn 'c::condexpr)
                     (list-lenp 1 args)))
        (no)))
    (fty-check-if-call (first args)))
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

(define atc-check-array-read ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (arr pseudo-termp)
               (sub pseudo-termp)
               (in-type1 typep)
               (in-type2 typep)
               (out-type typep))
  :short "Check if a term may represent an array read."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C array read operations,
     we return the two argument terms.")
   (xdoc::p
    "We also return the input and output C types of the array read.")
   (xdoc::p
    "If the term does not have the form explained above,
     we return an indication of failure."))
  (b* (((acl2::fun (no)) (mv nil nil nil (irr-type) (irr-type) (irr-type)))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       ((mv okp etype array read itype) (atc-check-symbol-4part term.fn))
       ((unless (and okp
                     (eq array 'array)
                     (eq read 'read)))
        (no))
       (out-type (fixtype-to-integer-type etype))
       ((when (not out-type)) (no))
       (in-type1 (type-pointer out-type))
       (in-type2 (fixtype-to-integer-type itype))
       ((when (not in-type2)) (no))
       ((unless (list-lenp 2 term.args)) (no))
       (arr (first term.args))
       (sub (second term.args)))
    (mv t arr sub in-type1 in-type2 out-type))
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
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-array-write ((var symbolp) (val pseudo-termp))
  :returns (mv (yes/no booleanp)
               (sub pseudo-termp)
               (elem pseudo-termp)
               (sub-type typep)
               (elem-type typep))
  :short "Check if a @(tsee let) binding may represent an array write."
  :long
  (xdoc::topstring
   (xdoc::p
    "An array write, i.e. an assignment to an array element,
     is represented by a @(tsee let) binding of the form")
   (xdoc::codeblock
    "(let ((<arr> (<type1>-array-write-<type2> <arr> <sub> <elem>))) ...)")
   (xdoc::p
    "where @('<arr>') is a variable of pointer type to an integer type,
     which must occur identically as
     both the @(tsee let) variable
     and as the first argument of @('<type1>-array-write-<type2>'),
     @('<sub>') is an expression that yields the index of the element to write,
     @('<elem>') is an expression that yields the element to write,
     and @('...') represents the code that follows the array assignment.
     This function takes as arguments
     the variable and value of a @(tsee let) binder,
     and checks if they have the form described above.
     If they do, the components are returned for further processing.
     We also return the types of the index and element
     as gathered from the name of the array write function."))
  (b* (((acl2::fun (no)) (mv nil nil nil (irr-type) (irr-type)))
       ((unless (pseudo-term-case val :fncall)) (no))
       ((pseudo-term-fncall val) val)
       ((mv okp etype array write itype) (atc-check-symbol-4part val.fn))
       ((unless (and okp
                     (eq array 'array)
                     (eq write 'write)))
        (no))
       (sub-type (fixtype-to-integer-type itype))
       ((unless sub-type) (no))
       (elem-type (fixtype-to-integer-type etype))
       ((when (not elem-type)) (no))
       ((unless (list-lenp 3 val.args)) (no))
       (arr (first val.args))
       (sub (second val.args))
       (elem (third val.args)))
    (if (eq arr var)
        (mv t sub elem sub-type elem-type)
      (no)))
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
  :returns (mv (yes/no booleanp)
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
  (b* (((acl2::fun (no))
        (mv nil nil (irr-ident) (irr-ident) (irr-type)))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       ((mv okp struct tag read member) (atc-check-symbol-4part term.fn))
       ((unless (and okp
                     (equal (symbol-name struct) "STRUCT")
                     (equal (symbol-name read) "READ")))
        (no))
       (tag (symbol-name tag))
       (info (cdr (assoc-equal tag prec-tags)))
       ((unless info) (no))
       (info (atc-tag-info->defstruct info))
       ((unless (member-eq term.fn (defstruct-info->readers info))) (no))
       (tag (defstruct-info->tag info))
       (members (defstruct-member-info-list->memtype-list
                  (defstruct-info->members info)))
       (member (symbol-name member))
       ((unless (paident-stringp member)) (no))
       (member (ident member))
       (mem-type (member-type-lookup member members))
       ((unless mem-type) (no))
       ((unless (list-lenp 1 term.args)) (no))
       (arg (car term.args)))
    (mv t arg tag member mem-type))
  ///

  (defret pseudo-term-count-of-atc-check-struct-read-scalar
    (implies yes/no
             (< (pseudo-term-count arg)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-struct-read-array ((term pseudo-termp)
                                     (prec-tags atc-string-taginfo-alistp))
  :returns (mv (yes/no booleanp)
               (index pseudo-termp)
               (struct pseudo-termp)
               (tag identp)
               (member identp)
               (index-type typep)
               (elem-type typep))
  :short "Check if a term may represent a structure read
          of an element of an array member."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C structure read operations for array members,
     we return the argument terms (index and structure),
     the tag name, and the name of the member.
     The C structure type of the reader must be in the preceding tags;
     we consult the alist to retrieve the relevant information.")
   (xdoc::p
    "We also return the types of the index and the array element.")
   (xdoc::p
    "If the term does not have the right form,
     we return an indication of failure."))
  (b* (((acl2::fun (no))
        (mv nil nil nil (irr-ident) (irr-ident) (irr-type) (irr-type)))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       ((mv okp struct tag read member type) (atc-check-symbol-5part term.fn))
       ((unless (and okp
                     (equal (symbol-name struct) "STRUCT")
                     (equal (symbol-name read) "READ")))
        (no))
       (tag (symbol-name tag))
       (info (cdr (assoc-equal tag prec-tags)))
       ((unless info) (no))
       (info (atc-tag-info->defstruct info))
       ((unless (member-eq term.fn (defstruct-info->readers info))) (no))
       (tag (defstruct-info->tag info))
       (members (defstruct-member-info-list->memtype-list
                  (defstruct-info->members info)))
       (member (symbol-name member))
       ((unless (paident-stringp member)) (no))
       (member (ident member))
       (mem-type (member-type-lookup member members))
       ((unless mem-type) (no))
       ((unless (type-case mem-type :array)) (no))
       (elem-type (type-array->of mem-type))
       (type (pack type))
       (index-type (fixtype-to-integer-type type))
       ((unless index-type) (no))
       ((unless (list-lenp 2 term.args)) (no))
       (index (first term.args))
       (struct (second term.args)))
    (mv t index struct tag member index-type elem-type))
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
  :returns (mv (yes/no booleanp)
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
  (b* (((acl2::fun (no)) (mv nil nil (irr-ident) (irr-ident) (irr-type)))
       ((unless (pseudo-term-case val :fncall)) (no))
       ((pseudo-term-fncall val) val)
       ((mv okp struct tag write member) (atc-check-symbol-4part val.fn))
       ((unless (and okp
                     (equal (symbol-name struct) "STRUCT")
                     (equal (symbol-name write) "WRITE")))
        (no))
       (tag (symbol-name tag))
       (info (cdr (assoc-equal tag prec-tags)))
       ((unless info) (no))
       (info (atc-tag-info->defstruct info))
       ((unless (member-eq val.fn (defstruct-info->writers info))) (no))
       (members (defstruct-member-info-list->memtype-list
                  (defstruct-info->members info)))
       (tag (defstruct-info->tag info))
       (member (symbol-name member))
       ((unless (paident-stringp member)) (no))
       (member (ident member))
       (mem-type (member-type-lookup member members))
       ((unless mem-type) (no))
       ((unless (list-lenp 2 val.args)) (no))
       (mem (first val.args))
       (struct (second val.args)))
    (if (equal struct var)
        (mv t mem tag member mem-type)
      (no)))
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
  :returns (mv (yes/no booleanp)
               (index pseudo-termp)
               (elem pseudo-termp)
               (tag identp)
               (member identp)
               (index-type typep)
               (elem-type typep))
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
            (struct-<tag>-write-<member>-<type> <index> <elem> <struct>)))
       ...)")
   (xdoc::p
    "where @('<struct>') is a variable of pointer type to a structure type,
     which must occur identically as
     both the @(tsee let) variable
     and as the last argument of @('struct-<tag>-write-<member>'),
     @('<index>') is an expression that yields an integer used as array index,
     @('<elem>') is an expression that yields the member element value to write,
     and @('...') represents the code that follows the assignment.
     This function takes as arguments
     the variable and value of a @(tsee let) binder,
     and checks if they have the form described above.
     If they do, the index and member argument
     are returned for further processing.
     We also return
     the tag, the member name, the index type, and the member type.")
   (xdoc::p
    "Similarly to @(tsee atc-check-struct-read-array),
     we consult the @('prec-tags') alist,
     which must contain the C structure type associated to the writer."))
  (b* (((acl2::fun (no))
        (mv nil nil nil (irr-ident) (irr-ident) (irr-type) (irr-type)))
       ((unless (pseudo-term-case val :fncall)) (no))
       ((pseudo-term-fncall val) val)
       ((mv okp struct tag write member type) (atc-check-symbol-5part val.fn))
       ((unless (and okp
                     (equal (symbol-name struct) "STRUCT")
                     (equal (symbol-name write) "WRITE")))
        (no))
       (tag (symbol-name tag))
       (info (cdr (assoc-equal tag prec-tags)))
       ((unless info) (no))
       (info (atc-tag-info->defstruct info))
       ((unless (member-eq val.fn (defstruct-info->writers info))) (no))
       (members (defstruct-member-info-list->memtype-list
                  (defstruct-info->members info)))
       (tag (defstruct-info->tag info))
       (member (symbol-name member))
       ((unless (paident-stringp member)) (no))
       (member (ident member))
       (mem-type (member-type-lookup member members))
       ((unless mem-type) (no))
       ((unless (type-case mem-type :array)) (no))
       (elem-type (type-array->of mem-type))
       (type (pack type))
       (index-type (fixtype-to-integer-type type))
       ((unless index-type) (no))
       ((unless (list-lenp 3 val.args)) (no))
       (index (first val.args))
       (mem (second val.args))
       (struct (third val.args)))
    (if (equal struct var)
        (mv t index mem tag member index-type elem-type)
      (no)))
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
  :returns (mv (yes/no booleanp)
               (fn symbolp)
               (args pseudo-term-listp)
               (in-types type-listp)
               (out-type typep)
               (affect symbol-listp)
               (limit pseudo-termp))
  :short "Check if a term may represent a call to a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check is successful, we return
     the called function along with the arguments.
     We also return the input and output types of the function,
     the variables affected by the function,
     and the limit sufficient to execute the function.")
   (xdoc::p
    "The limit retrieved from the function table
     refers to the formal parameters.
     We must instantiate it to the actual parameters
     in order to obtain an appropriate limit for the call,
     but we also need to substitute all the bindings
     in order to obtain the real arguments of the call
     from the point of view of the top level of
     where this call term occurs."))
  (b* (((acl2::fun (no)) (mv nil nil nil nil (irr-type) nil nil))
       ((unless (pseudo-term-case term :fncall)) (no))
       ((pseudo-term-fncall term) term)
       ((when (irecursivep+ term.fn wrld)) (no))
       (fn+info (assoc-eq term.fn (atc-symbol-fninfo-alist-fix prec-fns)))
       ((unless (consp fn+info)) (no))
       (info (cdr fn+info))
       (in-types (atc-fn-info->in-types info))
       (out-type (atc-fn-info->out-type info))
       (affect (atc-fn-info->affect info))
       ((when (null out-type)) (no))
       (limit (atc-fn-info->limit info))
       (limit (fty-fsublis-var var-term-alist limit)))
    (mv t term.fn term.args in-types out-type affect limit))
  ///

  (defret pseudo-term-count-of-atc-check-cfun-call-args
    (implies yes/no
             (< (pseudo-term-list-count args)
                (pseudo-term-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-cfun-call-args ((formals symbol-listp)
                                  (in-types type-listp)
                                  (args pseudo-term-listp))
  :returns (yes/no booleanp)
  :short "Check the arguments of a call to a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called after @(tsee atc-check-cfun-call),
     if the latter is successful.
     As stated in the user documentation of ATC,
     calls of non-recursive target functions must satisfy the property that
     the argument for a formal of pointer type must be identical to the formal.
     This is because these arguments and formals
     represent (pointers to) arrays and structures,
     and thus they must be passed around exactly by their name,
     similarly to stobjs in ACL2.
     This code checks the condition."))
  (b* (((when (endp formals))
        (cond ((consp in-types)
               (raise "Internal error: extra types ~x0." in-types))
              ((consp args)
               (raise "Internal error: extra arguments ~x0." args))
              (t t)))
       ((when (or (endp in-types)
                  (endp args)))
        (raise "Internal error: extra formals ~x0." formals))
       (formal (car formals))
       (in-type (car in-types))
       (arg (car args))
       ((unless (type-case in-type :pointer))
        (atc-check-cfun-call-args (cdr formals) (cdr in-types) (cdr args)))
       ((unless (eq formal arg)) nil))
    (atc-check-cfun-call-args (cdr formals) (cdr in-types) (cdr args))))

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
    "(mv-let (*1 *2 ... *<n>)"
    "  <wrapped>"
    "  (mv (<wrapper> *1) *2 ... *<n>))")
   (xdoc::p
    "which in translated terms looks like")
   (xdoc::codeblock
    "((lambda (mv)"
    "         ((lambda (*1 *2 ... *<n>)"
    "                  (cons ((<wrapper> *1) (cons *2 ... (cons *<n> 'nil)))))"
    "          (mv-nth '0 mv)"
    "          (mv-nth '1 mv)"
    "          ..."
    "          (mv-nth '<n-1> mv)))"
    " <wrapped>)")
   (xdoc::p
    "So here we attempt to recognize this for of translated terms.
     If successful, we return @('<wrapper>'), @('<n>'), and @('<wrapped>')."))
  (b* (((mv okp mv-var vars indices hides wrapped body)
        (fty-check-mv-let-call term))
       ((unless okp) (mv nil nil 0 nil))
       ((unless (eq mv-var 'mv)) (mv nil nil 0 nil))
       (n (len vars))
       ((unless (>= n 2)) (mv nil nil 0 nil))
       ((unless (equal vars
                       (loop$ for i of-type integer from 1 to n
                              collect (pack '* i))))
        (mv nil nil 0 nil))
       ((unless (equal indices
                       (loop$ for i of-type integer from 0 to (1- n)
                              collect i)))
        (mv nil nil 0 nil))
       ((unless (equal hides (repeat n nil)))
        (mv nil nil 0 nil))
       ((mv okp terms) (fty-check-list-call body))
       ((unless okp) (mv nil nil 0 nil))
       ((unless (equal (len terms) n)) (mv nil nil 0 nil))
       ((cons term terms) terms)
       ((unless (pseudo-term-case term :fncall)) (mv nil nil 0 nil))
       (wrapper (pseudo-term-fncall->fn term))
       ((unless (member-eq wrapper '(declar assign))) (mv nil nil 0 nil))
       ((unless (equal (pseudo-term-fncall->args term) (list '*1)))
        (mv nil nil 0 nil))
       ((unless (equal terms
                       (loop$ for i of-type integer from 2 to n
                              collect (pack '* i))))
        (mv nil nil 0 nil)))
    (mv t wrapper n wrapped))
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
