; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-structurals")

(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable type+ispace-p-when-result-not-error
                          type+ispace-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-matching-operations
  :parents (abstract-syntax)
  :short "Operations to match ASTs to patterns."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce operations to check whether
     certain ASTs match certain patterns,
     in which case the components of the pattern are returned.")
   (xdoc::p
    "We start by adding a few of them that are needed elsewhere,
     but we plan to add more."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-array ((type typep))
  :returns (type+ispace type+ispace-resultp)
  :short "Check if an array type is a non-variable array type or an atom type,
          returning its elements' atom type and its ispace if successful."
  :long
  (xdoc::topstring
   (xdoc::p
    "In ASTs, atom types may be used where array types are expected.
     Thus, this function succeeds on atom types,
     regarding them as scalar (i.e. 0-ranked) arrays.
     The function also succeeds in array types,
     both explicit and in bracket form.
     The only case in which this does not succeed is on array type variables,
     because we could not obtain the element atom type and the ispace."))
  (cond
   ((type-atomp type)
    (make-type+ispace :type type :ispace (ispace-shape (shape-dims nil))))
   ((type-case type :array)
    (make-type+ispace :type (type-array->elem type)
                      :ispace (type-array->ispace type)))
   ((type-case type :bracket)
    (make-type+ispace :type (type-bracket->elem type)
                      :ispace (ispace-shape
                               (shape-append
                                (shape-list-from-ispace-list
                                 (type-bracket->ispaces type))))))
   (t (reserr nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-match-array ((types type-listp))
  :returns (types+ispaces type+ispace-list-resultp)
  :short "Check if all the array types in a list are @(':array') summands,
          returning the list of their elements' atom types and its ispaces
          if successful."
  (b* (((when (endp types)) nil)
       ((ok type+ispace) (type-match-array (car types)))
       ((ok types+ispaces) (type-list-match-array (cdr types))))
    (cons type+ispace types+ispaces))

  ///

  (defret len-of-type-list-match-array
    (implies (not (reserrp types+ispaces))
             (equal (len types+ispaces)
                    (len types)))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-fun ((type typep))
  :returns (in+rest type+type-resultp)
  :short "Check if an atom type is a function type,
          peeling off its first input type if successful."
  :long
  (xdoc::topstring
   (xdoc::p
    "Consistently with the curried view of term applications
     (see @(tsee expr)),
     a function type is treated as
     the nesting of one-input function types.
     Accordingly, this matching operation peels off one input type:
     if the type is a function type with at least one input,
     we return the first input type,
     along with the output type of the function type
     if there are no other inputs,
     or otherwise the function type over the remaining inputs.
     A function type with no inputs fails to match.")
   (xdoc::p
    "Unlike @(tsee type-match-forall) and @(tsee type-match-product),
     there is no unary form of function type to match directly:
     a function type always has an explicit list of input types,
     which will be similarly given a unary form."))
  (b* (((unless (type-case type :fun)) (reserr nil))
       (ins (type-fun->in type))
       (out (type-fun->out type))
       ((unless (consp ins)) (reserr nil)))
    (make-type+type
     :type1 (car ins)
     :type2 (if (consp (cdr ins))
                (make-type-fun :in (cdr ins) :out out)
              out))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-forall ((type typep))
  :returns (var+type typevar+type-resultp)
  :short "Check if an atom type is a universal type,
          peeling off its first type parameter variable if successful."
  :long
  (xdoc::topstring
   (xdoc::p
    "A unary universal type is matched directly:
     we return its bound variable and its body.")
   (xdoc::p
    "Consistently with the curried view of type applications
     (see @(tsee expr)),
     an n-ary universal type is treated as
     the nesting of unary universal types.
     Accordingly, this matching operation peels off one variable:
     if the type is an n-ary universal type with at least one variable,
     we return the first variable,
     along with the body of the universal type
     if there are no other variables,
     or otherwise the universal type over the remaining variables.
     An n-ary universal type with no variables fails to match."))
  (b* (((when (type-case type :forall))
        (make-typevar+type :var (type-forall->param type)
                           :type (type-forall->body type)))
       ((unless (type-case type :foralln)) (reserr nil))
       (params (type-foralln->params type))
       (body (type-foralln->body type))
       ((unless (consp params)) (reserr nil)))
    (make-typevar+type
     :var (car params)
     :type (if (consp (cdr params))
               (make-type-foralln :params (cdr params) :body body)
             body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-product ((type typep))
  :returns (var+type ispacevar+type-resultp)
  :short "Check if an atom type is a product type,
          peeling off its first ispace parameter variable if successful."
  :long
  (xdoc::topstring
   (xdoc::p
    "A unary product type is matched directly:
     we return its bound variable and its body.")
   (xdoc::p
    "Consistently with the curried view of ispace applications
     (see @(tsee expr)),
     an n-ary product type is treated as
     the nesting of unary product types.
     Accordingly, this matching operation peels off one variable:
     if the type is an n-ary product type with at least one variable,
     we return the first variable,
     along with the body of the product type
     if there are no other variables,
     or otherwise the product type over the remaining variables.
     An n-ary product type with no variables fails to match."))
  (b* (((when (type-case type :pi))
        (make-ispacevar+type :var (type-pi->param type)
                             :type (type-pi->body type)))
       ((unless (type-case type :pin)) (reserr nil))
       (params (type-pin->params type))
       (body (type-pin->body type))
       ((unless (consp params)) (reserr nil)))
    (make-ispacevar+type
     :var (car params)
     :type (if (consp (cdr params))
               (make-type-pin :params (cdr params) :body body)
             body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-match-sum ((type typep))
  :returns (vars+type ispacevarlist+type-resultp)
  :short "Check if a type is a sum type,
          returning its ispace parameter variables and body array type
          if successful."
  (if (type-case type :sigman)
      (make-ispacevarlist+type :vars (type-sigman->params type)
                               :type (type-sigman->body type))
    (reserr nil)))
