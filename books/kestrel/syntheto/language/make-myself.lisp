; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/defset" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/nth" :dir :system))

(include-book "std/testing/assert-equal" :dir :system)

(include-book "abstract-syntax")

;; todo: take out unneeded include-book forms

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note, to serialize an AST object x of type TTT, do
;;   (ttt--make-myself x).
;; The resulting form, if submitted, creates an AST object equal to x.

;; WARNING: for now the make-mm-{prod,sum,list,option} forms
;; must be kept in sync with abstract-syntax.lisp.

;; This functionality can be better automated.
;; For now, it works, but it would be better to create the make-myself functions
;; either (1) from the fty tables (see books/centaur/fty/database.lisp)
;; or (2) when we do defprod, etc. we could change them to also generate
;; the ttt--make-myself functions as well.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: think about whether it is better to do
;;       (:PROD (name . fields))  or  (name (:prod . fields))
;;       or maybe some other form.

;; Here we represent the data type summaries compactly.
;;
;; The following is a mixup of syntaxes, we can make it more clear later.
;;
;; field = (fieldname . fieldtype)
;; prodtype = (:prod . (name . fields))
;; alternative = (name . fields)  ; the name is a keyword symbol
;; sumtype = (:sum . (name . alternatives))
;; optiontype = (:option . (name . basetype))
;; listtype = (:list . (name . basetype))
;; syntheto-type = prodtype | sumtype | optiontype | listtype
;; syntheto-types = ( syntheto-type.. )
;;
;; All the names here are symbols, mostly in the SYNTHETO package.
;;
;; fieldtype and basetype are either a primitive type or a defined type.
;; primitive types: bool, character, string, nat
;; predicates for primitive types: booleanp, characterp, stringp, natp

;; Predicates for syntheto ast types always just have "P" appended to the type name.

;; Examples:
#||
 (:prod . (identifier . ((name . string))))
 (:sum . (type . ( (:boolean . ())
                   (:character . ())
                   (:string . ())
                   (:integer . ())
                   (:set . ((element . type)))
                   (:sequence . ((element . type)))
                   (:map . ((domain . type)
                            (range . type)))
                   (:option . ((base . type)))
                   (:defined . ((name . identifier))) )))
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; types

;; For the subset of FTY used to define the Syntheto abstract syntax,
;; we use the fty::basetypes
;;   bool, character, string, nat
;; which have the corresponding predicates
;;   booleanp, characterp, stringp, and natp

(define mm-primitive-type-p ((typename symbolp))
  :returns (yes/no booleanp)
  (and (member typename '(bool character string nat))
       t))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; predicate function names

;; This works for all types except bool.
;; If we need this to work for primitive types, add a special case.
(define pred-name-for-typename ((typename symbolp))
  :returns (pred-name symbolp)
  (intern-in-package-of-symbol (fty::cat (symbol-name typename) "P")
                               typename))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; make-xxx function names

(define make-name-for-prodname ((prodname symbolp))
  :returns (make-name symbolp)
  (intern-in-package-of-symbol
   (fty::cat "MAKE-" (symbol-name prodname))
   prodname))

(define make-name-for-sum-alternative ((sumname symbolp) (altname symbolp))
  :returns (make-name symbolp)
  (intern-in-package-of-symbol
   (fty::cat "MAKE-" (symbol-name sumname) "-" (symbol-name altname))
   sumname))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; field accessor names

(define field-accessor-name-for-prodname ((prodname symbolp) (fieldname symbolp))
  :returns (field-accessor-name symbolp)
  (intern-in-package-of-symbol (fty::cat (symbol-name prodname) "->" (symbol-name fieldname))
                               prodname))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; case macro name for sum type
(define case-macro-name-for-sumname ((sumname symbolp))
  :returns (case-macro-name symbolp)
  (intern-in-package-of-symbol (fty::cat (symbol-name sumname) "-CASE")
                               sumname))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; make-myself function names

;; Each composite ast type in Syntheto has a specific make-myself function.

(define mm-def-name ((typename symbolp))
  :returns (defname symbolp)
  (intern-in-package-of-symbol (fty::cat (symbol-name typename) "--MAKE-MYSELF")
                               typename))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Construct form that calls the make-myself function on a field
;; of the object returned by callee-form.
;; E.g.
;;   (mm-subcomponent-make-call 'identifier 'identifier->name 'obj)

(define mm-subcomponent-make-call ((callee-typename symbolp)
                                   (field-accessor symbolp)
                                   callee-form)
  :returns (callform listp)
  (let ((callee-functionname (mm-def-name callee-typename)))
    (list callee-functionname
          (list field-accessor callee-form))))

;; todo: move field-specp and field-spec-listp elsewhere
(define field-specp (x)
  :returns (yes/no booleanp)
  :enabled t
  (and (consp x)
       (symbolp (car x))
       (symbolp (cdr x))))

(std::deflist field-spec-listp (x)
  (field-specp x)
  :true-listp t)


;; TODO: rationalize the parameters
;;
;; Internal part of make-mm-prod
;;
;; PRODNAME is the product type name,
;;   or in the case of a sum type , it is sumname-altname.
;; FIELD is (FIELDNAME . FIELDTYPE)

;; Returns something useful for putting into a
;;   MAKE-xxx call.
;; Example, atomic field type:
;;   (mm-field-maker 'obj 'identifier '(name . string))
;;   -->
;;   (:name (identifier->name obj))
;; Example, composite field type:
;;   (mm-field-maker 'obj 'typed-variable '(name . identifier))
;;   -->
;;   (:name (identifier--make-myself (typed-variable->name obj)))
;;
(define mm-field-maker (obj-form (prodname symbolp) (field field-specp))
  :returns (retform listp)
  (let ((fieldname (car field)) (fieldtype (cdr field)))
    (let ((field-accessor (field-accessor-name-for-prodname prodname fieldname)))
    (list (intern (symbol-name fieldname) "KEYWORD")
          (if (mm-primitive-type-p fieldtype)
              (if (equal fieldtype 'character)
                  `(list 'code-char (char-code (,field-accessor ,obj-form)))
                `(,field-accessor ,obj-form))
            (mm-subcomponent-make-call fieldtype field-accessor obj-form))))))


;; Internal part of make-mm-definition--prod
(define mm-field-makers (obj-form (prodname symbolp) (fields field-spec-listp))
  :returns (retform listp)
  (if (endp fields)
      nil
    (append (mm-field-maker obj-form prodname (first fields))
            (mm-field-makers obj-form prodname (rest fields)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Macro that generates make-myself definition for a specific product type.

;; E.g.
;;   (make-mm-prod IDENTIFIER ((NAME . STRING)))
;;   :pe IDENTIFIER--MAKE-MYSELF
;; shows
;;   (DEFINE IDENTIFIER--MAKE-MYSELF
;;         ((OBJ IDENTIFIERP))
;;         :RETURNS (RETFORM LISTP)
;;         (LIST 'MAKE-IDENTIFIER
;;               :NAME (IDENTIFIER->NAME OBJ)))

;; When the prod has a composite subcomponent, call it xx,
;; the generated definition will call the xx--MAKE-MYSELF function,
;; so the macro that defines xx--MAKEMYSELF must be invoked
;; prior to the macro that defines the prodname--MAKEMYSELF that calls it.

;; Similarly, when deftypes defines a clique of recursive types,
;; the corresponding macros should be inside a defines.

(defmacro make-mm-prod (prodname fields)
  (let ((def-name (mm-def-name prodname))
        (pred-name (pred-name-for-typename prodname))
        (make-name (make-name-for-prodname prodname))
        (make-fields (mm-field-makers 'obj prodname fields)))

    `(define ,def-name ((obj ,pred-name))
       :returns (retform listp) ; do we need a type for the return val?
       (list ',make-name
             ,@make-fields))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example.

(make-mm-prod identifier ((name . string)))

(acl2::assert-equal (identifier--make-myself (make-identifier :name "abc"))
                    '(make-identifier :name "abc"))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; generate cases for building sum type

(define alternative-specp (x)
  :returns (yes/no booleanp)
  :enabled t
  (and (consp x)
       (symbolp (car x))
       (field-spec-listp (cdr x))))

(std::deflist alternative-spec-listp (x)
  (alternative-specp x)
  :true-listp t)

(define make-mm-alt ((sumname symbolp)
                     (altname symbolp) ; in keyword package
                     (fields field-spec-listp)
                     callee-form)
  :returns (retform listp)
  (let ((sum-dash-alt (intern-in-package-of-symbol
                       (fty::cat (symbol-name sumname) "-" (symbol-name altname))
                       sumname)))
    (let ((make-name (make-name-for-sum-alternative sumname altname))
          (make-fields (mm-field-makers callee-form sum-dash-alt fields)))
      `(list ',make-name
             ,@make-fields))))

(define make-mm-sum-case ((sumname symbolp)
                           (alternative alternative-specp)
                           callee-form)
  :returns (retform listp)
  (let ((alternative-name (car alternative))
        (fields (cdr alternative)))
    (list alternative-name
          (make-mm-alt sumname alternative-name fields callee-form))))

(define make-mm-sum-cases ((sumname symbolp)
                           (alternatives alternative-spec-listp)
                           callee-form)
  :returns (retform listp)
  (if (endp alternatives)
      nil
    (let ((first-sum-case (make-mm-sum-case sumname (first alternatives) callee-form))
          (rest-sum-cases (make-mm-sum-cases sumname (rest alternatives) callee-form)))
      (append first-sum-case rest-sum-cases))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Macro that generates make-myself definition for a specific sum type.

;; This does not support recursive types yet,
;; e.g. these will be done by hand for now: syntheto::type and syntheto::expression

(defmacro make-mm-sum (sumname alternatives)
  (let ((def-name (mm-def-name sumname))
        (pred-name (pred-name-for-typename sumname))
        (case-name (case-macro-name-for-sumname sumname))
        )
    `(define ,def-name ((obj ,pred-name))
       :returns (retform listp)
       (,case-name obj ,@(make-mm-sum-cases sumname alternatives 'obj)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Define type--make-myself by hand due to the :measure.
;;  (Other than measure, the automatically-created version does generate
;;   the right code, as you can see by this:
;;   :trans1 (make-mm-sum type ( (:boolean . ()) (:character . ()) (:string . ()) (:integer . ()) (:set . ((element . type))) (:sequence . ((element . type))) (:map . ((domain . type) (range . type))) (:option . ((base . type))) (:defined . ((name . identifier))) ) )

;; Input: an object of type TYPE.
;; Output a form that makes that object, including its recursive components.
(define type--make-myself ((ty typep))
  :returns (make-myself-form listp)
  (type-case ty
    :boolean '(make-type-boolean)
    :character '(make-type-character)
    :string '(make-type-string)
    :integer '(make-type-integer)
    :set (list 'make-type-set ':element (type--make-myself (type-set->element ty)))
    :sequence (list 'make-type-sequence ':element (type--make-myself (type-sequence->element ty)))
    :map (list 'make-type-map
               ':domain (type--make-myself (type-map->domain ty))
               ':range (type--make-myself (type-map->range ty)))
    :option (list 'make-type-option ':base (type--make-myself (type-option->base ty)))
    :defined (list 'make-type-defined ':name (identifier--make-myself (type-defined->name ty))))
  :measure (type-count ty))

(acl2::assert-equal (type--make-myself
                     (make-type-set :element (make-type-boolean)))
                    '(make-type-set :element (make-type-boolean)))

(acl2::assert-equal (type--make-myself
                     (make-type-sequence :element (make-type-set :element (make-type-boolean))))
                    '(make-type-sequence :element (make-type-set :element (make-type-boolean))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Macro that generates make-myself definition for a list type

;; move this elsewhere, maybe
(define mms-name-for-list-type-name ((list-type-name symbolp))
  :returns (mms-name symbolp)
  (intern-in-package-of-symbol
   (fty::cat (symbol-name list-type-name) "--MAKE-MYSELFS")
   list-type-name))

;; NOTE:
;; loop$ doesn't work to do mapcar unless I badger it.
;; instead of loop$ I use defprojection.
;; A gotcha: (defprojection .. :result-type true-listp) does not work
;; because it already tries to define a thm with the same name,
;; and the second one fails.


;; The base type of a list type is always either a prod or sum type;
;; never a primitive, option, or list type.
(defmacro make-mm-list (list-type-name basetype)
  (let ((def-name (mm-def-name list-type-name))
        (pred-name (pred-name-for-typename list-type-name))
        (make-myselfs-name (mms-name-for-list-type-name list-type-name))
        (make-base-name (mm-def-name basetype)))
    `(progn
       (std::defprojection ,make-myselfs-name ((x ,pred-name))
          (,make-base-name x))
       (define ,def-name ((obj ,pred-name))
         :returns (retform listp)
         (let ((make-forms (,make-myselfs-name obj)))
           (cons 'list make-forms))))))

(make-mm-list identifier-list identifier)

(acl2::assert-equal (identifier-list--make-myself
               (list (make-identifier :name "a") (make-identifier :name "b")))
              '(list (make-identifier :name "a") (make-identifier :name "b")))


(make-mm-list type-list type)

(acl2::assert-equal
 (type-list--make-myself
  (list (make-type-boolean)
        (make-type-set :element (make-type-integer))
        (make-type-option :base
                          (make-type-defined :name
                                             (make-identifier :name "cde")))))
  '(list (make-type-boolean)
        (make-type-set :element (make-type-integer))
        (make-type-option :base
                          (make-type-defined :name
                                             (make-identifier :name "cde")))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Macro that generates make-myself definition for an option type


(defmacro make-mm-option (option-type-name basetype)
  (let ((def-name (mm-def-name option-type-name))
        (pred-name (pred-name-for-typename option-type-name))
        (base-def-name (mm-def-name basetype)))
    `(define ,def-name ((obj ,pred-name))
       :returns (retform listp)
       (if (null obj)
           nil
         (,base-def-name obj)))))

(make-mm-option maybe-type type)

(acl2::assert-equal (MAYBE-TYPE--MAKE-MYSELF nil)
                    nil)

(acl2::assert-equal (MAYBE-TYPE--MAKE-MYSELF
                     (make-type-boolean))
                    '(make-type-boolean))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Continuing with the definitions, following the order in
;; abstract-syntax.lisp

(make-mm-prod typed-variable ((name . identifier) (type . type)))

(acl2::assert-equal
 (typed-variable--make-myself
  (make-typed-variable :name (make-identifier :name "def") :type (make-type-string)))
 '(make-typed-variable :name (make-identifier :name "def") :type (make-type-string)))


(make-mm-list typed-variable-list typed-variable)

(acl2::assert-equal
 (typed-variable-list--make-myself
  (list (make-typed-variable :name (make-identifier :name "def") :type (make-type-string))
        (make-typed-variable :name (make-identifier :name "ghi") :type (make-type-character))))
  '(list (make-typed-variable :name (make-identifier :name "def") :type (make-type-string))
         (make-typed-variable :name (make-identifier :name "ghi") :type (make-type-character))))


(make-mm-sum literal ( (:boolean . ((value . bool)))
                       (:character . ((value . character)))
                       (:string . ((value . string)))
                       (:integer . ((value . nat))) ) )

(acl2::assert-equal (literal--make-myself
                     (make-literal-boolean :value t))
                    '(make-literal-boolean :value t))

(acl2::assert-equal (literal--make-myself
                     (make-literal-character :value (code-char 97)))
                    '(make-literal-character :value (code-char 97)))

(acl2::assert-equal (literal--make-myself
                     (make-literal-string :value "bag"))
                    '(make-literal-string :value "bag"))
;; TODO: also try strings with other unicode chars --- we will need to convert strings
;; to the form understood by the SExpression lexer.

(acl2::assert-equal (literal--make-myself
                     (make-literal-integer :value 28347293237842734028739428374298472934827934792834))
                    '(make-literal-integer :value 28347293237842734028739428374298472934827934792834))


(make-mm-sum unary-op ( (:not . ()) (:minus . ()) ))

(make-mm-sum binary-op ( (:eq . ()) (:ne . ()) (:gt . ()) (:ge . ()) (:lt . ()) (:le . ())
                         (:and . ()) (:or . ()) (:implies . ()) (:implied . ()) (:iff . ())
                         (:add . ()) (:sub . ()) (:mul . ()) (:div . ()) (:rem . ()) ))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The deftypes expression-fixtypes are mutually recursive.
;; We first generate the make-myself definitions by macroexpansion in the CLI,
;; then, since defprojection is not supported by mutual-recursion,
;; we convert the DEFPROJECTIONs to DEFINEs
;; then add :measures and wrap with defines.

#||
:trans1 (make-mm-sum expression
             (     (:literal . ((get . literal)))
    (:variable . ((name . identifier)))
    (:unary . ((operator . unary-op)
             (operand . expression)))
    (:binary . ((operator . binary-op)
              (left-operand . expression)
              (right-operand . expression)))
    (:if . ((test . expression)
          (then . expression)
          (else . expression)))
    (:when . ((test . expression)
            (then . expression)
            (else . expression)))
    (:unless . ((test . expression)
              (then . expression)
              (else . expression)))
    (:cond . ((branches . branch-list)))
    (:call . ((function . identifier)
            (types . type-list)
            (arguments . expression-list)))
    (:multi . ((arguments . expression-list)))
    (:component . ((multi . expression)
                 (index . nat)))
    (:bind . ((variables . typed-variable-list)
            (value . expression)
            (body . expression)))
    (:product-construct . ((type . identifier)
                         (fields . initializer-list)))
    (:product-field . ((type . identifier)
                     (target . expression)
                     (field . identifier)))
    (:product-update . ((type . identifier)
                      (target . expression)
                      (fields . initializer-list)))
    (:sum-construct . ((type . identifier)
                     (alternative . identifier)
                     (fields . initializer-list)))
    (:sum-field . ((type . identifier)
                 (target . expression)
                 (alternative . identifier)
                 (field . identifier)))
    (:sum-update . ((type . identifier)
                  (target . expression)
                  (alternative . identifier)
                  (fields . initializer-list)))
    (:sum-test . ((type . identifier)
                (target . expression)
                (alternative . identifier))) ))

:trans1 (make-mm-list expression-list expression)

:trans1 (make-mm-prod branch ((condition . expression) (action . expression)) )

:trans1 (make-mm-list branch-list branch)

:trans1 (make-mm-prod initializer ((field . identifier) (value . expression)) )

:trans1 (make-mm-list initializer-list initializer)



||#

(defines expression--make-myself-mutrec

 (DEFINE
  EXPRESSION--MAKE-MYSELF
  ((OBJ EXPRESSIONP))
  :RETURNS (RETFORM LISTP)
  (EXPRESSION-CASE
   OBJ
   :LITERAL (LIST 'MAKE-EXPRESSION-LITERAL
                  :GET (LITERAL--MAKE-MYSELF (EXPRESSION-LITERAL->GET OBJ)))
   :VARIABLE
   (LIST 'MAKE-EXPRESSION-VARIABLE
         :NAME (IDENTIFIER--MAKE-MYSELF (EXPRESSION-VARIABLE->NAME OBJ)))
   :UNARY
   (LIST 'MAKE-EXPRESSION-UNARY
         :OPERATOR (UNARY-OP--MAKE-MYSELF (EXPRESSION-UNARY->OPERATOR OBJ))
         :OPERAND (EXPRESSION--MAKE-MYSELF (EXPRESSION-UNARY->OPERAND OBJ)))
   :BINARY
   (LIST 'MAKE-EXPRESSION-BINARY
         :OPERATOR (BINARY-OP--MAKE-MYSELF (EXPRESSION-BINARY->OPERATOR OBJ))
         :LEFT-OPERAND
         (EXPRESSION--MAKE-MYSELF (EXPRESSION-BINARY->LEFT-OPERAND OBJ))
         :RIGHT-OPERAND
         (EXPRESSION--MAKE-MYSELF (EXPRESSION-BINARY->RIGHT-OPERAND OBJ)))
   :IF (LIST 'MAKE-EXPRESSION-IF
             :TEST (EXPRESSION--MAKE-MYSELF (EXPRESSION-IF->TEST OBJ))
             :THEN (EXPRESSION--MAKE-MYSELF (EXPRESSION-IF->THEN OBJ))
             :ELSE (EXPRESSION--MAKE-MYSELF (EXPRESSION-IF->ELSE OBJ)))
   :WHEN (LIST 'MAKE-EXPRESSION-WHEN
               :TEST (EXPRESSION--MAKE-MYSELF (EXPRESSION-WHEN->TEST OBJ))
               :THEN (EXPRESSION--MAKE-MYSELF (EXPRESSION-WHEN->THEN OBJ))
               :ELSE (EXPRESSION--MAKE-MYSELF (EXPRESSION-WHEN->ELSE OBJ)))
   :UNLESS
   (LIST 'MAKE-EXPRESSION-UNLESS
         :TEST (EXPRESSION--MAKE-MYSELF (EXPRESSION-UNLESS->TEST OBJ))
         :THEN (EXPRESSION--MAKE-MYSELF (EXPRESSION-UNLESS->THEN OBJ))
         :ELSE (EXPRESSION--MAKE-MYSELF (EXPRESSION-UNLESS->ELSE OBJ)))
   :COND
   (LIST
        'MAKE-EXPRESSION-COND
        :BRANCHES (BRANCH-LIST--MAKE-MYSELF (EXPRESSION-COND->BRANCHES OBJ)))
   :CALL
   (LIST 'MAKE-EXPRESSION-CALL
         :FUNCTION (IDENTIFIER--MAKE-MYSELF (EXPRESSION-CALL->FUNCTION OBJ))
         :TYPES (TYPE-LIST--MAKE-MYSELF (EXPRESSION-CALL->TYPES OBJ))
         :ARGUMENTS
         (EXPRESSION-LIST--MAKE-MYSELF (EXPRESSION-CALL->ARGUMENTS OBJ)))
   :MULTI
   (LIST 'MAKE-EXPRESSION-MULTI
         :ARGUMENTS
         (EXPRESSION-LIST--MAKE-MYSELF (EXPRESSION-MULTI->ARGUMENTS OBJ)))
   :COMPONENT
   (LIST 'MAKE-EXPRESSION-COMPONENT
         :MULTI (EXPRESSION--MAKE-MYSELF (EXPRESSION-COMPONENT->MULTI OBJ))
         :INDEX (EXPRESSION-COMPONENT->INDEX OBJ))
   :BIND
   (LIST 'MAKE-EXPRESSION-BIND
         :VARIABLES
         (TYPED-VARIABLE-LIST--MAKE-MYSELF (EXPRESSION-BIND->VARIABLES OBJ))
         :VALUE (EXPRESSION--MAKE-MYSELF (EXPRESSION-BIND->VALUE OBJ))
         :BODY (EXPRESSION--MAKE-MYSELF (EXPRESSION-BIND->BODY OBJ)))
   :PRODUCT-CONSTRUCT
   (LIST
     'MAKE-EXPRESSION-PRODUCT-CONSTRUCT
     :TYPE (IDENTIFIER--MAKE-MYSELF (EXPRESSION-PRODUCT-CONSTRUCT->TYPE OBJ))
     :FIELDS (INITIALIZER-LIST--MAKE-MYSELF
                  (EXPRESSION-PRODUCT-CONSTRUCT->FIELDS OBJ)))
   :PRODUCT-FIELD
   (LIST
     'MAKE-EXPRESSION-PRODUCT-FIELD
     :TYPE (IDENTIFIER--MAKE-MYSELF (EXPRESSION-PRODUCT-FIELD->TYPE OBJ))
     :TARGET (EXPRESSION--MAKE-MYSELF (EXPRESSION-PRODUCT-FIELD->TARGET OBJ))
     :FIELD (IDENTIFIER--MAKE-MYSELF (EXPRESSION-PRODUCT-FIELD->FIELD OBJ)))
   :PRODUCT-UPDATE
   (LIST
    'MAKE-EXPRESSION-PRODUCT-UPDATE
    :TYPE (IDENTIFIER--MAKE-MYSELF (EXPRESSION-PRODUCT-UPDATE->TYPE OBJ))
    :TARGET (EXPRESSION--MAKE-MYSELF (EXPRESSION-PRODUCT-UPDATE->TARGET OBJ))
    :FIELDS
    (INITIALIZER-LIST--MAKE-MYSELF (EXPRESSION-PRODUCT-UPDATE->FIELDS OBJ)))
   :SUM-CONSTRUCT
   (LIST
      'MAKE-EXPRESSION-SUM-CONSTRUCT
      :TYPE (IDENTIFIER--MAKE-MYSELF (EXPRESSION-SUM-CONSTRUCT->TYPE OBJ))
      :ALTERNATIVE
      (IDENTIFIER--MAKE-MYSELF (EXPRESSION-SUM-CONSTRUCT->ALTERNATIVE OBJ))
      :FIELDS
      (INITIALIZER-LIST--MAKE-MYSELF (EXPRESSION-SUM-CONSTRUCT->FIELDS OBJ)))
   :SUM-FIELD
   (LIST 'MAKE-EXPRESSION-SUM-FIELD
         :TYPE (IDENTIFIER--MAKE-MYSELF (EXPRESSION-SUM-FIELD->TYPE OBJ))
         :TARGET (EXPRESSION--MAKE-MYSELF (EXPRESSION-SUM-FIELD->TARGET OBJ))
         :ALTERNATIVE
         (IDENTIFIER--MAKE-MYSELF (EXPRESSION-SUM-FIELD->ALTERNATIVE OBJ))
         :FIELD (IDENTIFIER--MAKE-MYSELF (EXPRESSION-SUM-FIELD->FIELD OBJ)))
   :SUM-UPDATE
   (LIST
        'MAKE-EXPRESSION-SUM-UPDATE
        :TYPE (IDENTIFIER--MAKE-MYSELF (EXPRESSION-SUM-UPDATE->TYPE OBJ))
        :TARGET (EXPRESSION--MAKE-MYSELF (EXPRESSION-SUM-UPDATE->TARGET OBJ))
        :ALTERNATIVE
        (IDENTIFIER--MAKE-MYSELF (EXPRESSION-SUM-UPDATE->ALTERNATIVE OBJ))
        :FIELDS
        (INITIALIZER-LIST--MAKE-MYSELF (EXPRESSION-SUM-UPDATE->FIELDS OBJ)))
   :SUM-TEST
   (LIST 'MAKE-EXPRESSION-SUM-TEST
         :TYPE (IDENTIFIER--MAKE-MYSELF (EXPRESSION-SUM-TEST->TYPE OBJ))
         :TARGET (EXPRESSION--MAKE-MYSELF (EXPRESSION-SUM-TEST->TARGET OBJ))
         :ALTERNATIVE
         (IDENTIFIER--MAKE-MYSELF (EXPRESSION-SUM-TEST->ALTERNATIVE OBJ)))
   :bad-expression                      ; Shouldn't normally happen
   (list 'MAKE-EXPRESSION-BAD-EXPRESSION
         :info `',(expression-bad-expression->info obj))) ; This just quotes the info!
  :measure (two-nats-measure (expression-count obj) 0))

 (DEFINE EXPRESSION-LIST--MAKE-MYSELF
   ((OBJ EXPRESSION-LISTP))
   :RETURNS (RETFORM LISTP)
   (LET ((MAKE-FORMS (EXPRESSION-LIST--MAKE-MYSELFS OBJ)))
        (CONS 'LIST MAKE-FORMS))
  :measure (two-nats-measure (expression-list-count obj) 1))

 (DEFINE BRANCH--MAKE-MYSELF ((OBJ BRANCHP))
   :RETURNS (RETFORM LISTP)
   (LIST 'MAKE-BRANCH
         :CONDITION (EXPRESSION--MAKE-MYSELF (BRANCH->CONDITION OBJ))
         :ACTION (EXPRESSION--MAKE-MYSELF (BRANCH->ACTION OBJ)))
  :measure (two-nats-measure (branch-count obj) 0))

 (DEFINE BRANCH-LIST--MAKE-MYSELF
   ((OBJ BRANCH-LISTP))
   :RETURNS (RETFORM LISTP)
   (LET ((MAKE-FORMS (BRANCH-LIST--MAKE-MYSELFS OBJ)))
        (CONS 'LIST MAKE-FORMS))
  :measure (two-nats-measure (branch-list-count obj) 1))

 (DEFINE INITIALIZER--MAKE-MYSELF
   ((OBJ INITIALIZERP))
   :RETURNS (RETFORM LISTP)
   (LIST 'MAKE-INITIALIZER
         :FIELD (IDENTIFIER--MAKE-MYSELF (INITIALIZER->FIELD OBJ))
         :VALUE (EXPRESSION--MAKE-MYSELF (INITIALIZER->VALUE OBJ)))
  :measure (two-nats-measure (initializer-count obj) 0))

 (DEFINE INITIALIZER-LIST--MAKE-MYSELF
   ((OBJ INITIALIZER-LISTP))
   :RETURNS (RETFORM LISTP)
   (LET ((MAKE-FORMS (INITIALIZER-LIST--MAKE-MYSELFS OBJ)))
        (CONS 'LIST MAKE-FORMS))
  :measure (two-nats-measure (initializer-list-count obj) 1))

 (define EXPRESSION-LIST--MAKE-MYSELFS ((X EXPRESSION-LISTP))
   :RETURNS (RETFORM LISTP)
   (if (endp x)
       nil
     (cons (EXPRESSION--MAKE-MYSELF (car X))
           (EXPRESSION-LIST--MAKE-MYSELFS (cdr x))))
  :measure (two-nats-measure (expression-list-count x) 0))

 (define BRANCH-LIST--MAKE-MYSELFS ((X BRANCH-LISTP))
   :RETURNS (RETFORM LISTP)
   (if (endp x)
       nil
     (cons (BRANCH--MAKE-MYSELF (car x))
           (BRANCH-LIST--MAKE-MYSELFS (cdr x))))
  :measure (two-nats-measure (branch-list-count x) 0))

 (define INITIALIZER-LIST--MAKE-MYSELFS ((X INITIALIZER-LISTP))
   :RETURNS (RETFORM LISTP)
   (if (endp x)
       nil
     (cons (INITIALIZER--MAKE-MYSELF (car X))
           (INITIALIZER-LIST--MAKE-MYSELFS (cdr x))))
  :measure (two-nats-measure (initializer-list-count x) 0))

)

;; TODO NOTE:  The serialization should require that an empty value of a list type
;; is output as (LIST), for consistency.

(acl2::assert-equal (expression--make-myself
                     (make-expression-call
                      :function (make-identifier :name "gcd")
                      :types (list)
                      :arguments
                      (list
                       (make-expression-variable :name (make-identifier :name "x"))
                       (make-expression-binary
                        :operator (make-binary-op-rem)
                        :left-operand
                        (make-expression-variable :name (make-identifier :name "y"))
                        :right-operand
                        (make-expression-variable :name (make-identifier :name "x"))))))
                    '(make-expression-call
                      :function (make-identifier :name "gcd")
                      :types (list)
                      :arguments
                      (list
                       (make-expression-variable :name (make-identifier :name "x"))
                       (make-expression-binary
                        :operator (make-binary-op-rem)
                        :left-operand
                        (make-expression-variable :name (make-identifier :name "y"))
                        :right-operand
                        (make-expression-variable :name (make-identifier :name "x"))))))



;; TODO: add test cases on the rest

(make-mm-option maybe-expression expression)

(make-mm-prod field ((name . identifier) (type . type)))

(make-mm-list field-list field)

(make-mm-prod type-product ((fields . field-list) (invariant . maybe-expression)))

(make-mm-option maybe-type-product type-product)

(make-mm-prod alternative ((name . identifier) (product . type-product)))

(make-mm-list alternative-list alternative)

(make-mm-prod type-sum ((alternatives . alternative-list)))

(make-mm-option maybe-type-sum type-sum)

(make-mm-prod type-subset ((supertype . type) (variable . identifier) (restriction . expression) (witness . maybe-expression)))

(make-mm-option maybe-type-subset type-subset)

(make-mm-sum type-definer ( (:product . ((get . type-product)))
                            (:sum . ((get . type-sum)))
                            (:subset . ((get . type-subset))) ))

(make-mm-option maybe-type-definer type-definer)

(make-mm-prod type-definition ((name . identifier) (body . type-definer)))

(make-mm-list type-definition-list type-definition)

(make-mm-option maybe-type-definition type-definition)

(make-mm-prod type-recursion ((definitions . type-definition-list)))

(make-mm-prod function-header ((name . identifier) (inputs . typed-variable-list) (outputs . typed-variable-list)))

(make-mm-list function-header-list function-header)

(make-mm-option maybe-function-header function-header)

(make-mm-sum quantifier ( (:forall . ()) (:exists . ()) ))

(make-mm-sum function-definer ( (:regular . ((body . expression) (measure . maybe-expression)))
                                (:quantified . ((quantifier . quantifier) (variables . typed-variable-list) (matrix . expression))) ))

(make-mm-prod function-definition ((header . function-header)
                                   (precondition . maybe-expression)
                                   (postcondition . maybe-expression)
                                   (definer . function-definer)))

(make-mm-list function-definition-list function-definition)

(make-mm-option maybe-function-definition function-definition)

(make-mm-prod function-recursion ((definitions . function-definition-list)))

(make-mm-sum function-specifier ( (:regular . ((body . expression)))
                                  (:quantified . ((quantifier . quantifier) (variables . typed-variable-list) (matrix . expression)))
                                  (:input-output . ((relation . expression))) ))

(make-mm-prod function-specification ((name . identifier)
                                      (functions . function-header-list)
                                      (specifier . function-specifier)))

(make-mm-option maybe-function-specification function-specification)

(make-mm-prod theorem ((name .  identifier)
                       (variables . typed-variable-list)
                       (formula . expression)))

(make-mm-option maybe-theorem theorem)

(make-mm-sum transform-argument-value ( (:identifier . ((name . identifier)))
                                        (:identifier-list . ((names . identifier-list)))
                                        (:term . ((get . expression)))
                                        (:bool . ((val . bool)))))

(make-mm-prod transform-argument ((name . identifier)
                                  (value . transform-argument-value)))

(make-mm-list transform-argument-list transform-argument)

(make-mm-prod transform ((new-function-name . identifier)
                         (old-function-name . identifier)
                         (transform-name . string)
                         (arguments . transform-argument-list)))

(make-mm-sum toplevel ( (:type . ((get . type-definition)))
                        (:types . ((get . type-recursion)))
                        (:function . ((get . function-definition)))
                        (:functions . ((get . function-recursion)))
                        (:specification . ((get . function-specification)))
                        (:theorem . ((get . theorem)))
                        (:transform . ((get . transform)))))

;; Two tests from examples/fact.lisp

(acl2::assert-equal (toplevel--make-myself
                     (MAKE-TOPLEVEL-TRANSFORM
                      :GET
                      (MAKE-TRANSFORM
                       :NEW-FUNCTION-NAME (MAKE-IDENTIFIER :NAME "factorial__1")
                       :OLD-FUNCTION-NAME (MAKE-IDENTIFIER :NAME "factorial")
                       :TRANSFORM-NAME "tail_recursion"
                       :ARGUMENTS (LIST (MAKE-TRANSFORM-ARGUMENT
                                         :NAME (MAKE-IDENTIFIER :NAME "new_parameter_name")
                                         :VALUE (MAKE-TRANSFORM-ARGUMENT-VALUE-IDENTIFIER
                                                 :NAME (MAKE-IDENTIFIER :NAME "r")))))))
                    '(MAKE-TOPLEVEL-TRANSFORM
                      :GET
                      (MAKE-TRANSFORM
                       :NEW-FUNCTION-NAME (MAKE-IDENTIFIER :NAME "factorial__1")
                       :OLD-FUNCTION-NAME (MAKE-IDENTIFIER :NAME "factorial")
                       :TRANSFORM-NAME "tail_recursion"
                       :ARGUMENTS (LIST (MAKE-TRANSFORM-ARGUMENT
                                         :NAME (MAKE-IDENTIFIER :NAME "new_parameter_name")
                                         :VALUE (MAKE-TRANSFORM-ARGUMENT-VALUE-IDENTIFIER
                                                 :NAME (MAKE-IDENTIFIER :NAME "r")))))))

(acl2::assert-equal (toplevel--make-myself
                     (MAKE-TOPLEVEL-TRANSFORM
                      :GET
                      (MAKE-TRANSFORM
                       :NEW-FUNCTION-NAME (MAKE-IDENTIFIER :NAME "factorial__2")
                       :OLD-FUNCTION-NAME (MAKE-IDENTIFIER :NAME "factorial__1")
                       :TRANSFORM-NAME "rename_param"
                       :ARGUMENTS
                       (LIST
                        (MAKE-TRANSFORM-ARGUMENT :NAME (MAKE-IDENTIFIER :NAME "old")
                                                 :VALUE (MAKE-TRANSFORM-ARGUMENT-VALUE-IDENTIFIER
                                                         :NAME (MAKE-IDENTIFIER :NAME "r")))
                        (MAKE-TRANSFORM-ARGUMENT
                         :NAME (MAKE-IDENTIFIER :NAME "new")
                         :VALUE (MAKE-TRANSFORM-ARGUMENT-VALUE-IDENTIFIER
                                 :NAME (MAKE-IDENTIFIER :NAME "val")))))))
                    '(MAKE-TOPLEVEL-TRANSFORM
                      :GET
                      (MAKE-TRANSFORM
                       :NEW-FUNCTION-NAME (MAKE-IDENTIFIER :NAME "factorial__2")
                       :OLD-FUNCTION-NAME (MAKE-IDENTIFIER :NAME "factorial__1")
                       :TRANSFORM-NAME "rename_param"
                       :ARGUMENTS
                       (LIST
                        (MAKE-TRANSFORM-ARGUMENT :NAME (MAKE-IDENTIFIER :NAME "old")
                                                 :VALUE (MAKE-TRANSFORM-ARGUMENT-VALUE-IDENTIFIER
                                                         :NAME (MAKE-IDENTIFIER :NAME "r")))
                        (MAKE-TRANSFORM-ARGUMENT
                         :NAME (MAKE-IDENTIFIER :NAME "new")
                         :VALUE (MAKE-TRANSFORM-ARGUMENT-VALUE-IDENTIFIER
                                 :NAME (MAKE-IDENTIFIER :NAME "val")))))))

(make-mm-list toplevel-list toplevel)

(make-mm-prod program ((tops . toplevel-list)))


;; TODO: make some larger serialization tests.

;; TODO: consider how string values are serialized/deserialized.. make sure we standardize on the format
