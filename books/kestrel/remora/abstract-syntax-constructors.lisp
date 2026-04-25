; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-constructors
  :parents (abstract-syntax)
  :short "Readable constructors of ASTs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The fixtype constructors of ASTs are inherently fairly verbose.
     We provide more readable constructors, mainly in the form of macros.
     These can be regarded as forming a sort of
     embedded domain-specific language for Remora.")
   (xdoc::p
    "We start by providing constructors for indices and types.
     We plan to add constructors for other ASTs as well."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-string-split ((str stringp) (prefixes character-listp))
  :returns (mv (prefix characterp) (name stringp))
  :short "Split a string into its first character and the rest,
          provided that the first character is among the allowed prefixes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to turn, for example, the string @('$x')
     into the dimension variable with name @('x');
     the @('$') prefix is as in the concrete syntax (see ABNF grammar)."))
  (b* ((str (str::str-fix str))
       (prefixes (str::character-list-fix prefixes))
       (chars (str::explode str))
       ((unless (consp chars))
        (raise "Empty string.")
        (mv (code-char 0) ""))
       (prefix (car chars))
       ((unless (member prefix prefixes))
        (raise "Disallowed prefix ~x0." prefix)
        (mv (code-char 0) "")))
    (mv prefix (str::implode (cdr chars))))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dim-term-from-var/const/other (dim)
  :short "Create a dimension term from
          a string denoting a variable,
          or a natural number denoting a constant,
          or some other term that is left unchanged."
  :long
  (xdoc::topstring
   (xdoc::p
    "The string denoting a variable must start with @('$')."))
  (cond ((stringp dim)
         (b* (((mv & name) (var-string-split dim '(#\$))))
           `(dim-var ,name)))
        ((natp dim) `(dim-const ,dim))
        (t dim)))

;;;;;;;;;;;;;;;;;;;;

(define dim-terms-from-vars/consts/others ((dims true-listp))
  :short "Lift @(tsee dim-term-from-var/const/other) to lists."
  (cond ((endp dims) nil)
        (t (cons (dim-term-from-var/const/other (car dims))
                 (dim-terms-from-vars/consts/others (cdr dims))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ dim+ (&rest dims)
  :short "Construct an addition dimension term from addend dimensions."
  `(dim-add (list ,@(dim-terms-from-vars/consts/others dims))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ shape (&rest dims)
  :short "Construct a shape term from component dimensions."
  `(shape-dims (list ,@(dim-terms-from-vars/consts/others dims))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shape-term-from-var/dim/other (dim/shape)
  :short "Create a shape term from
          a string denoting a dimension or shape variable,
          or a natural number denoting a dimension,
          or a dimension addition term,
          or some other term that is left unchanged."
  :long
  (xdoc::topstring
   (xdoc::p
    "The string denoting a variable must start with @('$') or @('@')."))
  (cond ((stringp dim/shape)
         (b* (((mv prefix name) (var-string-split dim/shape '(#\$ #\@))))
           (case prefix
             (#\$ `(shape-dims (list (dim-var ,name))))
             (#\@ `(shape-var ,name)))))
        ((natp dim/shape) `(shape-dims (list (dim-const ,dim/shape))))
        ((and (consp dim/shape)
              (eq (car dim/shape) 'dim+))
         `(shape-dims (list ,dim/shape)))
        (t dim/shape)))

;;;;;;;;;;;;;;;;;;;;

(define shape-terms-from-vars/dims/others ((dims/shapes true-listp))
  :short "Lift @(tsee shape-term-from-var/dim/other) to lists."
  (cond ((endp dims/shapes) nil)
        (t (cons (shape-term-from-var/dim/other (car dims/shapes))
                 (shape-terms-from-vars/dims/others (cdr dims/shapes))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ shape++ (&rest dims/shapes)
  :short "Construct a shape concatenation term
          from dimensions and shapes to concatenate."
  `(shape-append (list ,@(shape-terms-from-vars/dims/others dims/shapes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ tvar (name)
  :short "Construct a type variable from its name."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just a slight abbreviation for @(tsee type-var)."))
  `(type-var ,name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-var/base/other (type)
  :short "Coerce a string or keyword
          to a type variable or base type,
          leaving other categories of types unchanged."
  :long
  (xdoc::topstring
   (xdoc::p
    "The base types are identified via certain keywords.")
   (xdoc::p
    "This is used to implement type constructors
     that can take, besides proper types,
     also strings and keywords,
     coercing the latter to types."))
  (cond ((stringp type) `(tvar ,type))
        ((eq type :bool) '(type-base (base-type-bool)))
        ((eq type :int) '(type-base (base-type-int)))
        ((eq type :float) '(type-base (base-type-float)))
        (t type)))

;;;;;;;;;;;;;;;;;;;;

(define type-list-var/base/other ((types true-listp))
  :returns (coerced-types true-listp)
  :short "Lift @(tsee type-var/base/other) to lists."
  (cond ((endp types) nil)
        (t (cons (type-var/base/other (car types))
                 (type-list-var/base/other (cdr types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ tarray (type dim/shape)
  :short "Construct an array type from the inner type and the shape."
  :long
  (xdoc::topstring
   (xdoc::p
    "Strings, natural numbers, and base type keywords
     are auto-coerced to indices and types."))
  `(type-array ,(type-var/base/other type)
               ,(shape-term-from-var/dim/other dim/shape)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ t-> (intypes outtype)
  :short "Construct a function type from the input and output types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Strings and base type keywords are auto-coerced to types."))
  `(type-fun (list ,@(type-list-var/base/other intypes))
             ,(type-var/base/other outtype)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define index-param-term-from-string ((str stringp))
  :short "Build an index parameter term from a string."
  :long
  (xdoc::topstring
   (xdoc::p
    "The string must be a variable name preceded by @('$') or @('@')."))
  (b* (((mv prefix name) (var-string-split str '(#\$ #\@))))
    (case prefix
      (#\$ `(index-param-dim ,name))
      (#\@ `(index-param-shape ,name)))))

;;;;;;;;;;;;;;;;;;;;

(define index-param-terms-from-strings ((strs string-listp))
  :short "Lift @(tsee index-param-term-from-string) to lists."
  (cond ((endp strs) nil)
        (t (cons (index-param-term-from-string (car strs))
                 (index-param-terms-from-strings (cdr strs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bindings-to-kinded-vars ((bindings true-listp))
  :returns (kinded-vars true-listp)
  :short "Turn a list of alternating strings and keywords
          into a list of kinded variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "The strings are the variable names.
     The keywords designate kinds.
     The list must have even length,
     with alternating strings and keywords, starting with a string."))
  (b* (((when (endp bindings)) nil)
       (var (car bindings))
       (kind (case (cadr bindings)
               (:array '(kind-array))
               (:atom '(kind-atom))
               (otherwise (raise "Unknown kind keyword: ~x0."
                                 (cadr bindings)))))
       (kvar `(kinded-var ,var ,kind))
       (kvars (bindings-to-kinded-vars (cddr bindings))))
    (cons kvar kvars))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ tforall (bindings type)
  :short "Construct a universal type from a list of bindings and a body type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The bindings are provided as a parenthesized list of
     alternating strings and keywords (see @(tsee bindings-to-kinded-vars)).
     A variable or base type keyword as the body type
     is auto-coerced to a type."))
  `(type-forall (list ,@(bindings-to-kinded-vars bindings))
                ,(type-var/base/other type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ tpi (params type)
  :short "Construct a product type term
          from a list of parameters and a body type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The parameters are provided as a parenthesized list of variable strings.
     A variable or base type keyword as the body type
     is auto-coerced to a type."))
  `(type-pi (list ,@(index-param-terms-from-strings params))
            ,(type-var/base/other type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ tsigma (params type)
  :short "Construct a sum type term
          from a list of parameters and a body type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The parameters are provided as a parenthesized list of variable strings.
     A variable or base type keyword as the body type
     is auto-coerced to a type."))
  `(type-sigma (list ,@(index-param-terms-from-strings params))
               ,(type-var/base/other type)))
