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
    "We start by providing constructors for ispaces and types.
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
  :short "Construct a dimension term from
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
  :short "Construct an addition dimension term from argument dimensions."
  `(dim-add (list ,@(dim-terms-from-vars/consts/others dims))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ dim* (&rest dims)
  :short "Construct a multiplication dimension term from argument dimensions."
  `(dim-mul (list ,@(dim-terms-from-vars/consts/others dims))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ dim- (&rest dims)
  :short "Construct a subtraction dimension term from argument dimensions."
  `(dim-sub (list ,@(dim-terms-from-vars/consts/others dims))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ shp (&rest dims)
  :short "Construct a shape term from component dimensions."
  `(shape-dims (list ,@(dim-terms-from-vars/consts/others dims))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shape-term-from-var/dim/other (dim/shape)
  :short "Construct a shape term from
          a string denoting a dimension or shape variable,
          or a natural number denoting a dimension,
          or a dimension arithmetic term
          (@(tsee dim+), @(tsee dim*), or @(tsee dim-)),
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
              (member-eq (car dim/shape) '(dim+ dim* dim-)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-var-term-from-string ((str stringp))
  :short "Build an ispace variable term from a string."
  :long
  (xdoc::topstring
   (xdoc::p
    "The string must be a variable name preceded by @('$') or @('@')."))
  (b* (((mv prefix name) (var-string-split str '(#\$ #\@))))
    (case prefix
      (#\$ `(ispace-var-dim ,name))
      (#\@ `(ispace-var-shape ,name)))))

;;;;;;;;;;;;;;;;;;;;

(define ispace-var-terms-from-strings ((strs string-listp))
  :short "Lift @(tsee ispace-var-term-from-string) to lists."
  (cond ((endp strs) nil)
        (t (cons (ispace-var-term-from-string (car strs))
                 (ispace-var-terms-from-strings (cdr strs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-var-term-from-string ((str stringp))
  :short "Build a type variable term from a string."
  :long
  (xdoc::topstring
   (xdoc::p
    "The string must be a variable name preceded by @('&') or @('*')."))
  (b* (((mv prefix name) (var-string-split str '(#\& #\*))))
    (case prefix
      (#\& `(type-var-atom ,name))
      (#\* `(type-var-array ,name)))))

;;;;;;;;;;;;;;;;;;;;

(define type-var-terms-from-strings ((strs string-listp))
  :short "Lift @(tsee type-var-term-from-string) to lists."
  (cond ((endp strs) nil)
        (t (cons (type-var-term-from-string (car strs))
                 (type-var-terms-from-strings (cdr strs))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-term-from-var/base/other (type)
  :short "Construct a type term from
          a string denoting an atom type variable,
          or a keyword denoting a base type,
          or some other term that is left unchanged."
  :long
  (xdoc::topstring
   (xdoc::p
    "The string denoting a variable must start with @('&') or @('*')."))
  (cond ((stringp type) `(type-var ,(type-var-term-from-string type)))
        ((eq type :bool) '(type-array (type-base (base-type-bool))
                                      (ispace-shape (shp))))
        ((eq type :int) '(type-array (type-base (base-type-int))
                                     (ispace-shape (shp))))
        ((eq type :float) '(type-array (type-base (base-type-float))
                                       (ispace-shape (shp))))
        (t type)))

;;;;;;;;;;;;;;;;;;;;

(define type-terms-from-vars/bases/others ((types true-listp))
  :short "Lift @(tsee type-term-from-var/base/other) to lists."
  (cond ((endp types) nil)
        (t (cons (type-term-from-var/base/other (car types))
                 (type-terms-from-vars/bases/others (cdr types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ t[] (type dim/shape)
  :short "Construct a type term from the element type and the shape."
  :long
  (xdoc::topstring
   (xdoc::p
    "Strings, natural numbers, and base type keywords
     are auto-coerced to ispaces and types."))
  `(type-array ,(type-term-from-var/base/other type)
               (ispace-shape ,(shape-term-from-var/dim/other dim/shape))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ t-> (intypes outtype)
  :short "Construct a function type term from the input and output types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Strings and base type keywords are auto-coerced to types."))
  `(type-fun (list ,@(type-terms-from-vars/bases/others intypes))
             ,(type-term-from-var/base/other outtype)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ tforall (params type)
  :short "Construct a universal type from
          a parenthesized list of variable strings (parameters)
          and a type term (body)."
  `(type-foralln (list ,@(type-var-terms-from-strings params))
                 ,(type-term-from-var/base/other type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ tpi (params type)
  :short "Construct a product type term from
          a parenthesized list of variable strings (parameters)
          and a type term (body)."
  `(type-pin (list ,@(ispace-var-terms-from-strings params))
             ,(type-term-from-var/base/other type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ tsigma (params type)
  :short "Construct a sum type term from
          a parenthesized list of variable strings (parameters)
          and a type term (body)."
  `(type-sigman (list ,@(ispace-var-terms-from-strings params))
                ,(type-term-from-var/base/other type)))
