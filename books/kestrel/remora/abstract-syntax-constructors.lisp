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

(defmacro+ ivar (name)
  :short "Construct an index variable from its name."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just a slight abbreviation for @(tsee index-var)."))
  `(index-var ,name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ iconst (value)
  :short "Construct an index constant from its value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just a slight abbreviation for @(tsee index-const)."))
  `(index-const ,value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define index-var/const/other (index)
  :short "Coerce a string or natural number
          to an index variable or constant,
          leaving other categories of indices unchanged."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to implement index constructors
     that can take, besides proper indices,
     also strings and natural numbers,
     coercing the latter to indices."))
  (cond ((stringp index) `(ivar ,index))
        ((natp index) `(iconst ,index))
        (t index)))

;;;;;;;;;;;;;;;;;;;;

(define indices-var/const/other ((indices true-listp))
  :returns (coerced-indices true-listp)
  :short "Lift @(tsee index-var/const/other) to lists."
  (cond ((endp indices) nil)
        (t (cons (index-var/const/other (car indices))
                 (indices-var/const/other (cdr indices))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ ishape (&rest indices)
  :short "Construct a shape index from component indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "Strings are auto-coerced to variables
     and natural numbers to constants."))
  `(index-shape (list ,@(indices-var/const/other indices))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ i+ (&rest indices)
  :short "Construct an addition index from component indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "Strings are auto-coerced to variables
     and natural numbers to constants."))
  `(index-add (list ,@(indices-var/const/other indices))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ i++ (&rest indices)
  :short "Construct a concatenation index from component indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "Strings are auto-coerced to variables
     and natural numbers to constants."))
  `(index-append (list ,@(indices-var/const/other indices))))

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
        ((eq type :char) '(type-base (base-type-char)))
        ((eq type :int) '(type-base (base-type-int)))
        (t type)))

;;;;;;;;;;;;;;;;;;;;

(define type-list-var/base/other ((types true-listp))
  :returns (coerced-types true-listp)
  :short "Lift @(tsee type-var/base/other) to lists."
  (cond ((endp types) nil)
        (t (cons (type-var/base/other (car types))
                 (type-list-var/base/other (cdr types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ tarray (type shape)
  :short "Construct an array type from the inner type and the shape."
  :long
  (xdoc::topstring
   (xdoc::p
    "Strings, natural numbers, and base type keywords
     are auto-coerced to indices and types."))
  `(type-array ,(type-var/base/other type) ,(index-var/const/other shape)))

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

(define bindings-to-sorted-vars ((bindings true-listp))
  :returns (sorted-vars true-listp)
  :short "Turn a list of alternating strings and keywords
          into a list of sorted variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "The strings are the variable names.
     The keywords designate sorts.
     The list must have even length,
     with alternating strings and keywords, starting with a string."))
  (b* (((when (endp bindings)) nil)
       (var (car bindings))
       (sort (case (cadr bindings)
               (:shape '(sort-shape))
               (:dim '(sort-dim))
               (otherwise (raise "Unknown sort keyword: ~x0."
                                 (cadr bindings)))))
       (svar `(sorted-var ,var ,sort))
       (svars (bindings-to-sorted-vars (cddr bindings))))
    (cons svar svars))
  :no-function nil)

;;;;;;;;;;;;;;;;;;;;

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

(defmacro+ tpi (bindings type)
  :short "Construct a product type from a list of bindings and a body type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The bindings are provided as a parenthesized list of
     alternating strings and keywords (see @(tsee bindings-to-sorted-vars)).
     A variable or base type keyword as the body type
     is auto-coerced to a type."))
  `(type-pi (list ,@(bindings-to-sorted-vars bindings))
            ,(type-var/base/other type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ tsigma (bindings type)
  :short "Construct a sum type from a list of bindings and a body type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The bindings are provided as a parenthesized list of
     alternating strings and keywords (see @(tsee bindings-to-sorted-vars)).
     A variable or base type keyword as the body type
     is auto-coerced to a type."))
  `(type-sigma (list ,@(bindings-to-sorted-vars bindings))
               ,(type-var/base/other type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: constructors for expressions and atoms
