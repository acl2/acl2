; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Macros for building expressions.
;; Superseded by expressions.lisp

;; See the UML diagram:
;; https://git.isis.vanderbilt.edu/midas/acl2.xtext/-/blob/devel/abstract-syntax/expressions-uml.png

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "centaur/fty/top" :dir :system)
(include-book "../syndef-package-utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Literals.  Do we need macros for these?

(defmacro s-literal-true ()
  'T)

(defmacro s-literal-false ()
  'NIL)

(defmacro s-literal-char (code-or-string)
  (cond ((and (natp code-or-string) (< code-or-string 256))
         `(code-char ,code-or-string))
        ((and (stringp code-or-string) (= 1 (length code-or-string)))
         `(char ,code-or-string 0))))

;; Let's stick with double quotes around literal strings.
;; No macros needed.

;; Let's stick with the regex [0-9]+ for literal integers in base 10.
;; Other bases can be added later.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Variable

(defmacro s-varref (varstring)
  (let ((varsymbol (intern-syndef varstring)))
    `,varsymbol))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Unary operators

;; boolean negation
(defmacro s-not (x)
  `(not ,x))

;; integer negation
(defmacro s-negate (x)
  `(acl2::unary-- ,x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Binary operators

(defmacro s-equal (left right)
  `(equal ,left ,right))

(defmacro s-notequal (left right)
  `(not (equal ,left ,right)))

(defmacro s-gt (left right)
  `(< ,right ,left))

(defmacro s-gte (left right)
  `(not (< ,left ,right)))

(defmacro s-lt (left right)
  `(< ,left ,right))

(defmacro s-lte (left right)
  `(not (< ,right ,left)))

(defmacro s-and (left right)
  `(if ,left ,right 'NIL))

(defmacro s-or (left right)
  `(if ,left ,left ,right))

(defmacro s-plus (left right)
  `(acl2::binary-+ ,left ,right))

(defmacro s-minus (left right)
  `(acl2::binary-+ ,left (acl2::unary-- ,right)))

(defmacro s-times (left right)
  `(acl2::binary-* ,left ,right))

(defmacro s-div (left right)
  `(acl2::truncate ,left ,right))

(defmacro s-rem (left right)
  `(acl2::rem ,left ,right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; product type field selection

;; The instance could be an expression, as long as its value
;; has the given prodname product type.
;; If the instance is a variable (parameter or let-var) X
;; then it would look like (s-varref "X") in the submitted form.

(defmacro s-prod-field-get (prodname fieldname instance)
  `(,(intern-syndef (concatenate 'string prodname "->" fieldname))
    ,instance))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conditional Expresssion

(defmacro s-conditional (test then-clause else-clause)
  `(if ,test
       ,then-clause
     ,else-clause))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Call Expresssion

;; Q: Is it OK to have rest args, or will it work better to have args be another list?
;;    Not sure what all the consequences are.

;; Currently requires function be in double-quotes.

(defmacro s-call (fnstring &rest args)
  (let ((fnsymbol (intern-syndef fnstring)))
    `(,fnsymbol ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Let Expresssion

;; UML diagram shows 1 or more LetBindings.
;; However, the body contains an expression.
;; Why not just allow one binding per let expression?

;; If there is more than one binding, it makes most sense for it to be parallel.
;; We decided NOT to generate the translated lambda form for let:
;;   ACL2 >:trans (let* ((x 3) (y 5)) (+ x y))
;;   ((LAMBDA (X)
;;            ((LAMBDA (Y X) (BINARY-+ X Y)) '5 X))
;;    '3)

;; let-string-bindings should look like
;;   (("VAR1" (expr-macro-1 ..)) ("VAR2" (expr-macro-2 ..)))
;; The variable strings are interned in SYNDEF.
(defun let-strings-to-syms (let-string-bindings)
  (if (endp let-string-bindings)
      nil
    (let ((var-string (car (first let-string-bindings)))
          (expr (cadr (first let-string-bindings))))
      (cons (list (intern-syndef var-string) expr)
            (let-strings-to-syms (cdr let-string-bindings))))))

(defmacro s-let (let-string-bindings let-body-expr)
  (let ((let-bindings (let-strings-to-syms let-string-bindings)))
    `(let ,let-bindings
       ,let-body-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Option expressions

(defmacro s-none (type-name)
  `(,(intern-syndef (concatenate 'string type-name "-NONE"))))

(defmacro s-some (type-name x)
  `(,(intern-syndef (concatenate 'string type-name "-SOME")) ,x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sequence expressions

;; just a start for some examples

(defmacro s-literal-empty-seq ()
  ())

(defmacro s-literal-sequence (&rest elements)
  `(list ,@elements))

(defmacro s-empty-p (s)
  `(endp ,s))

(defmacro s-head (s)
  `(car ,s))

(defmacro s-tail (s)
  `(cdr ,s))

(defmacro s-length (s)
  `(len ,s))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; String expressions

(defmacro s-string-length (s)
  `(length ,s))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests

(defun syndef::decdec (x)
  (- x 2))

(assert-event (s-notequal (s-literal-true) (s-literal-false)))

;; For now, operators on characters are supposed to be
;; equal, notequal, gt, gte, lt, lte

;; These inequalities don't yet work on characters.
;; The translation of s-lt will have to do a type check at runtime to
;; make that happen.  Something like
;; (if (characterp ..) (char-lessp ..)
;;   (if (integerp ..) (< ..) ..

(assert-event (s-notequal (s-literal-char "a") (s-literal-char "A")))
(assert-event (s-equal (s-literal-char "a") (s-literal-char 97)))

(assert-event (s-and (s-and (not (s-gt 2 2)) (s-gt 3 2))
                     (s-and (s-gte 2 2) (s-gte 3 2))))

(assert-event (s-and (s-and (not (s-lt 2 2)) (s-lt 2 3))
                     (s-and (s-lte 2 2) (s-lte 2 3))))

;; bignums: 2^257 + 2^257 = 2^258
(assert-event
 (s-equal
  (s-plus
   231584178474632390847141970017375815706539969331281128078915168015826259279872
   (s-minus
    (s-negate
     (s-minus
      (s-negate
       231584178474632390847141970017375815706539969331281128078915168015826259279872)
      1))
    1))
  463168356949264781694283940034751631413079938662562256157830336031652518559744))

(assert-event
 (s-and (s-equal (s-div 7 2) 3)
        (s-equal (s-div -7 2) -3)))

(assert-event
 (s-and (s-equal (s-rem 7 2) 1)
        (s-equal (s-rem -7 2) -1)))

(assert-event
 (s-equal (s-conditional (s-equal (s-literal-char "a") (s-literal-char 97))
                         22
                         "abc")
          22))

(assert-event
 (s-equal (s-conditional (s-equal (s-literal-char "a") (s-literal-char 98))
                         22
                         "abc")
          "abc"))

(assert-event
 (s-equal (s-call "DECDEC" (s-plus 2 5)) 5))

(assert-event (equal 22 (s-let (("X" 12) ("Y" 10)) (s-plus (s-varref "X") (s-varref "Y")))))

(assert-event (equal 24 (s-let (("X" 12) ("Y" 10))
                           (s-let (("X" (s-plus (s-varref "X") (s-varref "Y")))
                                   ("Y" (s-minus (s-varref "X") (s-varref "Y"))))
                               (s-plus (s-varref "X") (s-varref "Y"))))))

;; Test field selection.
;; To do this we need a product type.
;; However, this file is not yet dependent on types.lisp
;; Let's define the product type directly in ACL2.

(FTY::DEFPROD SYNDEF::|acid4|
	      ((SYNDEF::|id| INT))
	      :TAG :|acid4|)

(assert-event (equal 3 (let ((syndef::|ai| (syndef::|MAKE-acid4| :|id| 3))) (s-prod-field-get "acid4" "id" (s-varref "ai") ))))
