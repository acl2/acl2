; ACL2 Version 1.9

; Copyright (C) 1989-1996 Computational Logic, Inc. (CLI).  All rights reserved.

; Use of this software constitutes agreement with the terms of the
; license agreement, found in the file LICENSE.

(in-package "user")

(load-base "latex-init")

;                                     INFIX-OPS

; infix-ops (infix operators) should be function symbols of two or more
; arguments for which it is desired that one symbol come out between every
; adjacent pair of arguments.  E.g., invoking (make-infix-op plus "+") causes
; the term (plus a b c d) to be printed as (a $+$ b $+$ c $+$ d).  Invoking
; (make-infix-op equal "=" "\\not=") causes the term (equal x y) to be printed
; as (x $=$ y) and it also causes the term (not (equal x y)) to be printed as
; (x $\not= y).

; Thus, for example, if one introduces a new function, say join, and wants to
; print terms of the form (join x y) as (x \bigtriangledown y), cf. p. 44 of
; the Latex manual, then one should invoke:

;   (make-infix-op join "\\bigtriangledown")

; from Lisp.  That is all that need be done to cause infix-file to subsequently
; print `join' terms this way.

; Note that throughout the following examples, we have used two backslashes to
; get one because, in Common Lisp, backslash is a character for quoting other
; characters.

; Examples of make-infix-op.

(make-infix-op eq             "=_{eq}" "\\not=_{eq}")
(make-infix-op =              "=_{n}"  "\\not=_{n}")
(make-infix-op equal          "="      "\\not=")
(make-infix-op lessp          "<"        "\\not<")
(make-infix-op <              "<"        "\\not<")
(make-infix-op e0-ord-<       "\\leq_\\epsilon"    "\\not\\leq_\\epsilon")
(make-infix-op leq            "\\leq"    "\\not\\leq")
(make-infix-op <=             "\\leq"    "\\not\\leq")
(make-infix-op greaterp       ">"        "\\not>")
(make-infix-op >              ">"        "\\not>")
(make-infix-op geq            "\\geq"    "\\not\\geq")
(make-infix-op >=             "\\geq"    "\\not\\geq")
(make-infix-op member         "\\in"     "\\not\\in")

(make-infix-op append         " @ ")

(make-infix-op implies        "\\rightarrow")
(make-infix-op iff            "\\leftrightarrow")
(make-infix-op /              "/")
(make-infix-op remainder      "{\\rm\\bf{mod}}")
(make-infix-op union          "\\cup")
(make-infix-op +              "+")
(make-infix-op -              "-")
(make-infix-op *              "*")
(make-infix-op and            "\\wedge")
(make-infix-op or             "\\vee")
(make-infix-op congruent      "\\cong")

(defun zerop-printer (term)
  (infix-print-term1 (list 'congruent (cadr term) 0)))

(declare-fn-printer zerop (function zerop-printer))

(make-infix-op intersection-theories   "\\cap")
(make-infix-op set-difference-theories "{\\rm\\bf{less}}")
(make-infix-op union-theories          "\\cup")


;	UNARY-PREFIX-OPS, UNARY-SUFFIX-OPS, and UNARY-ABS-OPS

; Use make-unary-prefix-op and make-unary-suffix-op only for function symbols
; of one argument.  The string str (or *neg-str*) will be printed before or
; after the argument.

; unary-suffix-ops should be unary function symbols.

; (make-unary-suffix-op foo x str) makes (foo x) print as (x $str$).

; Examples of make-unary-suffix-op.

(make-unary-suffix-op sub1    "-\\;1")
(make-unary-suffix-op numberp "\\in {\\rm\\bf{N}}"        "\\not\\in {\\rm\\bf{N}}")
(make-unary-suffix-op zerop   "\\simeq {\\tt{0}}"         "\\not\\simeq {\\tt{0}}")
;; (make-unary-suffix-op nlistp "\\simeq {\\rm{\\bf{nil}}}" "\\not\\simeq {\\rm{\\bf{nil}}}")

; unary-prefix-ops should be unary function symbols.

; (make-unary-prefix-op foo str) makes (foo x) print as ($str$ x).

; Examples of make-unary-prefix-op.

(make-unary-prefix-op 1+    "1\\;+")
(make-unary-prefix-op minus "-")

; unary-abs-ops should be unary function symbols.

; To create syntax like that for absolute value, use (make-unary-absolute-op
; lhs-str rhs-str), where lhs-str and rhs-str are the strings to print on the
; left and right of the argument.  (make-unary-abs-op foo str1 str2) makes (foo
; x) print as (str1 x str2).  See the example for abs below.


;                           SOME POSSIBLE EXTENSIONS

(defun simple-extension ()

; Here are a few examples of normal mathematical notation for functions not in
; the bootstrap.  Invoke this function to put these into effect.

  (make-unary-abs-op    abs        "\\mid" "\\mid")

  (make-unary-suffix-op fact       "{\\rm{!}}")


  (make-infix-op        subsetp     "\\subset"         "\\not\\subset")
  (make-infix-op        intersect   "\\cap"))

(defun dmg-syntax ()

; Here are some examples once tentatively proposed by David Goldschlag for his
; work.  Invoke this function to put these into effect.

; prefix-multiple-op's should be function symbols that take as many arguments as
; make-prefix-multiple-op is given arguments.  (make-prefix-multiple-op foo str1
; str2) makes (foo x y) print as ($str1$ x $str2$ y).  That is, the first string
; comes first.

  (make-prefix-multiple-op invariant         "\\Box"           "{\\rm\\bf{in}}")
  (make-prefix-multiple-op eventually-stable "\\Diamond\\Box"  "{\\rm\\bf{in}}")

; infix-multiple-op's should be function symbols that take one more argument
; than make-infix-multiple-op is given arguments.  (make-infix-multiple-op foo
; str1 str2) makes (foo x y z) print as (x $str1$ y $str2$ z).  That is, the
; strings are placed between adjacent arguments.

  (make-infix-multiple-op leads-to       "\\mapsto"              "{\\rm\\bf{in}}")
  (make-infix-multiple-op unless         "{\\rm\\bf{unless}}"    "{\\rm\\bf{in}}")
  (make-infix-multiple-op ensures        "{\\rm\\bf{ensures}}"   "{\\rm\\bf{in}}")
  (make-infix-multiple-op e-ensures      "\,${\\rm\\bf{e-ensures}}$\," "{\\rm\\bf{for}}"
                          "{\\rm\\bf{in}}")
  (make-infix-multiple-op n              "\\leadsto"             "{\\rm\\bf{by}}")
  (make-infix-multiple-op initial-condition "{\\rm{\\bf{initially\\;in}}}"))

; Undoing.  To cause applications of a function symbol fn to be printed in the
; default way, i.e., fn(x, y), invoke (clean-up 'fn).

(defparameter *do-not-index-calls-of*
  (union *do-not-index-calls-of*
	 '(implies and or not if cond
		   implies iff union
		   eq = equal
		   le < > ge leq <= geq >= lessp e0-ord-<
		   greaterp
		   member append
		   + - * / remainder
		   union intersection
		   car cadr cdr cddr caddr cons consp
		   disable force integerp member-equal null
		   stringp symbolp true-listp alistp)))
