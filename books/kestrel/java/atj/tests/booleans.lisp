; Java Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../atj" :ttags ((:open-output-channel!) (:oslib) (:quicklisp) :quicklisp.osicat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functions on ACL2 booleans.

(defun negation (x)
  (declare (xargs :guard (booleanp x)))
  (not x))

(defun conjunction (x y)
  (declare (xargs :guard (and (booleanp x) (booleanp y))))
  (and x y))

(defun disjunction (x y)
  (declare (xargs :guard (and (booleanp x) (booleanp y))))
  (or x y))

(defun equality (x y)
  (declare (xargs :guard (and (booleanp x) (booleanp y))))
  (equal x y))

(defun nonequality (x y)
  (declare (xargs :guard (and (booleanp x) (booleanp y))))
  (not (equal x y)))

(defun project1 (x y)
  (declare (xargs :guard (and (booleanp x) (booleanp y)))
           (ignore y))
  x)

(defun project2 (x y)
  (declare (xargs :guard (and (booleanp x) (booleanp y)))
           (ignore x))
  y)

(defun addition (x y)
  (declare (xargs :guard (and (booleanp x) (booleanp y))))
  (let ((sum (not (equal x y)))
        (carry (and x y)))
    (mv sum carry)))

(defun tosymbol (x)
  (declare (xargs :guard (booleanp x)))
  (symbol-name x))

(defun fromsymbol (x)
  (declare (xargs :guard (symbolp x)))
  (if (booleanp x)
      (negation x)
    (equal (symbol-name x) "SOMETHING")))

(defun tovalue (x y)
  (declare (xargs :guard (and (booleanp x) (booleanp y))))
  (cons x y))

(defun fromvalue (x)
  (declare (xargs :guard t))
  (if (booleanp x)
      (negation x)
    (consp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests for the functions on ACL2 booleans.

(defconst *boolean-tests*
  '(("NegationT" (negation t))
    ("NegationF" (negation nil))
    ("ConjunctionTT" (conjunction t t))
    ("ConjunctionTF" (conjunction t nil))
    ("ConjunctionFT" (conjunction nil t))
    ("ConjunctionFF" (conjunction nil nil))
    ("DisjunctionTT" (disjunction t t))
    ("DisjunctionTF" (disjunction t nil))
    ("DisjunctionFT" (disjunction nil t))
    ("DisjunctionFF" (disjunction nil nil))
    ("EqualityTT" (equality t t))
    ("EqualityTF" (equality t nil))
    ("EqualityFT" (equality nil t))
    ("EqualityFF" (equality nil nil))
    ("NonequalityTT" (nonequality t t))
    ("NonequalityTF" (nonequality t nil))
    ("NonequalityFT" (nonequality nil t))
    ("NonequalityFF" (nonequality nil nil))
    ("Project1TT" (project1 t t))
    ("Project1TF" (project1 t nil))
    ("Project1FT" (project1 nil t))
    ("Project1FF" (project1 nil nil))
    ("Project2TT" (project2 t t))
    ("Project2TF" (project2 t nil))
    ("Project2FT" (project2 nil t))
    ("Project2FF" (project2 nil nil))
    ("AdditionTT" (addition t t))
    ("AdditionTF" (addition t nil))
    ("AdditionFT" (addition nil t))
    ("AdditionFF" (addition nil nil))
    ("ToSymbolT" (tosymbol t))
    ("ToSymbolF" (tosymbol nil))
    ("FromSymbolT" (fromsymbol t))
    ("FromSymbolF" (fromsymbol nil))
    ("FromSymbol0" (fromsymbol 'something))
    ("FromSymbol1" (fromsymbol 'other))
    ("ToValueTT" (tovalue t t))
    ("ToValueTF" (tovalue nil t))
    ("ToValueFT" (tovalue t nil))
    ("ToValueFF" (tovalue nil nil))
    ("FromValueT" (fromvalue t))
    ("FromValueF" (fromvalue nil))
    ("FromValue0" (fromvalue 'something))
    ("FromValue1" (fromvalue '(1 2 3)))
    ("FromValue2" (fromvalue "abc"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specialize input and output types, for shallow embedding with guards.

(java::atj-main-function-type negation (:aboolean) :aboolean)

(java::atj-main-function-type conjunction (:aboolean :aboolean) :aboolean)

(java::atj-main-function-type disjunction (:aboolean :aboolean) :aboolean)

(java::atj-main-function-type equality (:aboolean :aboolean) :aboolean)

(java::atj-main-function-type nonequality (:aboolean :aboolean) :aboolean)

(java::atj-main-function-type project1 (:aboolean :aboolean) :aboolean)

(java::atj-main-function-type project2 (:aboolean :aboolean) :aboolean)

(java::atj-main-function-type addition
                              (:aboolean :aboolean)
                              (:aboolean :aboolean))

(java::atj-main-function-type tosymbol (:aboolean) :astring)

(java::atj-main-function-type fromsymbol (:asymbol) :aboolean)

(java::atj-main-function-type tovalue (:aboolean :aboolean) :acons)

(java::atj-main-function-type fromvalue (:avalue) :aboolean)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Generate Java code, with tests.

(java::atj negation
           conjunction
           disjunction
           equality
           nonequality
           project1
           project2
           addition
           tosymbol
           fromsymbol
           tovalue
           fromvalue
           :deep t
           :guards nil
           :java-class "BooleansDeepUnguarded"
           :tests *boolean-tests*)

(java::atj negation
           conjunction
           disjunction
           equality
           nonequality
           project1
           project2
           addition
           tosymbol
           fromsymbol
           tovalue
           fromvalue
           :deep t
           :guards t
           :java-class "BooleansDeepGuarded"
           :tests *boolean-tests*)

(java::atj negation
           conjunction
           disjunction
           equality
           nonequality
           project1
           project2
           addition
           tosymbol
           fromsymbol
           tovalue
           fromvalue
           :deep nil
           :guards nil
           :java-class "BooleansShallowUnguarded"
           :tests *boolean-tests*)

(java::atj negation
           conjunction
           disjunction
           equality
           nonequality
           project1
           project2
           addition
           tosymbol
           fromsymbol
           tovalue
           fromvalue
           :deep nil
           :guards t
           :java-class "BooleansShallowGuarded"
           :tests *boolean-tests*)
