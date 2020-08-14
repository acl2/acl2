; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Since the official transformation is simplify, most of the tests here call
; simplify even though we could call simplify-term instead, since this file is
; about simplifying terms.

(in-package "ACL2")

(include-book "simplify")
(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

; Basic
(deftest
  (simplify (cons (car y) (cdr y)))
  (must-be-redundant
   (DEFTHM SIMPLIFY-TERM-THM
     (EQUAL (CONS (CAR Y) (CDR Y))
            (IF (CONSP Y) Y '(NIL))))))

; Basic, but with simplify-programmatic
(deftest
  (make-event (simplify-programmatic '(cons (car y) (cdr y))))
  (must-be-redundant
   (DEFTHM SIMPLIFY-TERM-THM
     (EQUAL (CONS (CAR Y) (CDR Y))
            (IF (CONSP Y) Y '(NIL))))))

; :Assumptions
(deftest
  (defthm cons-car-cdr-new
    (implies (consp x)
             (equal (cons (car x) (cdr x))
                    x)))
  (simplify (cons (car y) (cdr y))
            :disable cons-car-cdr
            :assumptions ((consp y)))
  (must-be-redundant
   (DEFTHM SIMPLIFY-TERM-THM
     (IMPLIES (CONSP Y)
              (EQUAL (CONS (CAR Y) (CDR Y)) Y)))))

; :Assumptions with extra variables (allowed for simplify-term)
(deftest
  (defthm cons-car-cdr-new
    (implies (consp x)
             (equal (cons (car x) (cdr x))
                    x)))
  (simplify (cons (car y) (cdr y))
            :disable cons-car-cdr
            :assumptions ((consp x) (consp y)))
  (must-be-redundant
   (DEFTHM SIMPLIFY-TERM-THM
     (IMPLIES (AND (CONSP X) (CONSP Y))
              (EQUAL (CONS (CAR Y) (CDR Y)) Y)))))

; :Equiv, with untranslate using t for iff-flg
(deftest
  (simplify (cons (car y) (cdr y)) :equiv iff)
  (must-be-redundant
   (DEFTHM SIMPLIFY-TERM-THM
     (IFF (CONS (CAR Y) (CDR Y))
          (OR (CONSP Y) '(NIL))))))

; :Theory, :disable, and :rule-classes
(deftest
  (simplify (list (* y x)
                  (car (cons a a)))
            :theory (theory 'ground-zero)
            :rule-classes nil)
  (DEFTHM SIMPLIFY-TERM-THM
    (EQUAL (LIST (* Y X) (CAR (CONS A A)))
           (LIST (* X Y) A))
    :RULE-CLASSES NIL)
  (make-event (simplify-programmatic '(list (* y x)
                                            (car (cons a a)))
                                     :theory '(theory 'ground-zero)
                                     :rule-classes nil))
  (DEFTHM SIMPLIFY-TERM-THM$1
    (EQUAL (LIST (* Y X) (CAR (CONS A A)))
           (LIST (* X Y) A))
    :RULE-CLASSES NIL)
  (simplify (list (* y x)
                  (car (cons a a)))
            :disable commutativity-of-*)
  (DEFTHM SIMPLIFY-TERM-THM$2
    (EQUAL (LIST (* Y X) (CAR (CONS A A)))
           (LIST (* Y X) A))))

; :Simplify-body
(deftest
  (simplify (list (+ 2 (+ 3 z))
                  (list (* 3 (+ 1 (+ 1 x)))
                        (* 3 (+ 1 (+ 1 x)))
                        (* 20 (+ 1 (+ 1 y)))))
            :simplify-body
            (list @ _ @)
            :theory (theory 'ground-zero))
  (must-be-redundant
   (DEFTHM SIMPLIFY-TERM-THM
     (EQUAL (LIST (+ 2 (+ 3 Z))
                  (LIST (* 3 (+ 1 (+ 1 X)))
                        (* 3 (+ 1 (+ 1 X)))
                        (* 20 (+ 1 (+ 1 Y)))))
            (LIST (+ 2 (+ 3 Z))
                  (LIST (+ 6 (* 3 X))
                        (* 3 (+ 1 (+ 1 X)))
                        (+ 40 (* 20 Y))))))))

; :Thm-name
(deftest
  (simplify (cons (car y) (cdr y))
            :thm-name foo)
  (must-be-redundant
   (DEFTHM FOO
     (EQUAL (CONS (CAR Y) (CDR Y))
            (IF (CONSP Y) Y '(NIL))))))

; :Thm-enable
(deftest
  (simplify (cons (car y) (cdr y))
            :thm-enable nil)
  (must-be-redundant
   (DEFTHM SIMPLIFY-TERM-THM
     (EQUAL (CONS (CAR Y) (CDR Y))
            (IF (CONSP Y) Y '(NIL)))))
  (assert-event (disabledp 'simplify-term-thm)))

; :Expand
(deftest
  (simplify (cons (nth n x) (nth k x))
            :expand ((nth n x)))
  (must-be-redundant
   (DEFTHM SIMPLIFY-TERM-THM
     (EQUAL (CONS (NTH N X) (NTH K X))
            (CONS (AND (CONSP X)
                       (IF (ZP N)
                           (CAR X)
                           (NTH (+ -1 N) (CDR X))))
                  (NTH K X))))))

; :Untranslate: note that we don't test :nice-expanded; see the comment near
; the top of simplify-defun-impl.lisp, "Do something about the case that
; :untranslate is :nice-expanded...."
(deftest
  (simplify (list (first x) (car (cons y y)))
            :thm-name untranslate-default)
  (assert-event (equal (getpropc 'untranslate-default 'untranslated-theorem)
                       '(EQUAL (LIST (FIRST X) (CAR (CONS Y y)))
                               (LIST (FIRST X) Y))))
  (simplify (list (first x) (car (cons y y)))
            :thm-name untranslate-nice)
  (assert-event (equal (getpropc 'untranslate-nice 'untranslated-theorem)
                       '(EQUAL (LIST (FIRST X) (CAR (CONS Y y)))
                               (LIST (FIRST X) Y))))
  (simplify (list (first x) (car (cons y y)))
            :untranslate nil
            :thm-name untranslate-nil)
  (assert-event (equal (getpropc 'untranslate-nil 'untranslated-theorem)
                       '(EQUAL (LIST (FIRST X) (CAR (CONS Y Y)))
                               (CONS (CAR X) (CONS Y 'NIL)))))
  (simplify (list (first x) (car (cons y y)))
            :untranslate t
            :thm-name untranslate-t)
  (assert-event (equal (getpropc 'untranslate-t 'untranslated-theorem)
                       '(EQUAL (LIST (FIRST X) (CAR (CONS Y Y)))
                               (LIST (CAR X) Y)))))

; Errors
(deftest
  (must-fail ; Error in hyps
   (simplify (cons (car y) (cdr y))
             :assumptions ((abcd))))
  (must-fail ; No change
   (simplify (car x)))
  (must-fail ; No change in untranslated term
   (simplify (if (atom x) y z)))
  (must-fail ; Name in Lisp package
   (simplify (cons (car y) (cdr y))
             :thm-name acosh))
  (must-fail ; Not a new name
   (simplify (cons (car y) (cdr y))
             :thm-name rewrite))
  (must-fail ; Undefined term
   (simplify (abc)))
  (must-fail ; Bad value for keyword
   (simplify (cons (car y) (cdr y))
             :untranslate hello))
  (must-fail ; Unknown rule
   (simplify (cons (car y) (cdr y))
             :enable hello))
  (must-fail ; Bad equivalence relation (not a symbol)
   (simplify (cons (car y) (cdr y))
             :equiv (iff)))
  (must-fail ; Bad equivalence relation
   (simplify (cons (car y) (cdr y))
             :equiv nth))
  (must-fail ; :Program mode functions
   (simplify (car (cons (fchecksum-atom x) x))))
  (must-fail ; Illegal to supply :theory and :enable
   (simplify (cons (car y) (cdr y))
             :theory (theory 'ground-zero)
             :disable nth))
  (must-fail ; Better error by having simplify check rule-classes explicitly
   (simplify (list (* y x) (car (cons a a)))
             :rule-classes :type-prescription)))

; Other variants
(deftest
  (must-succeed
   (show-simplify (list (* y x)
                        (car (cons a a)))
                  :theory (theory 'ground-zero)
                  :rule-classes nil))
  (must-succeed
   (show-simplify-term (list (* y x)
                             (car (cons a a)))
                       :theory (theory 'ground-zero)
                       :rule-classes nil))
  (simplify (cons (car y) (cdr y))
            :print :info)
  (must-be-redundant
   (DEFTHM SIMPLIFY-TERM-THM
     (EQUAL (CONS (CAR Y) (CDR Y))
            (IF (CONSP Y) Y '(NIL)))))
  (simplify-term (cons (car y) (cdr y))) ; redundant
  (simplify-term (cons (car y) (cdr y))
                 :rule-classes nil)
  (must-be-redundant
   (DEFTHM SIMPLIFY-TERM-THM$1
     (EQUAL (CONS (CAR Y) (CDR Y))
            (IF (CONSP Y) Y '(NIL)))
     :rule-classes nil))
  (make-event ; redundant
   (simplify-term-programmatic '(cons (car y) (cdr y))))
  (make-event
   (simplify-term-programmatic '(cons (car y) (cdr y))
                               :enable 'nth))
  (must-be-redundant
   (DEFTHM SIMPLIFY-TERM-THM$2
     (EQUAL (CONS (CAR Y) (CDR Y))
            (IF (CONSP Y) Y '(NIL))))))
