; Tests of rewriter-basic
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: add more tests
;; TODO: test xor normalization

(include-book "rewriter-basic")
(include-book "dag-to-term")
(include-book "make-term-into-dag-simple")
(include-book "make-equality-dag-basic")
(include-book "std/testing/assert-bang-stobj" :dir :system)
(include-book "kestrel/utilities/deftest" :dir :system)

;;;
;;; tests of simplify-term-to-term-basic (which returns a term)
;;;

(defmacro simplify-term-to-term-basic-wrapper (term
                                    &key
                                    (assumptions 'nil)
                                    (rule-alist 'nil)
                                    (interpreted-function-alist 'nil)
                                    (known-booleans 'nil)
                                    (normalize-xors 'nil)
                                    (limits 'nil)
                                    (memoizep 't)
                                    (count-hits 't)
                                    (print 't)
                                    (monitored-symbols 'nil)
                                    (fns-to-elide 'nil))
  `(simplify-term-to-term-basic ,term
                    ,assumptions
                    ,rule-alist
                    ,interpreted-function-alist
                    ,known-booleans
                    ,normalize-xors
                    ,limits
                    ,memoizep
                    ,count-hits
                    ,print
                    ,monitored-symbols
                    ,fns-to-elide))

;; A simple test that applies the rewrite rule CAR-CONS to simplify a term:
(assert!
  (mv-let (erp term)
    (simplify-term-to-term-basic-wrapper '(car (cons (foo x) (foo y)))
                             :rule-alist (make-rule-alist! '(car-cons) (w state))
                             :known-booleans (known-booleans (w state)))
    (and (not erp) ;no error
         ;; resulting term is (FOO X):
         (equal term '(foo x)))))

;; A test that computes a ground term
(assert!
  (mv-let (erp term)
    (simplify-term-to-term-basic-wrapper '(binary-+ '3 '4)
                             :known-booleans (known-booleans (w state)))
    (and (not erp)
         (equal term ''7))))

;; A test that uses an assumption
(assert!
  (mv-let (erp term)
    (simplify-term-to-term-basic-wrapper '(natp x)
                             :assumptions '((natp x))
                             :known-booleans (known-booleans (w state)))
    (and (not erp)
         (equal term ''t))))

;; A test that uses an equality assumption
(assert!
  (mv-let (erp term)
    (simplify-term-to-term-basic-wrapper '(binary-+ '1 x)
                             :assumptions '((equal x (binary-* y z)))
                             :known-booleans (known-booleans (w state)))
    (and (not erp)
         (equal term '(binary-+ '1 (binary-* y z))))))

;; A test that returns a variable
(assert!
 (mv-let (erp res)
   (simplify-term-to-term-basic '(car (cons x y)) nil (make-rule-alist! '(car-cons) (w state)) nil (known-booleans (w state)) nil nil nil nil t nil nil)
   (and (not erp)
        (equal res 'x))))

;; A test that returns a constant
(assert!
 (mv-let (erp res)
   (simplify-term-to-term-basic '(car (cons '2 y)) nil (make-rule-alist! '(car-cons) (w state)) nil (known-booleans (w state)) nil nil nil nil t nil nil)
   (and (not erp)
        (equal res ''2))))

;; todo: use more (add more options, such as rules)
;; todo: consider trying both with and without memoization, and other combinations of argument that shouldn't matter
;; to debug failures, consider doing (trace$ simplify-term-to-term-basic).
(defmacro test-simplify-term-to-term (input-term output-term
                                     &key
                                     (assumptions 'nil)
                                     (rules 'nil)
                                     (memoizep 't)
                                     (count-hits 't))
  `(assert!
     (mv-let (erp term)
       (simplify-term-to-term-basic ',input-term
                        ',assumptions
                        (make-rule-alist! ,rules (w state))
                        nil ; interpreted-function-alist
                        (known-booleans (w state))
                        nil ; normalize-xors
                        nil
                        ,memoizep
                        ,count-hits   ; count-hits
                        nil ; print
                        nil ; monitored-symbols
                        nil ; fns-to-elide
                        )
       (and (not erp)
            (equal term ',output-term)))))

;; TODO: Make versions of all of these that call simplify-dag-basic

(test-simplify-term-to-term (if a b c) (if a b c)) ; no change
(test-simplify-term-to-term (if 't x y) x)
(test-simplify-term-to-term (if '7 x y) x)
(test-simplify-term-to-term (if 'nil x y) y)
(test-simplify-term-to-term (if test x y) x :assumptions (test))

(test-simplify-term-to-term (not 't) 'nil)
(test-simplify-term-to-term (not '3) 'nil)
(test-simplify-term-to-term (not 'nil) 't)
(test-simplify-term-to-term (not (not 'nil)) 'nil)
(test-simplify-term-to-term (not (not 't)) 't)
(test-simplify-term-to-term (not (not '3)) 't)
(test-simplify-term-to-term (not (not (not 'nil))) 't)
(test-simplify-term-to-term (not test) 'nil :assumptions (test))

(test-simplify-term-to-term (myif a b c) (myif a b c)) ; no change
(test-simplify-term-to-term (myif 't x y) x)
(test-simplify-term-to-term (myif '7 x y) x)
(test-simplify-term-to-term (myif 'nil x y) y)
(test-simplify-term-to-term (myif test x y) x :assumptions (test))

(test-simplify-term-to-term (boolif a b c) (boolif a b c)) ; no change
(test-simplify-term-to-term (boolif 't x y) (bool-fix$inline x))
(test-simplify-term-to-term (boolif '7 x y) (bool-fix$inline x))
(test-simplify-term-to-term (boolif 'nil x y) (bool-fix$inline y))
;; for these, we can evaluate the bool-fix:
(test-simplify-term-to-term (boolif 't 't y) 't)
(test-simplify-term-to-term (boolif '7 '3 y) 't)
(test-simplify-term-to-term (boolif 'nil x 'nil) 'nil)
(test-simplify-term-to-term (boolif test x y) (bool-fix$inline x) :assumptions (test))

;; The then-branch of the BOOLIF gets simplified preserving IFF:
(test-simplify-term-to-term (boolif test x y) (boolif test 't y) :assumptions (x))
;; The else-branch of the BOOLIF gets simplified preserving IFF:
(test-simplify-term-to-term (boolif test x y) (boolif test x 't) :assumptions (y))


;; can't simplify the then-branch to t because we are memoizing:
(test-simplify-term-to-term (boolif (test x) (test x) y) (boolif (test x) (test x) y))
;; If we turn off memoization, the rewriter assumes the BOOLIF test when simplifying the then-branch:
(test-simplify-term-to-term (boolif (test x) (test x) y) (boolif (test x) 't y) :memoizep nil)
;; we now handle variable assumptions better:
(test-simplify-term-to-term (boolif test test y) (boolif test 't y) :memoizep nil)
(test-simplify-term-to-term (boolif (not test) test y) (boolif (not test) 'nil y) :memoizep nil)

;; can't simplify the else-branch to t because we are memoizing:
(test-simplify-term-to-term (boolif (not (test x)) y (test x)) (boolif (not (test x)) y (test x)))
;; If we turn off memoization, the rewriter assumes the BOOLIF test when simplifying the else-branch:
(test-simplify-term-to-term (boolif (not (test x)) y (test x)) (boolif (not (test x)) y 't) :memoizep nil)
(test-simplify-term-to-term (boolif (not test) y test) (boolif (not test) y 't) :memoizep nil)
(test-simplify-term-to-term (boolif test y test) (boolif test y 'nil) :memoizep nil)

;; Here the A is just one conjunct of the test we are assuming:
(test-simplify-term-to-term (boolif (if a y 'nil) a c)
                (boolif (if a y 'nil) 't c)
                :memoizep nil)

(test-simplify-term-to-term (boolif (if y a 'nil) a c)
                (boolif (if y a 'nil) 't c)
                :memoizep nil)

(test-simplify-term-to-term (bvif '32 a b c) (bvif '32 a b c)) ; no change
(test-simplify-term-to-term (bvif '32 't x y) (bvchop '32 x))
(test-simplify-term-to-term (bvif '32 '7 x y) (bvchop '32 x))
(test-simplify-term-to-term (bvif '32 'nil x y) (bvchop '32 y))
;; for these, we can evaluate the bvchop:
(test-simplify-term-to-term (bvif '32 't '1 y) '1)
(test-simplify-term-to-term (bvif '32 '7 (binary-+ '2 (expt '2 '32)) y) '2)
(test-simplify-term-to-term (bvif '32 'nil x '7) '7)

;; The test is used to rewrite the then-branch:
(test-simplify-term-to-term (bvif '32 (equal x '8) x y)
                (bvif '32 (equal x '8) '8 y)
                :memoizep nil)

;; The negation of the test is used to rewrite the else-branch:
(test-simplify-term-to-term (bvif '32 (not (equal x '8)) y x)
                (bvif '32 (not (equal x '8)) y '8)
                :memoizep nil)

;; Tests with rules:

(test-simplify-term-to-term (car (cons x y)) x :rules '(car-cons) :count-hits :total)
(test-simplify-term-to-term (car (cons x y)) x :rules '(car-cons) :count-hits t)
(test-simplify-term-to-term (car (cons x y)) x :rules '(car-cons) :count-hits nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; tests of simplify-term-basic (which returns a DAG)
;;;

(defmacro simplify-term-basic-wrapper (term
                                       &key
                                       (assumptions 'nil)
                                       (rule-alist 'nil)
                                       (interpreted-function-alist 'nil)
                                       (known-booleans 'nil)
                                       (normalize-xors 'nil)
                                       (limits 'nil)
                                       (memoizep 't)
                                       (count-hits 't)
                                       (print 't)
                                       (monitored-symbols 'nil)
                                       (fns-to-elide 'nil))
  `(simplify-term-basic ,term
                        ,assumptions
                        ,rule-alist
                        ,interpreted-function-alist
                        ,known-booleans
                        ,normalize-xors
                        ,limits
                        ,memoizep
                        ,count-hits
                        ,print
                        ,monitored-symbols
                        ,fns-to-elide))

(assert!
 (mv-let (erp result) ;; result is always DAG or a quotep
   (simplify-term-basic-wrapper '(binary-+ '0 '0)
                                :known-booleans (known-booleans (w state)))
   (and (not erp)
        (equal result ''0))))

(deftest
  (defthm if-same-branches
    (equal (if test x x)
           x))

  (defstub foo (x) t)

  (assert!
   (mv-let (erp res)
     ;; Returns (mv nil 't).
     (simplify-term-basic-wrapper '(if (not (consp x))
                                       (if (if (integer-listp x) (consp x) 'nil)
                                           (if (member-equal (foo x) x)
                                               (<=-all (foo x) x)
                                             'nil)
                                         't)
                                     't)
                                  :rule-alist (make-rule-alist! '(if-same-branches) (w state))
                                  :known-booleans (known-booleans (w state))
                                  :memoizep nil)
     (and (not erp)
          (equal res *t*)))))

;;;
;;; Tests when not memoizing
;;;

;; Test that (non-negated) if tests rewrite to t in the then branch when boolean
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (natp x) (natp x) y)
                                :known-booleans (known-booleans (w state)) :memoizep nil :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (natp x) 't y)))))

;; Test that (non-negated) if tests don't rewrite in the then branch when not boolean
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (foo x) (foo x) y)
                                :known-booleans (known-booleans (w state)) :memoizep nil :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (foo x) (foo x) y)))))

;; Test that (non-negated) if tests rewrite to nil in the else branch
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if x y x)
                                :known-booleans (known-booleans (w state)) :memoizep nil :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if x y 'nil)))))

;; Test that negated if tests rewrite to nil in the then branch
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (natp x)) (natp x) y)
                                :known-booleans (known-booleans (w state)) :memoizep nil :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (natp x)) 'nil y)))))

;; Test that negated if tests rewrite to nil in the then branch, negated in branch
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (natp x)) (not (natp x)) y)
                                :known-booleans (known-booleans (w state)) :memoizep nil :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (natp x)) 't y)))))

;; Test that negated if tests rewrite to t in the else branch when boolean
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (natp x)) y (natp x))
                                :known-booleans (known-booleans (w state)) :memoizep nil :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (natp x)) y 't)))))

;; Test that negated if tests rewrite to t in the else branch when boolean, negated in branch
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (natp x)) y (not (natp x)))
                                :known-booleans (known-booleans (w state)) :memoizep nil :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (natp x)) y 'nil)))))

;; Test that negated if tests don't rewrite in the else branch when not boolean
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (foo x)) y (foo x))
                                :known-booleans (known-booleans (w state)) :memoizep nil :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (foo x)) y (foo x))))))

;; Special case: Test that negated if tests rewrite in the else branch when negated there, even when not boolean.
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (foo x)) y (not (foo x)))
                                :known-booleans (known-booleans (w state)) :memoizep nil :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (foo x)) y 'nil)))))

;;;
;;; Tests when memoizing (no context info should be used)
;;;

;; Non-negated test in then-branch (boolean)
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (natp x) (natp x) y)
                                 :known-booleans (known-booleans (w state)) :count-hits nil
                                )
   (and (not erp)
        (equal (dag-to-term res) '(if (natp x) (natp x) y)))))

;; Non-negated test in else-branch (boolean)
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (natp x) y (natp x))
                                 :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (natp x) y (natp x))))))

;; Non-negated test in then-branch (not boolean)
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (foo x) (foo x) y)
                                 :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (foo x) (foo x) y)))))

;; Non-negated test in else-branch (not boolean)
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (foo x) y (foo x))
                                 :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (foo x) y (foo x))))))

;; Negated test in then-branch (boolean)
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (natp x)) (not (natp x)) y)
                                 :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (natp x)) (not (natp x)) y)))))

;; Negated test in then-branch (boolean), no negation in branch
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (natp x)) (natp x) y)
                                 :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (natp x)) (natp x) y)))))

;; Negated test in else-branch (boolean)
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (natp x)) y (not (natp x)))
                                 :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (natp x)) y (not (natp x)))))))

;; Negated test in else-branch (boolean), no negation in branch
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (natp x)) y (natp x))
                                 :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (natp x)) y (natp x))))))

;; Negated test in then-branch (not boolean)
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (foo x)) (not (foo x)) y)
                                 :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (foo x)) (not (foo x)) y)))))

;; Negated test in then-branch (not boolean), no negation in branch
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (foo x)) (foo x) y)
                                 :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (foo x)) (foo x) y)))))

;; Negated test in else-branch (not boolean)
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (foo x)) y (not (foo x)))
                                 :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (foo x)) y (not (foo x)))))))

;; Negated test in else-branch (not boolean), no negation in branch
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (foo x)) y (foo x))
                                 :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (foo x)) y (foo x))))))

;; Test with a non-boolean assumption that appears in an IF test.  This works
;; because we store :non-nil for it in the node-replacement-array
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (member-equal x y) w z)
                                :assumptions
                                '((member-equal x y))
                                :known-booleans (known-booleans (w state))
                                :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) 'w))))

;; The known assumption appears in a call of NOT.
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (member-equal x y)) w z)
                                :assumptions '((member-equal x y))
                                :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) 'z))))

;; Test with a non-boolean assumption that appears in an IF test.  This works
;; because we store :non-nil for it in the node-replacement-array
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (member-equal x y) w z)
                                :assumptions '((not (member-equal x y)))
                                :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) 'z))))

;; The known assumption appears in a call of NOT.
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (member-equal x y)) w z)
                                :assumptions '((not (member-equal x y)))
                                :known-booleans (known-booleans (w state)) :count-hits nil)
   (and (not erp)
        (equal (dag-to-term res) 'w))))



;; Note that the IF-TEST is an equality that should be used for replacement
(deftest
  (defthm if-same (equal (if x y y) y))
  (assert!
   (mv-let (erp res)
     (simplify-term-basic-wrapper '(if (equal x '3) (equal (binary-+ '1 x) '4) 't)
                                  :rule-alist (make-rule-alist! '(if-same) (w state))
                                  :known-booleans (known-booleans (w state))
                                  :memoizep nil ; can't be memoizing if we want to use contexts
                                  :count-hits nil)
     (and (not erp)
          (equal (dag-to-term res) ''t)))))

;; Note that the IF-TEST has a term that is needed for free var matching
(deftest
  (defthmd <-trans-simple
    (implies (and (< x z) (< z y))
             (< x y)))
  (assert!
   (mv-let (erp res)
     (simplify-term-basic-wrapper '(if (< x y) (if (< y z) (< x z) blah) blah2)
                                  :rule-alist (make-rule-alist! '(<-TRANS-simple) (w state))
                                  :known-booleans (known-booleans (w state))
                                  :monitored-symbols '(<-trans-simple)
                                  :memoizep nil :count-hits nil)
     (and (not erp)
          (equal (dag-to-term res) '(if (< x y) (if (< y z) 't blah) blah2))))))

;;; test (DEF-SIMPLIFIED-BASIC *foo* '((2 if 1 0 '3) (1 . 't) (0 . x)))

;;; tests with xor:

(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(bvxor '32 x y)
                                :known-booleans (known-booleans (w state)) :count-hits nil :normalize-xors t)
   (and (not erp)
        (equal (dag-to-term res) '(bvxor '32 x y)))))

(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(bvxor '32 x (bvxor '32 y x))
                                :known-booleans (known-booleans (w state)) :count-hits nil :normalize-xors t)
   (and (not erp)
        (equal (dag-to-term res) '(bvchop '32 y)))))

(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(bvxor '32 '16 (bvxor '32 x '1))
                                :known-booleans (known-booleans (w state)) :count-hits nil :normalize-xors t)
   (and (not erp)
        (equal (dag-to-term res) '(bvxor '32 '17 x)))))

;; tests about the memoization:

;; no change, since memoizing prevents us from using the context
;todo: support 2 passes, as we do for rewriting dags!
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(if (not (consp x)) (equal '3 (car x)) (equal '4 (car x)))
                                :rule-alist (make-rule-alist! '(default-car) (w state))
                                :known-booleans (known-booleans (w state))
                                :count-hits nil
                                :normalize-xors t)
   (and (not erp)
        (equal (dag-to-term res) '(if (not (consp x)) (equal '3 (car x)) (equal '4 (car x)))))))

;; Example where a BVIF becomes a (bvchop '32 '1), which can be evaluated.
;; Since we simplify the result, all is well.
(assert!
 (mv-let (erp res)
   (simplify-term-basic-wrapper '(bvif '32 't '1 x)
                                :known-booleans (known-booleans (w state))
                                :count-hits nil :normalize-xors t)
   (and (not erp)
        (equal (dag-to-term res) ''1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert!
 (mv-let (erp res limits)
   (simplify-dag-basic (make-term-into-dag-simple! '(cons a b)) nil (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
   (and (not erp) (null limits)
        (equal res (make-term-into-dag-simple! '(cons a b))))))

;; The test gets resolved:
(assert!
  (mv-let (erp res limits)
    (simplify-dag-basic (make-term-into-dag-simple! '(if 't a b)) nil (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
    (and (not erp) (null limits)
         (equal res (make-term-into-dag-simple! 'a)))))

;; The test gets resolved:
(assert!
  (mv-let (erp res limits)
    (simplify-dag-basic (make-term-into-dag-simple! '(if 'nil a b)) nil (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
    (and (not erp) (null limits)
         (equal res (make-term-into-dag-simple! 'b)))))

;; The test gets resolved:
(assert!
  (mv-let (erp res limits)
    (simplify-dag-basic (make-term-into-dag-simple! '(myif 't a b)) nil (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
    (and (not erp) (null limits)
         (equal res (make-term-into-dag-simple! 'a)))))

;; The test gets resolved:
(assert!
  (mv-let (erp res limits)
    (simplify-dag-basic (make-term-into-dag-simple! '(myif 'nil a b)) nil (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
    (and (not erp) (null limits)
         (equal res (make-term-into-dag-simple! 'b)))))

;; The test gets resolved:
(assert!
  (mv-let (erp res limits)
    (simplify-dag-basic (make-term-into-dag-simple! '(boolif 't a b)) nil (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
    (and (not erp) (null limits)
         (equal res (make-term-into-dag-simple! '(bool-fix$inline a))))))

;; The test gets resolved:
(assert!
  (mv-let (erp res limits)
    (simplify-dag-basic (make-term-into-dag-simple! '(boolif 'nil a b)) nil (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
    (and (not erp) (null limits)
         (equal res (make-term-into-dag-simple! '(bool-fix$inline b))))))

;; The test gets resolved:
(assert!
  (mv-let (erp res limits)
    (simplify-dag-basic (make-term-into-dag-simple! '(bvif '32 't a b)) nil (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
    (and (not erp) (null limits)
         (equal res (make-term-into-dag-simple! '(bvchop '32 a))))))

;; The test gets resolved:
(assert!
  (mv-let (erp res limits)
    (simplify-dag-basic (make-term-into-dag-simple! '(bvif '32 'nil a b)) nil (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
    (and (not erp) (null limits)
         (equal res (make-term-into-dag-simple! '(bvchop '32 b))))))

;; The test gets resolved, even when it's an assumption:
(assert!
  (mv-let (erp res limits)
    (simplify-dag-basic (make-term-into-dag-simple! '(if (natp x) a b)) '((natp x)) (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
    (and (not erp) (null limits)
         (equal res (make-term-into-dag-simple! 'a)))))

;; The test gets resolved, even when it's an assumption and is non-boolean:
(assert!
  (mv-let (erp res limits)
    (simplify-dag-basic (make-term-into-dag-simple! '(if x a b)) '(x) (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
    (and (not erp) (null limits)
         (equal res (make-term-into-dag-simple! 'a)))))

(assert!
 (mv-let (erp res limits)
   (simplify-dag-basic (make-term-into-dag-simple! '(not 't)) nil (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
   (and (not erp) (null limits)
        (equal res (make-term-into-dag-simple! ''nil)))))

(assert!
 (mv-let (erp res limits)
   (simplify-dag-basic (make-term-into-dag-simple! '(not '3)) nil (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
   (and (not erp) (null limits)
        (equal res (make-term-into-dag-simple! ''nil)))))

(assert!
 (mv-let (erp res limits)
   (simplify-dag-basic (make-term-into-dag-simple! '(not 'nil)) nil (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
   (and (not erp) (null limits)
        (equal res (make-term-into-dag-simple! ''t)))))

(assert!
 (mv-let (erp res limits)
   (simplify-dag-basic (make-term-into-dag-simple! '(not x))
                       '(x) ; assumptions
                       (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
   (and (not erp) (null limits)
        (equal res (make-term-into-dag-simple! ''nil)))))

;; todo: the NOT did not get resolved:
(assert!
 (mv-let (erp res limits)
   (simplify-dag-basic (make-term-into-dag-simple! '(not (foo x)))
                       '((foo x)) ; assumptions
                       (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
   (and (not erp) (null limits)
        (equal res (make-term-into-dag-simple! ''nil)))))

;; Rewriter replaces (foo x) with t because the args of boolif can be simplified using iff:
(assert!
 (mv-let (erp res limits)
   (simplify-dag-basic (make-term-into-dag-simple! '(boolif test (foo x) 'nil))
                       '((foo x)) ; assumptions
                       (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
   (and (not erp) (null limits)
        (equal res (make-term-into-dag-simple! '(boolif test 't 'nil))))))

;; Rewriter replaces (foo x) with t because the args of boolif can be simplified using iff:
(assert!
 (mv-let (erp res limits)
   (simplify-dag-basic (make-term-into-dag-simple! '(boolif test 'nil (foo x)))
                       '((foo x)) ; assumptions
                       (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
   (and (not erp) (null limits)
        (equal res (make-term-into-dag-simple! '(boolif test 'nil 't))))))

;; Substitutes 8 for x in the then-branch:
(assert!
  (mv-let (erp res limits)
    (simplify-dag-basic (make-term-into-dag-simple! '(if (equal x '8) (binary-+ x '1) '0))
                        '() ; assumptions
                        (empty-rule-alist) nil nil nil nil nil nil nil nil nil)
    (and (not erp) (null limits)
         (equal res (make-term-into-dag-simple! '(if (equal x '8) '9 '0))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; test with a binding hyp
(local (include-book "kestrel/lists-light/append" :dir :system))
(defthm rule1
  (implies (and (axe-binding-hyp (equal xlen (len x))) ; bind x to the length of y
                (< 5 xlen)
                )
           (equal (len (append x y))
                  (+ xlen (len y)))))

(assert!
 (mv-let (erp term)
   (simplify-term-to-term-basic '(len (binary-append '(1 2 3 4 5 6) y))
                    nil     ; assumptions
                    (make-rule-alist! '(rule1) (w state))
                    nil     ; interpreted-function-alist
                    (known-booleans (w state))
                    nil     ; normalize-xors
                    nil
                    t       ; memoizep
                    t       ; count-hits
                    t       ; print
                    nil     ; monitored-symbols
                    nil     ; fns-to-elide
                    )
   (and (not erp) ;no error
        ;; resulting term is (FOO X):
        (equal term '(binary-+ '6 (len y))))))

;; the rule doesn't fire because of the (< 5 xlen) hyp
(assert!
 (mv-let (erp term)
   (simplify-term-to-term-basic '(len (binary-append '(1 2 3) y))
                    nil     ; assumptions
                    (make-rule-alist! '(rule1) (w state))
                    nil     ; interpreted-function-alist
                    (known-booleans (w state))
                    nil     ; normalize-xors
                    nil
                    t       ; memoizep
                    t       ; count-hits
                    t       ; print
                    nil     ; monitored-symbols
                    nil     ; fns-to-elide
                    )
   (and (not erp) ;no error
        ;; resulting term is (FOO X):
        (equal term '(len (binary-append '(1 2 3) y))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test :compact xor normalization:

(include-book "basic-rules") ; for equal-same

(def-simplified-basic *result1*
  (acl2::make-equality-dag-basic! '(bvxor 32 6 (bvxor 32 x (bvxor 32 y 5)))
                                  '(bvxor 32 x (bvxor 32 (bvxor 32 5 y) 6))
                                  nil (w state))
  :rules '(equal-same)
  :normalize-xors :compact)

(must-be-redundant (defconst *result1* ''t))

(def-simplified-basic *result2*
  (acl2::make-equality-dag-basic! '(bitxor 0 (bitxor x (bitxor y 1)))
                                  '(bitxor x (bitxor (bitxor 1 y) 0))
                                  nil (w state))
  :rules '(equal-same)
  :normalize-xors :compact)

(must-be-redundant (defconst *result2* ''t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test of simplifying a term
(def-simplified-basic *result3* '(equal x x)
    :rules '(equal-same)
  :normalize-xors :compact)

(must-be-redundant (defconst *result3* ''t))
