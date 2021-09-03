; Tests of rewriter-new
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add tests about simplify-term (these mostly test rewrite-term)

(include-book "rewriter-alt")
(include-book "kestrel/utilities/deftest" :dir :system)
(include-book "kestrel/utilities/assert-with-stobjs" :dir :system)
(include-book "basic-rules") ;for equal-same

(defstub foo (x) t)


(check-rewrite 'x 'x)
(check-rewrite ''70 ''70)
(check-rewrite '(bar x) '(bar x))
(check-rewrite '(bvplus '32 '100 '7) ''107)
(defun test-ifn (x y) (+ x y)) ;for testing evaluation of interpreted functions
(check-rewrite '(test-ifn '78 '100) ''178 :interpreted-function-alist (add-fns-to-interpreted-function-alist '(test-ifn) nil (w state)))
(defstub bar (x) t)
(defstub baz (x) t)
(skip-proofs (defthmd foo-bar (equal (foo x) (bar x))))
(skip-proofs (defthmd bar-baz (equal (bar x) (baz x))))
(skip-proofs (defthm foo-foo (equal (foo x) (foo x)) :rule-classes nil)) ;no longer a legal rewrite rule
(check-rewrite '(foo x) '(foo x) :runes '(bar-baz))
(check-rewrite '(foo x) '(bar x) :runes '(foo-bar))
(check-rewrite '(foo x) '(baz x) :runes '(foo-bar bar-baz))
(check-rewrite '(foo (foo x)) '(baz (baz x)) :runes '(foo-bar bar-baz))
(check-rewrite '(foo (bvplus '32 '100 '7)) '(bar '107) :runes '(foo-bar))
(check-rewrite '(foo (bvplus '32 '100 '7)) '(baz '107) :runes '(foo-bar bar-baz))
(check-rewrite '(equal x x) ''t :runes '(EQUAL-SAME)) ;x appears twice
(check-rewrite '(equal x y) '(equal x y) :runes '(EQUAL-SAME))
;;(check-rewrite '(foo x) '(foo x) :runes '(foo-foo)) ;should loop forever
(check-rewrite '(if 't x y) '(if 't x y))
(check-rewrite '(if 't x y) 'x :runes '(if-when-not-nil))
(check-rewrite '(if 't x y) 'x :oi-runes '(if-when-not-nil))
(check-rewrite '(if '7 x y) 'x :oi-runes '(if-when-not-nil))
(check-rewrite '(if 'nil x y) 'y :runes '(if-when-nil))
(check-rewrite '(if 'nil x y) 'y :oi-runes '(if-when-nil))
(check-rewrite '(if (not (equal x x)) (foo x) y) 'y :runes '(equal-same):oi-runes '(if-when-nil)) ;this works even the test is not the constant nil
;;(check-rewrite '(if 'nil (foo x) y) 'y :oi-runes '() :runes '(if-of-nil foo-foo)) ;loops!
(check-rewrite '(if 'nil (foo x) y) 'y :oi-runes '(if-when-nil) :runes '(foo-foo)) ;doesn't loop!

;fixme add some tests for monitoring

(check-rewrite 'x 'y :assumptions '((equal x y)))
(check-rewrite 'x 'x :assumptions '((equal z y)))
(check-rewrite '(foo x) '(foo y) :assumptions '((equal x y)))
(check-rewrite '(foo x) '(foo y) :assumptions '((equal (foo x) (foo y))))
(check-rewrite 'x ''3 :assumptions '((equal x '3)))
(check-rewrite '(foo x) ''7 :assumptions '((equal x '3)(equal (foo '3) '7)))

;; ;the lambda gets expanded when the term is made into a dag:
;; (rewrite-term '((lambda (x y) (binary-+ x y)) '2 '3) nil nil)
;; (rewrite-term '((lambda (x y) (binary-+ x y)) (foo '2) '3) nil nil)
;; (rewrite-term '((lambda (x y) (binary-+ x y)) (foo '2) '3) nil *rule-alist2*)

;a condtional rule:
(DEFTHM my-CONS-CAR-CDR
  (implies (consp x)
           (EQUAL (CONS (CAR X) (CDR X))
                  X)))
(check-rewrite '(CONS (CAR X) (CDR X)) '(CONS (CAR X) (CDR X)) :runes '(my-CONS-CAR-CDR)) ;hyp not satisfied
(skip-proofs (defthmd consp-of-foo (equal (consp (foo x)) t)))
(check-rewrite '(cons (car (foo x)) (cdr (foo x))) '(foo x) :runes '(consp-of-foo my-cons-car-cdr)) ;hyp is satisfied

;tests for bvxor (add more):

(check-rewrite '(bvxor '32 '16 x) '(bvxor '32 '16 x))
(check-rewrite '(bvxor '32 x '16) '(bvxor '32 '16 x))
(check-rewrite '(bvxor '32 '15 '27) ''20)

(check-rewrite '(equal (bvxor '8 x y) (bvxor '8 x y)) *t* :runes '(equal-same))
(check-rewrite '(equal (bvxor '8 x y) (bvxor '8 y x)) *t* :runes '(equal-same))
(check-rewrite '(equal (bvxor '8 x (bvxor '8 y z)) (bvxor '8 y (bvxor '8 x z))) *t* :runes '(equal-same))
(check-rewrite '(equal (bvxor '8 x (bvxor '8 y z)) (bvxor '8 (bvxor '8 y z) x)) *t* :runes '(equal-same))
(check-rewrite '(equal (bvxor '8 x x) '0) *t* :runes '(equal-same))
(check-rewrite '(equal (bvxor '8 x (bvxor '8 x y)) (bvchop ;$inline
                                                    '8 y)) *t* :runes '(equal-same))

(check-rewrite '(DAG-VAL-WITH-AXE-EVALUATOR '((0 . x)) (acons 'x x 'nil) 'nil '0) 'x :runes (lookup-rules))
(check-rewrite '(DAG-VAL-WITH-AXE-EVALUATOR '((0 . x)) (acons 'x y 'nil) 'nil '0) 'y :runes (lookup-rules))
(check-rewrite '(DAG-VAL-WITH-AXE-EVALUATOR '((0 . x)) (acons 'x '3 'nil) 'nil '0) ''3 :runes (lookup-rules))
;fffixme do these even make sense, if we don't pass in a definition for foo??
(check-rewrite '(DAG-VAL-WITH-AXE-EVALUATOR '((2 foo 1 0)(1 . y)(0 . x)) (acons 'x x (acons 'y y 'nil)) 'nil '0) '(foo y x)  :runes (lookup-rules))
(check-rewrite '(DAG-VAL-WITH-AXE-EVALUATOR '((2 foo 1 0)(1 . y)(0 . x)) (acons 'x '3 (acons 'y z 'nil)) 'nil '0) '(foo z '3)  :runes (lookup-rules))


;this is a weakening
(defthmd test-of-rewrite-objective
  (implies (and (axe-rewrite-objective 't)
                (not (equal 3 x))
                (integerp x)
                )
           (equal (< 3 x)
                  (< 2 x))))

;this is a strengthening
(defthmd test-of-rewrite-objective2
  (implies (and (axe-rewrite-objective 'nil)
                (not (equal 3 x))
                (integerp x)
                )
           (equal (< 2 x)
                  (< 3 x))))



;tests of polarities:
(check-rewrite 'x 'x :runes '(test-of-rewrite-objective))
(check-rewrite 'x 'x :rewrite-objective 't :runes '(test-of-rewrite-objective))
(check-rewrite 'x 'x :rewrite-objective 'nil :runes '(test-of-rewrite-objective))
(check-rewrite 'x 'x :rewrite-objective '? :runes '(test-of-rewrite-objective))

(check-rewrite '(< '3 x) '(< '3 x) :rewrite-objective '? :assumptions '((not (equal '3 x))(integerp x)) :runes '(test-of-rewrite-objective))
(check-rewrite '(< '3 x) '(< '3 x) :rewrite-objective 'nil :assumptions '((not (equal '3 x))(integerp x)) :runes '(test-of-rewrite-objective))
;here the polarity rule fires, because we want to weaken (< 3 x)
(check-rewrite '(< '3 x) '(< '2 x) :rewrite-objective 't :assumptions '((not (equal '3 x))(integerp x)) :runes '(test-of-rewrite-objective))
(check-rewrite '(not (< '3 x)) '(not (< '3 x)) :rewrite-objective '? :assumptions '((not (equal '3 x))(integerp x)) :runes '(test-of-rewrite-objective))
;here the polarity rule fires, because we want to strengthen (not (< 3 x)) and so we want to weaken (< 3 x):
(check-rewrite '(not (< '3 x)) '(not (< '2 x)) :rewrite-objective 'nil :assumptions '((not (equal '3 x))(integerp x)) :runes '(test-of-rewrite-objective))
;does not fire:
(check-rewrite '(not (< '3 x)) '(not (< '3 x)) :rewrite-objective 't :assumptions '((not (equal '3 x))(integerp x)) :runes '(test-of-rewrite-objective))

;two nots is like no nots:
(check-rewrite '(not (not (< '3 x))) '(not (not (< '2 x))) :rewrite-objective 't :assumptions '((not (equal '3 x))(integerp x)) :runes '(test-of-rewrite-objective))


;; fixme add some tests with assumptions and free variable matching
