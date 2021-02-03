; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file contains various rather ad-hoc tests of the ruler-extenders
; mechanism, mostly written during development of that capability.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

; ==============================

; Example 1a.  Just a basic example.

(must-fail
 (defun fib (n)
   (+ (if (zp n)
          0
        (fib (1- n)))
      (if (zp n)
          0
        (if (equal n 1)
            1
          (fib (- n 2)))))))

(encapsulate
 ()
 (set-ruler-extenders :all)

 (defun fib (n)
   (+ (if (zp n)
          0
        (fib (1- n)))
      (if (zp n)
          0
        (if (equal n 1)
            1
          (fib (- n 2)))))))

(assert-event
 (equal (getprop 'fib 'induction-machine nil 'current-acl2-world (w state))
        '((TESTS-AND-CALLS ((ZP N)))
          (TESTS-AND-CALLS ((NOT (ZP N)) (EQUAL N '1))
                           (FIB (BINARY-+ '-1 N)))
          (TESTS-AND-CALLS ((NOT (ZP N)) (NOT (EQUAL N '1)))
                           (FIB (BINARY-+ '-1 N))
                           (FIB (BINARY-+ '-2 N))))))

; Induction machine computation.
;
; From arg1:
;
; Tests: {(zp n)}
; Calls: {}
;
; Tests: {(not (zp n))}
; Calls: {(fib (1- n))}
;
; From arg2:
;
; Tests: {(zp n)}
; Calls: {}
;
; Tests: {(not (zp n)), (equal n 1)}
; Calls: {}
;
; Tests: {(not (zp n)), (not (equal n 1))}
; Calls: {(fib (- n 2))}
;
; Combine by crossing and eliminating contradictions:
;
; Tests: {(zp n)}
; Calls: {}
;
; Tests: {(not (zp n)), (equal n 1)}
; Calls: {(fib (1- n))}
;
; Tests: {(not (zp n)), (not (equal n 1))}
; Calls: {(fib (1- n)), (fib (- n 2))}

; ==============================

; Example 1b.  Like 1a, but with xargs.

(defun fib1 (n)
  (declare (xargs :ruler-extenders (binary-+)))
  (+ (if (zp n)
         0
       (fib1 (1- n)))
     (if (zp n)
         0
       (if (equal n 1)
           1
         (fib1 (- n 2))))))

(assert-event
 (equal (getprop 'fib1 'induction-machine nil 'current-acl2-world (w state))
        '((TESTS-AND-CALLS ((ZP N)))
          (TESTS-AND-CALLS ((NOT (ZP N)) (EQUAL N '1))
                           (FIB1 (BINARY-+ '-1 N)))
          (TESTS-AND-CALLS ((NOT (ZP N)) (NOT (EQUAL N '1)))
                           (FIB1 (BINARY-+ '-1 N))
                           (FIB1 (BINARY-+ '-2 N))))))

; ==============================

; Example 2.  We check that a small variation of Example 1a (and 1b) gives the
; same induction machine.

(encapsulate
 ()
 (set-ruler-extenders '(binary-+))

 (defun fib2 (n)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       0
     (+ (fib2 (1- n))
        (if (equal n 1)
            1
          (fib2 (- n 2)))))))

(assert-event
 (equal (getprop 'fib2 'induction-machine nil 'current-acl2-world (w state))
        '((TESTS-AND-CALLS ((ZP N)))
          (TESTS-AND-CALLS ((NOT (ZP N)) (EQUAL N '1))
                           (FIB2 (BINARY-+ '-1 N)))
          (TESTS-AND-CALLS ((NOT (ZP N)) (NOT (EQUAL N '1)))
                           (FIB2 (BINARY-+ '-1 N))
                           (FIB2 (BINARY-+ '-2 N))))))

; Induction machine computation for false branch at the top-level.
;
; From arg1 of +, omitting "global" test (not (zp n)):
;
; Tests: {}
; Calls: {(fib2 (1- n))}
;
; From arg2:
;
; Tests: {(equal n 1)}
; Calls: {}
;
; Tests: {(not (equal n 1))}
; Calls: {(fib2 (- n 2))}
;
; Combine by crossing, using top-level test:
;
; Tests: {(zp n)}
; Calls: {}
;
; Tests: {(not (zp n)), (equal n 1)}
; Calls: {(fib2 (1- n))}
;
; Tests: {(not (zp n)), (not (equal n 1))}
; Calls: {(fib2 (1- n)), (fib2 (- n 2))}
;
; ==============================
;
; Example 3.  Let's try an example from Peter Dillinger.

(defun foop (x)
  (declare (xargs :measure (acl2-count x)
                  :ruler-extenders :lambdas))
  (let ((result (if (consp x)
                    (foop (cdr x))
                  (equal x nil))))
    result))

; i.e.:

; (defun foop (x)
;   ((lambda (result) result)
;    (if (consp x)
;        (foop (cdr x))
;      (equal x nil))))

(assert-event
 (equal (getprop 'foop 'induction-machine nil 'current-acl2-world (w state))
        '((TESTS-AND-CALLS ((CONSP X))
                           (FOOP (CDR X)))
          (TESTS-AND-CALLS ((NOT (CONSP X)))))))

; Now (lambda (result) result) generates (in environment with result bound to the
; IF term):
;
; Tests: {}
; Calls: {}
;
; And the IF term generates:
;
; Tests: {(consp x)}
; Calls: {(foop (cdr x))}
;
; Tests: {(not (consp x))}
; Calls: {}
;
; So combining, we get what the IF term generates.
;
; ==============================
;
; Example 4.  The following is adapted from an example discussed in the ACL2
; seminar, and begs for merging the tests-and-calls for two branches when the
; calls are empty for both.

(defstub our-test (x) t)

(defun app (x y)
  (declare (xargs :ruler-extenders :all))
  (let ((result (if (endp x)
                    y
                  (cons (car x)
                        (app (cdr x) y)))))
    (if (our-test result)
        result
      0)))

; i.e.:

; (defun app (x y)
;   ((lambda (result)
;      (if (our-test result)
;          result
;        0))
;    (if (endp x)
;        y
;      (cons (car x)
;            (app (cdr x) y)))))
;
(assert-event
 (equal
  (getprop 'app 'induction-machine nil 'current-acl2-world (w state))
  '((TESTS-AND-CALLS ((ENDP X)))
    (TESTS-AND-CALLS ((NOT (ENDP X)))
                     (APP (CDR X) Y)))))

; The lambda generates (in an alist binding result to the (if (endp x)...)
; term):
;
; Tests: {(our-test result)}
; Calls: {}
;
; Tests: {(not (our-test result))}
; Calls: {}
;
; The argument of the lambda generates:
;
; Tests: {(endp x)}
; Calls: {}
;
; Tests: {(not (endp x))}
; Calls: {(app (cdr x) y)}
;
; If we take the usual cross-product, we'll get four cases:
;
; Tests: {(our-test result), (endp x)}
; Calls: {}
;
; Tests: {(our-test result), (not (endp x))}
; Calls: {(app (cdr x) y)}
;
; Tests: {(not (our-test result)), (endp x)}
; Calls: {}
;
; Tests: {(not (our-test result)), (not (endp x))}
; Calls: {(app (cdr x) y)}
;
; But suppose instead we first merge the two IF branch results in the lambda
; body, since they have the same Calls (empty), giving:
;
; Tests: {}
; Calls: {}
;
; Then the merge is just the result from the argument of the lambda:
;
; Tests: {(endp x)}
; Calls: {}
;
; Tests: {(not (endp x))}
; Calls: {(app (cdr x) y)}
;
; ==============================
;
; Example 5.  Peter Dillinger sent essentially this one.  It illustrates the
; crossing of non-trivial tests-and-calls lists.

(skip-proofs
 (defun foo (x)
   (declare (xargs :ruler-extenders :all))
   (let ((y (if (endp x) nil (foo (cdr x)))))
     (if (true-listp y)
         y
       (foo (cons x y))))))

; i.e.:

; (defun foo (x)
;   ((lambda (y)
;      (if (true-listp y)
;          y
;        (foo (cons x y))))
;    (if (endp x) nil (foo (cdr x)))))

(assert-event
 (equal
  (getprop 'foo 'induction-machine nil 'current-acl2-world (w state))
  '((TESTS-AND-CALLS ((ENDP X)
                      (TRUE-LISTP (IF (ENDP X) 'NIL (FOO (CDR X))))))
    (TESTS-AND-CALLS ((ENDP X)
                      (NOT (TRUE-LISTP (IF (ENDP X) 'NIL (FOO (CDR X))))))
                     (FOO (CONS X (IF (ENDP X) 'NIL (FOO (CDR X))))))
    (TESTS-AND-CALLS ((NOT (ENDP X))
                      (TRUE-LISTP (IF (ENDP X) 'NIL (FOO (CDR X)))))
                     (FOO (CDR X)))
    (TESTS-AND-CALLS ((NOT (ENDP X))
                      (NOT (TRUE-LISTP (IF (ENDP X) 'NIL (FOO (CDR X))))))
                     (FOO (CDR X))
                     (FOO (CONS X (IF (ENDP X) 'NIL (FOO (CDR X)))))))))

; For the lambda body:
;
; Tests: {(true-listp (if (endp x) nil (foo (cdr x))))}
; Calls: {}
;
; Tests: {(not (true-listp (if (endp x) nil (foo (cdr x)))))}
; Calls: {(foo (cons x (if (endp x) nil (foo (cdr x)))))}
;
; For the argument of the lambda:
;
; Tests: {(endp x)}
; Calls: {}
;
; Tests: {(not (endp x))}
; Calls: {(foo (cdr x))}
;
; Now we cross them as usual.  What a mess!  Note that even though foo
; terminates, we cannot prove this, much as we cannot prove termination for
; other reflexive functions.
;
; ==============================
;
; Example 6.  This example gives the same induction machine as we have gotten
; before Version_3.5 (and subsequently as well) without :ruler-extenders
; specified.

(defstub h (x) t)

(defun bar (x)
  (declare (xargs :ruler-extenders :all))
  (if (consp x)
      (if (bar (cdr x))
          (h (bar (cdddr x)))
        17)
    23))

(assert-event
 (equal
  (getprop 'bar 'induction-machine nil 'current-acl2-world (w state))
  '((TESTS-AND-CALLS ((CONSP X) (BAR (CDR X)))
                     (BAR (CDR X))
                     (BAR (CDR (CDR (CDR X)))))
    (TESTS-AND-CALLS ((CONSP X) (NOT (BAR (CDR X))))
                     (BAR (CDR X)))
    (TESTS-AND-CALLS ((NOT (CONSP X)))))))

; The easy one is this:
;
; Tests: {(not (consp x))}
; Calls: {}
;
; But for test (consp x), we recur on the true branch.
;
;   Tests: {(bar (cdr x))}
;   Calls: {(bar (cdr x)), (bar (cdddr x))}
;
;   Tests: {(not (bar (cdr x)))}
;   Calls: {(bar (cdr x))}
;
; Merging back the top-level test:
;
; Tests: {(consp x), (bar (cdr x))}
; Calls: {(bar (cdr x)), (bar (cdddr x))}
;
; Tests: {(consp x), (not (bar (cdr x)))}
; Calls: {(bar (cdr x))}
;
; Tests: {(not (consp x))}
; Calls: {}

; ==============================

; Example 7.  Check that :ruler-extenders specified in a :program mode
; definition are considered by verify-termination (in analogy to the measure).

(defun f (x)
  (declare (xargs :mode :program
                  :ruler-extenders :all))
  (cons 3
        (if (consp x)
            (f (cdr x))
          nil)))

; Fails if we override previous :ruler-extenders.
(must-fail
 (verify-termination f (declare (xargs :ruler-extenders nil))))

(verify-termination f)

(defun f1 (x)
  (if (consp x)
      (cons 3 (f1 (cdr x)))
    (cons 3 nil)))

; Test induction:

(in-theory (disable (:induction f1)))

(defthm f-is-f1
  (equal (f x)
         (f1 x)))

(assert-event
 (equal
  (getprop 'f 'induction-machine nil 'current-acl2-world (w state))
  '((TESTS-AND-CALLS ((CONSP X))
                     (F (CDR X)))
    (TESTS-AND-CALLS ((NOT (CONSP X)))))))

; ==============================

; Example 8.  Using THE.

(must-fail
 (defun fact (n)
   (the (integer 1 *)
        (if (posp n)
            (* n (fact (1- n)))
          1))))

(defun fact (n)
  (declare (xargs :guard (natp n)
                  :ruler-extenders :lambdas))
  (the (integer 1 *)
       (if (posp n)
           (* n (fact (1- n)))
         1)))

(assert-event
 (equal
  (getprop 'fact 'induction-machine nil 'current-acl2-world (w state))
  '((TESTS-AND-CALLS ((POSP N))
                     (FACT (BINARY-+ '-1 N)))
    (TESTS-AND-CALLS ((NOT (POSP N)))))))

; ==============================

; Example 9. Cross tests-and-calls for an IF.  Notice that the tests are
; considered in an intuitive order.  One could argue about whether the ZP test
; should precede what is called top-test below, but it seems reasonable that it
; does, since the zp subexpression can presumably help simplify the top-test
; that comes after it.

(defun f2 (x)
  (declare (xargs :ruler-extenders (if)))
  (if (if (zp x) 3 (+ 4 (f2 (1- x))))
      (if (and (natp x) (< 1 x))
          (+ 6 (f2 (- x 2)))
        5)
    (if (equal x 7) 8 9)))

(assert-event
 (equal
  (getprop 'f2 'induction-machine nil 'current-acl2-world (w state))
  (let ((top-test '(IF (ZP X)
                       '3
                       (BINARY-+ '4 (F2 (BINARY-+ '-1 X)))))
        (sub-test '(IF (NATP X) (< '1 X) 'NIL)))
    `((TESTS-AND-CALLS ((ZP X)
                        ,top-test
                        ,sub-test)
                       (F2 (BINARY-+ '-2 X)))
      (TESTS-AND-CALLS ((ZP X)
                        ,top-test
                        (NOT ,sub-test)))
      (TESTS-AND-CALLS ((ZP X)
                        (NOT ,top-test)))
      (TESTS-AND-CALLS ((NOT (ZP X))
                        ,top-test
                        ,sub-test)
                       (F2 (BINARY-+ '-1 X))
                       (F2 (BINARY-+ '-2 X)))
      (TESTS-AND-CALLS ((NOT (ZP X))
                        ,top-test
                        (NOT ,sub-test))
                       (F2 (BINARY-+ '-1 X)))
      (TESTS-AND-CALLS ((NOT (ZP X))
                        (NOT ,top-test))
                       (F2 (BINARY-+ '-1 X)))))))

; ==============================

; Example 10. Cross tests-and-calls for an IF as in Example 9, but illustrating
; the lack of fancy merge/subsumption heuristics for repeated calls.

(defun f3 (x)
   (declare (xargs :ruler-extenders (if)))
   (if (if (zp x) 3 (+ 4 (f3 (1- x))))
       (if (posp x)
           (+ 6 (f3 (1- x)))
         5)
     (if (equal x 7) 8 9)))

(assert-event
 (equal
  (getprop 'f3 'induction-machine nil 'current-acl2-world (w state))
  (let ((top-test '(IF (ZP X)
                       '3
                       (BINARY-+ '4 (F3 (BINARY-+ '-1 X)))))
        (sub-test '(POSP X)))
    `((TESTS-AND-CALLS ((ZP X)
                        ,top-test
                        ,sub-test)
                       (F3 (BINARY-+ '-1 X)))
      (TESTS-AND-CALLS ((ZP X)
                        ,top-test
                        (NOT ,sub-test)))
      (TESTS-AND-CALLS ((ZP X)
                        (NOT ,top-test)))
      (TESTS-AND-CALLS ((NOT (ZP X))
                        ,top-test
                        ,sub-test)
                       (F3 (BINARY-+ '-1 X)))
      (TESTS-AND-CALLS ((NOT (ZP X))
                        ,top-test
                        (NOT ,sub-test))
                       (F3 (BINARY-+ '-1 X)))
      (TESTS-AND-CALLS ((NOT (ZP X))
                        (NOT ,top-test))
                       (F3 (BINARY-+ '-1 X)))))))

; ==============================

; Example 11.  Test for correct handling of PROG2$ (which, before v3-5, was
; missing a call as indicated below)

(defun f4 (x)
  (if (consp x)
      (if (f4 (cdr x))
          (prog2$ (h (f4 (cdddr x))) (h (f4 (cddr x))))
        17)
    23))

(assert-event
 (equal
  (getprop 'f4 'induction-machine nil 'current-acl2-world (w state))
  '((TESTS-AND-CALLS ((CONSP X) (F4 (CDR X))) ; reversed before v3-5
                     (F4 (CDR X)) ; missing before v3-5
                     (F4 (CDR (CDR (CDR X))))
                     (F4 (CDR (CDR X))))
    (TESTS-AND-CALLS ((CONSP X) (NOT (F4 (CDR X))))
                     (F4 (CDR X)))
    (TESTS-AND-CALLS ((NOT (CONSP X)))))))

; ==============================
