; Copyright (C) 2014, ForrestHunt, Inc.
; Written by J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (certify-book "if-tracker")

; IF-TRACKER Normalization
; J Strother Moore
; June 2013

; We introduce IF-TRACKER as a constrained function with the property:

;  (equal (if-tracker rtests (if a b c))
;         (if a
;             (if-tracker (cons a rtests) b)          ; (HIDE a)!
;             (if-tracker (cons (not a) rtests) c)))  ; (HIDE (not a))!

; Of course, if this were a rewrite rule, the a and the (not a) in the first
; arguments of the IF-TRACKER terms would be immediately rewritten to T and NIL
; (assuming a is Boolean) because of the governing test on a.  Thus, in actual
; applications, we HIDE those two terms.

; However, in the course of simplifying IF-TRACKER terms we sometimes produce
; terms like:

; (IF-TRACKER rtests (foo (bar (IF a b c))))

; where the IF is buried and thus the rule above is not applied.

; We wish to lift the IFs out of the second argument of IF-TRACKER and then
; apply the IF-TRACKER property (with the indicated terms hidden).  We do this
; with a metafunction.  The metafunction is not very efficient, but is easily
; proved correct.



(in-package "ACL2")

(encapsulate ((if-tracker (rtests term) t))
             (local (defun if-tracker (rtests term)
                      (declare (ignore rtests term))
                      t))
             (defthm if-tracker-ignores-rtests
               (implies (syntaxp (not (quotep rtests)))
                        (equal (if-tracker rtests term)
                               (if-tracker  nil term)))))

(defun find-first-test (flg x)
  (if flg
      (cond
       ((variablep x) nil)
       ((fquotep x) nil)
       ((eq (ffn-symb x) 'IF)
        (let ((temp (find-first-test t (fargn x 1))))
          (cond ((null temp) (fargn x 1))
                (t temp))))
       (t (find-first-test nil (fargs x))))
      (cond ((endp x) nil)
            (t (or (find-first-test t (car x))
                   (find-first-test nil (cdr x)))))))

(defun reduce-if-with-test (flg test val x)
  (if flg
      (cond ((variablep x) x)
            ((fquotep x) x)
            ((and (eq (ffn-symb x) 'IF)
                  (equal (fargn x 1) test))
             (if val
                 (reduce-if-with-test t test val (fargn x 2))
                 (reduce-if-with-test t test val (fargn x 3))))
            (t (cons (ffn-symb x)
                     (reduce-if-with-test nil test val (cdr x)))))
      (cond ((endp x) nil)
            (t (cons (reduce-if-with-test t test val (car x))
                     (reduce-if-with-test nil test val (cdr x)))))))

(defun lift-first-test-through-if-tracker (term)
  (cond
   ((and (not (variablep term))
         (not (fquotep term))
         (eq (ffn-symb term) 'IF-TRACKER))
    (let ((a (find-first-test t (fargn term 2)))
          (rtests-term (fargn term 1)))
      (cond
       (a (list 'IF
                a
                (list 'IF-TRACKER
                      (list 'CONS (list 'HIDE a) rtests-term)
                      (reduce-if-with-test t a t (fargn term 2)))
                (list 'IF-TRACKER
                      (list 'cons
                            (list 'HIDE (list 'NOT a))
                            rtests-term)
                      (reduce-if-with-test t a nil (fargn term 2)))))
       (t term))))
   (t term)))

(defevaluator if-tracker-evl if-tracker-evl-lst
  ((CONS x y)
   (HIDE x)
   (NOT p)
   (IF-TRACKER rtests term)
   (IF a b c)))

(defthm reduce-if-with-test-correct
  (and (implies (and flg
                     (pseudo-termp x)
                     (iff (if-tracker-evl test a) val))
                (equal (if-tracker-evl (reduce-if-with-test flg test val x)
                            a)
                       (if-tracker-evl x a)))
       (implies (and (not flg)
                     (pseudo-term-listp x)
                     (iff (if-tracker-evl test a) val))
                (equal (if-tracker-evl-lst (reduce-if-with-test flg test val x)
                                a)
                       (if-tracker-evl-lst x a))))
  :hints (("Goal"
           :in-theory (enable IF-TRACKER-EVL-CONSTRAINT-0)
           :induct (reduce-if-with-test flg test val x))))

(defthm lift-first-test-through-if-tracker-correct
  (implies (pseudo-termp x)
           (equal (if-tracker-evl x a)
                  (if-tracker-evl (lift-first-test-through-if-tracker x) a)))
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes ((:meta :trigger-fns (if-tracker))))

(in-theory (disable if-tracker-ignores-rtests))

#||

(defun steppe (x)

; Pretend this is the step function on an IFEQ, where the pc is (car x) and the
; stack is (cdr x).

  (cons (if (equal (car (cdr x)) 0) (+ 1 (car x)) (+ 2 (car x)))
        (if (evenp (car (cdr x)))
            (cddr x)
            (cdddr x))))

(thm (implies (and (integerp (car x))
                   (integerp (car (cdr x))))
              (if-tracker nil (car (steppe x))))
     :otf-flg t)
||#




