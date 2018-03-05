; Term Utilities -- Tests
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "terms")
(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (lambda-closedp '(lambda (x) (* '2 x))))

(assert! (lambda-closedp '(lambda (x y) (- y x))))

(assert! (not (lambda-closedp '(lambda (x) (cons x a)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (apply-term 'f '('4 y))
              '(f '4 y))

(assert-equal (apply-term '(lambda (x y) (* (1+ x) (1- y))) '(a b))
              '(* (1+ a) (1- b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (apply-term* 'f ''4 'y)
              '(f '4 y))

(assert-equal (apply-term* '(lambda (x y) (* (1+ x) (1- y))) 'a 'b)
              '(* (1+ a) (1- b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (apply-unary-to-terms 'f '(x (g y) '2))
              '((f x) (f (g y)) (f '2)))

(assert-equal (apply-unary-to-terms '(lambda (z) (cons z z))
                                    '(x (g y) '2))
              '((cons x x) (cons (g y) (g y)) '(2 . 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (fapply-term 'f '('4 y))
              '(f '4 y))

(assert-equal (fapply-term '(lambda (x y) (* (1+ x) (1- y))) '(a b))
              '(* (1+ a) (1- b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (fapply-term* 'f ''4 'y)
              '(f '4 y))

(assert-equal (fapply-term* '(lambda (x y) (* (1+ x) (1- y))) 'a 'b)
              '(* (1+ a) (1- b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (fapply-unary-to-terms 'f '(x (g y) '2))
              '((f x) (f (g y)) (f '2)))

(assert-equal (fapply-unary-to-terms '(lambda (z) (cons z z))
                                     '(x (g y) '2))
              '((cons x x) (cons (g y) (g y)) (cons '2 '2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (fsublis-var '((x . '1) (y . '2)) '(quote "a"))
              '(quote "a"))

(assert-equal (fsublis-var '((x . '1) (y . '2)) 'z)
              'z)

(assert-equal (fsublis-var '((x . '1) (y . '2)) 'x)
              '(quote 1))

(assert-equal (fsublis-var '((x . '1) (y . '2)) '((lambda (x) x) y))
              '((lambda (x) x) '2))

(assert-equal (fsublis-var '((x . '1) (y . '2)) '(f x (g z)))
              '(f '1 (g z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(quote #\c)
                          nil
                          t))
              '(nil (quote #\c)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(quote #\c)
                          nil
                          nil))
              '(nil (quote #\c)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          'y
                          nil
                          t))
              '(nil y))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          'y
                          nil
                          nil))
              '(nil y))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(f (r x) y)
                          nil
                          t))
              '(nil (g (r x) y)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(f (r x) y)
                          nil
                          nil))
              '(nil (g (r x) y)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(h a)
                          nil
                          t))
              '(nil (cons a y)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(h a)
                          nil
                          nil))
              '((y) (h a)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '((lambda (z w) (h (cons z w))) (f a) (j c))
                          nil
                          t))
              '(nil ((lambda (z w y) (cons (cons z w) y)) (g a) (j c) y)))

(assert-equal (mv-list 2 (fsublis-fn-rec
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '((lambda (z w) (h (cons z w))) (f a) (j c))
                          nil
                          nil))
              '((y) (h (cons z w))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 2 (fsublis-fn
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(quote #\c)
                          nil))
              '(nil (quote #\c)))

(assert-equal (mv-list 2 (fsublis-fn
                          '((f . g) (h . (lambda (x) (cons x y))))
                          'y
                          nil))
              '(nil y))

(assert-equal (mv-list 2 (fsublis-fn
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(f (r x) y)
                          nil))
              '(nil (g (r x) y)))

(assert-equal (mv-list 2 (fsublis-fn
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '(h a)
                          nil))
              '(nil (cons a y)))

(assert-equal (mv-list 2 (fsublis-fn
                          '((f . g) (h . (lambda (x) (cons x y))))
                          '((lambda (z w) (h (cons z w))) (f a) (j c))
                          nil))
              '(nil ((lambda (z w y) (cons (cons z w) y)) (g a) (j c) y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (fsublis-fn-simple '((f . g) (h . i)) '(quote '(1 2 3)))
              '(quote '(1 2 3)))

(assert-equal (fsublis-fn-simple '((f . g) (h . i)) 'xyz)
              'xyz)

(assert-equal (fsublis-fn-simple '((f . g) (h . i))
                                 '(f (cons (g (h a) b) c) d))
              '(g (cons (g (i a) b) c) d))

(assert-equal (fsublis-fn-simple '((f . g) (h . i))
                                 '(f ((lambda (x) (cons x (h 'a))) (g b))))
              '(g ((lambda (x) (cons x (i 'a))) (g b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (all-program-ffn-symbs 'x nil (w state)) nil)

(assert-equal (all-program-ffn-symbs '(quote 4) nil (w state)) nil)

(assert-equal (all-program-ffn-symbs '(cons x y) nil (w state)) nil)

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (defun g (x) (declare (xargs :mode :logic)) x)
 (assert!
  (set-equiv (all-program-ffn-symbs '(cons (f x) (g (f y))) nil (w state))
             '(f))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (lambda-logic-fnsp '(lambda (x y) (len (cons x x))) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :mode :program)) x)
 (assert! (not (lambda-logic-fnsp '(lambda (z) (cons (f x) '3)) (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (guard-verified-fnsp '(cons (len a) '3) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (assert! (not (guard-verified-fnsp '(zp (f '4)) (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (lambda-guard-verified-fnsp '(lambda (a) (cons (len a) '3)) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (assert!
  (not (lambda-guard-verified-fnsp '(lambda (x) (zp (f '4))) (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (all-non-gv-ffn-symbs 'x nil (w state)) nil)

(assert-equal (all-non-gv-ffn-symbs '(quote 4) nil (w state)) nil)

(assert-equal (all-non-gv-ffn-symbs '(cons (len a) '3) nil (w state)) nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (assert-equal (all-non-gv-ffn-symbs '(zp (f '4)) nil (w state)) '(f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (guard-verified-exec-fnsp 'x (w state)))

(assert! (guard-verified-exec-fnsp '(quote 4) (w state)))

(assert! (guard-verified-exec-fnsp '(cons x y) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards t)) x)
 (assert! (not (guard-verified-exec-fnsp '(cons (f x) (g (f y))) (w state)))))

(must-succeed*
 (defun mycar (x) (declare (xargs :verify-guards nil)) (car x))
 (assert! (not (guard-verified-exec-fnsp '(cons (mycar z) (len y)) (w state))))
 (defun f (x) (mbe :logic (mycar x) :exec (if (consp x) (car x) nil)))
 (assert! (guard-verified-exec-fnsp (ubody 'f (w state)) (w state))))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards t)) (cons (ec-call (f x)) (len x)))
 (assert! (guard-verified-exec-fnsp (ubody 'g (w state)) (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (lambda-guard-verified-exec-fnsp '(lambda (x) x) (w state)))

(assert! (lambda-guard-verified-exec-fnsp '(lambda (tt) '4) (w state)))

(assert! (lambda-guard-verified-exec-fnsp '(lambda (x y) (cons x y)) (w state)))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards t)) x)
 (assert! (not (lambda-guard-verified-exec-fnsp
                '(lambda (x y) (cons (f x) (g (f y)))) (w state)))))

(must-succeed*
 (defun mycar (x) (declare (xargs :verify-guards nil)) (car x))
 (assert! (not (lambda-guard-verified-exec-fnsp
                '(lambda (x y z) (cons (mycar z) (len y))) (w state))))
 (defun f (x) (mbe :logic (mycar x) :exec (if (consp x) (car x) nil)))
 (assert! (lambda-guard-verified-exec-fnsp
           (make-lambda '(x) (ubody 'f (w state))) (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (all-non-gv-exec-ffn-symbs 'x (w state)) nil)

(assert-equal (all-non-gv-exec-ffn-symbs '(quote 4) (w state)) nil)

(assert-equal (all-non-gv-exec-ffn-symbs '(cons x y) (w state)) nil)

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards t)) x)
 (assert!
  (set-equiv (all-non-gv-exec-ffn-symbs '(cons (f x) (g (f y))) (w state))
             '(f))))

(must-succeed*
 (defun mycar (x) (declare (xargs :verify-guards nil)) (car x))
 (assert!
  (set-equiv (all-non-gv-exec-ffn-symbs '(cons (mycar z) (len y)) (w state))
             '(mycar)))
 (defun f (x) (mbe :logic (mycar x) :exec (if (consp x) (car x) nil)))
 (assert-equal (all-non-gv-exec-ffn-symbs (ubody 'f (w state)) (w state))
               nil))

(must-succeed*
 (defun f (x) (declare (xargs :verify-guards nil)) x)
 (defun g (x) (declare (xargs :verify-guards t)) (cons (ec-call (f x)) (len x)))
 (assert-equal (all-non-gv-exec-ffn-symbs (ubody 'g (w state)) (w state))
               nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (mv-list 2 (check-user-term 3 (w state)))
              '('3 (nil)))

(assert-equal (mv-list 2 (check-user-term 'x (w state)))
              '(x (nil)))

(assert-equal (mv-list 2 (check-user-term '(len x) (w state)))
              '((len x) (nil)))

(assert-equal (mv-list 2 (check-user-term '(mv x y z) (w state)))
              '((cons x (cons y (cons z 'nil))) (nil nil nil)))

(assert-equal (mv-list 2 (check-user-term 'state (w state)))
              '(state (state)))

(assert-equal (mv-list 2 (check-user-term '(mv state 1) (w state)))
              '((cons state (cons '1 'nil)) (state nil)))

(must-succeed*
 (defstobj s)
 (assert-equal (mv-list 2 (check-user-term '(mv s 0 state) (w state)))
               '((cons s (cons '0 (cons state 'nil))) (s nil state))))

(assert-equal (mv-list 2 (check-user-term '(+ x y) (w state)))
              '((binary-+ x y) (nil)))

(assert-equal (mv-list 2 (check-user-term '(+ (len x) 55) (w state)))
              '((binary-+ (len x) '55) (nil)))

(assert-equal
 (mv-list 2 (check-user-term '(let ((x 4)) (+ x (len y))) (w state)))
 '(((lambda (x y) (binary-+ x (len y))) '4 y) (nil)))

(assert! (msgp (nth 0 (mv-list 2 (check-user-term '(f x) (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  "(lambda (x) x)" (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda (x) x . more) (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda (x) x y) (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda (x)) (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambdaa (x) x) (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda "x" x) (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda (x x) x) (w state))))))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda (x "y") x) (w state))))))

(assert-equal (mv-list 2 (check-user-lambda '(lambda (x) 3) (w state)))
              '((lambda (x) '3) (nil)))

(assert-equal (mv-list 2 (check-user-lambda '(lambda (x) x) (w state)))
              '((lambda (x) x) (nil)))

(assert-equal (mv-list 2 (check-user-lambda '(lambda (y) (len x)) (w state)))
              '((lambda (y) (len x)) (nil)))

(assert-equal
 (mv-list 2 (check-user-lambda '(lambda (x y) (mv x y z)) (w state)))
 '((lambda (x y) (cons x (cons y (cons z 'nil)))) (nil nil nil)))

(assert-equal (mv-list 2 (check-user-lambda '(lambda (state) state) (w state)))
              '((lambda (state) state) (state)))

(assert-equal
 (mv-list 2 (check-user-lambda '(lambda (state) (mv state 1)) (w state)))
 '((lambda (state) (cons state (cons '1 'nil))) (state nil)))

(must-succeed*
 (defstobj s)
 (assert-equal (mv-list 2 (check-user-lambda
                           '(lambda (state s) (mv s 0 state)) (w state)))
               '((lambda (state s) (cons s (cons '0 (cons state 'nil))))
                 (s nil state))))

(assert-equal (mv-list 2 (check-user-lambda '(lambda (x y) (+ x y)) (w state)))
              '((lambda (x y) (binary-+ x y)) (nil)))

(assert-equal
 (mv-list 2 (check-user-lambda '(lambda (z) (+ (len x) 55)) (w state)))
 '((lambda (z) (binary-+ (len x) '55)) (nil)))

(assert-equal (mv-list 2 (check-user-lambda
                          '(lambda (u) (let ((x 4)) (+ x (len y)))) (w state)))
              '((lambda (u) ((lambda (x y) (binary-+ x (len y))) '4 y))
                (nil)))

(assert! (msgp (nth 0 (mv-list 2 (check-user-lambda
                                  '(lambda (x) (f x)) (w state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (term-guard-obligation 'x state)
              ''t)

(assert-equal (term-guard-obligation '(binary-+ x '4) state)
              '(acl2-numberp x))
