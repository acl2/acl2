; Tests of serialize-lambdas.lisp
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "serialize-lambdas-in-term")
(include-book "std/testing/assert-equal" :dir :system)

;; A simple test.  The lambda binds (non-trivially) both X and Y, so
;; serialize-lambdas-in-term splits it into two separate lambdas.
(assert-equal
 ;; :trans (let ((x (+ 1 x)) (y (+ 2 y))) (< x y))
 (serialize-lambdas-in-term '((lambda (x y) (< x y))
                              (binary-+ '1 x)
                              (binary-+ '2 y))
                            nil)
 ;; :trans (let ((x (+ 1 x))) (let ((y (+ 2 y))) (< x y)))
 '((lambda (x y)
     ((lambda (y x) (< x y))
      (binary-+ '2 y)
      x))
   (binary-+ '1 x)
   y))

;; An example where we have to introduce a temporary:
(assert-equal
 ;; swaps a and b:
 ;; :trans (let ((a b) (b a)) (< a b))
 (serialize-lambda-application '((lambda (a b) (< a b)) b a) nil)
 ;; TODO: Generate something better?
 ;; :trans (let ((a-temp a)) (let ((a b)) (let ((b a-temp)) (< a b))))
 '((lambda (a-temp b)
     ((lambda (a a-temp)
        ((lambda (b a) (< a b)) a-temp a))
      b
      a-temp))
   a
   b))

;; Pathological example where temp name is already a lambda formal.
(assert-equal
 ;; swaps a and b:
 (serialize-lambda-application '((lambda (a b a-temp) (< a b)) b a 'unused) nil)
 ;; Uses the name a-temp1 instead of a-temp, to avoid the name of the existing formal:
 '((lambda (a-temp1 b)
     ((lambda (a a-temp1)
        ((lambda (b a) (< a b)) a-temp1 a))
      b a-temp1))
   a b))

;; More convenient interface for testing
;move?  also of general use?
(include-book "kestrel/utilities/translate" :dir :system)
(defun serialize-lets-in-term (term wrld)
  (declare (xargs :mode :program))
  (untranslate (serialize-lambdas-in-term (translate-term term 'serialize-lets-in-term wrld) nil)
               nil
               wrld))

(assert-equal (serialize-lets-in-term '(let ((a b) (b a)) (< a b)) (w state))
              '(let* ((a-temp a) (a b) (b a-temp))
                 (< a b)))

;; Tricky case where a-temp is a free var used to define b, so a-temp should not be used as the temp name
(assert-equal (serialize-lets-in-term '(let ((a b) (b (cons a a-temp))) (< a b)) (w state))
              '(let* ((a-temp1 a) (a b) (b (cons a-temp1 a-temp)))
                 (< a b)))

;; Old behavior, that shows that using sublis-var can inroduce unserialized lambdas!
;; (assert-equal (serialize-lets-in-term '(let ((a b) (b (let ((b y)) (< a b)))) (< a b)) (w state))
;;               '(let* ((a-temp a)
;;                       (a b)
;;                       (b (let ((b y) (a a-temp)) (< a b)))) ; the let binds 2 vars!
;;                  (< a b)))

(assert-equal (serialize-lets-in-term '(let ((a b) (b (let ((b y)) (< a b)))) (< a b)) (w state))
              '(let* ((a-temp a)
                      (a b)
                      (b (let ((b y)) (< a-temp b))))
                 (< a b)))

;; alternate behavior (todo: compare to the above!):
;; (assert-equal (serialize-lets-in-term '(let ((a b) (b (let ((b y)) (< a b)))) (< a b)) (w state))
;;               '(let* ((a-temp a)
;;                       (a b)
;;                       (b (let ((a a-temp)) (let ((b y)) (< a b)))))
;;                  (< a b)))
