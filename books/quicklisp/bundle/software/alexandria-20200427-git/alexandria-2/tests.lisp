(in-package :cl-user)

(defpackage :alexandria2-tests
  (:use :cl :alexandria-2 #+sbcl :sb-rt #-sbcl :rtest)
  (:import-from #+sbcl :sb-rt #-sbcl :rtest
                #:*compile-tests* #:*expected-failures*))

(in-package :alexandria2-tests)

(deftest delete-from-plist*.middle
    (let ((input (list 'a 1 'b 2 'c 3 'd 4 'd 5)))
      (multiple-value-list (delete-from-plist* input 'b 'c)))
  ((a 1 d 4 d 5)
   ((c . 3) (b . 2))))

(deftest delete-from-plist*.start
    (let ((input (list 'a 1 'b 2 'c 3 'd 4 'd 5)))
      (multiple-value-list (delete-from-plist* input 'a 'c)))
  ((b 2 d 4 d 5)
   ((c . 3) (a . 1))))


;; Control Flow tests

(deftest line-up-first.no-form
    (values
     (equal (macroexpand '(line-up-first 5))
            5)
     (equal (macroexpand '(line-up-first (+ 1 2)))
            '(+ 1 2)))
  t
  t)

(deftest line-up-first.function-names-are-threaded
    (values
     (equal (macroexpand '(line-up-first 5 -))
            '(- 5))
     (equal (macroexpand '(line-up-first (+ 1 2) -))
            '(- (+ 1 2))))
  t
  t)

(deftest line-up-first.list-promotion
    (macroexpand '(line-up-first
                   5
                   (+ 20)
                   (/ 25)
                   -
                   (+ 40)))
  (+ (- (/ (+ 5 20) 25)) 40)
  t)

(deftest line-up-first.multiple-args
    (macroexpand '(line-up-first
                   "this-is-a-string"
                   (subseq 0 4)))
  (subseq "this-is-a-string" 0 4)
  t)

(deftest line-up-first.several-examples
    (values
     (equal (line-up-first (+ 40 2)) 42)
     (equal (line-up-first
             5
             (+ 20)
             (/ 25)
             -
             (+ 40)) 39)
     (equal (line-up-first
             "this-is-a-string"
             (subseq 4 5)
             (string-trim  "--------good"))
            "good"))
  t
  t
  t)

;; Thread last tests

(deftest line-up-last.no-forms
    (values
     (equal (macroexpand '(line-up-last 5)) 5)
     (equal (macroexpand '(line-up-last (+ 1 2))) '(+ 1 2)))
  t
  t)

(deftest line-up-last.function-names-are-threaded
    (values (equal (macroexpand
                    '(line-up-last 5
                      -))
                   '(- 5))
            (equal (macroexpand
                    '(line-up-last (+ 1 2)
                      -))
                   '(- (+ 1 2))))
  t
  t)

(deftest line-up-last.lisp-promotion
    (macroexpand '(line-up-last
                   5
                   (+ 20)
                   (/ 25)
                   -
                   (+ 40)))
  (+ 40 (- (/ 25 (+ 20 5))))
  t)

(deftest line-up-last.several-examples
    (values (equal (line-up-last (+ 40 2)) 42)
            (equal (line-up-last
                    5
                    (+ 20)
                    (/ 25)
                    -
                    (+ 40))
                   39)
            (equal (line-up-last
                    (list 1 -2 3 -4 5)
                    (mapcar #'abs)
                    (reduce #'+)
                    (format nil "abs sum is: ~D"))
                   "abs sum is: 15"))
  t
  t
  t)
