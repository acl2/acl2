(in-package :cl-user)

(defpackage :alexandria-2/tests
  (:use :cl :alexandria-2 #+sbcl :sb-rt #-sbcl :rtest)
  (:import-from #+sbcl :sb-rt #-sbcl :rtest
                #:*compile-tests* #:*expected-failures*))

(in-package :alexandria-2/tests)

;; Arrays Tests
(deftest dim-in-bounds-p.0
    (dim-in-bounds-p '(2 2) 0 1 1)
  nil)

(deftest dim-in-bounds-p.1
    (dim-in-bounds-p '(2 2) 0 1)
  t)

(deftest dim-in-bounds-p.2
    (dim-in-bounds-p '(2 2) 0 2)
  nil)

(deftest row-major-index.0
    (let* ((dims '(4 3 2 1))
           (test-arr (make-array dims))
           (idcs '(0 0 0 0)))
      (= 0 (apply #'row-major-index dims idcs) (apply #'array-row-major-index test-arr idcs)))
  t)

(deftest row-major-index.1
    (let* ((dims '(4 3 2 1))
           (test-arr (make-array dims))
           (idcs '(3 2 1 0)))
      (= 23 (apply #'row-major-index dims idcs) (apply #'array-row-major-index test-arr idcs)))
  t)

(deftest row-major-index.2
    (let* ((dims '(4 3 2 1))
           (test-arr (make-array dims))
           (idcs '(2 1 0 0)))
      (= 14 (apply #'row-major-index dims idcs) (apply #'array-row-major-index test-arr idcs)))
  t)

(deftest row-major-index.3
    (let* ((dims '(4 3 2 1))
           (test-arr (make-array dims))
           (idcs '(0 2 1 0)))
      (= 5 (apply #'row-major-index dims idcs) (apply #'array-row-major-index test-arr idcs)))
  t)

(deftest rmajor-to-indices.0
    (loop for dims in '((70 30 4 2) (50 200 5 7) (5 4 300 2) (5 2 30 19))
          with index = 173
          with indices = '(4 0 3 1)
          always (and (= index (apply #'row-major-index dims (rmajor-to-indices dims index)))
                      (equalp indices (rmajor-to-indices dims
                                                         (apply #'row-major-index dims indices)))))
  t)

;; List Tests

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


(deftest subseq*.1
    (values (subseq* "abcdef" 0 3)
            (subseq* "abcdef" 1 3)
            (subseq* "abcdef" 1)
            (subseq* "abcdef" 1 9))
  "abc"
  "bc"
  "bcdef"
  "bcdef")
