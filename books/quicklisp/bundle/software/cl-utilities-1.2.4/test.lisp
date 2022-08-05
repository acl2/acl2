;; This file requires the FiveAM unit testing framework.
(eval-when (:compile-toplevel :load-toplevel :execute)
  (asdf:oos 'asdf:load-op :fiveam)
  (asdf:oos 'asdf:load-op :cl-utilities))

;; To run all the tests:
;; (5am:run! 'cl-utilities-tests::cl-utilities-suite)

(defpackage :cl-utilities-tests
  (:use :common-lisp :cl-utilities :5am))

(in-package :cl-utilities-tests)

(def-suite cl-utilities-suite :description "Test suite for cl-utilities")
(in-suite cl-utilities-suite)

;; These tests were taken directly from the comments at the top of
;; split-sequence.lisp
(test split-sequence
  (is (tree-equal (values (split-sequence #\; "a;;b;c"))
		  '("a" "" "b" "c") :test #'equal))
  (is (tree-equal (values (split-sequence #\; "a;;b;c" :from-end t))
		  '("a" "" "b" "c") :test #'equal))
  (is (tree-equal (values (split-sequence #\; "a;;b;c" :from-end t :count 1))
		  '("c") :test #'equal))
  (is (tree-equal (values (split-sequence #\; "a;;b;c" :remove-empty-subseqs t))
		  '("a" "b" "c") :test #'equal))
  (is (tree-equal (values (split-sequence-if (lambda (x)
					       (member x '(#\a #\b)))
					     "abracadabra"))
		  '("" "" "r" "c" "d" "" "r" "") :test #'equal))
  (is (tree-equal (values (split-sequence-if-not (lambda (x)
						   (member x '(#\a #\b)))
						 "abracadabra"))
		  '("ab" "a" "a" "ab" "a") :test #'equal))
  (is (tree-equal (values (split-sequence #\; ";oo;bar;ba;" :start 1 :end 9))
		  '("oo" "bar" "b") :test #'equal)))

(test extremum
  (is (= (extremum '(1 23 3 4 5 0) #'< :start 1 :end 4) 3))
  (signals no-extremum (extremum '() #'<))
  (is-false (handler-bind ((no-extremum #'continue))
	      (extremum '() #'<)))
  (is (= (extremum '(2/3 2 3 4) #'> :key (lambda (x) (/ 1 x))) 2/3))
  (is (= (locally (declare (optimize (speed 3) (safety 0)))
	   (extremum #(1 23 3 4 5 0) #'>))
	 23))
  (is (= (extremum-fastkey '(2/3 2 3 4) #'> :key (lambda (x) (/ 1 x))) 2/3)))

(test extrema
  (is (tree-equal (extrema '(3 2 1 1 2 1) #'<)
		  '(1 1 1)))
  (is (tree-equal (extrema #(3 2 1 1 2 1) #'<)
		  '(1 1 1)))
  (is (tree-equal (extrema #(3 2 1 1 2 1) #'< :end 4)
		  '(1 1)))
  (is (tree-equal (extrema '(3 2 1 1 2 1) #'< :end 4)
		  '(1 1)))
  (is (tree-equal (extrema #(3 2 1 1 2 1) #'< :start 3 :end 4)
		  '(1)))
  (is (tree-equal (extrema '((A . 3) (B . 1) (C . 2) (D . 1)) #'< :key #'cdr)
		  '((B . 1) (D . 1)))))

(defmacro quietly (&body body)
  "Perform BODY quietly, muffling any warnings that may arise"
  `(handler-bind ((warning #'muffle-warning))
    ,@body))

(test n-most-extreme
  (is (tree-equal (n-most-extreme 1 '(3 1 2 1) #'>)
		  '(3)))
  (is (tree-equal (n-most-extreme 2 '(3 1 2 1) #'>)
		  '(3 2)))
  (is (tree-equal (n-most-extreme 2 '(3 1 2 1) #'<)
		  '(1 1)))
  (is (tree-equal (n-most-extreme 1 '((A . 3) (B . 1) (C . 2) (D . 1)) #'> :key #'cdr)
		  '((A . 3))))
  (is (tree-equal (n-most-extreme 2 '((A . 3) (B . 1) (C . 2) (D . 1)) #'< :key #'cdr)
		  '((B . 1) (D . 1))))
  (is (tree-equal (quietly (n-most-extreme 20 '((A . 3) (B . 1) (C . 2) (D . 1)) #'< :key #'cdr))
		  '((B . 1) (D . 1) (C . 2) (A . 3))))
  (is (tree-equal (quietly (n-most-extreme 2 '((A . 3) (B . 1) (C . 2) (D . 1)) #'< :key #'cdr :start 1 :end 2))
		  '((B . 1))))
  (signals n-most-extreme-not-enough-elements (n-most-extreme 2 '((A . 3) (B . 1) (C . 2) (D . 1)) #'< :key #'cdr :start 1 :end 2)))

(defun delimited-test (&key (delimiter #\|) (start 0) end
		       (string "foogo|ogreogrjejgierjijri|bar|baz"))
  (with-input-from-string (str string)
    (let ((buffer (copy-seq "            ")))
      (multiple-value-bind (position delimited-p)
	  (read-delimited buffer str
			  :delimiter delimiter :start start :end end)
	(declare (ignore delimited-p))
	(subseq buffer 0 position)))))

(test read-delimited
  (is (string= (delimited-test) "foogo"))
  (is (string= (delimited-test :delimiter #\t) "foogo|ogreog"))
  (is (string= (delimited-test :delimiter #\t :start 3) "   foogo|ogr"))
  (is (string= (delimited-test :start 3) "   foogo"))
  (is (string= (delimited-test :end 3) "foo"))
  (is (string= (delimited-test :start 1 :end 3) " fo"))
  (is (string= (delimited-test :string "Hello") "Hello"))
  (is (string= (delimited-test :string "Hello" :start 3) "   Hello"))
  (is (string= (handler-bind ((read-delimited-bounds-error #'continue))
		 (delimited-test :start 3 :end 1))
	       " fo"))
  (signals type-error (delimited-test :start 3/2))
  (signals read-delimited-bounds-error (delimited-test :start -3))
  (signals read-delimited-bounds-error (delimited-test :end 30))
  (signals read-delimited-bounds-error (delimited-test :start 3 :end 1)))

;; Random testing would probably work better here.
(test expt-mod
  (is (= (expt-mod 2 34 54) (mod (expt 2 34) 54)))
  (is (= (expt-mod 20 3 54) (mod (expt 20 3) 54)))
  (is (= (expt-mod 2.5 3.8 34.9) (mod (expt 2.5 3.8) 34.9)))
  (is (= (expt-mod 2/5 3/8 34/9) (mod (expt 2/5 3/8) 34/9))))

(test collecting
  (is (tree-equal (collecting (dotimes (x 10) (collect x)))
		  '(0 1 2 3 4 5 6 7 8 9)))
  (is (tree-equal (collecting
		   (labels ((collect-it (x) (collect x)))
		     (mapcar #'collect-it (reverse '(c b a)))))
		  '(a b c)))
  (is (tree-equal (multiple-value-bind (a b)
		      (with-collectors (x y)
			(x 1)
			(y 2)
			(x 3))
		    (append a b))
		  '(1 3 2))))

(test with-unique-names
  (is (equalp (subseq (with-unique-names (foo)
			(string foo))
		      0 3)
	      "foo"))
  (is (equalp (subseq (with-unique-names ((foo "bar"))
			(string foo))
		      0 3)
	      "bar"))
  (is (equalp (subseq (with-unique-names ((foo baz))
			(string foo))
		      0 3)
	      "baz"))
  (is (equalp (subseq (with-unique-names ((foo #\y))
			(string foo))
		      0 1)
	      "y"))
  (is (equalp (subseq (with-gensyms (foo)
			(string foo))
		      0 3)
	      "foo")))

;; Taken from spec
(test rotate-byte
  (is (= (rotate-byte 3 (byte 32 0) 3) 24))
  (is (= (rotate-byte 3 (byte 5 5) 3) 3))
  (is (= (rotate-byte 6 (byte 8 0) -3) -129)))

(test copy-array
  (let ((test-array (make-array '(10 10) :initial-element 5)))
    (is (not (eq (copy-array test-array) test-array)))
    (is (equalp (copy-array test-array) test-array))))

(test compose
  (labels ((2* (x) (* 2 x)))
    (is (= (funcall (compose #'1+ #'1+) 1) 3))
    (is (= (funcall (compose '1+ #'2*) 5) 11))
    (is (= (funcall (compose #'1+ #'2* '1+) 6) 15))
    ;; This should signal an undefined function error, since we're
    ;; using '2* rather than #'2*, which means that COMPOSE will use
    ;; the dynamic binding at the time it is called rather than the
    ;; lexical binding here.
    (signals undefined-function
	     (= (funcall (compose #'1+ '2* '1+) 6) 15))))