;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-

(defpackage :split-sequence/tests
  (:use :common-lisp :split-sequence :fiveam))

(in-package :split-sequence/tests)

(in-suite* :split-sequence)

;;; UNIT TESTS

(defmacro define-test (name (&key input output index) &body forms)
  ;; This macro automatically generates test code for testing vector and list input.
  ;; Vector input and output is automatically coerced into list form for the list tests.
  ;; (DEFINE-TEST FOO ...) generates FIVEAM tests FOO.VECTOR and FOO.LIST.
  (check-type name symbol)
  (check-type input (cons symbol (cons vector null)))
  (check-type output (cons symbol (cons list null)))
  (check-type index (cons symbol (cons unsigned-byte null)))
  (let* ((input-symbol (first input)) (vector-input (second input))
         (output-symbol (first output)) (vector-output (second output))
         (index-symbol (first index)) (index-value (second index))
         (list-input (coerce vector-input 'list))
         (list-output (mapcar (lambda (x) (coerce x 'list)) vector-output))
         (vector-name (intern (concatenate 'string (symbol-name name) ".VECTOR")))
         (list-name (intern (concatenate 'string (symbol-name name) ".LIST"))))
    `(progn
       (test (,vector-name :compile-at :definition-time)
         (let ((,input-symbol ',vector-input)
               (,output-symbol ',vector-output)
               (,index-symbol ,index-value))
           ,@forms))
       (test (,list-name :compile-at :definition-time)
         (let ((,input-symbol ',list-input)
               (,output-symbol ',list-output)
               (,index-symbol ,index-value))
           ,@forms)))))

(define-test split-sequence.0 (:input (input "")
                               :output (output (""))
                               :index (index 0))
  (is (equalp (split-sequence #\; input)
              (values output index))))

(define-test split-sequence.1 (:input (input "a;;b;c")
                               :output (output ("a" "" "b" "c"))
                               :index (index 6))
  (is (equalp (split-sequence #\; input)
              (values output index))))

(define-test split-sequence.2 (:input (input "a;;b;c")
                               :output (output ("a" "" "b" "c"))
                               :index (index 0))
  (is (equalp (split-sequence #\; input :from-end t)
              (values output index))))

(define-test split-sequence.3 (:input (input "a;;b;c")
                               :output (output ("c"))
                               :index (index 4))
  (is (equalp (split-sequence #\; input :from-end t :count 1)
              (values output index))))

(define-test split-sequence.4 (:input (input "a;;b;c")
                               :output (output ("a" "b" "c"))
                               :index (index 6))
  (is (equalp (split-sequence #\; input :remove-empty-subseqs t)
              (values output index))))

(define-test split-sequence.5 (:input (input ";oo;bar;ba;")
                               :output (output ("oo" "bar" "b"))
                               :index (index 9))
  (is (equalp (split-sequence #\; input :start 1 :end 9)
              (values output index))))

(define-test split-sequence.6 (:input (input "abracadabra")
                               :output (output ("" "br" "c" "d" "br" ""))
                               :index (index 11))
  (is (equalp (split-sequence #\A input :key #'char-upcase)
              (values output index))))

(define-test split-sequence.7 (:input (input "abracadabra")
                               :output (output ("r" "c" "d"))
                               :index (index 7))
  (is (equalp (split-sequence #\A input :key #'char-upcase :start 2 :end 7)
              (values output index))))

(define-test split-sequence.8 (:input (input "abracadabra")
                               :output (output ("r" "c" "d"))
                               :index (index 2))
  (is (equalp (split-sequence #\A input :key #'char-upcase :start 2 :end 7 :from-end t)
              (values output index))))

(define-test split-sequence.9 (:input (input #(1 2 0))
                               :output (output (#(1 2) #()))
                               :index (index 0))
  (is (equalp (split-sequence 0 input :from-end t)
              (values output index))))

(define-test split-sequence.10 (:input (input #(2 0 0 2 3 2 0 1 0 3))
                                :output (output ())
                                :index (index 8))
  (is (equalp (split-sequence 0 input :start 8 :end 9 :from-end t :count 0 :remove-empty-subseqs t)
              (values output index))))

(define-test split-sequence.11 (:input (input #(0 1 3 0 3 1 2 2 1 0))
                                :output (output ())
                                :index (index 0))
  (is (equalp (split-sequence 0 input :start 0 :end 0 :remove-empty-subseqs t)
              (values output index))))

(define-test split-sequence.12 (:input (input #(3 0 0 0 3 3 0 3 1 0))
                                :output (output ())
                                :index (index 10))
  (is (equalp (split-sequence 0 input :start 9 :end 10 :from-end t :count 0)
              (values output index))))

(define-test split-sequence.13 (:input (input #(3 3 3 3 0 2 0 0 1 2))
                                :output (output (#(1)))
                                :index (index 6))
  (is (equalp (split-sequence 0 input :start 6 :end 9 :from-end t :count 1 :remove-empty-subseqs t)
              (values output index))))

(define-test split-sequence.14 (:input (input #(1 0))
                                :output (output (#(1)))
                                :index (index 0))
  (is (equalp (split-sequence 0 input :from-end t :count 1 :remove-empty-subseqs t)
              (values output index))))

(define-test split-sequence.15 (:input (input #(0 0))
                                :output (output ())
                                :index (index 1))
  (is (equalp (split-sequence 0 input :start 0 :end 1 :count 0 :remove-empty-subseqs t)
              (values output index))))

(define-test split-sequence.16 (:input (input "a;;b;c")
                                :output (output ("" ";;" ";" ""))
                                :index (index 6))
  (is (equalp (split-sequence #\; input :test-not #'eql)
              (values output index))))

(define-test split-sequence.17 (:input (input "a;;b;c")
                                :output (output ("" ";;" ";" ""))
                                :index (index 0))
  (is (equalp (split-sequence #\; input :from-end t :test-not #'eql)
              (values output index))))

(define-test split-sequence.18 (:input (input #(1 0 2 0 3 0 4))
                                :output (output (#(1) #(2) #(3)))
                                :index (index 6))
  (is (equalp (split-sequence 0 input :count 3)
              (values output index))))

(define-test split-sequence-if.1 (:input (input "abracadabra")
                                  :output (output ("" "" "r" "c" "d" "" "r" ""))
                                  :index (index 11))
  (is (equalp (split-sequence-if (lambda (x) (member x '(#\a #\b))) input)
              (values output index))))

(define-test split-sequence-if.2 (:input (input "123456")
                                  :output (output ("1" "3" "5"))
                                  :index (index 6))
  (is (equalp (split-sequence-if (lambda (x) (evenp (parse-integer (string x)))) input
                                 :remove-empty-subseqs t)
              (values output index))))

(define-test split-sequence-if.3 (:input (input "123456")
                                  :output (output ("1" "3" "5" ""))
                                  :index (index 6))
  (is (equalp (split-sequence-if (lambda (x) (evenp (parse-integer (string x)))) input)
              (values output index))))

(define-test split-sequence-if-not.1 (:input (input "abracadabra")
                                      :output (output ("ab" "a" "a" "ab" "a"))
                                      :index (index 11))
  (is (equalp (split-sequence-if-not (lambda (x) (member x '(#\a #\b))) input)
              (values output index))))

(test split-sequence.start-end-error
  (signals error (split-sequence 0 #(0 1 2 3) :start nil))
  (signals error (split-sequence 0 #(0 1 2 3) :end '#:end))
  (signals error (split-sequence 0 #(0 1 2 3) :start 0 :end 8))
  (signals error (split-sequence 0 #(0 1 2 3) :start 2 :end 0)))

(test split-sequence.test-provided
  ;; Neither provided
  (is (equal '((1) (3)) (split-sequence 2 '(1 2 3))))
  ;; Either provided
  (is (equal '((1) (3)) (split-sequence 2 '(1 2 3) :test #'eql)))
  (is (equal '(() (2) ()) (split-sequence 2 '(1 2 3) :test-not #'eql)))
  (signals type-error (split-sequence 2 '(1 2 3) :test nil))
  (signals type-error (split-sequence 2 '(1 2 3) :test-not nil))
  ;; Both provided
  (signals program-error (split-sequence 2 '(1 2 3) :test #'eql :test-not nil))
  (signals program-error (split-sequence 2 '(1 2 3) :test nil :test-not #'eql))
  (signals program-error (split-sequence 2 '(1 2 3) :test #'eql :test-not #'eql))
  (signals program-error (split-sequence 2 '(1 2 3) :test nil :test-not nil)))

;;; FUZZ TEST

(test split-sequence.fuzz
  (fuzz :verbose nil :fiveamp t))

(defun fuzz (&key (max-length 100) (repetitions 1000000) (verbose t) (print-every 10000) (fiveamp nil))
  (flet ((random-vector (n)
           (let ((vector (make-array n :element-type '(unsigned-byte 2))))
             (dotimes (i n) (setf (aref vector i) (random 4)))
             vector))
         (random-boolean () (if (= 0 (random 2)) t nil))
         (fuzz-failure (vector start end from-end count remove-empty-subseqs
                        expected-splits expected-index actual-splits actual-index)
           (format nil "Fuzz failure:
\(MULTIPLE-VALUE-CALL #'VALUES
  (SPLIT-SEQUENCE 0 ~S
                  :START ~S :END ~S :FROM-END ~S :COUNT ~S :REMOVE-EMPTY-SUBSEQS ~S)
  (SPLIT-SEQUENCE 0 (COERCE ~S 'LIST)
                  :START ~S :END ~S :FROM-END ~S :COUNT ~S :REMOVE-EMPTY-SUBSEQS ~S))
~S~%~S~%~S~%~S"
                   vector start end from-end count remove-empty-subseqs
                   vector start end from-end count remove-empty-subseqs
                   expected-splits expected-index actual-splits actual-index)))
    (let ((failure-string nil)
          (predicate (lambda (x) (= x 0)))
          (predicate-not (lambda (x) (/= x 0))))
      (dotimes (i repetitions)
        (when (and verbose (= 0 (mod (1+ i) print-every)))
          (format t "Fuzz: Pass ~D passed.~%" (1+ i)))
        (let* ((length (1+ (random max-length)))
               (vector (random-vector length))
               (list (coerce vector 'list))
               (remove-empty-subseqs (random-boolean))
               (start 0) end from-end count)
          (case (random 5)
            (0)
            (1 (setf start (random length)))
            (2 (setf start (random length)
                     end (+ start (random (1+ (- length start))))))
            (3 (setf start (random length)
                     end (+ start (random (1+ (- length start))))
                     from-end t))
            (4 (setf start (random length)
                     end (+ start (random (1+ (- length start))))
                     from-end t
                     count (random (1+ (- end start))))))
          (let ((args (list :start start :end end :from-end from-end :count count
                            :remove-empty-subseqs remove-empty-subseqs)))
            (multiple-value-bind (expected-splits expected-index)
                (case (random 3)
                  (0 (apply #'split-sequence 0 vector args))
                  (1 (apply #'split-sequence-if predicate vector args))
                  (2 (apply #'split-sequence-if-not predicate-not vector args)))
              (multiple-value-bind (actual-splits actual-index)
                  (case (random 3)
                    (0 (apply #'split-sequence 0 list args))
                    (1 (apply #'split-sequence-if predicate list args))
                    (2 (apply #'split-sequence-if-not predicate-not list args)))
                (let* ((expected-splits (mapcar (lambda (x) (coerce x 'list)) expected-splits))
                       (result (and (equal actual-splits expected-splits)
                                    (= expected-index actual-index))))
                  (unless result
                    (let ((string (fuzz-failure
                                   vector start end from-end count remove-empty-subseqs
                                   expected-splits expected-index actual-splits actual-index)))
                      (cond (fiveamp
                             (setf failure-string string)
                             (return))
                            (t (assert result () string)))))))))))
      (when fiveamp
        (is (not failure-string) failure-string)))))
