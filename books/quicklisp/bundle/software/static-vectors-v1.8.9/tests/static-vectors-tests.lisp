;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-
;;;
;;; --- FiveAM Tests
;;;

(defpackage :static-vectors/test
  (:use #:cl #:static-vectors #:fiveam))

(in-package :static-vectors/test)

(in-suite* :static-vectors)

(test (make-static-vector.defaults
       :compile-at :definition-time)
  (let ((v (make-static-vector 5)))
    (is (= 5 (length v)))
    (is (equal (array-element-type v)
               (upgraded-array-element-type
                '(unsigned-byte 8))))))

(test (make-static-vector.element-type.non-literal
       :compile-at :definition-time)
  (let* ((element-type '(unsigned-byte 16))
         (v (make-static-vector 5 :element-type element-type)))
    (is (= 5 (length v)))
    (is (equal (array-element-type v)
               (upgraded-array-element-type
                '(unsigned-byte 16))))))

(test (make-static-vector.defaults.notinline
       :compile-at :definition-time)
  (locally
      (declare (notinline make-static-vector))
    (let ((v (make-static-vector 5)))
      (is (equal 5 (length v))))))

(test (make-static-vector.initial-element.notinline
       :compile-at :definition-time)
  (locally
      (declare (notinline make-static-vector))
    (let ((v (make-static-vector 5 :initial-element 3)))
      (is (equal 5 (length v)))
      (is (not (find 3 v :test-not #'=))))))

(test (make-static-vector.initial-contents.notinline
       :compile-at :definition-time)
  (locally
      (declare (notinline make-static-vector))
    (let ((v (make-static-vector 5 :initial-contents '(1 2 3 4 5))))
      (is (equal 5 (length v)))
      (is (not (mismatch v '(1 2 3 4 5)))))))

(test (with-static-vector.defaults
       :compile-at :definition-time)
  (with-static-vector (v 5)
    (is (= 5 (length v)))
    (is (equal (array-element-type v)
               (upgraded-array-element-type
                '(unsigned-byte 8))))))

(test (with-static-vector.element-type.literal
       :compile-at :definition-time)
  (with-static-vector (v 3 :element-type '(unsigned-byte 16))
    (is (= 3 (length v)))
    (is (equal (array-element-type v)
               (upgraded-array-element-type
                '(unsigned-byte 16))))))

(test (with-static-vector.element-type.non-literal
       :compile-at :definition-time)
  (let ((element-type '(unsigned-byte 16)))
    (with-static-vector (v 3 :element-type element-type)
      (is (= 3 (length v)))
      (is (equal (array-element-type v)
                 (upgraded-array-element-type
                  '(unsigned-byte 16)))))))

(test (with-static-vector.initial-element.non-literal
       :compile-at :definition-time)
  (let ((element-type '(unsigned-byte 16))
        (initial-element 5))
    (with-static-vector (v 3 :element-type element-type
                             :initial-element initial-element)
      (is (= 3 (length v)))
      (is (equal (array-element-type v)
                 (upgraded-array-element-type
                  '(unsigned-byte 16))))
      (is (= 5 (aref v 0))))))

(test (with-static-vector.initial-contents.non-literal
       :compile-at :definition-time)
  (let ((element-type '(unsigned-byte 16))
        (initial-contents '(1 2 3)))
    (with-static-vector (v 3 :element-type element-type
                             :initial-contents initial-contents)
      (is (= 3 (length v)))
      (is (equal (array-element-type v)
                 (upgraded-array-element-type
                  '(unsigned-byte 16))))
      (is (every #'= v initial-contents)))))

(deftype eltype ()
  '(unsigned-byte 32))

(test (with-static-vector.element-type.deftype
        :compile-at :definition-time)
  (with-static-vector (v 3 :element-type 'eltype)
    (is (= 3 (length v)))
    (is (equal (array-element-type v)
               (upgraded-array-element-type
                '(unsigned-byte 32))))))

(test (with-static-vector.initial-element
       :compile-at :definition-time)
  (with-static-vector (v 3 :initial-element 7)
    (is (= 3 (length v)))
    (is (equalp v #(7 7 7)))))

(test (with-static-vector.initial-contents
       :compile-at :definition-time)
  (with-static-vector (v 3 :initial-contents '(3 14 29))
    (is (= 3 (length v)))
    (is (equalp v #(3 14 29)))))

(test (with-static-vectors.initialization
       :compile-at :definition-time)
  (with-static-vectors ((v1 3 :initial-element 7)
                        (v2 5 :initial-contents '(1 2 3 4 5)))
    (is (equalp v1 #(7 7 7)))
    (is (equalp v2 #(1 2 3 4 5)))))
