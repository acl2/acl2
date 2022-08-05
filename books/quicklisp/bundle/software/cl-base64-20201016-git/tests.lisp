;;;; -*- Mode: LISP; Syntax: ANSI-Common-Lisp; Base: 10 -*-
;;;; *************************************************************************
;;;; FILE IDENTIFICATION
;;;;
;;;; Name:          test.lisp
;;;; Purpose:       Regression tests for cl-base64
;;;; Programmer:    Kevin M. Rosenberg
;;;; Date Started:  Jan 2003
;;;;
;;;; $Id$
;;;; *************************************************************************

(in-package #:cl-user)

(defpackage #:cl-base64/test
  (:use #:cl #:kmrcl #:cl-base64 #:ptester))

(in-package #:cl-base64/test)

(defun test-valid-input (exp input)
  (test exp (base64-string-to-usb8-array input) :test #'equalp))

(defun test-broken-input (arg)
  (let ((.hole. (make-broadcast-stream)))
    (test-error (base64-string-to-usb8-array arg)
                :condition-type 'base64-error
                :include-subtypes t)
    (test-error (base64-string-to-string arg)
                :condition-type 'base64-error
                :include-subtypes t)
    (test-error (base64-string-to-integer arg)
                :condition-type 'base64-error
                :include-subtypes t)
    (test-error (base64-string-to-stream arg :stream .hole.)
                :condition-type 'base64-error
                :include-subtypes t)
    (test-error (with-input-from-string (in arg)
                  (base64-stream-to-usb8-array in))
                :condition-type 'base64-error
                :include-subtypes t)
    (test-error (with-input-from-string (in arg)
                  (base64-stream-to-string in))
                :condition-type 'base64-error
                :include-subtypes t)
    (test-error (with-input-from-string (in arg)
                  (base64-stream-to-stream in :stream .hole.))
                :condition-type 'base64-error
                :include-subtypes t)
    (test-error (with-input-from-string (in arg)
                  (base64-stream-to-integer in))
                :condition-type 'base64-error
                :include-subtypes t)))

(defun test-valid ()
  (test-valid-input #(0) "AA==")
  (test-valid-input #(0 0) "AAA=")
  (test-valid-input #(0 0 0) "AAAA")
  (test-valid-input #(0) " A A = = ")
  (test-valid-input #(0 0) " A A A = ")
  (test-valid-input #(0 0 0) " A A A A "))

(defun test-broken-1 ()
  (test-broken-input "A")
  (test-broken-input "AA")
  (test-broken-input "AAA")
  (test-broken-input "AA=")
  (test-broken-input "A==")
  (test-broken-input "A===")
  (test-broken-input "AA===")
  (test-broken-input "AAA===")
  (test-broken-input "AAA==")
  (test-broken-input "A=A")
  (test-broken-input "AA=A")
  (test-broken-input "AAA=A")
  (test-broken-input "A==A"))

(defun test-broken-2 ()
  (flet ((test-invalid-char (char)
           (test-broken-input (format nil "~C" char))
           (test-broken-input (format nil "A~C" char))
           (test-broken-input (format nil "AA~C" char))
           (test-broken-input (format nil "AAA~C" char))
           (test-broken-input (format nil "AAAA~C" char))
           (test-broken-input (format nil "AAA=~C" char))
           (test-broken-input (format nil "AA==~C" char))))
    (test-invalid-char #\$)
    (test-invalid-char (code-char 0))
    (test-invalid-char (code-char 256))))

(defun do-tests (&key ((:break-on-failures *break-on-test-failures*) nil))
  (with-tests (:name "cl-base64 tests")
    (test-valid)
    (test-broken-1)
    (test-broken-2)
      (do* ((length 0 (+ 3 length))
            (string (make-string length) (make-string length))
            (usb8 (make-usb8-array length) (make-usb8-array length))
            (integer (random (expt 10 length)) (random (expt 10 length))))
           ((>= length 300))
        (dotimes (i length)
          (declare (fixnum i))
          (let ((code (random 256)))
            (setf (schar string i) (code-char code))
        (setf (aref usb8 i) code)))

        (do* ((columns 0 (+ columns 4)))
             ((> columns length))
          ;; Test against cl-base64 routines
          (test integer (base64-string-to-integer
                         (integer-to-base64-string integer :columns columns)))
          (test string (base64-string-to-string
                        (string-to-base64-string string :columns columns))
                :test #'string=)
        (test usb8 (base64-string-to-usb8-array
                    (usb8-array-to-base64-string usb8))
              :test #'equalp)

          ;; Test against AllegroCL built-in routines
          #+allegro
          (progn
          (test integer (excl:base64-string-to-integer
                         (integer-to-base64-string integer :columns columns)))
          (test integer (base64-string-to-integer
                         (excl:integer-to-base64-string integer)))
          (test (string-to-base64-string string :columns columns)
                (excl:usb8-array-to-base64-string usb8
                                                  (if (zerop columns)
                                                      nil
                                                      columns))
                :test #'string=)
          (test string (base64-string-to-string
                        (excl:usb8-array-to-base64-string
                         usb8
                         (if (zerop columns)
                             nil
                             columns)))
                :test #'string=)))))
  t)


(defun time-routines (&key (iterations nil)
                           (length 256)
                           (padding 0))
  (assert (zerop (rem length 4)) (length))
  (assert (<= 0 padding 2) (padding))
  (let* ((str (make-string length :initial-element #\q))
         (usb8 (map '(simple-array (unsigned-byte 8) (*)) #'char-code str))
         (int 12345678901234567890)
         (n (or iterations (ceiling (* 32 1024 1024) length))))
    (loop for i downfrom (1- length)
          repeat padding
          do (setf (aref str i) #\=))
    (time-iterations 50000 (integer-to-base64-string int))
    (time-iterations n (string-to-base64-string str))
    (time-iterations n (usb8-array-to-base64-string usb8))

    (let ((displaced (make-array (length str)
                                 :displaced-to str
                                 :element-type (array-element-type str)))
          (base (coerce str 'simple-base-string)))
      (time-iterations n (base64-string-to-usb8-array displaced))
      (time-iterations n (base64-string-to-usb8-array str))
      (time-iterations n (base64-string-to-usb8-array base)))

    #+allegro
    (progn
      (time-iterations n (excl:integer-to-base64-string int))
      (time-iterations n (excl:usb8-array-to-base64-string usb8)))))


;;#+run-test (test-base64)
