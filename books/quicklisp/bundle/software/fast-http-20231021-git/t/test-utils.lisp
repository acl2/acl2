(in-package :cl-user)
(defpackage fast-http-test.test-utils
  (:use :cl)
  (:export :str
           :bv))
(in-package :fast-http-test.test-utils)

(defun str (&rest strings)
  (apply #'concatenate 'string strings))

(defun bv (object &key length)
  (flet ((to-bv (object)
           (etypecase object
             ((simple-array (unsigned-byte 8) (*)) object)
             (string (babel:string-to-octets object))
             (vector (make-array (length object)
                                 :element-type '(unsigned-byte 8)
                                 :initial-contents object)))))
    (if length
        (let ((buf (make-array length :element-type '(unsigned-byte 8))))
          (loop for i from 0
                for el across (to-bv object)
                do (setf (aref buf i) el))
          buf)
        (to-bv object))))
