(in-package :cl-user)
(defpackage smart-buffer-test
  (:use :cl
        :smart-buffer
        :prove)
  (:import-from :smart-buffer
                :buffer-on-memory-p
                :buffer-limit-exceeded))
(in-package :smart-buffer-test)

(plan nil)

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

(subtest "swithcing buffer"
  (let ((buffer (make-smart-buffer :memory-limit 10 :disk-limit 15)))
    (is (buffer-on-memory-p buffer) t "on memory")
    (write-to-buffer buffer (bv "Hello"))
    (is (buffer-on-memory-p buffer) t "still on memory")
    (write-to-buffer buffer (bv "World!"))
    (is (buffer-on-memory-p buffer) nil "on disk")
    (is-error (write-to-buffer buffer (bv "Hello!"))
              'buffer-limit-exceeded
              "body buffer limit exceeded")))

(subtest "finalize-buffer"
  (let ((buffer (make-smart-buffer :memory-limit 10 :disk-limit 15)))
    (write-to-buffer buffer (bv "Hello!"))
    (let ((read-buf (make-array 6 :element-type '(unsigned-byte 8))))
      (read-sequence read-buf (finalize-buffer buffer))
      (is read-buf (bv "Hello!") :test #'equalp "on memory")))

  (let ((buffer (make-smart-buffer :memory-limit 10 :disk-limit 15)))
    (write-to-buffer buffer (bv "Hello, World!"))
    (let ((read-buf (make-array 13 :element-type '(unsigned-byte 8))))
      (read-sequence read-buf (finalize-buffer buffer))
      (is read-buf (bv "Hello, World!") :test #'equalp "on disk"))))

(finalize)
