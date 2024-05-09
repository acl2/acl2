(in-package :cl-user)
(defpackage fast-http-test.body-buffer
  (:use :cl
        :fast-http.body-buffer
        :fast-http-test.test-utils
        :prove))
(in-package :fast-http-test.body-buffer)

(plan nil)

(subtest "swithcing buffer"
  (let ((buffer (make-body-buffer :memory-limit 10 :disk-limit 15)))
    (is (buffer-on-memory-p buffer) t "on memory")
    (write-to-buffer buffer (bv "Hello"))
    (is (buffer-on-memory-p buffer) t "still on memory")
    (write-to-buffer buffer (bv "World!"))
    (is (buffer-on-memory-p buffer) nil "on disk")
    (is-error (write-to-buffer buffer (bv "Hello!"))
              'body-buffer-limit-exceeded
              "body buffer limit exceeded")))

(subtest "finalize-buffer"
  (let ((buffer (make-body-buffer :memory-limit 10 :disk-limit 15)))
    (write-to-buffer buffer (bv "Hello!"))
    (let ((read-buf (make-array 6 :element-type '(unsigned-byte 8))))
      (read-sequence read-buf (finalize-buffer buffer))
      (is read-buf (bv "Hello!") :test #'equalp "on memory")))

  (let ((buffer (make-body-buffer :memory-limit 10 :disk-limit 15)))
    (write-to-buffer buffer (bv "Hello, World!"))
    (let ((read-buf (make-array 13 :element-type '(unsigned-byte 8))))
      (read-sequence read-buf (finalize-buffer buffer))
      (is read-buf (bv "Hello, World!") :test #'equalp "on disk"))))

(finalize)
