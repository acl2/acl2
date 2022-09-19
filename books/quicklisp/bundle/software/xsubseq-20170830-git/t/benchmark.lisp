(in-package :cl-user)
(defpackage xsubseq-test.benchmark
  (:use :cl
        :xsubseq)
  (:export :run-benchmark))
(in-package :xsubseq-test.benchmark)

(defun run-benchmark ()
  (declare (optimize (speed 3) (safety 0)))
  (time
   (let ((result (xsubseq
                  (the (simple-array (unsigned-byte 8) (*))
                       (make-array 0 :element-type '(unsigned-byte 8))) 0)))
     (dotimes (i 100000)
       (xnconcf result
                (xsubseq (the (simple-array (unsigned-byte 8) (100))
                              (make-array 100 :element-type '(unsigned-byte 8)))
                         10
                         30))))))
