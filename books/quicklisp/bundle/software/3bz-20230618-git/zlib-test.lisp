(in-package 3bz)
#++ (ql:quickload '(3bz deoxybyte-gzip chipz))
(defvar *zlib* nil)
(let* ((d (time
           (alexandria:read-file-into-byte-vector "e:/tmp/t/linux-2.2.26.tar")))
       (tmp (make-array (length d) :element-type 'octet
                                   :initial-element 0))
       (v (or *zlib*
              (setf *zlib*
                    (time
                     (multiple-value-bind (x r w)
                         (gz:deflate-vector d (make-array (* 2 (length d))
                                                          :element-type 'octet)
                           :compression 9
                           )
                       (declare (ignore r))
                       (subseq x 0 w)))))))
  (format t "chipz:~%")
  (fill tmp 0)
  (with-simple-restart (continue "continue")
    (let ((x (time (chipz:decompress tmp 'chipz:zlib v))))
      (declare (ignore x))
      (assert (equalp d tmp))))

  (fill tmp 0)
  (format t "3bz:~%") ;; 0.33
  (let ((x (time (decompress-zlib (make-instance 'octet-vector-context
                                            :octet-vector v
                                            :boxes (make-context-boxes
                                                    :end (length v)))
                             (make-zlib-state :output-buffer tmp)))))
    (assert (equalp (if (consp x)
                        (time (apply 'concatenate 'octet-vector x))
                        (subseq tmp 0 x))
                    d)))
  (fill tmp 0)
  (format t "gz:~%")
  (let ((x (time (gz:inflate-vector v tmp))))
    (assert (equalp x d)))

  nil)
