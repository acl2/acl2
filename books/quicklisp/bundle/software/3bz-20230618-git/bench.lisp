(in-package 3bz)

#++(ql:quickload '(3bz salza2 flexi-streams chipz deoxybyte-gzip))


(defvar *foo* nil)
(defvar *chipz* nil)
(defvar *3bz* nil)
#++
(prog1 nil
  (push *foo* *chipz*))
#++
(prog1 nil
  (push *foo* *3bz*))

(defvar *zzz* nil)
(let* ((d (time
           (alexandria:read-file-into-byte-vector "e:/tmp/t/linux-2.2.26.tar"))
          #++(setf *foo*
                   (time
                    (map-into (make-array (expt 2 24) :element-type 'octet)
                              (lambda () (random 225))))))
       (tmp (make-array (length d) :element-type 'octet
                                   :initial-element 0))
       (v #++(time
              (salza2:compress-data d 'salza2:deflate-compressor))
          (or *zzz*
              (setf *zzz*
                    (time
                     (multiple-value-bind (x r w)
                         (gz:deflate-vector d tmp :compression 9
                           :suppress-header t)
                       (declare (ignore r))
                       (subseq x 0 w))))))
       (c (make-instance 'octet-vector-context
                         :octet-vector v
                         :boxes (make-context-boxes :end (length v))))
       (state (make-deflate-state :output-buffer tmp)))
  #++(time (dump-deflate v "-sirqq"))
  #++(time (dump-deflate v "-sir"))
  (format t "chipz:~%")
  (fill tmp 0)
  (with-simple-restart (continue "continue")
    (let ((x (time (chipz:decompress tmp 'chipz:deflate v))))
      (declare (ignore x))
      (assert (equalp d tmp))))
  (fill tmp 0)
  (format t "3bz:~%") ;; 0.36
  (let ((x (time (decompress c state))))
    (assert (not (ds-output-overflow state)))
    (assert (ds-finished state))
    (assert (equalp (typecase x
                      (cons
                       (time (apply 'concatenate 'octet-vector x)))
                      (vector x)
                      (number
                       (subseq tmp 0 x)))
                    d)))
  (fill tmp 0)
  (format t "3bz/pointer:~%") ;; 0.36
  (cffi:with-pointer-to-vector-data (p v)
    (with-octet-pointer (op p (length v))
      (let ((x (time (decompress (make-instance 'octet-pointer-context
                                                :pointer p :op op
                                                :boxes (make-context-boxes :end (length v)))
                                 (make-deflate-state :output-buffer tmp)))))
        (assert (equalp (if (consp x)
                            (time (apply 'concatenate 'octet-vector x))
                            (subseq tmp 0 x))
                        d)))))
  (fill tmp 0)
  (format t "3bz/stream:~%")
  (flex:with-input-from-sequence (s v)
    (let ((x (time (decompress (make-instance 'octet-stream-context
                                              :octet-stream s
                                              :boxes (make-context-boxes :end (length v)))
                               (make-deflate-state :output-buffer tmp)))))
      (assert (equalp (if (consp x)
                          (time (apply 'concatenate 'octet-vector x))
                          (subseq tmp 0 x))
                      d))))

  (fill tmp 0)
  (format t "gz:~%")
  (let ((x (time (gz:inflate-vector v tmp :suppress-header t))))
    (assert (equalp x d)))
  (print (length v))
  nil)

(let* ((d (time
           (alexandria:read-file-into-byte-vector "e:/tmp/t/linux-2.2.26.tar")))
       (tmp (make-array (length d) :element-type 'octet
                                   :initial-element 0))
       (v (or *zzz*
              (setf *zzz*
                    (time
                     (multiple-value-bind (x r w)
                         (gz:deflate-vector d tmp :compression 9
                           :suppress-header t)
                       (declare (ignore r))
                       (subseq x 0 w)))))))
  (fill tmp 0)
  (format t "3bz:~%") ;; 0.33
  (let ((x (time (decompress (make-instance 'octet-vector-context
                                            :octet-vector v
                                            :boxes (make-context-boxes
                                                    :end (length v)))
                             (make-deflate-state :output-buffer tmp)))))
    (assert (equalp (if (consp x)
                        (time (apply 'concatenate 'octet-vector x))
                        (subseq tmp 0 x))
                    d)))
  (format t " x10:~%")
  (time
   (loop repeat 10
         do (decompress (make-instance 'octet-vector-context
                                       :octet-vector v
                                       :boxes (make-context-boxes
                                               :end (length v)))
                        (make-deflate-state :output-buffer tmp))))

  nil)
