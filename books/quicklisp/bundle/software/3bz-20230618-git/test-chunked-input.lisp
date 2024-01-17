(in-package 3bz)


#++
(ql:quickload '(deoxybyte-gzip))

#++
(let ((*default-pathname-defaults* (asdf:system-relative-pathname '3bz "")))
  (with-open-file (o "test.deflated" :element-type 'octet :direction :output
                                     :if-does-not-exist :create :if-exists :error)
    (let* ((i (alexandria:read-file-into-byte-vector "deflate.lisp"))
           (tmp (make-array (length i) :element-type 'octet
                                       :initial-element 0)))
      (multiple-value-bind (x r w)
          (gz:deflate-vector i
            tmp :compression 9
            :suppress-header t)
        (declare (ignore r))
        (nibbles:write-ub64/le (length i) o)
        (write-sequence (subseq x 0 w) o)))))

(defparameter *test-file*
  (let ((f (alexandria:read-file-into-byte-vector (asdf:system-relative-pathname '3bz "test.deflated"))))
    (list (nibbles:ub64ref/le f 0)
          (subseq f 8))))

(defun test-chunked (decompressed-size vector generator)
  (let* ((l (length vector))
         (o 0)
         (tmp (make-array decompressed-size :element-type 'octet
                                            :initial-element 0))
         (state (make-deflate-state :output-buffer tmp)))
    (loop for end = (min l (+ o (funcall generator)))
          for s = (unless (= o l)
                    (subseq vector o end))
          for c = (make-instance 'octet-vector-context
                                 :octet-vector s
                                 :boxes (make-context-boxes :end (length s)))
          while s
          do (decompress c state)
             (assert (or (ds-finished state)
                         (ds-input-underrun state)))
             (setf o end))
    tmp))

(equalp
 (gz:inflate-vector (second *test-file*)
                    (make-array (first *test-file*)
                                :element-type 'octet)
                    :suppress-header t)
 (test-chunked (first *test-file*) (second *test-file*)
               (constantly 3)))

(defparameter *foo* nil)
(defparameter *c* 0)
(let ((ref (gz:inflate-vector (second *test-file*)
                              (make-array (first *test-file*)
                                          :element-type 'octet)
                              :suppress-header t)))
  (loop
    for i from 0
    repeat 30000
    do (print i)
    while
    (progn
      (setf *foo* nil)
      (incf *c*)
      (equalp
       ref
       (test-chunked (first *test-file*) (second *test-file*)
                     (lambda ()
                       (let ((r (random 1234)))
                         (push r *foo*)
                         r)))))
    count t))


(let ((*default-pathname-defaults* (asdf:system-relative-pathname '3bz "")))
  (let* ((i (alexandria:read-file-into-byte-vector "deflate.lisp"))
         (tmp (make-array (* 2 (length i)) :element-type 'octet
                                           :initial-element 0)))
    (multiple-value-bind (x r w)
        (gz:deflate-vector i
          tmp :compression 0
          :suppress-header t)
      (declare (ignore r))
      (mismatch i
                (test-chunked (length i) (subseq x 0 w) (constantly 1323134)
                              #++(lambda () (random 4)))))))
