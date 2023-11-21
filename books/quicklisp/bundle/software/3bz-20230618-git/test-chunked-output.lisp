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

(defun test-chunked-output (vector generator)
  (let* ((l (length vector))
         (state (make-deflate-state))
         (c (make-instance 'octet-vector-context
                           :octet-vector vector
                           :boxes (make-context-boxes :end l))))
    (setf (ds-output-buffer state)
          (make-array (funcall generator)
                      :element-type 'octet :initial-element 0))
    (setf (ds-output-offset state) 0)

    (coerce
     (loop
       for x = (decompress c state)
       #+do (format t "~s ~s~%" ss (subseq (ds-output-buffer state) 0 x))
       sum x into ss
       when (or (ds-finished state)
                (ds-output-overflow state))
         append (coerce (subseq (ds-output-buffer state) 0 x) 'list)
         and
           do (setf (ds-output-buffer state)
                    (make-array (funcall generator) :element-type 'octet
                                                    :initial-element 0))
              (Setf (ds-output-offset state) 0)
       until (ds-finished state))
     'vector)))


(let* ((a (gz:inflate-vector (second *test-file*)
                             (make-array (first *test-file*)
                                         :element-type 'octet)
                             :suppress-header t))
       (b (test-chunked-output (second *test-file*)
                               (constantly 3)))
       (c (mismatch a b)))
  (when c
    (list c
          (subseq a c (length a))
          (subseq b c (length b))
          c)))

(defparameter *foo* nil)
(defparameter *c* 0)
(let ((ref (gz:inflate-vector (second *test-file*)
                              (make-array (first *test-file*)
                                          :element-type 'octet)
                              :suppress-header t)))
  (loop
    for i from 0
    repeat 30000
    do (princ i) (terpri)
    while
    (progn
      (setf *foo* nil)
      (incf *c*)
      (equalp
       ref
       (test-chunked-output (second *test-file*)
                            (lambda ()
                              (let ((r (+ 1 (random 12345))))
                                (push r *foo*)
                                r)))))
    count t))

