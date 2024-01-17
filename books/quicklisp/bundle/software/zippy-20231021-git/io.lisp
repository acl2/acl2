(in-package #:org.shirakumo.zippy)

(deftype io ()
  `(or stream vector-input directory-input))

(defstruct (vector-input (:constructor make-vector-input (vector index start end)))
  (vector NIL :type (simple-array (unsigned-byte 8) (*)) :read-only T)
  (start 0 :type fixnum :read-only T)
  (end 0 :type fixnum :read-only T)
  (index 0 :type fixnum))

(defstruct directory-input)

(defun seek (io target)
  (etypecase io
    (vector-input
     (if (<= (vector-input-start io) target (1- (vector-input-end io)))
         (setf (vector-input-index io) target)
         (error 'out-of-bounds-seek :target target)))
    (stream
     (file-position io target))))

(defun has-more (io)
  (etypecase io
    (vector-input
     (< (vector-input-index io) (vector-input-end io)))
    (stream
     (< (file-position io) (file-length io)))))

(defun index (io)
  (etypecase io
    (vector-input
     (vector-input-index io))
    (stream ; works for e.g. flexi-stream:in-memory-*-stream
     (file-position io))))

(defun start (io)
  (etypecase io
    (vector-input
     (vector-input-start io))
    (stream
     0)))

(defun end (io)
  (etypecase io
    (vector-input
     (vector-input-end io))
    (stream
     (file-length io))))

(defmethod size ((io vector-input))
  (- (vector-input-end io) (vector-input-start io)))

(defmethod size ((io stream))
  (file-length io))

(defun ub32 (io)
  (etypecase io
    (vector-input
     (prog1 (nibbles:ub32ref/le (vector-input-vector io) (vector-input-index io))
       (incf (vector-input-index io) 4)))
    (stream
     (nibbles:read-ub32/le io))))

(defun output (io array start end)
  (etypecase io
    (vector-input
     (when (<= (vector-input-end io) (+ (vector-input-index io) (- end start)))
       (error 'out-of-bounds-seek :target (+ (vector-input-index io) (- end start))))
     (loop with vector = (vector-input-vector io)
           for i from start below end
           for j from (vector-input-index io)
           do (setf (aref vector j) (aref array i)))
     (incf (vector-input-index io) (- end start)))
    (stream
     (write-sequence array io :start start :end end))))

(defun parse-structure* (io)
  (etypecase io
    (vector-input
     (multiple-value-bind (value index)
         (decode-structure (vector-input-vector io) (vector-input-index io))
       (setf (vector-input-index io) index)
       value))
    (stream
     (read-structure io))))

(defun write-structure* (structure io)
  (etypecase io
    (vector-input
     (setf (vector-input-index io)
           (encode-structure structure (vector-input-vector io) (vector-input-index io))))
    (stream
     (write-structure structure io)))
  io)

(defmacro parse-structure (structure-type io-var)
  (let ((io (gensym "IO")))
    `(let ((,io ,io-var))
       (etypecase ,io
         (vector-input
          (multiple-value-bind (value index)
              (,(intern (format NIL "~a-~a" 'decode structure-type))
               (vector-input-vector ,io) (vector-input-index ,io))
            (setf (vector-input-index ,io) index)
            value))
         (stream
          (,(intern (format NIL "~a-~a" 'read structure-type)) ,io))))))

(defun call-with-io (function io &key (start 0) end (if-exists :error) (direction :input))
  (etypecase io
    ((or string pathname)
     (if (pathname-utils:directory-p io)
         (funcall function (make-directory-input))
         (with-open-file (stream io :direction direction
                                    :element-type '(unsigned-byte 8)
                                    :if-exists if-exists)
           (funcall function stream))))
    (io
     (funcall function io))
    (vector
     (funcall function (make-vector-input io start start (or end (length io)))))))

(defmacro with-io ((io target &rest args) &body body)
  `(call-with-io (lambda (,io) ,@body) ,target ,@args))
