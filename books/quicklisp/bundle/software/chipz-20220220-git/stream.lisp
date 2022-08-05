;;;; stream.lisp -- gray stream wrappers for INFLATE

(in-package :chipz)

(eval-when (:compile-toplevel :load-toplevel)
  #-chipz-system:gray-streams
  (error "gray streams are not supported in this lisp implementation"))

;;; portability definitions

#+ecl
(eval-when (:compile-toplevel :load-toplevel :execute)
  (gray::redefine-cl-functions))

#+cmu
(eval-when (:compile-toplevel :load-toplevel :execute)
  (require :gray-streams))

;;; TRIVIAL-GRAY-STREAMS has it, we might as well, too...
#+allegro
(eval-when (:compile-toplevel :load-toplevel :execute)
  (unless (fboundp 'excl:stream-write-string)
    (require "streamc.fasl")))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *binary-input-stream-class*
     #+lispworks 'stream:fundamental-binary-input-stream
     #+sbcl 'sb-gray:fundamental-binary-input-stream
     #+openmcl 'gray:fundamental-binary-input-stream
     #+cmu 'ext:fundamental-binary-input-stream
     #+allegro 'excl:fundamental-binary-input-stream
     #+clisp 'gray:fundamental-binary-input-stream
     #+ecl 'gray:fundamental-binary-input-stream
     #+clasp 'gray:fundamental-binary-input-stream
     #+genera 'gray-streams:fundamental-binary-input-stream)

  (defvar *stream-read-byte-function*
     #+lispworks 'stream:stream-read-byte
     #+sbcl 'sb-gray:stream-read-byte
     #+openmcl 'gray:stream-read-byte
     #+cmu 'ext:stream-read-byte
     #+allegro 'excl:stream-read-byte
     #+clisp 'gray:stream-read-byte
     #+ecl 'gray:stream-read-byte
     #+clasp 'gray:stream-read-byte
     #+genera 'gray-streams:stream-read-byte)

  (defvar *stream-read-sequence-function*
     #+lispworks 'stream:stream-read-sequence
     #+sbcl 'sb-gray:stream-read-sequence
     #+openmcl 'ccl:stream-read-vector
     #+cmu 'ext:stream-read-sequence
     #+allegro 'excl:stream-read-sequence
     #+clisp 'gray:stream-read-byte-sequence
     #+ecl 'gray:stream-read-sequence
     #+clasp 'gray:stream-read-sequence
     #+genera 'gray-streams:stream-read-sequence)
) ; EVAL-WHEN

;;; READ-SEQUENCE

(defmacro define-stream-read-sequence (specializer &body body)
  (let ((definition
          `(cond
             ((not (typep seq 'simple-octet-vector))
                (call-next-method))
              (t
                (let ((end (or end (length seq))))
                  ,@body)))))

    #+(or cmu sbcl allegro ecl clasp genera)
    `(defmethod #.*stream-read-sequence-function* ((stream ,specializer) seq &optional (start 0) end)
       ,definition)

    #+(or lispworks openmcl)
    `(defmethod #.*stream-read-sequence-function* ((stream ,specializer) seq start end)
       ,definition)

    #+clisp
    `(defmethod #.*stream-read-sequence-function* ((stream ,specializer) seq
                                                   &optional (start 0) end
                                                   ,(gensym "no-hang")
                                                   ,(gensym "interactive"))
       ,definition)))

;;; class definition

(defclass decompressing-stream (#.*binary-input-stream-class*)
  ((wrapped-stream :initarg :stream :reader wrapped-stream)
   (dstate :initarg :dstate :reader dstate)
   (dfun :initarg :dfun :reader dfun)
   (input-buffer :initform (make-array 4096 :element-type '(unsigned-byte 8))
                 :reader input-buffer)
   (input-buffer-index :initform 0 :accessor input-buffer-index)
   (input-buffer-n-bytes :initform 0 :accessor input-buffer-n-bytes)
   (output-buffer :initform (make-array 4096 :element-type '(unsigned-byte 8))
                  :reader output-buffer)
   (output-buffer-index :initform 0 :accessor output-buffer-index)
   (output-buffer-n-bytes :initform 0 :accessor output-buffer-n-bytes)))

;;; constructors
(defun make-decompressing-stream (format stream)
  (multiple-value-bind (state dfun)
      (ecase format
        ((:deflate :zlib :gzip deflate zlib gzip)
         (values (make-inflate-state format) #'%inflate))
        ((:bzip2 bzip2)
         (values (make-bzip2-state) #'%bzip2-decompress)))
    (make-instance 'decompressing-stream
                   :stream stream
                   :dstate state
                   :dfun dfun)))


;;; stream management

(defun output-available-p (stream)
  (/= (output-buffer-index stream) (output-buffer-n-bytes stream)))

(defun input-available-p (stream)
  (/= (input-buffer-index stream) (input-buffer-n-bytes stream)))

(defun refill-stream-input-buffer (stream)
  (with-slots (input-buffer wrapped-stream
                            input-buffer-index input-buffer-n-bytes)
      stream
    (let ((n-bytes-read (read-sequence input-buffer wrapped-stream)))
      (setf input-buffer-index 0 input-buffer-n-bytes n-bytes-read)
      #+nil
      (format *trace-output* "index: ~D | n-bytes ~D~%"
              input-buffer-index input-buffer-n-bytes)
      (values))))

(defun refill-stream-output-buffer (stream)
  (unless (input-available-p stream)
    (refill-stream-input-buffer stream))
  (multiple-value-bind (bytes-read bytes-output)
      (funcall (the function (dfun stream))
               (dstate stream)
               (input-buffer stream)
               (output-buffer stream)
                :input-start (input-buffer-index stream)
                :input-end (input-buffer-n-bytes stream))
    (setf (output-buffer-index stream) 0
          (output-buffer-n-bytes stream) bytes-output
          (input-buffer-index stream) (+ (input-buffer-index stream) bytes-read))
    (assert (<= (input-buffer-index stream) (input-buffer-n-bytes stream)))))


;;; methods

(defun read-and-decompress-byte (stream)
  (flet ((maybe-done ()
           (when (output-available-p stream)
             (return-from read-and-decompress-byte
               (aref (output-buffer stream)
                     (prog1 (output-buffer-index stream)
                       (incf (output-buffer-index stream))))))))
    ;; several input buffers may be used up before output is available
    ;; => read-byte should refill "something" while at all possible,
    ;; like read-sequence already does.
    (loop initially (maybe-done)
          do (refill-stream-output-buffer stream)
             (maybe-done)
             (unless (input-available-p stream)
               (refill-stream-input-buffer stream))
             ;; If we didn't refill, then we must be all done.
             (unless (input-available-p stream)
               (finish-dstate (dstate stream))
               (return :eof)))))

(defun copy-existing-output (stream seq start end)
  (declare (type simple-octet-vector seq))
  (let ((amount (min (- end start)
                     (- (output-buffer-n-bytes stream)
                        (output-buffer-index stream)))))
    (replace seq (output-buffer stream)
             :start1 start :end1 end
             :start2 (output-buffer-index stream)
             :end2 (output-buffer-n-bytes stream))
    (incf (output-buffer-index stream) amount)
    (+ start amount)))

(define-stream-read-sequence decompressing-stream
  (unless (typep seq 'simple-octet-vector)
    (return-from #.*stream-read-sequence-function* (call-next-method)))
  (loop initially (when (output-available-p stream)
                    (setf start (copy-existing-output stream seq
                                                      start end)))
     while (< start end)
     do (unless (input-available-p stream)
          (refill-stream-input-buffer stream))
       ;; If we didn't refill, then we must be all done.
       (unless (input-available-p stream)
         (finish-dstate (dstate stream))
         (loop-finish))
       ;; Decompress directly into the user-provided buffer.
       (multiple-value-bind (bytes-read bytes-output)
           (funcall (the function (dfun stream))
                    (dstate stream)
                    (input-buffer stream)
                    seq
                    :input-start (input-buffer-index stream)
                    :input-end (input-buffer-n-bytes stream)
                    :output-start start
                    :output-end end)
         (incf (input-buffer-index stream) bytes-read)
         (incf start bytes-output))
     finally (return start)))

(defmethod #.*stream-read-byte-function* ((stream decompressing-stream))
  (read-and-decompress-byte stream))
