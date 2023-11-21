(in-package :cl-user)
(defpackage dexador.keep-alive-stream
  (:use :cl)
  (:import-from :trivial-gray-streams
                :fundamental-input-stream
                :stream-read-byte
                :stream-read-sequence
                :stream-element-type
                :open-stream-p)
  (:import-from :alexandria
                :xor)
  (:export :make-keep-alive-stream
           :keep-alive-stream
           :keep-alive-chunked-stream
   :keep-alive-stream-close-underlying-stream
   :keep-alive-stream-stream))
(in-package :dexador.keep-alive-stream)

(defclass keep-alive-stream (fundamental-input-stream)
  ((stream :type (or null stream)
           :initarg :stream
           :initform (error ":stream is required")
           :accessor keep-alive-stream-stream
           :documentation "A stream; when we read END elements from it, we call CLOSE-ACTION on it and
   set this slot to nil.")
   (end :initarg :end
        :initform nil
        :accessor keep-alive-stream-end)
   (close-action :initarg :on-close-or-eof :reader close-action
                 :documentation "A (lambda (stream abort)) which will be called with keep-alive-stream-stream
   when the stream is either closed or we hit end of file or we hit end")))

(defun keep-alive-stream-close-underlying-stream (underlying-stream abort)
  (when (and underlying-stream (open-stream-p underlying-stream))
    (close underlying-stream :abort abort)))

(defclass keep-alive-chunked-stream (keep-alive-stream)
  ((chunga-stream :initarg :chunga-stream :accessor chunga-stream)))

(defun make-keep-alive-stream (stream &key end chunked-stream (on-close-or-eof #'keep-alive-stream-close-underlying-stream))
  "ON-CLOSE-OR-EOF takes a single parameter, STREAM (the stream passed in here, not the
keep-alive-stream), and should handle clean-up of it"
  (assert (xor end chunked-stream))
  (if chunked-stream
      (make-instance 'keep-alive-chunked-stream :stream stream :chunga-stream chunked-stream :on-close-or-eof on-close-or-eof)
      (make-instance 'keep-alive-stream :stream stream :end end :on-close-or-eof on-close-or-eof)))

(defun maybe-close (stream &optional (close-if nil))
  "Will close the underlying stream if close-if is T (unless it is already closed).
   If the stream is already closed or we closed it returns :EOF otherwise NIL."
  (let ((underlying-stream (keep-alive-stream-stream stream)))
    (cond
      ((not underlying-stream)
       :eof)
      (close-if
       (funcall (close-action stream) underlying-stream nil)
       (setf (keep-alive-stream-stream stream) nil)
       :eof)
      (t nil))))

(defmethod stream-read-byte ((stream keep-alive-stream))
  "Return :EOF or byte read.  When we hit EOF or finish reading our allowed content,
   call the close-action on our underlying-stream and return EOF."
  (let ((byte :eof)
        (underlying-stream (keep-alive-stream-stream stream)))
    (or (maybe-close stream (<= (keep-alive-stream-end stream) 0))
        (progn
          (setf byte (read-byte underlying-stream nil :eof))
          (decf (keep-alive-stream-end stream) 1)
          (maybe-close stream (or (<= (keep-alive-stream-end stream) 0) (eql byte :eof)))
          byte))))

(defmethod stream-read-byte ((stream keep-alive-chunked-stream))
  "Return :EOF or byte read.  When we hit :EOF or finish reading our chunk,
   call the close-action on our underlying-stream and return :EOF"
  (or (maybe-close stream)
      (if (chunga:chunked-stream-input-chunking-p (chunga-stream stream))
          (let ((byte (read-byte (chunga-stream stream) nil :eof)))
            (if (eql byte :eof)
                (prog1
                    byte
                  (maybe-close stream t))
                byte))
          (or (maybe-close stream t) :eof))))

(defmethod stream-read-sequence ((stream keep-alive-stream) sequence start end &key)
  (declare (optimize speed))
  (if (null (keep-alive-stream-stream stream)) ;; we already closed it
      start
      (let* ((to-read (min (- end start) (keep-alive-stream-end stream)))
             (n (read-sequence sequence (keep-alive-stream-stream stream)
                               :start start
                               :end (+ start to-read))))
        (decf (keep-alive-stream-end stream) (- n start))
        (maybe-close stream (<= (keep-alive-stream-end stream) 0))
        n)))

(defmethod stream-read-sequence ((stream keep-alive-chunked-stream) sequence start end &key)
  (declare (optimize speed))
  (if (null (keep-alive-stream-stream stream)) ;; we already closed it
      start
      (if (chunga:chunked-stream-input-chunking-p (chunga-stream stream))
          (prog1
              (let ((num-read (read-sequence sequence (chunga-stream stream) :start start :end end)))
                num-read)
            (maybe-close stream (not (chunga:chunked-stream-input-chunking-p (chunga-stream stream)))))
          start)))

(defmethod stream-element-type ((stream keep-alive-chunked-stream))
  (stream-element-type (chunga-stream stream)))

(defmethod stream-element-type ((stream keep-alive-stream))
  '(unsigned-byte 8))

(defmethod open-stream-p ((stream keep-alive-stream))
  (let ((underlying-stream (keep-alive-stream-stream stream)))
    (and underlying-stream (open-stream-p underlying-stream))))

(defmethod close ((stream keep-alive-stream) &key abort)
  (funcall (close-action stream) (keep-alive-stream-stream stream) abort)
  (setf (keep-alive-stream-stream stream) nil))
