(in-package :fast-io)

;; fast-stream

(defclass fast-io-stream (fundamental-stream)
  ((openp :type boolean :initform t)))

(defmethod stream-file-position ((stream fast-io-stream))
  (with-slots (buffer) stream
    (buffer-position buffer)))

(defmethod open-stream-p ((stream fast-io-stream))
  (slot-value stream 'openep))

 ;; fast-output-stream

(defclass fast-output-stream (fast-io-stream fundamental-output-stream)
  ((buffer :type output-buffer)))

(defmethod initialize-instance ((self fast-output-stream) &key stream
                                buffer-size &allow-other-keys)
  (call-next-method)
  (let ((*default-output-buffer-size* (or buffer-size *default-output-buffer-size*)))
    (with-slots (buffer) self
      (setf buffer (make-output-buffer :output stream)))))

(defmethod output-stream-p ((stream fast-output-stream))
  (with-slots (buffer) stream
    (and (typep buffer 'output-buffer))))

(defmethod stream-element-type ((stream fast-output-stream))
  "Return the underlying array element-type.
   Should always return '(unsigned-byte 8)."
  (with-slots (buffer) stream
    (array-element-type (output-buffer-vector buffer))))

(defmethod stream-write-byte ((stream fast-output-stream) byte)
  (with-slots (buffer) stream
    (fast-write-byte byte buffer)))

(defmethod stream-write-sequence ((stream fast-output-stream) sequence start end
                                  &key &allow-other-keys)
  (with-slots (buffer) stream
    (fast-write-sequence sequence buffer start end))
  sequence)

(defun finish-output-stream (stream)
  (with-slots (buffer) stream
    (if (streamp (output-buffer-output buffer))
        (flush buffer)
        (finish-output-buffer buffer))))

(defmethod close ((stream fast-output-stream) &key abort)
  (declare (ignore abort))
  (finish-output-stream stream)
  (setf (slot-value stream 'openp) nil))

 ;; fast-input-stream

(defclass fast-input-stream (fast-io-stream fundamental-input-stream)
  ((buffer :type input-buffer)))

(defmethod initialize-instance ((self fast-input-stream) &key stream
                                vector &allow-other-keys)
  (call-next-method)
  (with-slots (buffer) self
    (setf buffer (make-input-buffer :vector vector :stream stream))))

(defmethod input-stream-p ((stream fast-input-stream))
  (with-slots (buffer) stream
    (and (typep buffer 'input-buffer))))

(defmethod stream-element-type ((stream fast-input-stream))
  "Return element-type of the underlying vector or stream.
   Return NIL if none are present."
  (with-slots (buffer) stream
    (if-let ((vec (input-buffer-vector buffer)))
      (array-element-type vec)
      (if-let ((stream (input-buffer-stream buffer)))
        (stream-element-type stream)))))

(defmethod (setf stream-file-position) (new-pos (stream fast-input-stream))
  (with-slots (buffer) stream
    (setf (buffer-position buffer) new-pos)))

(defmethod peek-byte ((stream fast-input-stream) &optional peek-type (eof-error-p t) eof-value)
  (with-slots (buffer) stream
    (fast-peek-byte buffer peek-type eof-error-p eof-value)))

(defmethod stream-read-byte ((stream fast-input-stream))
  (with-slots (buffer) stream
    (fast-read-byte buffer)))

(defmethod stream-read-sequence ((stream fast-input-stream) sequence start end
                                 &key &allow-other-keys)
  (with-slots (buffer) stream
    (fast-read-sequence sequence buffer start end)))

(defmethod close ((stream fast-input-stream) &key abort)
  (declare (ignore abort))
  (setf (slot-value stream 'openp) nil))
