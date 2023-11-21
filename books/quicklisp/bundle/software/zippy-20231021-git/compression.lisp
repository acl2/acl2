(in-package #:org.shirakumo.zippy)

(defgeneric make-decompression-state (format &key buffer))
(defgeneric call-with-decompressed-buffer (function vector start end state))

(defgeneric make-compression-state (format &key buffer))
(defgeneric call-with-compressed-buffer (function vector start end state))
(defgeneric call-with-completed-compressed-buffer (function state))

(defmethod make-decompression-state (format &key buffer)
  (declare (ignore buffer))
  (error 'unsupported-compression-method :compression-method format))

(defmethod make-decompression-state ((format (eql NIL)) &key buffer)
  (declare (ignore buffer))
  NIL)

(defmethod make-decompression-state ((format (eql :store)) &key buffer)
  (declare (ignore buffer))
  NIL)

(defmethod call-with-decompressed-buffer (function input start end (state (eql NIL)))
  (funcall function input start end))

(defstruct (deflate-state (:include 3bz::deflate-state))
  (last-read 0 :type (signed-byte 32))
  (available 0 :type (signed-byte 32))
  (input-state NIL :type T))

(defmethod make-decompression-state ((format (eql :deflate)) &key buffer)
  (make-deflate-state :output-buffer (ensure-buffer buffer)))

(defmethod call-with-decompressed-buffer (function input start end (state 3bz::deflate-state))
  (when (or (null (deflate-state-input-state state))
            (3bz:input-underrun state))
    (setf (deflate-state-input-state state) (3bz:make-octet-vector-context input :start start :end end))
    (setf (deflate-state-available state) (3bz:decompress (deflate-state-input-state state) state)))
  (loop while (or (< (deflate-state-last-read state) (deflate-state-available state))
                  (3bz:output-overflow state))
        do (let ((consumed (funcall function (3bz::ds-output-buffer state) (deflate-state-last-read state) (deflate-state-available state))))
             (setf (deflate-state-last-read state) consumed)
             (cond ((< consumed (deflate-state-available state))
                    (return))
                   (T
                    (when (3bz:output-overflow state)
                      (3bz:replace-output-buffer state (3bz::ds-output-buffer state))
                      (setf (deflate-state-last-read state) 0))
                    (setf (deflate-state-available state) (3bz:decompress (deflate-state-input-state state) state))))))
  (if (or (3bz:finished state) (3bz:input-underrun state))
      end start))

(defmethod make-compression-state ((format (eql NIL)) &key buffer)
  (declare (ignore buffer))
  NIL)

(defmethod make-compression-state ((format (eql :store)) &key buffer)
  (declare  (ignore buffer))
  NIL)

(defmethod call-with-compressed-buffer (function vector start end (state null))
  (funcall function vector start end))

(defmethod call-with-completed-compressed-buffer (function (state (eql NIL)))
  (funcall function #() 0 0))

(defmethod make-compression-state ((format (eql :deflate)) &key buffer)
  (declare (ignore buffer))
  (make-instance 'salza2:deflate-compressor))

(defmethod call-with-compressed-buffer (function vector start end (state salza2:deflate-compressor))
  (setf (salza2:callback state) (lambda (buffer end) (funcall function buffer 0 end)))
  (salza2:compress-octet-vector vector state :start start :end end))

(defmethod call-with-completed-compressed-buffer (function (state salza2:deflate-compressor))
  (setf (salza2:callback state) (lambda (buffer end) (funcall function buffer 0 end)))
  (salza2:finish-compression state))
