#|
 This file is a part of zippy
 (c) 2020 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(in-package #:org.shirakumo.zippy)

(defgeneric make-decryption-state (format input password &key buffer &allow-other-keys))
(defgeneric call-with-decrypted-buffer (function input length state))

(defgeneric make-encryption-state (format password &key buffer))
(defgeneric call-with-encrypted-buffer (function vector start end state))
(defgeneric call-with-completed-encrypted-buffer (function state))

(defmethod make-decryption-state (format input password &rest args)
  (declare (ignore args))
  (error "Unsupported encryption method: ~a" format))

(defstruct (vector-decryption-state
            (:constructor make-vector-decryption-state ()))
  (consumed 0 :type (unsigned-byte 32)))

(defmethod make-decryption-state ((format (eql NIL)) (input vector-input) password &key buffer)
  (declare (ignore buffer))
  (make-vector-decryption-state))

(defstruct (stream-decryption-state
            (:constructor make-stream-decryption-state (buffer)))
  (buffer NIL :type (simple-array (unsigned-byte 8) (*)))
  (start 0 :type (unsigned-byte 32))
  (end 0 :type (unsigned-byte 32)))

(defmethod make-decryption-state ((format (eql NIL)) (input stream) password &key buffer)
  (make-stream-decryption-state (ensure-buffer buffer)))

(defmethod call-with-decrypted-buffer (function (input stream) length (state stream-decryption-state))
  (let ((buffer (stream-decryption-state-buffer state))
        (total-consumed 0))
    (flet ((output (start end)
             (let ((consumed (funcall function buffer start end)))
               (setf (stream-decryption-state-start state) consumed)
               (setf (stream-decryption-state-end state) end)
               (when (< consumed end)
                 (return-from call-with-decrypted-buffer consumed))
               consumed)))
      (output (stream-decryption-state-start state)
              (stream-decryption-state-end state))
      (loop while (< total-consumed length)
            for read = (read-sequence buffer input :end (min (length buffer) length))
            for consumed = (output 0 read)
            do (cond ((= 0 consumed)
                      (setf (stream-decryption-state-end state) 0)
                      (return))
                     (T
                      (incf total-consumed consumed))))
      total-consumed)))

(defmethod call-with-decrypted-buffer (function (input vector-input) length state)
  (let* ((start (vector-input-index input))
         (offset (+ start (vector-decryption-state-consumed state)))
         (read (funcall function (vector-input-vector input) offset (+ start length))))
    (prog1 (- read offset)
      (setf (vector-decryption-state-consumed state) (- read start)))))

(defmethod make-encryption-state ((format (eql NIL)) password &key buffer)
  NIL)

(defmethod call-with-encrypted-buffer (function vector start end (state (eql NIL)))
  (funcall function vector start end))

(defmethod call-with-completed-encrypted-buffer (function (state (eql NIL)))
  (funcall function #() 0 0))

;; TODO: Support for AE-X https://www.winzip.com/win/en/aes_info.html
;; TODO: Support for other encryption methods
;; TODO: Support for central directory encryption
