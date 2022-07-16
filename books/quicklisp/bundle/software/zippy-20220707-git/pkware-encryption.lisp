#|
 This file is a part of zippy
 (c) 2020 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(in-package #:org.shirakumo.zippy)

(defstruct (pkware-decrypt-state
            (:constructor %make-pkware-decrypt-state (buffer)))
  (buffer NIL :type (simple-array (unsigned-byte 8) (*)))
  (k0 305419896 :type (unsigned-byte 32))
  (k1 591751049 :type (unsigned-byte 32))
  (k2 878082192 :type (unsigned-byte 32)))

(defun crc32-rotate (crc byte)
  (logxor (ldb (byte 24 8) crc)
          (aref 3bz::+crc32/table+ (ldb (byte 8 0) (logxor crc byte)))))

(defun update-pkware-state (state byte)
  (setf (pkware-decrypt-state-k0 state) (crc32-rotate (pkware-decrypt-state-k0 state) byte))
  (setf (pkware-decrypt-state-k1 state) (logand #xFFFFFFFF (+ (pkware-decrypt-state-k1 state)
                                                              (logand (pkware-decrypt-state-k0 state) #xFF))))
  (setf (pkware-decrypt-state-k1 state) (logand #xFFFFFFFF (1+ (* (pkware-decrypt-state-k1 state) 134775813))))
  (setf (pkware-decrypt-state-k2 state) (crc32-rotate (pkware-decrypt-state-k2 state) (ash (pkware-decrypt-state-k1 state) -24))))

(defun pkware-decrypt-byte (state)
  (let ((temp (logand #xFFFF (logior 2 (pkware-decrypt-state-k2 state)))))
    (ash (* temp (logxor temp 1)) -8)))

(defun make-pkware-decrypt-state (buffer password initial-state index)
  (let ((state (%make-pkware-decrypt-state buffer)))
    (loop for byte across password
          do (update-pkware-state state byte))
    (loop for i from index below (+ index 12)
          for byte = (aref initial-state i)
          for c = (logxor byte (pkware-decrypt-byte state))
          do (update-pkware-state state c))
    state))

(defmethod make-decryption-state ((format (eql :pkware)) (input stream) password &key buffer)
  (let ((initial-state (make-array 12 :element-type '(unsigned-byte 8))))
    (read-sequence initial-state input)
    (make-pkware-decrypt-state (ensure-buffer buffer) (ensure-password password) initial-state 0)))

(defmethod make-decryption-state ((format (eql :pkware)) (input vector-input) password &key buffer)
  (let ((state (make-pkware-decrypt-state (ensure-buffer buffer) (ensure-password password)
                                          (vector-input-vector input) (vector-input-index input))))
    (incf (vector-input-index input) 12)
    state))

(defmethod call-with-decrypted-buffer (function (input stream) length (state pkware-decrypt-state))
  (loop with buffer = (pkware-decrypt-state-buffer state)
        while (< 0 length)
        for read = (read-sequence buffer input :end length)
        do (loop for i from 0 below read
                 for byte = (aref buffer i)
                 for decrypted = (logxor byte (pkware-decrypt-byte state))
                 do (update-pkware-state state decrypted)
                    (setf (aref buffer i) (ldb (byte 8 0) decrypted)))
           (decf length read)
           ;; FIXME: does not work correctly.
           (let ((consumed (funcall function buffer 0 read)))
             (when (< consumed read)
               (return read)))))

(defmethod call-with-decrypted-buffer (function (input vector-input) length (state pkware-decrypt-state))
  (loop with inbuffer = (vector-input-vector input)
        with index = (vector-input-index input)
        with buffer = (pkware-decrypt-state-buffer state)
        for read = (min length (length buffer))
        while (< 0 length)
        do (loop for i from 0 below read
                 for byte = (aref inbuffer index)
                 for decrypted = (logxor byte (pkware-decrypt-byte state))
                 do (update-pkware-state state decrypted)
                    (setf (aref buffer i) decrypted)
                    (incf index))
           (decf length read)
           ;; FIXME: does not work correctly.
           (let ((consumed (funcall function buffer 0 read)))
             (when (< consumed read)
               (return read)))))
