#|
 This file is a part of zippy
 (c) 2020 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(in-package #:org.shirakumo.zippy)

(defvar *version*
  '(4 5))

(defvar *compatibility*
  #+windows :ntfs
  #+darwin :darwin
  #+(and unix (not darwin)) :unix)

(defun default-attributes-for (system)
  (case system
    ((:darwin :unix) #o644)
    (T 0)))

(defun ensure-buffer (buffer)
  (etypecase buffer
    (vector buffer)
    (integer (make-array buffer :element-type '(unsigned-byte 8)))
    (null (make-array 4096 :element-type '(unsigned-byte 8)))))

(defun ensure-password (password)
  (etypecase password
    (string (babel:string-to-octets password :encoding :utf-8))
    ((vector (unsigned-byte 8)) password)
    (null (restart-case (error "Password is required")
            (use-value (password)
              (ensure-password password))))))

(defun alist-vector (alist)
  (let* ((max (loop for cons in alist maximize (car cons)))
         (vec (make-array (1+ max) :initial-element :unknown)))
    (loop for (i . e) in alist
          do (setf (svref vec i) e))
    vec))

(defun alist-table (alist)
  (let ((table (make-hash-table)))
    (loop for (i . e) in alist
          do (setf (gethash i table) e))
    table))

(defun cap (value bits)
  (let ((max (1- (ash 1 bits))))
    (if (< max value)
        max
        value)))

(defun bitfield (&rest bits)
  (let ((int 0))
    (loop for i from 0
          for bit in bits
          do (when bit (setf (ldb (byte 1 i) int) 1)))
    int))

(defun enbitfield (list &rest bits)
  (let ((int 0))
    (loop for i from 0
          for bit in bits
          do (when (find bit list) (setf (ldb (byte 1 i) int) 1)))
    int))

(defun debitfield (int &rest bits)
  (loop for i from 0
        for bit in bits
        when (logbitp i int)
        collect bit))

(defun enlist (thing &rest values)
  (if (listp thing) thing (list* thing values)))
