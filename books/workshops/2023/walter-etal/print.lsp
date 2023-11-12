(in-package :print)

;; Some functions for 
(defparameter *FD-PRINT-STREAM* *standard-output*)
(defparameter *FD-ERROR-STREAM* *error-output*)

(defun make-output-fd-stream (fd)
  (sb-sys:make-fd-stream fd :output t :buffering :none))

(defun print-to-fd (str fd)
  (write-line str fd))

(defun print-to-fd-nonl (str fd)
  (write-string str fd))

(defun set-print2-fd (fd)
  (setq *FD-PRINT-STREAM* (make-output-fd-stream fd)))

(defun set-print3-fd (fd)
  (setq *FD-ERROR-STREAM* (make-output-fd-stream fd)))

(defun set-print2-stream (stream)
  (setq *FD-PRINT-STREAM* stream))

(defun set-print3-stream (stream)
  (setq *FD-ERROR-STREAM* stream))

(defun print2 (str &key (prefix "") (nl (format nil "~%")))
  (progn (print-to-fd-nonl prefix *FD-PRINT-STREAM*)
         (print-to-fd-nonl str *FD-PRINT-STREAM*)
         (print-to-fd-nonl nl *FD-PRINT-STREAM*)))

(defun print3 (str &key (prefix "") (nl (format nil "~%")))
  (progn (print-to-fd-nonl prefix *FD-ERROR-STREAM*)
         (print-to-fd-nonl str *FD-ERROR-STREAM*)
         (print-to-fd-nonl nl *FD-ERROR-STREAM*)))
