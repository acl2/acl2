(in-package :cl-user)
(defpackage quri.encode
  (:use :cl
        :quri.util)
  (:import-from :babel-encodings
                :*default-character-encoding*)
  (:export :url-encode
           :url-encode-params))
(in-package :quri.encode)

(declaim (type (simple-array character (16)) +hexdigit-char+))
(defvar +hexdigit-char+
  (let ((ary (make-array 16 :element-type 'character)))
    (loop for char across "0123456789ABCDEF"
          for i from 0
          do (setf (aref ary i) char))
    ary))

(defun integer-to-hexdigit (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3) (safety 0)))
  (let ((res (make-string 2)))
    (multiple-value-bind (quotient remainder)
        (floor byte 16)
      (setf (aref res 0) (aref +hexdigit-char+ quotient)
            (aref res 1) (aref +hexdigit-char+ remainder)))
    res))

(defun unreservedp (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3) (safety 0)))
  (or (<= (char-code #\A) byte (char-code #\Z))
      (<= (char-code #\a) byte (char-code #\z))
      (<= (char-code #\0) byte (char-code #\9))
      #.`(or ,@(loop for char across "-._~"
                     collect `(= byte ,(char-code char))))))

(declaim (type (simple-array string (97)) +byte-to-string+))
(defvar +byte-to-string+
  (let ((ary (make-array 97 :element-type 'string :initial-element "")))
    (loop for i from 0 to 96
          unless (unreservedp i)
            do (setf (aref ary i) (integer-to-hexdigit i)))
    ary))

(defun url-encode (data &key
                          (encoding babel-encodings:*default-character-encoding*)
                          (start 0)
                          end
                          space-to-plus)
  (declare (type (or string simple-byte-vector) data)
           (type integer start)
           (optimize (speed 3) (safety 2)))
  (let* ((octets (if (stringp data)
                     (babel:string-to-octets data :encoding encoding :start start :end end)
                     data))
         (res (make-array (* (length octets) 3) :element-type 'character :fill-pointer t))
         (i 0))
    (declare (type simple-byte-vector octets)
             (type string res)
             (type integer i))
    (loop for byte of-type (unsigned-byte 8) across octets do
      (cond
        ((and space-to-plus
              (= byte #.(char-code #\Space)))
         (setf (aref res i) #\+)
         (incf i))
        ((< byte #.(char-code #\a))
         (locally (declare (optimize (speed 3) (safety 0)))
           (let ((converted (aref +byte-to-string+ byte)))
             (if (zerop (length converted))
                 (progn
                   (setf (aref res i) (code-char byte))
                   (incf i))
                 (progn
                   (setf (aref res i) #\%)
                   (incf i)
                   (replace res converted :start1 i)
                   (incf i 2))))))
        ((unreservedp byte)
         (setf (aref res i) (code-char byte))
         (incf i))
        (t
         (setf (aref res i) #\%)
         (incf i)
         (replace res (integer-to-hexdigit byte) :start1 i)
         (incf i 2))))
    (setf (fill-pointer res) i)
    res))

(defun url-encode-params (params-alist &key (encoding babel-encodings:*default-character-encoding*)
                                         space-to-plus)
  (declare (optimize (speed 3)))
  (check-type params-alist list)
  (with-output-to-string (s)
    (loop for ((field . value) . rest) on params-alist do
      (write-string (url-encode field :encoding encoding :space-to-plus space-to-plus) s)
      (when value
        (write-char #\= s)
        (check-type value (or string number simple-byte-vector))
        (write-string (url-encode (if (numberp value)
                                      (with-standard-io-syntax
                                        (write-to-string value))
                                      value)
                                  :encoding encoding
                                  :space-to-plus space-to-plus)
                      s))
      (when rest
        (write-char #\& s)))))
