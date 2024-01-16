(in-package :cl-user)
(defpackage fast-http.byte-vector
  (:use :cl)
  (:import-from :alexandria
                :define-constant)
  (:export :+cr+
           :+lf+
           :+space+
           :+tab+
           :+page+
           :+dash+
           :+crlf+

           :simple-byte-vector
           :make-byte-vector
           :digit-byte-char-p
           :digit-byte-char-to-integer
           :alpha-byte-char-p
           :alpha-byte-char-to-lower-char
           :alphanumeric-byte-char-p
           :mark-byte-char-p
           :ascii-octets-to-string
           :ascii-octets-to-lower-string
           :append-byte-vectors))
(in-package :fast-http.byte-vector)

(defconstant +cr+ (char-code #\Return))
(defconstant +lf+ (char-code #\Newline))
(defconstant +space+ (char-code #\Space))
(defconstant +tab+ (char-code #\Tab))
(defconstant +page+ (char-code #\Page))
(defconstant +dash+ #.(char-code #\-))

(define-constant +crlf+
  (make-array 2 :element-type '(unsigned-byte 8)
                :initial-contents (list +cr+ +lf+))
  :test 'equalp)

(deftype simple-byte-vector (&optional (len '*))
  `(simple-array (unsigned-byte 8) (,len)))

(declaim (inline digit-byte-char-p
                 digit-byte-char-to-integer
                 alpha-byte-char-p
                 alpha-byte-char-to-lower-char
                 alphanumeric-byte-char-p
                 mark-byte-char-p))

(defun digit-byte-char-p (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3) (safety 0)))
  (<= #.(char-code #\0) byte #.(char-code #\9)))

(declaim (ftype (function ((unsigned-byte 8)) fixnum) digit-byte-char-to-integer))
(defun digit-byte-char-to-integer (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3) (safety 0)))
  (the fixnum (- byte #.(char-code #\0))))

(defun alpha-byte-char-p (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3) (safety 0)))
  (or (<= #.(char-code #\A) byte #.(char-code #\Z))
      (<= #.(char-code #\a) byte #.(char-code #\z))))

(defun alpha-byte-char-to-lower-char (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3) (safety 0)))
  (the character
       (cond
         ((<= #.(char-code #\A) byte #.(char-code #\Z))
          (code-char (+ byte #x20)))
         (T #+nil(<= #.(char-code #\a) byte #.(char-code #\z))
            (code-char byte)))))

(defun alphanumeric-byte-char-p (byte)
  (declare (type (unsigned-byte 8) byte))
  (or (alpha-byte-char-p byte)
      (digit-byte-char-p byte)))

(defun mark-byte-char-p (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3) (safety 0)))
  (or (= byte #.(char-code #\-))
      (= byte #.(char-code #\_))
      (= byte #.(char-code #\.))
      (= byte #.(char-code #\!))
      (= byte #.(char-code #\~))
      (= byte #.(char-code #\*))
      (= byte #.(char-code #\'))
      (= byte #.(char-code #\())
      (= byte #.(char-code #\)))))

(declaim (ftype (function ((unsigned-byte 8)) (unsigned-byte 8)) byte-to-ascii-lower)
         (inline byte-to-ascii-lower))
(defun byte-to-ascii-lower (x)
  (declare (type (unsigned-byte 8) x)
           (optimize (speed 3) (safety 0)))
  (if (<= #.(char-code #\A) x #.(char-code #\Z))
      (- x #.(- (char-code #\A) (char-code #\a)))
      x))

(declaim (inline ascii-octets-to-string))
(defun ascii-octets-to-string (octets &key (start 0) (end (length octets)))
  (declare (type simple-byte-vector octets)
           (type (unsigned-byte 64) start end)
           (optimize (speed 3) (safety 0)))
  (let* ((len (the (unsigned-byte 64) (- end start)))
         (string (make-string len :element-type 'character)))
    (declare (type (unsigned-byte 64) len)
             (type simple-string string))
    (do ((i 0 (1+ i))
         (j start (1+ j)))
        ((= j end) string)
      (setf (aref string i)
            (code-char (aref octets j))))))

(declaim (inline ascii-octets-to-lower-string))
(defun ascii-octets-to-lower-string (octets &key (start 0) (end (length octets)))
  (declare (type simple-byte-vector octets)
           (type (unsigned-byte 64) start end)
           (optimize (speed 3) (safety 0)))
  (let* ((len (the (unsigned-byte 64) (- end start)))
         (string (make-string len :element-type 'character)))
    (declare (type (unsigned-byte 64) len)
             (type simple-string string))
    (do ((i 0 (1+ i))
         (j start (1+ j)))
        ((= j end) string)
      (setf (aref string i)
            (code-char (byte-to-ascii-lower (aref octets j)))))))

(defun append-byte-vectors (vec1 vec2)
  (declare (type simple-byte-vector vec1 vec2)
           (optimize (speed 3) (safety 0)))
  (let* ((vec1-len (length vec1))
         (vec2-len (length vec2))
         (result (make-array (+ vec1-len vec2-len)
                             :element-type '(unsigned-byte 8))))
    (declare (type simple-byte-vector result))
    (replace result vec1 :start1 0)
    (replace result vec2 :start1 vec1-len)
    result))
