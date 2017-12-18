;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

(in-package :cl+ssl)

#|
ASN1 string validation references:
 - https://github.com/digitalbazaar/forge/blob/909e312878838f46ba6d70e90264650b05eb8bde/js/asn1.js
 - http://www.obj-sys.com/asn1tutorial/node128.html
 - https://github.com/deadtrickster/ssl_verify_hostname.erl/blob/master/src/ssl_verify_hostname.erl
 - https://golang.org/src/encoding/asn1/asn1.go?m=text
|#
(defgeneric decode-asn1-string (asn1-string type))

(defun copy-bytes-to-lisp-vector (src-ptr vector count)
  (declare (type (simple-array (unsigned-byte 8)) vector)
           (type fixnum count)
           (optimize (safety 0) (debug 0) (speed 3)))
  (dotimes (i count vector)
    (setf (aref vector i) (cffi:mem-aref src-ptr :unsigned-char i))))

(defun asn1-string-bytes-vector (asn1-string)
  (let* ((data (asn1-string-data asn1-string))
         (length (asn1-string-length asn1-string))
         (vector (cffi:make-shareable-byte-vector length)))
    (copy-bytes-to-lisp-vector data vector length)
    vector))

(defun asn1-iastring-char-p (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3)
                     (debug 0)
                     (safety 0)))
  (< byte #x80))

(defun asn1-iastring-p (bytes)
  (declare (type (simple-array (unsigned-byte 8)) bytes)
           (optimize (speed 3)
                     (debug 0)
                     (safety 0)))
  (every #'asn1-iastring-char-p bytes))

(defmethod decode-asn1-string (asn1-string (type (eql +v-asn1-iastring+)))
  (let ((bytes (asn1-string-bytes-vector asn1-string)))
    (if (asn1-iastring-p bytes)
        (flex:octets-to-string bytes :external-format :ascii)
        (error 'invalid-asn1-string :type '+v-asn1-iastring+))))

(defun asn1-printable-char-p (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3)
                     (debug 0)
                     (safety 0)))
  (cond
    ;; a-z
    ((and (>= byte #.(char-code #\a))
          (<= byte #.(char-code #\z)))
     t)
    ;; '-/
    ((and (>= byte #.(char-code #\'))
          (<= byte #.(char-code #\/)))
     t)
    ;; 0-9
    ((and (>= byte #.(char-code #\0))
          (<= byte #.(char-code #\9)))
     t)
    ;; A-Z
    ((and (>= byte #.(char-code #\A))
          (<= byte #.(char-code #\Z)))
     t)
    ;; other
    ((= byte #.(char-code #\ )) t)
    ((= byte #.(char-code #\:)) t)
    ((= byte #.(char-code #\=)) t)
    ((= byte #.(char-code #\?)) t)))

(defun asn1-printable-string-p (bytes)
  (declare (type (simple-array (unsigned-byte 8)) bytes)
           (optimize (speed 3)
                     (debug 0)
                     (safety 0)))
  (every #'asn1-printable-char-p bytes))

(defmethod decode-asn1-string (asn1-string (type (eql +v-asn1-printablestring+)))
  (let* ((bytes (asn1-string-bytes-vector asn1-string)))
    (if (asn1-printable-string-p bytes)
        (flex:octets-to-string bytes :external-format :ascii)
        (error 'invalid-asn1-string :type '+v-asn1-printablestring+))))

(defmethod decode-asn1-string (asn1-string (type (eql +v-asn1-utf8string+)))
  (let* ((data (asn1-string-data asn1-string))
         (length (asn1-string-length asn1-string)))
    (cffi:foreign-string-to-lisp data :count length :encoding :utf-8)))

(defmethod decode-asn1-string (asn1-string (type (eql +v-asn1-universalstring+)))
  (if (= 0 (mod (asn1-string-length asn1-string) 4))
      ;; cffi sometimes fails here on sbcl? idk why (maybe threading?)
      ;; fail: Illegal :UTF-32 character starting at position 48...
      ;; when (length bytes) is 48...
      ;; so I'm passing :count explicitly
      (or (ignore-errors (cffi:foreign-string-to-lisp (asn1-string-data asn1-string) :count (asn1-string-length asn1-string) :encoding :utf-32))
          (error 'invalid-asn1-string :type '+v-asn1-universalstring+))
      (error 'invalid-asn1-string :type '+v-asn1-universalstring+)))

(defun asn1-teletex-char-p (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3)
                     (debug 0)
                     (safety 0)))
  (and (>= byte #x20)
       (< byte #x80)))

(defun asn1-teletex-string-p (bytes)
  (declare (type (simple-array (unsigned-byte 8)) bytes)
           (optimize (speed 3)
                     (debug 0)
                     (safety 0)))
  (every #'asn1-teletex-char-p bytes))

(defmethod decode-asn1-string (asn1-string (type (eql +v-asn1-teletexstring+)))
  (let ((bytes (asn1-string-bytes-vector asn1-string)))
    (if (asn1-teletex-string-p bytes)
        (flex:octets-to-string bytes :external-format :ascii)
        (error 'invalid-asn1-string :type '+v-asn1-teletexstring+))))

(defmethod decode-asn1-string (asn1-string (type (eql +v-asn1-bmpstring+)))
  (if (= 0 (mod (asn1-string-length asn1-string) 2))
      (or (ignore-errors (cffi:foreign-string-to-lisp (asn1-string-data asn1-string) :count (asn1-string-length asn1-string) :encoding :utf-16/be))
          (error 'invalid-asn1-string :type '+v-asn1-bmpstring+))
      (error 'invalid-asn1-string :type '+v-asn1-bmpstring+)))

;; TODO: respect asn1-string type
(defun try-get-asn1-string-data (asn1-string allowed-types)
  (let ((type (asn1-string-type asn1-string)))
    (assert (member (asn1-string-type asn1-string) allowed-types) nil "Invalid asn1 string type")
    (decode-asn1-string asn1-string type)))

(defun slurp-stream (stream)
  (let ((seq (make-array (file-length stream) :element-type '(unsigned-byte 8))))
    (read-sequence seq stream)
    seq))

(defmethod decode-certificate ((format (eql :der)) bytes)
  (cffi:with-pointer-to-vector-data (buf* bytes)
    (cffi:with-foreign-object (buf** :pointer)
      (setf (cffi:mem-ref buf** :pointer) buf*)
      (let ((cert (d2i-x509 (cffi:null-pointer) buf** (length bytes))))
        (when (cffi:null-pointer-p cert)
          (error 'ssl-error-call :message "d2i-X509 failed" :queue (read-ssl-error-queue)))
        cert))))

(defun cert-format-from-path (path)
  ;; or match "pem" type too and raise unknown format error?
  (if (equal "der" (pathname-type path))
      :der
      :pem))

(defun decode-certificate-from-file (path &key format)
  (let ((bytes (with-open-file (stream path :element-type '(unsigned-byte 8))
                 (slurp-stream stream)))
        (format (or format (cert-format-from-path path))))
    (decode-certificate format bytes)))

(defun certificate-alt-names (cert)
  #|
  * The return value is the decoded extension or NULL on
  * error. The actual error can have several different causes,
  * the value of *crit reflects the cause:
  * >= 0, extension found but not decoded (reflects critical value).
  * -1 extension not found.
  * -2 extension occurs more than once.
  |#
  (cffi:with-foreign-object (crit* :int)
    (let ((result (x509-get-ext-d2i cert +NID-subject-alt-name+ crit* (cffi:null-pointer))))
      (if (cffi:null-pointer-p result)
          (let ((crit (cffi:mem-ref crit* :int)))
            (cond
              ((>= crit 0)
               (error "X509_get_ext_d2i: subject-alt-name extension decoding error"))
              ((= crit -1) ;; extension not found, return NULL
               result)
              ((= crit -2)
               (error "X509_get_ext_d2i: subject-alt-name extension occurs more than once"))))
          result))))

(defun certificate-dns-alt-names (cert)
  (let ((altnames (certificate-alt-names cert)))
    (unless (cffi:null-pointer-p altnames)
      (unwind-protect
           (flet ((alt-name-to-string (alt-name)
                    (cffi:with-foreign-slots ((type data) alt-name (:struct general-name))
                      (when (= type +GEN-DNS+)
                        (alexandria:if-let ((string (try-get-asn1-string-data data '(#.+v-asn1-iastring+))))
                          string
                          (error "Malformed certificate: possibly NULL in dns-alt-name"))))))
             (let ((altnames-count (sk-general-name-num altnames)))
               (loop for i from 0 below altnames-count
                     as alt-name = (sk-general-name-value altnames i)
                     collect (alt-name-to-string alt-name))))
        (general-names-free altnames)))))

(defun certificate-subject-common-names (cert)
  (let ((i -1)
        (subject-name (x509-get-subject-name cert)))
    (when (cffi:null-pointer-p subject-name)
      (error "X509_get_subject_name returned NULL"))
    (flet ((extract-cn ()
             (setf i (x509-name-get-index-by-nid subject-name +NID-commonName+ i))
             (when (>= i 0)
               (let* ((entry (x509-name-get-entry subject-name i)))
                 (when (cffi:null-pointer-p entry)
                   (error "X509_NAME_get_entry returned NULL"))
                 (let ((entry-data (x509-name-entry-get-data entry)))
                   (when (cffi:null-pointer-p entry-data)
                     (error "X509_NAME_ENTRY_get_data returned NULL"))
                   (try-get-asn1-string-data entry-data '(#.+v-asn1-utf8string+
                                                          #.+v-asn1-bmpstring+
                                                          #.+v-asn1-printablestring+
                                                          #.+v-asn1-universalstring+
                                                          #.+v-asn1-teletexstring+)))))))
      (loop
        as cn = (extract-cn)
        if cn collect cn
        if (not cn) do
           (loop-finish)))))
