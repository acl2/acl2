;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) contributors as per cl+ssl git history
;;;
;;; See LICENSE for details.

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

;; ASN1 Times are represented with ASN1 Strings
(defun decode-asn1-time (asn1-time)
  (when (zerop (asn1-time-check asn1-time))
    (error "asn1-time is not a syntactically valid ASN1 UTCTime"))
  (let ((time-string (flex:octets-to-string (asn1-string-bytes-vector asn1-time)
                                            :external-format :ascii)))
    (let* ((utctime-p (= 1 (asn1-utctime-check asn1-time)))
           (year-len (if utctime-p 2 4))
           (year-part (parse-integer (subseq time-string 0 year-len)))
           (year (if utctime-p
                     (if (>= year-part 50)
                         (+ 1900 year-part)
                         (+ 2000 year-part))
                     year-part)))
      (flet ((get-element-after-year (position)
               (parse-integer
                (subseq time-string
                        (+ position year-len)
                        (+ position year-len 2)))))
        (let ((month  (get-element-after-year 0))
              (day    (get-element-after-year 2))
              (hour   (get-element-after-year 4))
              (minute (get-element-after-year 6))
              (second (get-element-after-year 8)))
          (encode-universal-time second minute hour day month year 0))))))

(defun slurp-stream (stream)
  "Returns a sequence containing the STREAM bytes; the
sequence is created by CFFI:MAKE-SHAREABLE-BYTE-VECTOR,
therefore it can safely be passed to
 CFFI:WITH-POINTER-TO-VECTOR-DATA."
  (let ((seq (cffi:make-shareable-byte-vector (file-length stream))))
    (read-sequence seq stream)
    seq))

(defgeneric decode-certificate (format bytes)
  (:documentation
   "The BYTES must be created by CFFI:MAKE-SHAREABLE-BYTE-VECTOR (because
we are going to pass them to CFFI:WITH-POINTER-TO-VECTOR-DATA)"))

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
                     (case type
                       (#. +GEN-IPADD+
                         (let ((address (asn1-string-bytes-vector data)))
                           (usocket:host-to-hostname address)))
                       (#. +GEN-DNS+
                         (or (try-get-asn1-string-data data '(#. +v-asn1-iastring+))
                             (error "Malformed certificate: possibly NULL in dns-alt-name")))))))
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

(defun certificate-not-after-time (certificate)
  "Returns a universal-time representing the time after
which the CERTIFICATE is not valid. Signals an ERROR if the
CERTIFICATE does not have a properly formatted time. "

  (when (or (openssl-is-not-even 1 1 0)
            (libresslp))
    (error "certificate-not-after-time currently requires version OpenSSL 1.1.0 or newer"))

  (let ((asn1-time (x509-get0-not-after certificate)))
    (when (cffi:null-pointer-p asn1-time)
      (error "X509_get0_notAfter returned NULL"))
    (decode-asn1-time asn1-time)))

(defun certificate-not-before-time (certificate)
  "Returns a universal-time representing the time before
which the CERTIFICATE is not valid. Signals an ERROR if
the CERTIFICATE does not have a properly formatted time."

  (when (or (openssl-is-not-even 1 1 0)
            (libresslp))
    (error "certificate-not-before-time currently requires version OpenSSL 1.1.0 or newer"))

  (let ((asn1-time (x509-get0-not-before certificate)))
    (when (cffi:null-pointer-p asn1-time)
      (error "X509_get0_notBefore returned NULL"))
    (decode-asn1-time asn1-time)))

(defun certificate-fingerprint (certificate &optional (algorithm :sha1))
  "Return the fingerprint of CERTIFICATE as a byte-vector. ALGORITHM is a string
designator for the digest algorithm to use (it defaults to SHA-1)."
  (ensure-initialized)
  (let ((evp (evp-get-digest-by-name (string algorithm))))
    (when (cffi:null-pointer-p evp)
      (error 'ssl-error-call
             :message (format nil "unknown digest algorithm ~A" algorithm)
             :queue (read-ssl-error-queue)))
    (let* ((size (funcall (if (openssl-is-at-least 3 0 0)
                                  'evp-md-get-size
                                  'evp-md-size)
                          evp))
           (fingerprint (cffi:make-shareable-byte-vector size)))
      (cffi:with-pointer-to-vector-data (buf fingerprint)
        (unless (= 1 (x509-digest certificate evp buf (cffi:null-pointer)))
          (error 'ssl-error-call
                 :message "failed to compute fingerprint of certificate"
                 :queue (read-ssl-error-queue))))
      fingerprint)))

(defun x509-cert-from-pem (pem)
  (with-bio-input-from-string (bio pem)
    (pem-read-x509 bio 0 0 0)))

(defun certificate-pem (x509)
  (with-bio-output-to-string (bio)
    ;; man PEM_write_bio_X509:
    ;; The write routines return 1 for success or 0 for failure.
    (unless (= 1 (pem-write-x509 bio x509))
      (error "X509 cert cant be printed: ~s"
             (cl+ssl::err-error-string (cl+ssl::err-get-error) (cffi:null-pointer))))))
