(defpackage #:dexador.body
  (:use #:cl)
  (:import-from #:dexador.encoding
                #:detect-charset)
  (:import-from #:dexador.decoding-stream
                #:make-decoding-stream)
  (:import-from #:dexador.util
                #:ascii-string-to-octets
                #:+crlf+)
  (:import-from #:babel
                #:octets-to-string
                #:character-decoding-error)
  (:import-from #:babel-encodings
                #:*suppress-character-coding-errors*)
  (:import-from :trivial-mimes
                :mime)
  (:import-from #:quri
                #:url-encode)
  (:import-from #:chipz
                #:make-decompressing-stream
                #:decompress
                #:make-dstate)
  (:export #:decode-body
           #:write-multipart-content
           #:decompress-body))
(in-package #:dexador.body)

(defun decode-body (content-type body &key default-charset on-close)
  (let ((charset (or (and content-type
                          (detect-charset content-type body))
                     default-charset))
        (babel-encodings:*suppress-character-coding-errors* t))
    (if charset
        (handler-case
            (if (streamp body)
                (make-decoding-stream body :encoding charset :on-close on-close)
                (babel:octets-to-string body :encoding charset))
          (babel:character-decoding-error (e)
            (warn (format nil "Failed to decode the body to ~S due to the following error (falling back to binary):~%  ~A"
                          charset
                          e))
            (return-from decode-body body)))
        body)))

(defun content-disposition (key val)
  (if (pathnamep val)
      (let* ((filename (file-namestring val))
             (utf8-filename-p (find-if (lambda (char)
                                         (< 127 (char-code char)))
                                       filename)))
        (format nil "Content-Disposition: form-data; name=\"~A\"; ~:[filename=\"~A\"~;filename*=UTF-8''~A~]~C~C"
                key
                utf8-filename-p
                (if utf8-filename-p
                    (url-encode filename :encoding :utf-8)
                    filename)
                #\Return #\Newline))
      (format nil "Content-Disposition: form-data; name=\"~A\"~C~C"
              key
              #\Return #\Newline)))

(defun write-multipart-content (content boundary stream)
  (let ((boundary (ascii-string-to-octets boundary)))
    (labels ((boundary-line (&optional endp)
               (write-sequence (ascii-string-to-octets "--") stream)
               (write-sequence boundary stream)
               (when endp
                 (write-sequence (ascii-string-to-octets "--") stream))
               (crlf))
             (crlf () (write-sequence +crlf+ stream)))
      (loop for (key . val) in content
            do (boundary-line)
               (write-sequence (ascii-string-to-octets (content-disposition key val)) stream)
               (when (pathnamep val)
                 (write-sequence
                  (ascii-string-to-octets
                   (format nil "Content-Type: ~A~C~C"
                           (mimes:mime val)
                           #\Return #\Newline))
                  stream))
               (crlf)
               (typecase val
                 (pathname (let ((buf (make-array 1024 :element-type '(unsigned-byte 8))))
                             (with-open-file (in val :element-type '(unsigned-byte 8))
                               (loop for n of-type fixnum = (read-sequence buf in)
                                     until (zerop n)
                                     do (write-sequence buf stream :end n)))))
                 (string (write-sequence (babel:string-to-octets val) stream))
                 (otherwise (write-sequence (babel:string-to-octets (princ-to-string val)) stream)))
               (crlf)
            finally
               (boundary-line t)))))

(defun decompress-body (content-encoding body)
  (unless content-encoding
    (return-from decompress-body body))

  (cond
    ((string= content-encoding "gzip")
     (if (streamp body)
         (chipz:make-decompressing-stream :gzip body)
         (chipz:decompress nil (chipz:make-dstate :gzip) body)))
    ((string= content-encoding "deflate")
     (if (streamp body)
         (chipz:make-decompressing-stream :zlib body)
         (chipz:decompress nil (chipz:make-dstate :zlib) body)))
    (t body)))
