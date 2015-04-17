;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: HTML-TEMPLATE; Base: 10 -*-
;;; $Header: /usr/local/cvsrep/html-template/api.lisp,v 1.22 2007/03/09 13:09:16 edi Exp $

;;; Copyright (c) 2003-2007, Dr. Edmund Weitz. All rights reserved.

;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:

;;;   * Redistributions of source code must retain the above copyright
;;;     notice, this list of conditions and the following disclaimer.

;;;   * Redistributions in binary form must reproduce the above
;;;     copyright notice, this list of conditions and the following
;;;     disclaimer in the documentation and/or other materials
;;;     provided with the distribution.

;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
;;; OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
;;; DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
;;; GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

(in-package #:html-template)

(defgeneric create-template-printer (template
                                     &key force
                                          element-type
                                          if-does-not-exist
                                          external-format)
  (:documentation "Creates a template printer from TEMPLATE which is
an open input stream, a string, or a pathname.  If FORCE is true a
printer will be newly created no matter what the state of the cache
is.  If FORCE is :DO-NOT-CACHE the newly created printer won't be
cached.  Other keyword arguments will be given to WITH-OPEN-FILE.
Keyword arguments will only be accepted if TEMPLATE is a PATHNAME."))

(defmethod create-template-printer ((input-stream stream) &rest rest)
  (when rest
    (signal-template-invocation-error
     "This method doesn't accept keyword arguments"))
  (let ((*standard-input* input-stream))
    (%create-template-printer-aux nil nil)))

(defmethod create-template-printer ((string string) &rest rest)
  (when rest
    (signal-template-invocation-error
     "This method doesn't accept keyword arguments"))
  (with-input-from-string (*standard-input* string)
    (%create-template-printer-aux nil nil)))

(defmethod create-template-printer ((pathname pathname)
                                    &key (force *force-default*)
                                         (element-type #-:lispworks 'character
                                                       #+:lispworks 'lw:simple-char)
                                         (if-does-not-exist :error)
                                         (external-format *external-format*))
  (let* ((merged-pathname (merge-pathnames pathname
                                           *default-template-pathname*))
         (file-write-date (or *no-cache-check*
                              (file-write-date merged-pathname))))
    (destructuring-bind (hashed-printer . creation-date)
        ;; see if a printer for this pathname is in the cache
        (or (gethash merged-pathname *printer-hash*)
            '(nil . nil))
      (when (and hashed-printer
                 ;; and if we may use it
                 (not force)
                 ;; and if it's not too old (or maybe we don't have to
                 ;; check)
                 (or *no-cache-check*
                     (and file-write-date
                          (<= file-write-date creation-date))))
        (return-from create-template-printer hashed-printer))
      (let ((new-printer
              ;; push this pathname onto stack of included files (so
              ;; to say) to make sure a file can't include itself
              ;; recursively
              (let ((*included-files* (cons merged-pathname
                                            *included-files*))
                    (*external-format* external-format))
                (with-open-file (*standard-input* merged-pathname
                                 :direction :input
                                 :if-does-not-exist if-does-not-exist
                                 :element-type element-type
                                 :external-format external-format)
                  (%create-template-printer-aux nil nil)))))
        ;; cache newly created printer (together with current time)
        (unless (eq force :do-not-cache)
          (setf (gethash merged-pathname *printer-hash*)
                  (cons new-printer (get-universal-time))))
        ;; optionally issue a warning
        (when *warn-on-creation*
          (warn "New template printer for ~S created" merged-pathname))
        new-printer))))

(defgeneric fill-and-print-template (template/printer values
                                     &key stream
                                     &allow-other-keys)
  (:documentation "Fills the template denoted by TEMPLATE/PRINTER with
VALUES and print it to STREAM. If TEMPLATE/PRINTER is a function uses
it as if it were a template printer, otherwise creates a printer \(or
pull one out of the cache) with CREATE-TEMPLATE-PRINTER. Optional
keyword arguments are given to CREATE-TEMPLATE printer and can only be
used if TEMPLATE/PRINTER is a pathname."))

(defmethod fill-and-print-template ((function function) values
                                    &rest rest
                                    &key (stream *default-template-output*))
  (remf rest :stream)
  (when rest
    (signal-template-invocation-error
     "This method doesn't accept keyword arguments other than STREAM"))
  (let ((*template-output* stream))
    (funcall function values)))

(defmethod fill-and-print-template ((string string) values
                                    &rest rest
                                    &key (stream *default-template-output*))
  (remf rest :stream)
  (when rest
    (signal-template-invocation-error
     "This method doesn't accept keyword arguments other than STREAM"))
  (let ((*template-output* stream))
    (funcall (create-template-printer string) values)))

(defmethod fill-and-print-template ((input-stream stream) values
                                    &rest rest
                                    &key (stream *default-template-output*))
  (remf rest :stream)
  (when rest
    (signal-template-invocation-error
     "This method doesn't accept keyword arguments other than STREAM"))
  (let ((*template-output* stream))
    (funcall (create-template-printer input-stream) values)))

(defmethod fill-and-print-template ((pathname pathname) values
                                    &rest rest
                                    &key (stream *default-template-output*))
  (remf rest :stream)
  (let ((*template-output* stream))
    (funcall (apply #'create-template-printer pathname rest) values)))

(defun clear-template-cache ()
  "Complete clears all template printers from the cache."
  (clrhash *printer-hash*)
  (values))

(defun delete-from-template-cache (pathname)
  "Deletes the template printer denoted by PATHNAME from the
cache. Returns true if such a printer existed, false otherwise."
  (remhash (merge-pathnames pathname
                            *default-template-pathname*)
           *printer-hash*))
