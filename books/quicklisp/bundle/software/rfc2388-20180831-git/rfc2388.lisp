;;;; -*- mode: LISP; package: RFC2388 -*-
;;;; Copyright (c) 2003 Janis Dzerins
;;;; Modifications for TBNL Copyright (c) 2004 Michael Weber and Dr. Edmund Weitz
;;;;
;;;; Redistribution and use in source and binary forms, with or without
;;;; modification, are permitted provided that the following conditions
;;;; are met:
;;;; 1. Redistributions of source code must retain the above copyright
;;;;    notice, this list of conditions and the following disclaimer.
;;;; 2. Redistributions in binary form must reproduce the above copyright
;;;;    notice, this list of conditions and the following disclaimer in the
;;;;    documentation and/or other materials provided with the distribution.
;;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
;;;; IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
;;;; OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
;;;; IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
;;;; INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
;;;; NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;;;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;;;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;;;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
;;;; THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#+xcvb (module (:depends-on ("packages")))

(in-package :rfc2388)



;;; Utility functions


(defun lwsp-char-p (char)
  "Returns true if CHAR is a linear-whitespace-char (LWSP-char).  Either
   space or tab, in short."
  (or (char= char #\space)
      (char= char #\tab)))


;;; *** This actually belongs to RFC2046
;;;
(defun read-until-next-boundary (stream boundary &optional discard out-stream)
  "Reads from STREAM up to the next boundary.  Returns two values: read
   data (nil if DISCARD is true), and true if the boundary is not last
   (i.e., there's more data)."
  ;; Read until [CRLF]--boundary[--][transport-padding]CRLF
  ;; States:     1 2  345        67  8                 9 10
  ;;
  ;; *** This will WARN like crazy on some bad input -- should only do each
  ;; warning once.

  (let ((length (length boundary)))
    (unless (<= 1 length 70)
      (warn "Boundary has invalid length -- must be between 1 and 70, but is: ~S" length))
    (when (lwsp-char-p (schar boundary (1- length)))
      (warn "Boundary has trailing whitespace: ~S" boundary)))

  (flet ((run (result)
           "This one writes everything up to a boundary to RESULT stream,
            and returns false if the closing delimiter has been read, and
            true otherwise."
           (let ((state 1)
                 (boundary-index 0)
                 (boundary-length (length boundary))
                 (closed nil)
                 (queued-chars (make-string 4))
                 (queue-index 0)
                 char
                 (leave-char nil))

             (flet ((write-queued-chars ()
                      (dotimes (i queue-index)
                        (write-char (schar queued-chars i) result))
                      (setf queue-index 0))

                    (enqueue-char ()
                      (setf (schar queued-chars queue-index) char)
                      (incf queue-index)))

               (loop

                 (if leave-char
                     (setq leave-char nil)
                     (setq char (read-char stream)))

                  #-(and)
                  (format t "~&S:~D QI:~D BI:~2,'0D CH:~:[~;*~]~S~%"
                          state queue-index boundary-index leave-char char)

                 (case state
                   (1 ;; optional starting CR
                    (cond ((char= char #\return)
                           (enqueue-char)
                           (setq state 2))
                          ((char= char #\-)
                           (setq leave-char t
                                 state 3))
                          (t
                           (write-char char result))))

                   (2 ;; optional starting LF
                    (cond ((char= char #\linefeed)
                           (enqueue-char)
                           (setq state 3))
                          (t
                           (write-queued-chars)
                           (setq leave-char t
                                 state 1))))

                   (3 ;; first dash in dash-boundary
                    (cond ((char= char #\-)
                           (enqueue-char)
                           (setq state 4))
                          (t
                           (write-queued-chars)
                           (setq leave-char t
                                 state 1))))

                   (4 ;; second dash in dash-boundary
                    (cond ((char= char #\-)
                           (enqueue-char)
                           (setq state 5))
                          (t
                           (write-queued-chars)
                           (setq leave-char t
                                 state 1))))

                   (5 ;; boundary
                    (cond ((char= char (schar boundary boundary-index))
                           (incf boundary-index)
                           (when (= boundary-index boundary-length)
                             (setq state 6)))
                          (t
                           (write-queued-chars)
                           (write-sequence boundary result :end boundary-index)
                           (setq boundary-index 0
                                 leave-char t
                                 state 1))))

                   (6 ;; first dash in close-delimiter
                    (cond ((char= char #\-)
                           (setq state 7))
                          (t
                           (setq leave-char t)
                           (setq state 8))))

                   (7 ;; second dash in close-delimiter
                    (cond ((char= char #\-)
                           (setq closed t
                                 state 8))
                          (t
                           ;; this is a strange situation -- only two dashes, linear
                           ;; whitespace or CR is allowed after boundary, but there was
                           ;; a single dash...  One thing is clear -- this is not a
                           ;; close-delimiter.  Hence this is garbage what we're looking
                           ;; at!
                           (warn "Garbage where expecting close-delimiter!")
                           (setq leave-char t)
                           (setq state 8))))

                   (8 ;; transport-padding (LWSP* == [#\space #\tab]*)
                    (cond ((lwsp-char-p char)
                           ;; ignore these
                           )
                          (t
                           (setq leave-char t)
                           (setq state 9))))

                   (9 ;; CR
                    (cond ((char= char #\return)
                           (setq state 10))
                          (t
                           (warn "Garbage where expecting CR!"))))

                   (10 ;; LF
                    (cond ((char= char #\linefeed)
                           ;; the end
                           (return))
                          (t
                           (warn "Garbage where expecting LF!")))))))
             (not closed))))

    (if discard
        (let ((stream (make-broadcast-stream)))
          (values nil (run stream)))
        (let* ((stream (or out-stream (make-string-output-stream)))
               (closed (run stream)))
          (values (or out-stream (get-output-stream-string stream))
                  closed)))))


(defun make-tmp-file-name ()
  (if (find-package :tbnl)
      (funcall (find-symbol #.(string '#:make-tmp-file-name) :tbnl))
      (error "WRITE-CONTENT-TO-FILE keyword argument to PARSE-MIME is supported in TBNL only at the moment.")))



;;; Header parsing


(defstruct (header (:type list)
                   (:constructor make-header (name value parameters)))
  name
  value
  parameters)


(defun skip-linear-whitespace (string &key (start 0) end)
  "Returns the position of first non-linear-whitespace character in STRING
   bound by START and END."
  (position-if-not #'lwsp-char-p string :start start :end end))


(defgeneric parse-header (source &optional start-state)
  (:documentation "Parses SOURCE and returs a single MIME header.

Header is a list of the form (NAME VALUE PARAMETERS), PARAMETERS
is a list of (NAME . VALUE)"))


(defmethod parse-header ((source string) &optional (start-state :name))
  (with-input-from-string (in source)
    (parse-header in start-state)))


;;; *** I don't like this parser -- it will have to be rewritten when I
;;; make my state-machine parser-generator macro!
;;;
(defmethod parse-header ((stream stream) &optional (start-state :name))
  "Returns a MIME part header, or NIL, if there is no header.  Header is
   terminated by CRLF."
  (let ((state (ecase start-state
                 (:name 1)
                 (:value 2)
                 (:parameters 3)))
        (result (make-string-output-stream))
        char
        (leave-char nil)
        name
        value
        parameter-name
        parameters)

    (labels ((skip-lwsp (next-state)
               (loop
                 do (setq char (read-char stream nil nil))
                 while (and char (lwsp-char-p char)))
               (setq leave-char t
                     state next-state))

             (collect-parameter ()
               (push (cons parameter-name
                           (get-output-stream-string result))
                     parameters)
               (setq parameter-name nil)
               (skip-lwsp 3))

             (token-end-char-p (char)
               (or (char= char #\;)
                   (lwsp-char-p char))))

      (loop

        (if leave-char
            (setq leave-char nil)
            (setq char (read-char stream nil nil)))

        ;; end of stream
        (unless char
          (return))

        (when (char= #\return char)
          (setq char (read-char stream nil nil))
          (cond ((or (null char)
                     (char= #\linefeed char))
                 ;; CRLF ends the input
                 (return))
                (t
                 (warn "LINEFEED without RETURN in header.")
                 (write-char #\return result)
                 (setq leave-char t))))

        #-(and)
        (format t "~&S:~,'0D CH:~:[~;*~]~S~%"
                state leave-char char)

        (ecase state
          (1 ;; NAME
           (cond ((char= char #\:)
                  ;; end of name
                  (setq name (get-output-stream-string result))
                  (skip-lwsp 2))
                 (t
                  (write-char char result))))

          (2 ;; VALUE
           (cond ((token-end-char-p char)
                  (setq value (get-output-stream-string result))
                  (skip-lwsp 3))
                 (t
                  (write-char char result))))

          (3 ;; PARAMETER name
           (cond ((char= #\= char)
                  (setq parameter-name (get-output-stream-string result)
                        state 4))
                 (t
                  (write-char char result))))

          (4 ;; PARAMETER value start
           (cond ((char= #\" char)
                  (setq state 5))
                 (t
                  (setq leave-char t
                        state 7))))

          (5 ;; Quoted PARAMETER value
           (cond ((char= #\" char)
                  (setq state 6))
                 (t
                  (write-char char result))))

          (6 ;; End of quoted PARAMETER value
           (cond ((token-end-char-p char)
                  (collect-parameter))
                 (t
                  ;; no space or semicolon after quoted parameter value
                  (setq leave-char t
                        state 3))))

          (7 ;; Unquoted PARAMETER value
           (cond ((token-end-char-p char)
                  (collect-parameter))
                 (t
                  (write-char char result))))))

      (case state
        (1
         (setq name (get-output-stream-string result)))
        (2
         (setq value (get-output-stream-string result)))
        ((3 4)
         (let ((name (get-output-stream-string result)))
           (unless (zerop (length name))
             (warn "Parameter without value in header.")
             (push (cons name nil) parameters))))
        ((5 6 7)
         (push (cons parameter-name (get-output-stream-string result)) parameters))))

    (if (and (or (null name)
                 (zerop (length name)))
             (null value)
             (null parameters))
        nil
        (make-header name value parameters))))



;;; _The_ MIME parsing


(defgeneric parse-mime (source boundary &key write-content-to-file)
  (:documentation
   "Parses MIME entities, returning them as a list.  Each element in the
    list is of form: (body headers), where BODY is the contents of MIME
    part, and HEADERS are all headers for that part.  BOUNDARY is a string
    used to separate MIME entities."))


(defstruct (content-type (:type list)
                         (:constructor make-content-type (super sub)))
  super
  sub)


(defun parse-content-type (string)
  "Returns content-type which is parsed from STRING."
  (let ((sep-offset (position #\/ string))
        (type (array-element-type string)))
    (if (numberp sep-offset)
        (make-content-type (make-array sep-offset
                                       :element-type type
                                       :displaced-to string)
                           (make-array (- (length string) (incf sep-offset))
                                       :element-type type
                                       :displaced-to string
                                       :displaced-index-offset sep-offset))
        (make-content-type string nil))))


(defun unparse-content-type (ct)
  "Returns content-type CT in string representation."
  (let ((super (content-type-super ct))
        (sub (content-type-sub ct)))
    (cond ((and super sub)
           (concatenate 'string super "/" sub))
          (t (or super "")))))

(defstruct (mime-part (:type list)
                      (:constructor make-mime-part (contents headers)))
  contents
  headers)


(defmethod parse-mime ((input string) separator &key (write-content-to-file t))
  (with-input-from-string (stream input)
    (parse-mime stream separator :write-content-to-file write-content-to-file)))


(defmethod parse-mime ((input stream) boundary &key (write-content-to-file t))
  ;; Find the first boundary.  Return immediately if it is also the last
  ;; one.
  (unless (nth-value 1 (read-until-next-boundary input boundary t))
    (return-from parse-mime nil))

  (let ((result ()))
    (loop
      (let ((headers (loop
                      for header = (parse-header input)
                      while header
                      when (string-equal "CONTENT-TYPE" (header-name header))
                      do (setf (header-value header) (parse-content-type (header-value header)))
                      collect header)))
        (let ((file-name (get-file-name headers)))
          (cond ((and write-content-to-file
                      file-name)
                 (let ((temp-file (make-tmp-file-name)))
                   (multiple-value-bind (text more)
                       (with-open-file (out-file (ensure-directories-exist temp-file)
                                                 :direction :output
                                                 ;; external format for faithful I/O
                                                 ;; see <http://cl-cookbook.sourceforge.net/io.html#faith>
                                                 #+(or :sbcl :lispworks :allegro :openmcl :clisp)
                                                 :external-format
                                                 #+sbcl :latin-1
                                                 #+:lispworks '(:latin-1 :eol-style :lf)
                                                 #+:allegro (excl:crlf-base-ef :latin1)
                                                 #+:openmcl '(:character-encoding :iso-8859-1
                                                              :line-termination :unix)
                                                 #+:clisp (ext:make-encoding :charset 'charset:iso-8859-1
                                                                             :line-terminator :unix))
                         (read-until-next-boundary input boundary nil out-file))
                     (declare (ignore text))
                     (when (and (stringp file-name)
                                (plusp (length file-name)))
                       (push (make-mime-part temp-file headers) result))
                     (when (not more)
                       (return)))))
                (t
                 (multiple-value-bind (text more)
                     (read-until-next-boundary input boundary)
                   (push (make-mime-part text headers) result)
                   (when (not more)
                     (return))))))))
    (nreverse result)))


(defun find-header (label headers)
  "Find header by label from set of headers."
  (find label headers :key #'rfc2388:header-name :test #'string-equal))


(defun find-parameter (name params)
  "Find header parameter by name from set of parameters."
  (assoc name params :test #'string-equal))


(defun content-type (part &key as-string)
  "Returns the Content-Type header of mime-part PART."
  (let ((header (find-header "CONTENT-TYPE" (mime-part-headers part))))
    (if header
        (if as-string
            (or (unparse-content-type (header-value header)) "")
            (header-value header))
        (when as-string ""))))


(defun find-content-disposition-header (headers)
  (find-if (lambda (header)
             (and (string-equal "CONTENT-DISPOSITION"
                                (rfc2388:header-name header))
                  (string-equal "FORM-DATA"
                                (rfc2388:header-value header))))
           headers))


(defun get-file-name (headers)
  (cdr (find-parameter "FILENAME"
                       (header-parameters (find-content-disposition-header headers)))))
