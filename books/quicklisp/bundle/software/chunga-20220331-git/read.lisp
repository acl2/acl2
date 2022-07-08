;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: CHUNGA; Base: 10 -*-
;;; $Header: /usr/local/cvsrep/chunga/read.lisp,v 1.22 2008/05/26 08:18:00 edi Exp $

;;; Copyright (c) 2006-2010, Dr. Edmund Weitz.  All rights reserved.

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

(in-package :chunga)

(defun signal-unexpected-chars (stream last-char expected-chars)
  "Signals an error that LAST-CHAR was read although one of
EXPECTED-CHARS was expected.  \(Note that EXPECTED-CHARS, despite its
name, can also be a single character instead of a list).  Calls
*CURRENT-ERROR-FUNCTION* if it's not NIL, or uses
*CURRENT-ERROR-MESSAGE* otherwise."
  (cond (*current-error-function*
         (funcall *current-error-function* last-char expected-chars))
        (t
         (error 'syntax-error
                :stream stream
                :format-control "~@[~A~%~]~:[End of file~;Read character ~:*~S~], ~
but expected ~:[a member of ~S~;~S~]."
                :format-arguments (list *current-error-message*
                                        last-char
                                        (atom expected-chars)
                                        expected-chars)))))

(defun charp (char)
  "Returns true if the Lisp character CHAR is a CHAR according to RFC 2616."
  (<= 0 (char-code char) 127))

(defun controlp (char)
  "Returns true if the Lisp character CHAR is a CTL according to RFC 2616."
  (or (<= 0 (char-code char) 31)
      (= (char-code char) 127)))

(defun separatorp (char)
  "Returns true if the Lisp character CHAR is a separator
according to RFC 2616."
  (find char #.(format nil " ()<>@,;:\\\"/[]?={}~C" #\Tab)
        :test #'char=))

(defun whitespacep (char)
  "Returns true if the Lisp character CHAR is whitespace
according to RFC 2616."
  (member char '(#\Space #\Tab) :test #'char=))

(defun token-char-p (char)
  "Returns true if the Lisp character CHAR is a token constituent
according to RFC 2616."
  (and (charp char)
       (not (or (controlp char)
                (separatorp char)))))

(defun assert-char (stream expected-char)
  "Reads the next character from STREAM and checks if it is the
character EXPECTED-CHAR.  Signals an error otherwise."
  (let ((char (read-char* stream)))
    (unless (char= char expected-char)
      (signal-unexpected-chars stream char expected-char))
    char))

(defun assert-crlf (stream)
  "Reads the next two characters from STREAM and checks if these
are a carriage return and a linefeed.  Signals an error
otherwise."
  (assert-char stream #\Return)
  (assert-char stream #\Linefeed))

(defun read-line* (stream &optional log-stream)
  "Reads and assembles characters from the binary stream STREAM until
a carriage return is read.  Makes sure that the following character is
a linefeed.  If *ACCEPT-BOGUS-EOLS* is not NIL, then the function will
also accept a lone carriage return or linefeed as an acceptable line
break.  Returns the string of characters read excluding the line
break.  Returns NIL if input ends before one character was read.
Additionally logs this string to LOG-STREAM if it is not NIL."
  (let ((result
         (with-output-to-string (line)
           (loop for char-seen-p = nil then t
                 for char = (read-char* stream nil)
                 for is-cr-p = (and char (char= char #\Return))
                 until (or (null char)
                           is-cr-p
                           (and *accept-bogus-eols*
                                (char= char #\Linefeed)))
                 do (write-char char line)
                 finally (cond ((and (not char-seen-p)
                                     (null char))
                                (return-from read-line* nil))
                               ((not *accept-bogus-eols*)
                                (assert-char stream #\Linefeed))
                               (is-cr-p
                                (when (eql (peek-char* stream) #\Linefeed)
                                  (read-char* stream))))))))
    (when log-stream
      (write-line result log-stream)
      (finish-output log-stream))
    result))

(defun trim-whitespace (string &key (start 0) (end (length string)))
  "Returns a version of the string STRING \(between START and END)
where spaces and tab characters are trimmed from the start and the
end.  Might return STRING."
  ;; optimized version to replace STRING-TRIM, suggested by Jason Kantz
  (declare (optimize
            speed
            (space 0)
            (debug 1)
            (compilation-speed 0)
            #+:lispworks (hcl:fixnum-safety 0)))
  (declare (string string))
  (let* ((start% (loop for i of-type fixnum from start below end
                       while (or (char= #\space (char string i))
                                 (char= #\tab (char string i)))
                       finally (return i)))
         (end% (loop for i of-type fixnum downfrom (1- end) to start
                     while (or (char= #\space (char string i))
                               (char= #\tab (char string i)))
                     finally (return (1+ i)))))
    (declare (fixnum start% end%))
    (cond ((and (zerop start%) (= end% (length string))) string)
          ((> start% end%) "")
          (t (subseq string start% end%)))))

(defun read-http-headers (stream &optional log-stream)
  "Reads HTTP header lines from STREAM \(except for the initial
status line which is supposed to be read already) and returns a
corresponding alist of names and values where the names are
keywords and the values are strings.  Multiple lines with the
same name are combined into one value, the individual values
separated by commas.  Header lines which are spread across
multiple lines are recognized and treated correctly.  Additonally
logs the header lines to LOG-STREAM if it is not NIL."
  (let (headers
        (*current-error-message* "While reading HTTP headers:"))
    (labels ((read-header-line ()
               "Reads one header line, considering continuations."
               (with-output-to-string (header-line)
                 (loop
                  (let ((line (trim-whitespace (read-line* stream log-stream))))
                    (when (zerop (length line))
                      (return))
                    (write-sequence line header-line)
                    (let ((next (peek-char* stream)))
                      (unless (whitespacep next)
                        (return)))
                    ;; we've seen whitespace starting a continutation,
                    ;; so we loop
                    (write-char #\Space header-line)))))
             (split-header (line)
               "Splits line at colon and converts it into a cons.
Returns NIL if LINE consists solely of whitespace."
               (unless (zerop (length (trim-whitespace line)))
                 (let ((colon-pos (or (position #\: line :test #'char=)
                                      (error 'syntax-error
                                             :stream stream
                                             :format-control "Couldn't find colon in header line ~S."
                                             :format-arguments (list line)))))
                   (cons (as-keyword (subseq line 0 colon-pos))
                         (trim-whitespace (subseq line (1+ colon-pos)))))))
             (add-header (pair)
               "Adds the name/value cons PAIR to HEADERS.  Takes
care of multiple headers with the same name."
               (let* ((name (car pair))
                      (existing-header (assoc name headers :test #'eq))
                      (existing-value (cdr existing-header)))
                 (cond (existing-header
                        (setf (cdr existing-header)
                              (format nil "~A~:[,~;~]~A"
                                      existing-value
                                      (and *treat-semicolon-as-continuation*
                                           (eq name :set-cookie)
                                           (ends-with-p (trim-whitespace existing-value) ";"))
                                      (cdr pair))))
                       (t (push pair headers))))))
      (loop for header-pair = (split-header (read-header-line))
            while header-pair
            do (add-header header-pair)))
    (nreverse headers)))

(defun skip-whitespace (stream)
  "Consume characters from STREAM until an END-OF-FILE is
encountered or a non-whitespace \(according to RFC 2616)
characters is seen.  This character is returned \(or NIL in case
of END-OF-FILE)."
  (loop for char = (peek-char* stream nil)
        while (and char (whitespacep char))
        do (read-char* stream)
        finally (return char)))

(defun read-token (stream)
  "Read characters from STREAM while they are token constituents
\(according to RFC 2616).  It is assumed that there's a token
character at the current position.  The token read is returned as
a string.  Doesn't signal an error \(but simply stops reading) if
END-OF-FILE is encountered after the first character."
  (with-output-to-string (out)
    (loop for first = t then nil
          for char = (if first
                       (peek-char* stream)
                       (or (peek-char* stream nil) (return)))
          while (token-char-p char)
          do (write-char (read-char* stream) out))))

(defun read-quoted-string (stream)
  "Reads a quoted string \(according to RFC 2616).  It is assumed
that the character at the current position is the opening quote
character.  Returns the string read without quotes and escape
characters."
  (read-char* stream)
  (with-output-to-string (out)
    (loop for char = (read-char* stream)
          until (char= char #\")
          do (case char
               (#\\ (write-char (read-char* stream) out))
               (#\Return (assert-char stream #\Linefeed)
                         (let ((char (read-char* stream)))
                           (unless (whitespacep char)
                             (signal-unexpected-chars stream char '(#\Space #\Tab)))))
               (otherwise (write-char char out))))))

(defun read-cookie-value (stream &key (separators ";"))
  "Reads a cookie parameter value from STREAM which is returned as a
string.  Simply reads until a semicolon is seen \(or an element of
SEPARATORS).  Also reads quoted strings if the first non-whitespace
character is a quotation mark \(as in RFC 2109)."
  (if (char= #\" (peek-char* stream))
      (read-quoted-string stream)
      (trim-whitespace
       (with-output-to-string (out)
         (loop for char = (peek-char* stream nil)
               until (or (null char) (find char separators :test #'char=))
               do (write-char (read-char* stream) out))))))

(defun read-name-value-pair (stream &key (value-required-p t) cookie-syntax)
  "Reads a typical \(in RFC 2616) name/value or attribute/value
combination from STREAM - a token followed by a #\\= character and
another token or a quoted string.  Returns a cons of name and value,
both as strings.  If VALUE-REQUIRED-P is NIL, the #\\= sign and the
value are optional.  If COOKIE-SYNTAX is true, uses READ-COOKIE-VALUE
internally."
  (skip-whitespace stream)
  (let ((name (if cookie-syntax
                (read-cookie-value stream :separators "=;")
                (read-token stream))))
    (skip-whitespace stream)
    (cons name
          (when (or value-required-p
                    (eql (peek-char* stream nil) #\=))
            (assert-char stream #\=)
            (skip-whitespace stream)
            (cond (cookie-syntax (read-cookie-value stream))
                  ((char= (peek-char* stream) #\") (read-quoted-string stream))
                  (t (read-token stream)))))))

(defun read-name-value-pairs (stream &key (value-required-p t) cookie-syntax)
  "Uses READ-NAME-VALUE-PAIR to read and return an alist of
name/value pairs from STREAM.  It is assumed that the pairs are
separated by semicolons and that the first char read \(except for
whitespace) will be a semicolon.  The parameters are used as in
READ-NAME-VALUE-PAIR.  Stops reading in case of END-OF-FILE
\(instead of signaling an error)."
  (loop for char = (skip-whitespace stream)
        while (and char (char= char #\;))
        do (read-char* stream)
        ;; guard against a stray semicolon at the end
        when (skip-whitespace stream)
        collect (read-name-value-pair stream
                                      :value-required-p value-required-p
                                      :cookie-syntax cookie-syntax)))
