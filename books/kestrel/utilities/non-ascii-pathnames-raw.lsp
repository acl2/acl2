; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(or (and (eq (f-get-global 'host-lisp *the-live-state*) :ccl)
         (not (eq (os (w *the-live-state*)) :mswindows)))

; For now we implement this utility only for CCL, and not on Windows (where we
; have seen an error).  For SBCL it seems possible that
; acl2-string-to-filename, in place of the call of
; ccl::decode-string-from-octets, we could use:

;            (sb-ext::octets-to-string
;             (coerce x '(vector (unsigned-byte 8)))
;             :external-format :utf-8)

; But there may be other issues for SBCL.  For example, the following caused an
; error on a Mac:

;   touch $'\xe2\x82\xac'
;   sbcl
;   (directory "./*")

; The error message said the following.

;  :ASCII c-string decoding error: the octet sequence #(226) cannot be decoded.

; Presumably this is solvable, but let's put off solving this until it's
; needed.

    (error "Attempted to load non-ascii-pathnames-raw.lsp in other than CCL!"))

(setq *check-namestring*

; Set this back to t to recover original behavior.

      nil)

(defun seven-bit-chars-stringp (s)
  (loop for i from 0 to (1- (length s))
        do (when (> (char-code (char s i)) 127)
             (return nil))
        finally (return t)))

(defun acl2-string-to-filename (x &optional error-p)

  (assert (not (equal x "")))

; X is a string other than "", which is returned unchanged if it is a valid
; filename for the current filesystem.  In particular, the return value is x if
; x has only characters with code at most 127.  Otherwise, if the sequence of
; bytes (i.e., char-code values) in x encodes a filename string on the current
; platform, then that string is returned.  If they don't, then nil is returned
; unless error-p is true, in which case an error is signalled.

; Example: Suppose you create a file in bash as follows.

;   touch $'\xe2\x82\xac'

; You might see the resulting filename as the euro sign if you list the current
; directory using "ls" on linux or a Mac.

; We can form a Lisp string directly from those bytes as follows.

;   (coerce (list (code-char #xE2) (code-char #x82) (code-char #xAC)) 'string)

; Regardless of the appearance of this string (perhaps as a euro sign), it is
; suitable input to the present function, whose output will be a filename for
; the given file, suitable for input to Common Lisp functions such as
; file-write-date.  Here is an example to be evaluated after running the
; "touch" command above; we have checked that this CCL log looks the same in
; Linux as on the Mac.

;   ? (file-write-date
;      (acl2-string-to-filename
;       (coerce (list (code-char #xE2) (code-char #x82) (code-char #xAC)) 'string)))
;   3674228526
;   ?

; If *check-namestring* is true (note that t is the default), or if every
; character code in x is at most 127, then we simply return x.  The remaining
; comments below assume that *check-namestring* is nil.

  (when (or *check-namestring*
            (seven-bit-chars-stringp x))
    (return-from acl2-string-to-filename x))

  (let* ((octets ; X is an ACL2 string, so all its char-codes are under 256.
          (loop for i from 0 to (1- (length x))
                collect (char-code (char x i))))
         (s0 (ignore-errors
               (ccl::decode-string-from-octets
                (coerce octets '(vector (unsigned-byte 8)))
                :external-format (ccl::pathname-encoding-name))))
         (s (if (equal s0 "") nil s0)))
    (or s
        (and error-p
             (error "For ~s, unable to decode octet sequence: ~s"
                    `(acl2-string-to-filename ,x)
                    octets)))))

(defun filename-to-acl2-string (s &optional error-p)

; This is an inverse of acl2-string-to-filename.  Thus, the return value is an
; ACL2 string, but the string input s might have characters with codes
; exceeding 255.  See the definition of acl2-string-to-filename for more
; comments.

  (when (or *check-namestring*
            (seven-bit-chars-stringp s))
    (return-from filename-to-acl2-string s))

; Next, we check that for the presence of a character in s that has attributes,
; since that would make it impossible for acl2-string-to-filename to invert
; filename-to-acl2-string.  We'll check that separately anyhow, but the
; following error gives more information.

  (loop for i from 0 to (1- (length s))
        when (let ((c (char s i)))
               (not (eql c (code-char (char-code c)))))
        do
        (if error-p
            (error "For ~s, encountered a character c with char-code ~s, ~
                    namely c = ~s, such that (eql c (code-char (char-code ~
                    c))) is false."
                    `(filename-to-acl2-string ,s)
                    (char-code c)
                    c)
          (return-from filename-to-acl2-string nil)))

  (let* ((octets (ignore-errors (ccl::encode-string-to-octets
                                 s
                                 :external-format (ccl:pathname-encoding-name)))))
    (cond
     (octets
      (let ((result (coerce (loop for i from 0 to (1- (length octets))
                                  collect (code-char (aref octets i)))
                            'string)))
        (cond
         ((equal (acl2-string-to-filename result nil) s)
          result)
         (t (error "For ~s, unable to encode string to octets because the ~
                    application of acl2-string-to-filename to the result does ~
                    not produce the original string."
                   `(filename-to-acl2-string ,s))))))
     (t (and error-p
             (error "For ~s, unable to encode string to octets: ~s"
                    `(filename-to-acl2-string ,s)
                    octets))))))

; A nice little test:
(assert
 (let* ((acl2-string
         (coerce (list (code-char #xE2) (code-char #x82) (code-char #xAC) ; euro
                       #\a #\b
                       (code-char #xE2) (code-char #x82) (code-char #xAC) ; euro
                       #\C)
                 'string))
        (filename-string (acl2-string-to-filename acl2-string)))
   (equal acl2-string (filename-to-acl2-string filename-string))))

#-acl2-loop-only
(defun pathname-unix-to-os (str state)

; Here we modify the definition of the corresponding ACL2 source function by
; adding a call of acl2-string-to-filename.

; This function takes an ACL2 pathname and converts it to an OS pathname; see
; the Essay on Pathnames.  In the case of :mswindows, the ACL2 filename may or
; may not start with the drive, but the result definitely does.

  #+(and ccl mswindows)

; We believe that CCL 1.2 traffics in Unix-style pathnames, so it would be a
; mistake to convert them to use #\\, because then (for example) probe-file may
; fail.  However, we will allow Windows-style pathnames for CCL Versions 1.3
; and beyond, based on the following quote from
; http://trac.clozure.com/ccl/wiki/WindowsNotes (4/30/09):

;   Windows pathnames can use either forward-slash or backward-slash characters
;   as directory separators. As of the 1.3 release, CCL should handle
;   namestrings which use either forward- or backward-slashes; some prereleases
;   and release-candidates generally had difficulty with backslashes.

  (when (not (ccl-at-least-1-3-p))
    (return-from pathname-unix-to-os str))

  (if (equal str "")
      str
    (let* ((os (os (w state)))
           (str-orig str)
           (str (acl2-string-to-filename str t)))
      (case os
        (:unix str)
        (:mswindows
         (let ((sep #\\))
           (if (position sep str)
               (illegal 'pathname-unix-to-os
                        "Unable to convert pathname ~p0 for OS ~p1 because ~
                         character ~p2 occurs in that pathname string at ~
                         position ~p3."
                        (list (cons #\0 str-orig)
                              (cons #\1 os)
                              (cons #\2 sep)
                              (cons #\3 (position sep str))))
             (let* ((sep-is-first (eql (char str 0) *directory-separator*))
                    (str0 (substitute sep *directory-separator* str)))
               (if sep-is-first
                   (string-append (mswindows-drive nil state)
                                  str0)
                 str0)))))
        (otherwise (os-er os 'pathname-unix-to-os))))))

#-acl2-loop-only
(defun pathname-os-to-unix (str os state)

; Warning: Keep this in sync with the corresponding redefinition in file
; non-ascii-pathnames-raw.lsp, under books/kestrel/.

; This function takes an OS pathname and converts it to an ACL2 pathname; see
; the Essay on Pathnames.

  (if (equal str "")
      str
    (let ((result
           (case os
             (:unix str)
             (:mswindows
              (let* ((sep #\\)
                     (str0 (substitute *directory-separator* sep str)))
                (cond
                 ((and (eq os :mswindows)
                       (eql (char str0 0) *directory-separator*))

; Warning: Do not append the drive if there is already a drive present.  We
; rely on this in LP, where we initialize state global 'system-books-dir based
; on environment variable ACL2_SYSTEM_BOOKS, which might already have a drive
; that differs from that of the user.

                  (string-append (mswindows-drive nil state)
                                 str0))
                 (t
                  str0))))
             (otherwise (os-er os 'pathname-os-to-unix)))))
      (let ((msg (and result
                      *check-namestring* ; always true unless a ttag is used
                      (bad-lisp-stringp result))))
        (cond (msg (interface-er
                    "Illegal ACL2 pathname, ~x0:~%~@1"
                    result msg))
              (t (and result
                      (filename-to-acl2-string ; identity if *check-namestring*
                       result t))))))))


