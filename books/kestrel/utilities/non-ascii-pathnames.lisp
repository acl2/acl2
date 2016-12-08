; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; NOTE: Although this book should certify regardless of the host Lisp, it only
; has the desired behavior in CCL.  That could likely be extended as needed.

; See non-ascii-pathnames-raw.lsp for comments that explain this utility.  Once
; it's been used a bit, it would be good to document it with xdoc.  For now,
; here is a brief explanation, followed by an example that illustrates what's
; going on.

; ACL2 characters have char-codes not exceeding 255.  However, filenames can
; have characters with larger char-codes.  ACL2 "out of the box" cannot deal
; with such filenames, but this book provides such support.  The key notions
; are those of "ACL2 pathname" and "OS pathname", as discussed in the Essay on
; Pathnames in ACL2 source file interface-raw.lisp.  An OS pathname is a string
; that the underlying Lisp uses for a pathname.  But ACL2's interface to the
; file system uses ACL2 pathnames, which are valid ACL2 strings.  For ACL2 out
; of the box, the OS pathname and ACL2 pathname are the same when the OS
; pathname is a valid ACL2 pathname.  After including this book, however, these
; are only guaranteed to be the same if moreover, all characters in the OS
; pathname are 7-bit characters.  (As of this writing, it's not clear whether
; 8-bit characters would suffice; quite possibly that's the case, but we are
; being conservative.)  Otherwise, the ACL2 pathname is a different string,
; which we think of -- and this might be true -- as the string of 8-bit
; characters whose char-codes are the bytes (in order) in the OS pathname.

; In a nutshell: the way to deal with an OS pathname that is not a valid ACL2
; string is to include this book, translate it to an ACL2 pathname (for
; example, in raw Lisp as shown below), and then use that ACL2 pathname within
; ACL2.

#|| EXAMPLE:

# It may be best to start in a fresh directory.
# It's OK to skip the bash command if you are already running bash.
bash
# Create a file whose name probably looks like a Euro sign.
touch $'\xe2\x82\xac'
# Start ACL2 here, based on CCL.  Then:
(include-book  ;break line to fool dependency scanner
 "kestrel/utilities/non-ascii-pathnames" :dir :system)
(set-raw-mode-on!)
# Next we use a new utility, which converts OS pathnames to ACL2 pathnames,
# to store the ACL2 pathname of the new file into a global.
(assign my-file ; Make an ACL2 pathname from the OS pathname of the new file.
        (filename-to-acl2-string (pathname-name (car (directory "./*")))))
(assert (equal (length (@ my-file)) 3)) ; should return nil, not an error
(set-raw-mode nil)
(mv-let
  (channel state)
  (open-input-channel (@ my-file) :object state)
  (cond
   ((null channel) (value :failed))
   (t (pprogn (close-input-channel channel state)
              (value :ok)))))
||#

(in-package "ACL2")

(include-book "tools/include-raw" :dir :system)

(defttag :non-ascii-pathnames)

; (depends-on "non-ascii-pathnames-raw.lsp")
(make-event
 (er-progn (if (and (eq (@ host-lisp) :ccl)
                    (not (eq (os (w state)) :mswindows)))
               (include-raw "non-ascii-pathnames-raw.lsp")
             (value (cw "Skipping include-raw for non-ascii-pathnames-raw.lsp ~
                         (supported in non-Windows CCL only).")))
           (value '(value-triple nil)))
 :check-expansion t)
