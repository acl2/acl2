; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann (but adapted from email by Sol Swords)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This test, without the local, is essentially from Sol Swords.  Below, "fahs"
; comes from the filename.  It failed to certify before mid-February, 2021,
; with the error message, "Fast alist stolen by
; HL-HSPACE-RESTORE-FAL-FOR-SERIALIZE."  The error from Sol's original test was
; as follows.

#||
* Step 5:  Compile the functions defined in 
"/Users/kaufmann/Dropbox/fh/acl2/patches/stolen-alist-2020-02/test-from-sol.lisp".


Writing book expansion file, /Users/kaufmann/Dropbox/fh/acl2/patches/stolen-
alist-2020-02/test-from-sol@expansion.lsp.
*****************************************************************
Fast alist stolen by HL-HSPACE-RESTORE-FAL-FOR-SERIALIZE.
See the documentation for fast alists for how to fix the problem,
or suppress this warning message with
  (SET-SLOW-ALIST-ACTION NIL)
||#

; The fix is to avoid get-slow-alist-action during the compilation phase of
; certify-book, which includes reading the expansion file.  Not tested here,
; but worth testing, is to certify after (assign save-expansion-file t) and
; then, after deleting the compiled file, run (include-book
; "fast-alist-hons-copy" :load-compiled-file :comp).  That now works because
; include-book-fn1 binds *defeat-slow-alist-action* to 'stolen.  That's weaker
; than binding to t but safer.

(in-package "ACL2")

(make-event
 `(defconst *fahc* ',(make-fast-alist
                      (hons-copy '(("a" . "b"))))))
