; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; If you get an error certifying this book, then the output should indicate
; where the problem is.  For example, suppose you see the following.
#|
Checking defthm...
  ERROR: Unexpected line(s):
>   (with-ctx-summarized xx
|#
; That indicates a mismatch between ACL2 source file defthm.lisp and patch file
; books/kestrel/acl2data/gather/patch-defthm.lsp.  The expectation is that
; comment lines and blank lines are allowed to differ and the source file may
; contain extra lines, but all other lines in the patch file that are not in
; the source file should end with ";patch;".  Any other differences indicate a
; change in the ACL2 source file (in this case, defthm.lisp) that invalidated
; this property.  The fix is to look carefully at a comparison of the patch
; file with corresponding definitions in the source file, and update the patch
; file accordingly.

; In some cases, the patches for an ACL2 source file F are split into more than
; one patch file patch-F-n.lsp (n=1,2,...).  For example, as of this writing
; the patches for ACL2 source file rewrite.lisp are split into
; patch-rewrite-1.lsp and patch-rewrite-2.lsp.  The reason is that the use of
; diff seemed to require this; see patch-diff.sh.

(in-package "ACL2")

(defttag t)

(make-event
 (prog2$ (sys-call (concatenate 'string (cbd) "patch-diff.sh") nil)
         (mv-let (status state)
           (sys-call-status state)
           (value `(defconst *run-tests-status* ,status)))))

(make-event
 (if (equal *run-tests-status* 0)
     '(value-triple :success)
   (er hard 'run-tests
       "Failed!  See file~|~s0patch-diff.lisp~|for a discussion of how to ~
        fix this problem."
       (cbd))))
