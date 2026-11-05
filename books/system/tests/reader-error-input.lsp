; See: https://github.com/acl2/acl2/issues/2099

; A reader error while reading this file should not discard the commands that
; follow (run-script "reader-error") in reader-error-book.acl2.  When cert.pl
; certifies reader-error-book, ACL2 reads those commands, including the
; certify-book command, from its standard input.

(in-package "ACL2")

(defun f1 (x) x)

; A reader error at the end of a top-level form, so that reading continues
; with the next form.

#.*no-such-constant*

(defun f2 (x) x)

(defun f3 (x) (list (f1 x) (f2 x)))
