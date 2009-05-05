(in-package "ACL2")

; In order to avoid seeing the following message twice, be sure that there is
; no compiled file for top.lisp.  The standard "make" procedure ensures this
; through top.acl2.
(value-triple
 (cw "~%To turn on non-linear arithmetic:~|~%~Y01"
     '(set-default-hints '((nonlinearp-default-hint
                            stable-under-simplificationp hist pspv)))
     nil)
 :on-skip-proofs t)
