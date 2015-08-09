(in-package "ACL2")

; Not in :expansion-alist-nonlocal of .pcert0 file, because there is no local
; elision.
; [1]
(make-event '(defun f (x) x))

; In :expansion-alist-nonlocal of .pcert0 file, because there is local
; elision.
; [2]
(encapsulate
 ()
 (local (make-event '(defun g (x) x)))
 (defun h (x) x))

; Not in :expansion-alist-nonlocal of .pcert0 file, because
; unelided expansion is already in .acl2x file.
; [3]
(encapsulate
 ()
 (local (make-event '(defun g2 (x) x)))
 (defun h2 (x) x))

; Not in :expansion-alist-nonlocal of .pcert0 file, even there is local elision
; for this form in the .acl2x file as compared to the form below, because the
; form below is actually irrelevant.
; [4]
(encapsulate
 ()
 (local (make-event '(defun g3 (x) x)))
 (defun h3 (x) x))
