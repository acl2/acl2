(in-package "ACL2")

; (defun bad (x) (mac (x)))

; (defun r3 (x) x)

(defun g (x) x)

(local (make-event (list 'defun 'g2 '(x) 'x)))

(encapsulate
 ()
 (local (make-event (list 'defun 'g3 '(x) 'x)))
 (defun g4 (x) x)
 (make-event (er-progn
; We should not be seeing this make-event when another book includes sub, since
; in that case sub.acl2 will contain the expansion.  For that matter, we
; shouldn't be doing make-event expansion when including this book, either.
              (cond ((global-val 'include-book-path (w state))
                     (er soft 'testing-pcert
                         "Unexpected error; see books/system/pcert/sub.lisp."))
                    (t (value nil)))
              (value (list 'defun 'g5 '(x) 'x)))))

(defun h (x)
  (if (consp x) (h (cddr x)) x))
