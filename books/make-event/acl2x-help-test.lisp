(in-package "ACL2")

(include-book "acl2x-help")

(make-event
 (er-progn
  (thm (equal (append (append x y) z)
              (append x y z)))
  (value '(maybe-skip-proofs
           (defthm app-assoc
             (equal (append (append x y) z)
                    (append x y z)))))))

; Make sure that we don't elide local events arising from make-event when
; writing to the .acl2x file.

(local
 (make-event
  '(defun f1 (x) x)))

(local (in-theory (disable f1)))

(make-event
 '(local
   (defun f2 (x) x)))

(local (in-theory (disable f2)))

(encapsulate
 ()
 (progn (local (defun g1 (x) x))
        (defun g2 (x) x)))
