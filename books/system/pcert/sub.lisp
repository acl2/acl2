(in-package "ACL2")

; (defun bad (x) (mac (x)))

; (defun r3 (x) x)

(defun g (x) x)

(local (make-event (list 'defun 'g2 '(x) 'x)))

(encapsulate
 ()
 (local (make-event (list 'defun 'g3 '(x) 'x)))
 (defun g4 (x) x)
 (make-event (list 'defun 'g5 '(x) 'x)))

(defun h (x)
  (if (consp x) (h (cddr x)) x))
