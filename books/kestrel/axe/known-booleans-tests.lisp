(in-package "ACL2")

(include-book "std/testing/eval" :dir :system) ;for ensure-soft-error
(include-book "known-booleans")

(defun foo (x y z)
  (if (< x (+ y z))
      t
    nil))

(add-known-boolean foo)
(add-known-boolean foo) ;okay to do it twice

(ensure-soft-error (add-known-boolean len)) ; len does not return a boolean

(ensure-soft-error (add-known-boolean dfdfdg)) ;undefined function

(ensure-soft-error (add-known-boolean translate)) ; not in logic mode
