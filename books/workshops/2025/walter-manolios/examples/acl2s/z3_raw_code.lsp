(load "~/quicklisp/setup.lisp")

(pushnew (truename "../../") ql:*local-project-directories*)
(ql:register-local-projects)
(ql:quickload :cl-z3)

;; We need to define these fns in a package that ACL2 knows about so
;; that they can be referenced in defun-bridge.

(defun z3-assert-fn (types query)
  (z3::z3-assert-fn types query))

(defun z3-check-sat ()
  (z3:check-sat))

(defun z3-get-model-as-assignment ()
  (z3:get-model-as-assignment))

(defun z3-solver-init ()
  (z3:solver-init))
