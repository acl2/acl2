(in-package "DJVM")
(include-book "../M6-DJVM-shared/jvm-thread")


;;; Mon Mar 29 20:57:27 2004
;;; The following is used by DJVM so need to be guard verified. 
(acl2::set-verify-guards-eagerness 2)

;; (defun method-stackMap (Method)
;;   (declare (xargs :guard (and (wff-method-decl method)
;;                               (wff-code (method-code method)))))
;;   (code-stackmaps (method-code method)))

;; (defun method-maxStack (Method)
;;   (declare (xargs :guard (and (wff-method-decl method)
;;                               (wff-code (method-code method)))))
;;    (code-max-Stack (method-code method)))

;; (defun method-maxLocals (Method)
;;   (declare (xargs :guard (and (wff-method-decl method)
;;                               (wff-code (method-code method)))))
;;    (code-max-local (method-code method)))

;; (defun method-handlers (Method)
;;   (declare (xargs :guard (and (wff-method-decl method)
;;                               (wff-code (method-code method)))))
;;    (code-handlers (method-code method)))

(acl2::set-verify-guards-eagerness 0)
