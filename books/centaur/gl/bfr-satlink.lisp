
(in-package "GL")

(include-book "bfr-sat")
(include-book "../aig/aig-sat")

(encapsulate
  (((gl-satlink-config) => *))
  (local (defun gl-satlink-config ()
           satlink::*default-config*))
  (defthm gl-satlink-config-constraint
    (satlink::config-p (gl-satlink-config))))

(defun gl-default-satlink-config ()
  (declare (xargs :guard t))
  (satlink::change-config satlink::*default-config*
                          :verbose nil))

(defattach gl-satlink-config gl-default-satlink-config)

(defun bfr-satlink (prop)
  (declare (xargs :guard t))
  (bfr-case
   :bdd (mv nil nil nil) ;; fail
   :aig
   (b* (((mv status env)
         (acl2::aig-sat prop :config (gl-satlink-config))))
     (case status
       (:sat (mv t t env))
       (:unsat (mv nil t nil))
       (t ;; failed
        (mv nil nil nil))))))

(defsection gl-satlink-mode
  :parents (modes reference)
  :short "GL: Use AIGs as the Boolean function representation and @(see
satlink) to solve queries."

  (defmacro gl-satlink-mode ()
    '(progn
       (defattach bfr-mode bfr-aig)
       (defattach bfr-counterex-mode bfr-counterex-alist)
       (defattach (bfr-sat bfr-satlink)
         :hints(("Goal" :in-theory (enable bfr-eval)))))))

