

(in-package "ACL2")




(local
 (progn

   (include-book "outer-local")

   (defmacro fn-exists? (flg fn)
     `(make-event
       (let ((fn ',fn) (flg ,flg))
         (if (iff (eq :none (getprop fn 'formals
                                     :none 'current-acl2-world (w state)))
                  flg)
             (er hard? 'fn-exists
                 (if flg "~x0 should exist but doesn't"
                   "~x0 shouldn't exist but does")
                 fn)
           `(value-triple ',fn)))))


   (encapsulate nil
     (with-outer-locals
       (with-outer-locals
         (outer-local (defun xa () nil))
         (outer-local :level 2
                      (defun xb () nil)
                      (outer-local
                       (defun xc () nil))))
       (outer-local (defun xd () nil))
       (fn-exists? t xa)
       (fn-exists? t xb)
       (fn-exists? t xc)
       (fn-exists? t xd))
     (fn-exists? nil xa)
     (fn-exists? t xb)
     (fn-exists? nil xc)
     (fn-exists? t xd))

   (fn-exists? nil xa)
   (fn-exists? nil xb)
   (fn-exists? nil xc)
   (fn-exists? nil xd)))
