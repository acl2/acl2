(in-package "ACL2")

#|

This is a hack to add some special features to PROGN!:

(progn! :compile-only ...)  expands to the given forms ONLY for the raw
lisp compiler and not the ACL2 loop.

(progn! :loop-only ...) expands to the given forms ONLY for the ACL2 loop
and not the raw lisp compiler.

This is currently the basis for implementing DEFCODE, and may not be
in the future.

|#

(defttag defcode)

(progn!
 (set-ld-redefinition-action '(:doit! . :overwrite) state)
 (defmacro progn! (&rest r)
   (declare (xargs :guard (or (not (symbolp (car r)))
                              (member-eq (car r)
                                         '(:state-global-bindings
                                           :compile-only
                                           :loop-only)))))
   (cond
    ((not (consp r))
     '(progn!-fn nil nil state))
    ((eq (car r) :compile-only)
     `(progn!-fn nil nil state))
    ((eq (car r) :state-global-bindings)
     `(state-global-let* ,(cadr r)
                         (progn!-fn ',(cddr r) ',(cadr r) state)))
    ((eq (car r) :loop-only)
     `(progn!-fn ',(cdr r) nil state))
    (t
     `(progn!-fn ',r nil state))))
 (set-ld-redefinition-action nil state)
 (set-raw-mode t)
 (progn
  (defmacro progn! (&rest r)
    (let ((sym (gensym)))
      `(let ((state *the-live-state*)
             (,sym (f-get-global 'acl2-raw-mode-p *the-live-state*)))
         (declare (ignorable state))
         ,@(cond ((not (consp r))
                  (list nil))
                 ((eq (car r) :loop-only)
                  (list nil))
                 ((eq (car r) :compile-only)
                  (cdr r))
                 ((eq (car r) :state-global-bindings)
                  (cddr r))
                 (t r))
         (f-put-global 'acl2-raw-mode-p ,sym state)
         (value nil))))
  nil)
 (set-raw-mode nil))

;(reset-prehistory t)

