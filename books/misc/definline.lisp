;; definline.lisp - The definline and definlined macros.
;; Jared Davis <jared@cs.utexas.edu>
;;
;; This file is in the public domain.  You can freely redistribute it and modify
;; it for any purpose.  This file comes with absolutely no warranty, including the 
;; implied warranties of merchantibility and fitness for a particular purpose.

(in-package "ACL2")

(defdoc definline
  ":Doc-Section definline
  Define an inline function~/
  Examples:
  ~bv[]
    (definline car-alias (x)
      (car x))
  ~ev[]~/
  ~c[definline] is the same as ~il[defun], but also issues a Common Lisp ``proclaim''
  form instructing the compiler to inline later calls to this function.  Some Lisps 
  ignore these ``proclaim'' forms and make inlining worthless.  However, inlining 
  may provide significant gains on other Lisps.

  Inlining is usually beneficial for ``small'' non-recursive functions which are
  called frequently.")

(defdoc definlined
  ":Doc-Section definline
  Define an inline function and then disable it.~/
  ~/
  This is a ~il[defund]-like version of ~il[definline].")


(defun redefine-inline-fn (name state)
  ;; has an under-the-hood definition
  (declare (xargs :guard t :stobjs state)
           (ignorable state))
  (prog2$
   (cw "Warning: redefine-inline-fn has not been redefined and is doing nothing.")
   name))

(defmacro redefine-inline (name)
  `(make-event (let ((name (redefine-inline-fn ',name state)))
                 (value `(value-triple ',name)))
               :check-expansion t))

(defmacro definline (name &rest args)
  `(progn (defun ,name ,@args)
          (redefine-inline ,name)))

(defmacro definlined (name &rest args)
  `(progn (defund ,name ,@args)
          (redefine-inline ,name)))

(defttag definline)

(progn!
 (set-raw-mode t)
 (defun redefine-inline-fn (name state)
   (unless (live-state-p state)
     (er hard? 'redefine-inline-fn
         "redefine-inline-fn can only be called on live states."))
   (unless (symbolp name)
     (er hard? 'redefine-inline-fn
         "expected ~x0 to be a symbol." name))
   (let ((def (get-def name (w state))))
     (unless def
       (er hard? 'redefine-inline-fn "~x0 does not appear to be defined."))
     (eval `(proclaim '(inline ,name)))
     (eval (cons 'defun def)))
   name))

(defttag nil)


