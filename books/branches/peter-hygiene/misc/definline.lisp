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
  ~c[definline] is the same as ~il[defun], but also issues a Common Lisp ``declaim''
  form instructing the compiler to inline later calls to this function.  Some Lisps 
  ignore these ``declaim'' forms and make inlining worthless.  However, inlining 
  may provide significant gains on other Lisps.

  Inlining is usually beneficial for ``small'' non-recursive functions which are
  called frequently.")

(defdoc definlined
  ":Doc-Section definline
  Define an inline function and then disable it.~/
  ~/
  This is a ~il[defund]-like version of ~il[definline].")

(defun proclaim-inline (name)
  (declare (xargs :guard t)
           (ignore name))
  (cw "Warning: proclaim-inline has not been redefined and is doing nothing."))

(defun definline-fn (defun-fn args)
  (declare (xargs :mode :program))
  (if (not (consp args))
      ;; This is the same message "defun" gives when it's unhappy.
      (ACL2::er hard 'definline "A definition must be given three or more arguments, ~
                                but ~x0 has length only 0.~%" args)
    (let ((name (first args)))
      (if (symbolp name)
          `(ACL2::progn
            ;; Need to check expansion to get them to work with included books.
            (make-event (let ((invisible-work (proclaim-inline ',name)))
                          (declare (ignore invisible-work))
                          (value '(value-triple '(:proclaim-inline ,name))))
                        :check-expansion t)
            (,defun-fn ,@args))
        ;; This is the same message "defun" gives when it's unhappy.
        (ACL2::er hard 'definline "Names must be symbols and ~x0 is not.~%" name)))))

(defmacro definline (&rest args)
  (definline-fn 'defun args))

(defmacro definlined (&rest args)
  (definline-fn 'defund args))
  
(defttag definline)

(progn!
 (set-raw-mode t)
 (defun proclaim-inline (name)
   (progn
     (eval `(proclaim '(inline ,name)))
     nil)))

