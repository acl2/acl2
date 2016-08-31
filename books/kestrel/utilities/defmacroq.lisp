; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defun defmacroq-binding (arg)
  (declare (xargs :guard t))
  `(,arg (if (and (consp ,arg)
                  (eq (car ,arg) :eval))
             (cadr ,arg)
           (list 'quote ,arg))))

(defun defmacroq-bindings (args)
  (declare (xargs :guard (true-listp args)))
  (cond ((endp args) nil)
        (t (cons (defmacroq-binding (car args))
                 (defmacroq-bindings (cdr args))))))

(defmacro defmacroq (fn args &rest rest)

; TODO: Perhaps Propagate ignore and ignorable declarations into the generated
; LET.

  (let* ((vars (macro-vars args))
         (bindings (defmacroq-bindings vars))
         (dcls (butlast rest 1))
         (body (car (last rest))))
    (cond ((member-eq 'state vars)
           (er hard 'defmacroq
               "It is illegal to supply STATE as an argument of DEFMACROQ."))
          (t `(defmacro ,fn ,args
                ,@dcls
                (let ,bindings
                  ,body))))))

;;; tests

(local (progn

(defmacroq mac4 (x y z w)
  `(list ,x ,y ,z ,w (f-boundp-global 'boot-strap-flg state)))

(defun f (a state b)
  (declare (xargs :stobjs state))
  (cons 17 (mac4 c (:eval (cons a b)) b (:eval (expt 2 3)))))

(assert-event (equal (f (expt 4 1) state (reverse '(i j k)))
                     '(17 C (4 K J I) B 8 T)))

))
