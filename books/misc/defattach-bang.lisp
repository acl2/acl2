; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann, April, 2011
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; We define a macro based on defattach that does not require guard verification
; for a function to be attached to a constrained function.

(in-package "ACL2")

(defun defattach!-defun (name ctx wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))
                  :mode :program))
  (let ((cl (getprop name 'symbol-class nil 'current-acl2-world wrld)))
    (case cl
      (:ideal (let ((formals (formals name wrld)))
                (list 'defun
                      (intern-in-package-of-symbol
                       (concatenate 'string
                                    (symbol-name name)
                                    "$GUARD-VERIFIED")
                       name)
                      formals
                      '(declare (xargs :guard t :verify-guards t))
                      (list 'ec-call (cons name formals)))))
      (:common-lisp-compliant nil)
      (t (er hard ctx
             "Not a logic-mode function symbol: ~x0"
             name)))))

(defun defattach!-event (args wrld defs new-args)
  (declare (xargs :mode :program))
  (cond ((or (endp args)
             (keywordp (car args)))
         (and defs
              (cons 'progn
                    (append defs
                            (list (cons 'defattach (revappend new-args
                                                              args)))))))
        (t (let* ((arg (car args))
                  (f (car arg))
                  (g (cadr arg))
                  (ctx 'defattach!)
                  (def (defattach!-defun g ctx wrld))
                  (new-args (if def
                                (cons (list* f (cadr def) (cddr arg))
                                      new-args)
                              (cons arg new-args))))
             (cond (def
                    (defattach!-event (cdr args) wrld
                      (cons def defs) new-args))
                   (t
                    (defattach!-event (cdr args) wrld
                      defs new-args)))))))

(defun defattach!-fn (args)
  `(make-event
    (let ((event (defattach!-event ',args (w state) nil nil)))
      (or event
          (cons 'defattach ',args)))))

(defmacro defattach! (&rest args)
  (cond ((and (eql (length args) 2)
              (symbolp (car args))) ; (defattach f g)
         (defattach!-fn (list args)))
        (t
         (defattach!-fn args))))
