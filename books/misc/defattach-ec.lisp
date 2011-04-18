; Matt Kaufmann
; April 18, 2011

; We define a macro based on defattach that does not require guard verification
; for a function to be attached to a constrained function.  The suffix "ec"
; stands for "executable-counterpart", as with "ec-fncall".

(in-package "ACL2")

(defun ec-name (sym)
  (declare (xargs :guard (symbolp sym)))
  (intern-in-package-of-symbol (concatenate 'string (symbol-name sym) "$EC")
                               sym))

(defun defun-ec-event (name wrld)
  (declare (xargs :guard (and (symbolp name)
                              (plist-worldp wrld))
                  :mode :program))
  (let ((cl (getprop name 'symbol-class nil 'current-acl2-world wrld)))
    (case cl
      (:ideal (let ((formals (formals name wrld)))
                (list 'defun (ec-name name) formals
                      '(declare (xargs :guard t :verify-guards t))
                      (list 'ec-call (cons name formals)))))
      (:common-lisp-compliant (list 'value-triple (list 'quote name)))
      (t (er hard 'defun-ec
             "Not a logic-mode function symbol: ~x0"
             name)))))

(defun defattach-ec-event (args wrld defs new-args)
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
                  (def (defun-ec-event g wrld))
                  (new-args (cons (if def
                                      (list* f (cadr def) (cddr arg))
                                    arg)
                                  new-args)))
             (cond (def
                    (defattach-ec-event (cdr args) wrld
                      (cons def defs) new-args))
                   (t
                    (defattach-ec-event (cdr args) wrld
                      defs new-args)))))))

(defun defattach-ec-fn (args)
  `(make-event
    (let ((event (defattach-ec-event ',args (w state) nil nil)))
      (or event
          (cons 'defattach ',args)))))

(defmacro defattach-ec (&rest args)
  (cond ((and (eql (length args) 2)
              (symbolp (car args))) ; (defattach f g)
         (defattach-ec-fn (list args)))
        (t
         (defattach-ec-fn args))))
