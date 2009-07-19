; This is a modification of eval.lisp that uses :check-expansion t.

(in-package "ACL2")

(defmacro must-eval-to (&whole must-eval-to-form
                               form val)

; Form should evaluate to an error triple (mv erp val2 state).  If erp is nil
; and val2 is val then (must-eval-to form val) expands to (value-triple val);
; otherwise expansion causes an appropriate soft error.

  `(make-event
    (er-let* ((val ,form))
             (cond ((eq val t)
                    (value '(value-triple ,val)))
                   (t (er soft
                          (msg "( MUST-EVAL-TO ~@0 ~@1)"
                               (tilde-@-abbreviate-object-phrase ',form)
                               (tilde-@-abbreviate-object-phrase ',val))
                          "Evaluation returned ~X01, not ~x2."
                          val
                          (evisc-tuple 4 3 nil nil)
                          t))))
    :on-behalf-of ,must-eval-to-form
    :check-expansion t))

(defmacro must-eval-to-t (form)

; Form should evaluate to an error triple (mv erp val state).  If erp is nil
; and val is t then (must-eval-to-t form) expands to (value-triple t);
; otherwise expansion causes an appropriate soft error.

  `(must-eval-to ,form t))

(defmacro must-succeed (&whole must-succeed-form
                               form)

; (Must-succeed form) expands to (value-triple t) if evaluation of form is an
; error triple (mv nil val state), and causes a soft error otherwise.

  `(make-event
    '(must-eval-to-t
      (mv-let (erp val state)
              ,form
              (declare (ignore val))
              (value (eq erp nil))))
    :check-expansion t
    :on-behalf-of ,must-succeed-form))

(defmacro must-fail (&whole must-fail-form
                            form)

; Form should evaluate to an error triple (mv erp val state).  (Must-succeed
; form) expands to (value-triple t) if erp is non-nil, and expansion causes a
; soft error otherwise.

  `(make-event
    '(must-eval-to-t
      (mv-let (erp val state)
              ,form
              (declare (ignore val))
              (value (not (eq erp nil)))))
    :check-expansion t
    :on-behalf-of ,must-fail-form))
