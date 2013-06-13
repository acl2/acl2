; Here we define macros that employ make-event to check evaluations of forms.
; See community book make-event/eval-tests.lisp (and many other .lisp files in
; that directory) for how these macros may be employed.  See also
; make-event/eval-check.lisp for a similar book that adds :check-expansion t to
; its make-event forms.

(in-package "ACL2")

(defmacro must-eval-to (&whole must-eval-to-form
                               form expr
                               &key (ld-skip-proofsp ':default))

; Warning: Keep this in sync with the definition of must-eval-to in community
; book make-event/eval-check.lisp.

; Form should evaluate to an error triple (mv erp form-val state).  If erp is
; nil and expr-val is the value of expr then (must-eval-to form expr) expands
; to (value-triple 'expr-val); otherwise expansion causes an appropriate soft
; error.  Note that both form and expr are evaluated.

  (let ((body
         `(er-let* ((form-val-use-nowhere-else ,form))
            (let ((expr-val (check-vars-not-free
                             (form-val-use-nowhere-else)
                             ,expr)))
              (cond ((eq form-val-use-nowhere-else expr-val)
                     (value (list 'value-triple (list 'quote expr-val))))
                    (t (er soft
                           (msg "( MUST-EVAL-TO ~@0 ~@1)"
                                (tilde-@-abbreviate-object-phrase ',form)
                                (tilde-@-abbreviate-object-phrase ',expr))
                           "Evaluation returned ~X01, not the value ~x2 of ~
                            the expression ~x3."
                           form-val-use-nowhere-else
                           (evisc-tuple 4 3 nil nil)
                           expr-val
                           ',expr)))))))
    `(make-event ,(if (eq ld-skip-proofsp :default)
                      body
                    `(state-global-let*
                      ((ld-skip-proofsp ,ld-skip-proofsp))
                      ,body))
                 :on-behalf-of ,must-eval-to-form)))

(defmacro must-eval-to-t (form &key (ld-skip-proofsp ':default))

; Form should evaluate to an error triple (mv erp val state).  If erp is nil
; and val is t then (must-eval-to-t form) expands to (value-triple t);
; otherwise expansion causes an appropriate soft error.

  `(must-eval-to ,form t ,@(and (not (eq ld-skip-proofsp :default))
                                `(:ld-skip-proofsp ,ld-skip-proofsp))))

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
    :on-behalf-of ,must-succeed-form))

(defmacro must-fail (&whole must-fail-form
                            form)

; Form should evaluate to an error triple (mv erp val state).  (Must-fail
; form) expands to (value-triple t) if erp is non-nil, and expansion causes a
; soft error otherwise.

; Remark on provisional certification: By default we bind state global
; ld-skip-proofsp to nil when generating the .acl2x file for this book during
; provisional certification.  We do this because in some cases must-fail
; expects proofs to fail.  Some books in the distributed books/make-event/
; directory have the following comment when this change was necessary for
; .acl2x file generation during provisional certification:
; "; See note about ld-skip-proofsp in the definition of must-fail."

  `(make-event
    '(must-eval-to-t
      (mv-let (erp val state)
              ,form
              (declare (ignore val))
              (value (not (eq erp nil))))
      :ld-skip-proofsp
      (if (eq (cert-op state) :write-acl2xu)
          nil
        (f-get-global 'ld-skip-proofsp state)))
    :on-behalf-of ,must-fail-form))

(defmacro thm? (&rest args)
  `(must-succeed (thm ,@args)))

(defmacro not-thm? (&rest args)
  `(must-fail (thm ,@args)))
