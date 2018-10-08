; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann (original date October, 2006)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defmacro with-output$ (&rest args)

; This is basically just the #+acl2-loop-only definition of with-output.

  `(if (eq (ld-skip-proofsp state) 'include-book)
       ,(car (last args))
     ,(let ((val (with-output-fn 'with-output$
                                 args nil nil nil nil nil nil nil nil nil nil)))
        (or val
            (illegal 'with-output$
                     "Macroexpansion of ~q0 failed."
                     (list (cons #\0 (cons 'with-output$ args))))))))

(defun prove$-fn (term state hints otf-flg)

; This function is based on thm-fn.  It returns

  (declare (xargs :mode :program :stobjs state))
  (with-ctx-summarized
   "( PROVE$ ...)"
   (let ((wrld (w state))
         (ens (ens state)))
     (mv-let
       (erp val state)
       (er-let* ((hints (translate-hints+ 'thm
                                          hints
                                          (default-hints wrld)
                                          ctx wrld state))
                 (tterm (translate term t t t ctx wrld state)))
; known-stobjs = t (stobjs-out = t)
         (prove tterm
                (make-pspv ens wrld state
                           :displayed-goal term
                           :otf-flg otf-flg)
                hints ens wrld ctx state))
       (declare (ignore val)) ; ttree
       (value (null erp))))))

(defmacro convert-soft-error-to-value (form val)
  `(let ((val ,val))
     (mv-let (erp val2 state)
       ,form
       (cond (erp (value val))
             (t (value val2))))))

(defmacro prove$ (term &key
                       hints otf-flg
                       (with-output '(:off :all :gag-mode nil))
                       time-limit
                       step-limit)

; All of the arguments except :with-output are evaluated.  The result is
; (mv nil t state) if the proof is successful, otherwise (mv nil nil state).

  (let* ((form `(prove$-fn ,term state ,hints ,otf-flg))
         (form (if with-output
                   `(with-output$ ,@with-output ,form)
                 form))
         (form (if time-limit
                   `(with-prover-time-limit ,time-limit ,form)
                 form))
         (form (if step-limit
                   `(with-prover-step-limit ,step-limit ,form)
                 form)))
    `(convert-soft-error-to-value ,form nil)))

(defxdoc prove$
  :parents (kestrel-utilities system-utilities-non-built-in)
  :short "A way to call the prover from a program."
  :long "<p>For examples, see community book
 @('books/kestrel/utilities/prove-interface-tests.lisp').</p>

 @({
 General Form:
 (prove$ term &key
         hints
         otf-flg
         with-output ; :off, :all, :gag-mode, or the default, nil
         time-limit
         step-limit)
 })")
