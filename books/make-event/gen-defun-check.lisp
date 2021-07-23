; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See gen-defun.lisp.  The only difference here is that we use :check-expansion
; t (see comment on that below).

(in-package "ACL2")

(program)

(set-state-ok t)

(defun defun-from-body (name body stobjs ctx state)
  (let ((stobjs (cond ((and stobjs (symbolp stobjs))
                       (list stobjs))
                      (t stobjs))))
    (mv-let (erp tbody bindings state)
            (translate1 body name (list (cons name name)) stobjs
                        ctx (w state) state)
            (declare (ignore bindings))
            (cond (erp (er soft ctx
                           "Translation of ~X01 failed."
                           body
                           (evisc-tuple 4 3 nil nil)))
                  ((ffnnamep name tbody)
                   (er soft ctx
                       "Generation of non-recursive definition of ~x0 from ~
                        body ~X12 failed because the function symbol ~x0 ~
                        occurs in the body."
                       name tbody (evisc-tuple 4 3 nil nil)))
                  (t (let ((vars (merge-sort-symbol< (all-vars body))))
                       (value `(defun ,name ,vars
                                 ,@(and stobjs
                                        `((declare (xargs :stobjs ,stobjs))))
                                 ,body))))))))

(defun gen-name (root index wrld)
  (let ((name
         (intern-in-package-of-symbol (coerce (packn1 (list root "-" index))
                                              'string)
                                      root)))

    (cond ((function-symbolp name wrld)
           (gen-name root (1+ index) wrld))
          (t name))))

(defmacro gen-defun (&whole ev
                            body &key stobjs root)

; Stobjs should be a symbol naming a stobj, or a list of such.  Root is a
; string or symbol, default 'fn, for use as the prefix of the generated
; function name.

  (let ((root (or root 'fn)))
    `(make-event
      (let ((wrld (w state)))
        (defun-from-body
          (gen-name ',root 0 wrld)
          ',body
          ',stobjs
          'gen-defun
          state))
      :on-behalf-of ,ev
; The following will allow the definitions to fail at include-book time with an
; error message about the expansion changing rather than an error message
; saying that fn-0 (say) is already defined.
      :check-expansion t)))

; Examples.

(gen-defun (+ x y))

(gen-defun (* x y))

(gen-defun (* x y y))

(defthm gen-defun-test
  (equal (list (fn-0 x y) (fn-1 x y) (fn-2 x y))
         (list (+ x y) (* x y) (* x y y)))
  :rule-classes nil)

(gen-defun (mv x y state) :stobjs state :root foo)
