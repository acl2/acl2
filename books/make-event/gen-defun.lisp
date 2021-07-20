; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file illustrates how to generate events and event names based on the
; current logical world, using make-event.

; Our particular application here is just a simple one to illustrate the idea.
; We introduce a special form, gen-defun, that automatically generates a
; function definition for a given non-recursive body.  This particular
; gen-defun macro is probably not all that useful; the point is to illustrate
; make-event's capability for accessing the state and logical world.

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
      :on-behalf-of ,ev)))

; Examples.

; generates (DEFUN FN-0 (X Y) (+ X Y))
(gen-defun (+ x y))

; generates (DEFUN FN-1 (X Y) (* X Y))
(gen-defun (* x y))

; generates (DEFUN FN-2 (X Y) (* X Y Y))
(gen-defun (* x y y))

; Check that the above definitions are as expected.
(defthm gen-defun-test
  (equal (list (fn-0 x y) (fn-1 x y) (fn-2 x y))
         (list (+ x y) (* x y) (* x y y)))
  :rule-classes nil)

; generates
; (DEFUN FOO-0 (STATE X Y) (DECLARE (XARGS :STOBJS (STATE))) (MV X Y STATE))
(gen-defun (mv x y state) :stobjs state :root foo)
