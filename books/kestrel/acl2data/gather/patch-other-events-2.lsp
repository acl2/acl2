; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; ...
; Also Copyright (C) 2023, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; as this is derived from ACL2 source file other-events.lisp.

; Last updated for git commit: 8ef94c04ca9a3c7b9d7708696479d609944db454

(defun progn-fn1 (ev-lst progn!p bindings state)

; Important Note:  Don't change the formals of this function without reading
; the *initial-event-defmacros* discussion in axioms.lisp.

; If progn!p is nil, then we have a progn and bindings is nil.  Otherwise we
; have a progn! and bindings is a list of bindings as for state-global-let*.

  (let ((ctx (cond (ev-lst
                    (msg "( PROGN~s0 ~@1 ...)"
                         (if progn!p "!" "")
                         (tilde-@-abbreviate-object-phrase (car ev-lst))))
                   (t (if progn!p "( PROGN!)" "( PROGN)"))))
; patch file addition:
        (*expansion-stack* (cons 'progn *expansion-stack*)) ;patch;
        (in-encapsulatep
         (in-encapsulatep (global-val 'embedded-event-lst (w state)) nil)))
    (with-ctx-summarized
     ctx
     (revert-world-on-error
      (state-global-let*
       ((inside-progn-fn1 t))
       (mv-let
         (erp val expansion-alist ignore-kpa state)
         (pprogn
          (f-put-global 'redo-flat-succ nil state)
          (f-put-global 'redo-flat-fail nil state)
          (eval-event-lst
           0 nil
           ev-lst
           (or (ld-skip-proofsp state)
               progn!p) ; quietp
           (eval-event-lst-environment in-encapsulatep state)
           (f-get-global 'in-local-flg state)
           nil
           (if progn!p
               :non-event-ok

; It is unknown here whether make-event must have a consp :check-expansion, but
; if this progn is in such a context, chk-embedded-event-form will check that
; for us.

             nil)
           nil
           'progn-fn1 ctx (proofs-co state) state))
         (declare (ignore ignore-kpa))
         (pprogn
          (if erp
              (update-for-redo-flat val ev-lst state)
            state)
          (cond ((eq erp 'non-event)
                 (er soft ctx
                     "PROGN may only be used on legal event forms (see :DOC ~
                    embedded-event-form).  Consider using ER-PROGN instead."))
                (erp

; The component events are responsible for reporting errors.

                 (silent-error state))
                (t (pprogn (f-put-global 'last-make-event-expansion
                                         (and expansion-alist
                                              (cons (if progn!p 'progn! 'progn)
                                                    (if bindings
                                                        (assert$
                                                         progn!p
                                                         `(:state-global-bindings
                                                           ,bindings
                                                           ,@(subst-by-position
                                                              expansion-alist
                                                              ev-lst
                                                              0)))
                                                      (subst-by-position
                                                       expansion-alist
                                                       ev-lst
                                                       0))))
                                         state)
                           (value (and (not (f-get-global 'acl2-raw-mode-p
                                                          state))

; If we allow a non-nil value in raw-mode (so presumably we are in progn!, not
; progn), then it might be a bad-lisp-objectp.  Of course, in raw-mode one can
; assign bad lisp objects to state globals which then become visible out of
; raw-mode -- so the point here isn't to make raw-mode sound.  But this nulling
; out in raw-mode should prevent most bad-lisp-objectp surprises from progn!.

                                       val)))))))))
     :event-type 'progn)))
