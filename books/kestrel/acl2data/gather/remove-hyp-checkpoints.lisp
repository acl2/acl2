; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "kestrel/utilities/checkpoints" :dir :system)

(defun replace-defthm-body (defthm-event body)

; This trivial function replaces the body of a defthm with the given body,
; which is typically an untranslated term.

; Note that this function does nothing with other fields of the defthm,
; such as corollaries (whose proofs might depend on body).

  (case-match defthm-event
    (('defthm name & . rest)
     `(defthm ,name ,body ,@rest))
    (& (er hard 'replace-defthm-body
           "Unexpected form of defthm-event~|(expected (defthm NAME TERM ~
            ...):~|~x0"
           defthm-event))))

(defun collect-conjuncts-of-uterm (uterm)
  (case-match uterm
    (('and) nil)
    (('and x . y)
     (append? (collect-conjuncts-of-uterm x)
              (collect-conjuncts-of-uterm `(and ,@y))))
    (& (list uterm))))

(defun hyps-and-concl-of-uterm (uterm)
  (case-match uterm
    (('implies h c)
     (mv-let (h-lst c0)
       (hyps-and-concl-of-uterm c)
       (mv (append? (collect-conjuncts-of-uterm h) h-lst) c0)))
    (& (mv nil uterm))))

(program)
(set-state-ok t)

(defun remove-hyp-checkpoints-1 (uhyps1 uhyps2 thyps1 thyps2 uconcl tconcl
                                        pspv hints time-limit event-form
                                        ens wrld ctx state)
  (cond
   ((endp thyps2) (value nil))
   ((ffn-symb-p (car thyps2) 'synp)
    (remove-hyp-checkpoints-1
     (cons (car uhyps2) uhyps1)
     (cdr uhyps2)
     (cons (car thyps2) thyps1)
     (cdr thyps2)
     uconcl tconcl
     pspv hints time-limit event-form ens wrld ctx state))
   (t (let* ((thyp (car thyps2))
             (thyps (revappend thyps1 (cdr thyps2)))
             (tterm (make-implication thyps tconcl)))
        (mv-let (erp gag-state state)
          (save-event-state-globals
           (mv-let (erp val state)
             (with-prover-time-limit
              time-limit
              (prove tterm pspv hints ens wrld ctx state))
             (declare (ignore val))
             (mv erp (@ gag-state) state)))
          (let* ((state (f-put-global 'gag-state-saved gag-state state))
                 (uhyp (car uhyps2))
                 (uhyps (revappend uhyps1 (cdr uhyps2)))
                 (new-event (replace-defthm-body
                             event-form
                             (if uhyps
                                 `(implies ,(conjoin-untranslated-terms uhyps)
                                           ,uconcl)
                               uconcl)))
                 (entry

; If prove caused an error, then we expect checkpoints.  An error without
; checkpoints may be unusual, since it means that the proof failed but there
; were no checkpoints, perhaps because the time-limit was reached before any
; checkpoints were created; we return (list hyp :fail) in that case.  If prove
; did not cause an error, then we return (list hyp :remove) to indicate that
; the hypothesis can be removed.

                  (cond (erp (let ((c1 (checkpoint-list t state))
                                   (c2 (checkpoint-list nil state)))
                               (cond ((or c1 c2)
                                      (list thyp
                                            c1
                                            (prettyify-clause-lst c1 nil wrld)
                                            c2
                                            (prettyify-clause-lst c2 nil wrld)
                                            new-event
                                            uhyp))
                                     (t (list thyp :fail new-event uhyp)))))
                        (t (list thyp :remove new-event uhyp)))))
            (er-let* ((val (remove-hyp-checkpoints-1
                            (cons uhyp uhyps1) (cdr uhyps2)
                            (cons thyp thyps1) (cdr thyps2)
                            uconcl tconcl
                            pspv hints time-limit event-form
                            ens wrld ctx state)))
              (value (cons entry val)))))))))

(defun remove-hyp-checkpoints (uterm pspv hints time-limit
                                     event-form ens wrld ctx state)
  (cond
   ((or (null time-limit)
        (ld-skip-proofsp state))
    (value nil))
   (t
    (mv-let (uhyps uconcl)
      (hyps-and-concl-of-uterm uterm)
      (cond
       ((null uhyps) (value nil)) ; fail
       (t
        (mv-let (erp thyps state)
          (translate-term-lst uhyps
                              t   ; stobjs-out
                              nil ; logic-modep (could be t, but no need)
                              t ; known-stobjs-lst (as in translate-for-defthm)
                              ctx wrld state)
          (cond
           (erp (value nil)) ; fail
           (t
            (mv-let (erp tconcl state)
              (translate uconcl t nil t ctx wrld state) ; args as above
              (cond
               (erp (value nil)) ; fail
               (t
                (mv-let
                  (erp val state)
                  (with-output!
                    :off :all
                    :gag-mode nil
                    (state-global-let*
                     ((abort-soft ; interrupts abort immediately to top level
                       nil))
                     (remove-hyp-checkpoints-1
                      nil uhyps nil thyps uconcl tconcl
                      pspv hints time-limit event-form ens wrld ctx state)))
                  (value (and (null erp) val)))))))))))))))
