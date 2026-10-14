; This book was produced by Claude and passed along by Eric Smith, except for
; the events added at the end as clearly marked.  It illustrates a soundness
; bug in ACL2 Version 8.7 fixed before ACL2 Version 8.8.  The fix was to add
; some top-level proof-builder functions to *initial-untouchable-fns*.

; Finding 58: the fix for the 'PC-OUTPUT finding (Finding 30) is incomplete.
; Three independent links remain, and together they give a proof of nil from a
; single :INSTRUCTIONS hint.
;
; L1 -- :SEQUENCE's SUCCESS-EXPR is an unguarded trans-eval channel.
; proof-builder-b.lisp:2412 defines (define-pc-meta sequence (instr-list
; &optional strict-flg protect-flg success-expr ...)), which calls
; modified-error-triple-for-sequence (:2375), whose body is
;     (trans-eval-default-warning success-expr :sequence state t)
; with NO in-verify-flg guard -- unlike the LISP command
; (proof-builder-b.lisp:123-127), which exists precisely to block this.  SEQUENCE
; is PREDEFINED, so pc-single-step-1 admits it from a book.  Second entry point:
; (define-pc-macro set-success (instr form) ... (sequence (,instr) nil nil ,form))
; at proof-builder-b.lisp:2841.
;
; L2 -- xtrans-eval does not restore 'PC-OUTPUT either: history-management.lisp
; :4233 deliberately excludes pc-output from *protected-system-state-globals*
; (";;; for thm-fn") and :4232 excludes pc-ss-alist, so a user define-pc-macro
; body is a second arbitrary-eval channel whose goal-stack writes persist.
;
; L3 -- the functions that WRITE the goal stack are not untouchable.
; axioms.lisp:22915-22921 added only initialize-pc-acl2,
; pc-single-step-primitive, pc-single-step, assign-event-name-and-rule-classes
; and save-fn, with the comment "as of this writing (9/2026), we haven't tried to
; exploit the lack of untouchability of these functions".  pc-top
; (proof-builder-a.lisp:1406) and pc-main (:1389) both run
; install-initial-state-stack (:1372-1380), whose (pc-assign state-stack) is
; compiled into their bodies, so translate's untouchable-vars check never sees
; it.  proof-builder-cl-proc-1 then reads the clobbered stack --
; (goals-to-clause-list (goals)), proof-builder-b.lisp:4845/4951 -- and returns
; it as the trusted clause processor's output.
;
; POLARITY: the MUST-FAIL states the CORRECT behaviour.  RED while present.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

; THE DEFECT, in full: one defthm, one hint, no auxiliary definitions.
(must-fail
 (defthm nil-proved
   nil
   :hints (("Goal" :instructions
            ((:sequence nil nil nil
                        (mv-let (erp val state)
                                (pc-top 't nil nil nil nil nil state)
                                (declare (ignore erp val))
                                (mv nil t state))))))
   :rule-classes nil))

; CONTROL 1: the same payload through the LISP command IS refused, which is the
; guard that :SEQUENCE is missing.  Expected:
;   "You may only invoke the proof-builder LISP command when you are inside the
;    interactive loop."
(must-fail
 (defthm ctl-lisp
   nil
   :hints (("Goal" :instructions ((:lisp (pc-top 't nil nil nil nil nil state)))))
   :rule-classes nil))

; CONTROL 2: writing the state global directly IS refused -- 'PC-OUTPUT really is
; untouchable, which is what Finding 30's fix achieved.  So the remaining hole is
; the compiled write inside pc-top, not the global's protection.
(must-fail
 (defthm ctl-putglobal
   nil
   :hints (("Goal" :instructions
            ((:sequence nil nil nil (f-put-global 'pc-output nil state)))))
   :rule-classes nil))

; CONTROL 3: an honest :INSTRUCTIONS proof must still work, so the fix cannot be
; to disable the proof-builder from books.
(defthm honest-instructions
  (equal (car (cons x y)) x)
  :hints (("Goal" :instructions ((:prove))))
  :rule-classes nil)

; Additional tests by Matt Kaufmann based on what is above:

(must-fail
 (thm nil
      :hints (("Goal" :instructions
               ((:sequence nil nil nil
                           (mv-let (erp val state)
                             (pc-main ''t 't nil nil nil nil t nil state)
                             (declare (ignore erp val))
                             (mv nil t state))))))))

(must-fail
 (thm nil
      :hints (("Goal" :instructions
               ((:sequence nil nil nil
                           (mv-let (erp val state)
                             (pc-main ''t 't nil nil nil nil nil nil state)
                             (declare (ignore erp val))
                             (mv nil t state))))))))

(must-fail
 (thm nil
      :hints (("Goal" :instructions
               ((:sequence nil nil nil
                           (mv-let (erp val state)
                             (pc-main1 '((:sequence nil nil nil
                                                    (mv-let (erp val state)
                                                      (pc-main ''t
                                                               't
                                                               nil nil nil nil nil nil state)
                                                      (declare (ignore erp val))
                                                      (mv nil t state))))
                                       '(signal value)
                                       t state)
                             (declare (ignore erp val))
                             (mv nil t state))))))))

(must-fail
 (thm nil
      :hints (("Goal" :instructions
               ((:sequence nil nil nil
                           (mv-let (erp val state)
                             (pc-main-loop
                              '((:sequence
                                 nil nil nil
                                 (mv-let
                                   (erp val state)
                                   (pc-main1
                                    '((:sequence nil nil nil
                                                 (mv-let (erp val state)
                                                   (pc-main ''t
                                                            't
                                                            nil nil nil nil nil nil state)
                                                   (declare (ignore erp val))
                                                   (mv nil t state))))
                                    '(signal value)
                                    t state)
                                   (declare (ignore erp val))
                                   (mv nil t state))))
                              '(signal value)
                              t t state)
                             (declare (ignore erp val))
                             (mv nil t state))))))))
