; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug fixed before ACL2 Version 8.8.

; A wormhole does not change the logical state, and changes made to the file
; system inside a wormhole are not undone when it exits.  That is why
; open-output-channel causes an error inside a wormhole.  But serialize-write,
; delete-file$, and dmr-start did not, so canonical-pathname could return two
; different values for the same state: one before a wormhole that creates or
; deletes a file and one after.  A clause processor could thus prove nil.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defevaluator evl evl-list ((if x y z)))

(defun run-in-wormhole (form)
  (declare (xargs :guard t))
  (wormhole 'wormhole-file-changes
            '(lambda (whs) (make-wormhole-status whs :enter nil))
            nil
            form
            :ld-error-action :return
            :ld-verbose nil
            :ld-prompt nil
            :ld-pre-eval-print nil
            :ld-post-eval-print nil))

(defun test-file (state)
  (declare (xargs :stobjs state))
  (let ((dir (cbd)))
    (if (stringp dir)
        (concatenate 'string dir "wormhole-file-changes.sao")
      "wormhole-file-changes.sao")))

; The following clause processor checks whether the test file exists, creates
; it in a wormhole, checks again, deletes it in a wormhole, and checks again.
; The three checks are made on the same state, so logically they agree.

(defun wormhole-file-cp (cl hint state)
  (declare (xargs :stobjs state)
           (ignore hint))
  (let* ((file (test-file state))
         (x (canonical-pathname file nil state))
         (y (prog2$ (run-in-wormhole
                     `(pprogn (serialize-write ,file 17)
                              (value :q)))
                    (canonical-pathname file nil state)))
         (z (prog2$ (run-in-wormhole
                     `(mv-let (flg state)
                        (delete-file$ ,file state)
                        (declare (ignore flg))
                        (value :q)))
                    (canonical-pathname file nil state))))
    (mv nil
        (if (and (equal x y) (equal y z))
            (list cl)
          nil)
        state)))

(defthm wormhole-file-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses
                      (clauses-result (wormhole-file-cp cl hint state)))
                     a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

; Before the fix, the file was created and then deleted, so the clause
; processor returned no clauses.

(must-fail
 (defthm nil-proved
   nil
   :hints (("Goal" :clause-processor (wormhole-file-cp clause nil state)))
   :rule-classes nil))

; Dmr-start, which creates a file, also causes an error inside a wormhole now.
; The wormhole status records whether the dmr-start call completed.

(make-event
 (prog2$
  (run-in-wormhole
   '(pprogn (dmr-start)
            (dmr-stop)
            (set-persistent-whs-and-ephemeral-whs
             'wormhole-file-changes
             (make-wormhole-status (@ wormhole-status) :enter :dmr-started)
             state)
            (value :q)))
  (er-let* ((whs (get-persistent-whs 'wormhole-file-changes state)))
    (value `(assert-event (null ',(wormhole-data whs)))))))
