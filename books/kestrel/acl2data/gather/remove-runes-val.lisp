; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "kestrel/utilities/checkpoints" :dir :system)

(program)
(set-state-ok t)

(defttag :acl2data)
(remove-untouchable global-enabled-structure nil)

(defconst *remove-rune-val*
  '(:remove))

(defun remove-runes-val (augmented-runes term pspv hints time-limit ens wrld
                                         ctx state)

; The value here is to be associated with a rune in the :runes-alist.  It is a
; list consisting even of just a keyword (:remove or :fail) or else checkpoint
; information.

  (save-event-state-globals
   (mv-let (erp ign state)
     (state-global-let*
      ((my-augmented-disabled-runes augmented-runes)
       (global-enabled-structure
        (useless-runes-ens ens wrld state)))
      (with-prover-time-limit
       time-limit
       (prove term
              (change prove-spec-var pspv
                      :rewrite-constant
                      (change rewrite-constant
                              (access prove-spec-var pspv
                                      :rewrite-constant)
                              :current-enabled-structure
                              (ens state)))
              hints (ens state) wrld ctx state)))
     (declare (ignore ign))
     (pprogn
      (f-put-global 'gag-state-saved (@ gag-state) state)
      (value

; If prove caused an error, then we expect checkpoints.  An error without
; checkpoints could be caused because the time-limit was reached before any
; checkpoints were created; we return (:fail) in that case.  If prove did not
; cause an error, then we return (:remove) to indicate that the proof succeeds
; even with removal.  Otherwise we return a list indicating the checkpoints.

       (cond (erp (let ((c1 (checkpoint-list t state))
                        (c2 (checkpoint-list nil state)))
                    (cond ((or c1 c2)
                           (list c1
                                 (prettyify-clause-lst c1 nil wrld)
                                 c2
                                 (prettyify-clause-lst c2 nil wrld)))
                          (t '(:fail)))))
             (t *remove-rune-val*)))))))
