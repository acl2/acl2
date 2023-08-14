; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "kestrel/utilities/checkpoints" :dir :system)

(program)
(set-state-ok t)

(defttag :acl2data)
(remove-untouchable global-enabled-structure nil)

(defun remove-runes-entry (augmented-runes term pspv hints time-limit key
                                           ens wrld ctx state)
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
; checkpoints may be unusual, since it means that the proof failed but there
; were no checkpoints, perhaps because the time-limit was reached before any
; checkpoints were created; we return (list key :fail) in that case.  If prove
; did not cause an error, then we return (list key :remove) to indicate that
; the rune(s) indicated by key can be removed.

       (cond (erp (let ((c1 (checkpoint-list t state))
                        (c2 (checkpoint-list nil state)))
                    (cond ((or c1 c2)
                           (list key
                                 c1
                                 (prettyify-clause-lst c1 nil wrld)
                                 c2
                                 (prettyify-clause-lst c2 nil wrld)))
                          (t (list key :fail)))))
             (t (list key :remove))))))))
