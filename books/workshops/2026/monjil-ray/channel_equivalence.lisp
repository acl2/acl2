; MIT License
;
; Copyright (c) 2026 Mohammad Bin Monjil and Sandip Ray
;
; Permission is hereby granted, free of charge, to any person obtaining a copy
; of this software and associated documentation files (the "Software"), to deal
; in the Software without restriction, including without limitation the rights
; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
; copies of the Software, and to permit persons to whom the Software is
; furnished to do so, subject to the following conditions:
;
; The above copyright notice and this permission notice shall be included in all
; copies or substantial portions of the Software.
;
; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
; SOFTWARE.


(in-package "ACL2")
(include-book "model")
(include-book "good_state_inv")

;end setup


;start definitions: imp/spec equivalence predicates


(defun imp-spec-channel-msgs-equivalent-p (imp-msgs spec-msgs)
  ;; SPEC-MSGS should be exactly the normal-message projection of IMP-MSGS.
  (if (endp imp-msgs)
      (endp spec-msgs)
    (let ((msg (first imp-msgs)))
      (if (equal (msg-type msg) :normal)
          (and
           (consp spec-msgs)
           (equal msg (first spec-msgs))
           (imp-spec-channel-msgs-equivalent-p
            (rest imp-msgs)
            (rest spec-msgs)))
        (imp-spec-channel-msgs-equivalent-p
         (rest imp-msgs)
         spec-msgs)))))

(defun incoming-channels-equivalent-for-proc-p
    (srcs dst imp-channels spec-channels)
  ;; Check every incoming channel src -> dst.
  (if (endp srcs)
      t
    (and
     (imp-spec-channel-msgs-equivalent-p
      (channel-state (first srcs) dst imp-channels)
      (channel-state (first srcs) dst spec-channels))
     (incoming-channels-equivalent-for-proc-p
      (rest srcs)
      dst
      imp-channels
      spec-channels))))

(defun imp-spec-channels-equivalent-p-aux
    (dsts imp-procs imp-channels spec-channels)
  ;; For each destination process, check all of its incoming channels.
  (if (endp dsts)
      t
    (let* ((dst       (first dsts))
           (imp-p     (g dst imp-procs))
           (srcs      (nbrs-from imp-p)))
      (and
       (incoming-channels-equivalent-for-proc-p
        srcs
        dst
        imp-channels
        spec-channels)
       (imp-spec-channels-equivalent-p-aux
        (rest dsts)
        imp-procs
        imp-channels
        spec-channels)))))

(defun imp-spec-channels-equivalent-p (ids imp-st spec-st)
  (imp-spec-channels-equivalent-p-aux
   ids
   (procs imp-st)
   (channels imp-st)
   (channels spec-st)))

(defun imp-spec-equivalent-p (imp-st spec-st)
  ;; Full implementation/spec equivalence:
  (let ((ids (proc-ids imp-st)))
    (and
     (equal (proc-ids imp-st)
            (proc-ids spec-st))
     (procs-equivalent-p
      ids
      (procs imp-st)
      (procs spec-st))
     (imp-spec-channels-equivalent-p
      ids
      imp-st
      spec-st))))

;end definitions: imp/spec equivalence predicates


;start basic consequences of equivalence
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic consequences of full equivalence
;; Small projection facts used by later step-level proofs.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(encapsulate ()

(local-defthm proc-ids-equal-when-imp-spec-equivalent-p
  (implies
   (imp-spec-equivalent-p imp-st spec-st)
   (equal (proc-ids imp-st)
          (proc-ids spec-st))))

(local-defthm proc-equivalent-p-implies-local-state-equal
  (implies
   (proc-equivalent-p imp-p spec-p)
   (equal
    (local-state imp-p)
    (local-state spec-p))))

;end basic consequences of equivalence


;start normal-step process update lemmas
;; Normal-step process update lemmas A normal local step updates the same visible local-state field on both sides.
(local-defthm proc-equivalent-p-of-same-local-state-update
  (implies
   (proc-equivalent-p imp-p spec-p)
   (proc-equivalent-p
    (s :local-state new-local imp-p)
    (s :local-state new-local spec-p))))

(defthm procs-equivalent-p-of-same-local-state-update
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (procs-equivalent-p
    ids
    (s i
       (s :local-state new-local
          (g i imp-procs))
       imp-procs)
    (s i
       (s :local-state new-local
          (g i spec-procs))
       spec-procs))))

(local-defthm procs-equivalent-p-of-normal-local-state-update
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (procs-equivalent-p
    ids

    ;; Updated implementation process table.
    (s i
       (s :local-state
          (update-local-state-normal
           (local-state
            (g i imp-procs)))
          (g i imp-procs))
       imp-procs)

    ;; Updated spec process table.
    (s i
       (s :local-state
          (update-local-state-normal
           (local-state
            (g i spec-procs)))
          (g i spec-procs))
       spec-procs))))

;end normal-step process update lemmas


;start normal-step send-compute channel lemmas
;; Normal-step send-compute channel lemmas send-compute-message appends the same normal messages to implementation and spec channels.
(defun send-compute-message-pair-induct
    (local sender nbrs imp-channels spec-channels)
  (if (endp nbrs)
      (list imp-channels spec-channels)
    (if (message-to-send? local (first nbrs))
        (let* ((nbr           (first nbrs))
               (msg           (create-compute-message local nbr))

               ;; Update implementation channel sender -> nbr.
               (imp-channel   (channel-state sender nbr imp-channels))
               (imp-channel   (snoc imp-channel msg))
               (imp-channels  (>channel sender nbr imp-channel imp-channels))

               ;; Update spec channel sender -> nbr in the same way.
               (spec-channel  (channel-state sender nbr spec-channels))
               (spec-channel  (snoc spec-channel msg))
               (spec-channels (>channel sender nbr spec-channel spec-channels)))
          (send-compute-message-pair-induct
           local
           sender
           (rest nbrs)
           imp-channels
           spec-channels))
      (send-compute-message-pair-induct
       local
       sender
       (rest nbrs)
       imp-channels
       spec-channels))))

(local-defthm imp-spec-channel-msgs-equivalent-p-of-snoc-create-compute-message
  (implies
   (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
   (imp-spec-channel-msgs-equivalent-p
    (snoc imp-msgs
          (create-compute-message local nbr))
    (snoc spec-msgs
          (create-compute-message local nbr)))))

(local-defthm imp-spec-channel-msgs-equivalent-p-of-send-compute-message
  (implies
   (imp-spec-channel-msgs-equivalent-p
    (channel-state src dst imp-channels)
    (channel-state src dst spec-channels))

   (imp-spec-channel-msgs-equivalent-p
    (channel-state
     src dst
     (send-compute-message local sender nbrs imp-channels))
    (channel-state
     src dst
     (send-compute-message local sender nbrs spec-channels))))

  :hints
  (("Goal"
    :induct
    (send-compute-message-pair-induct
     local sender nbrs imp-channels spec-channels))))

(local-defthm incoming-channels-equivalent-for-proc-p-of-send-compute-message-same
  (implies
   (incoming-channels-equivalent-for-proc-p
    srcs dst imp-channels spec-channels)
   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (send-compute-message local sender nbrs imp-channels)
    (send-compute-message local sender nbrs spec-channels))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-send-compute-message-same
  (implies
   (imp-spec-channels-equivalent-p-aux
    ids imp-procs imp-channels spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (send-compute-message local sender nbrs imp-channels)
    (send-compute-message local sender nbrs spec-channels))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-local-state-update-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (s i
       (s :local-state new-local (g i procs))
       procs)
    imp-channels
    spec-channels)

   (imp-spec-channels-equivalent-p-aux
    ids
    procs
    imp-channels
    spec-channels)))

;end normal-step send-compute channel lemmas


;start projection facts from process equivalence
;; Projection facts from process equivalence When process tables are equivalent, the spec process has the same visible fields as the implementation process.
(defthm local-state-of-spec-proc-when-procs-equivalent-p
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (equal
    (local-state (g i spec-procs))
    (local-state (g i imp-procs)))))

(defthm nbrs-to-of-spec-proc-when-procs-equivalent-p
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (equal
    (nbrs-to (g i spec-procs))
    (nbrs-to (g i imp-procs)))))

;end projection facts from process equivalence


;start main theorem: normal step preserves full equivalence
;; Main theorem: normal step preserves full equivalence Implementation and spec both perform the same normal local-state update and send the same compute messages.
(local-defthm imp-spec-equivalent-p-of-step-normal
  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)
    (imp-spec-equivalent-p imp-st spec-st)
    (memberp i (proc-ids imp-st)))
   (imp-spec-equivalent-p
    (step-normal imp-st i)
    (spec-step-normal spec-st i)))
  :hints
  (("Goal"
    :in-theory
    (disable
      good-state-p
      good-spec-state-p
      good-proc-p
      good-spec-proc-p
      send-compute-message))))

;end main theorem: normal step preserves full equivalence


;start checkpoint helper process lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Checkpoint helper process lemmas
;; Starting a checkpoint only changes implementation snapshot metadata. It
;; does not change the visible fields used by proc-equivalent-p.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(local-defthm proc-equivalent-p-of-start-checkpoint-helper-left-same-proc
  (implies
   (proc-equivalent-p (g i imp-procs)
                      (g i spec-procs))
   (proc-equivalent-p
    (g i (start-checkpoint-helper imp-procs i))
    (g i spec-procs))))

(local-defthm proc-equivalent-p-of-start-checkpoint-helper-left-diff-proc
  (implies
   (and
    (not (equal k i))
    (proc-equivalent-p (g k imp-procs)
                       (g k spec-procs)))
   (proc-equivalent-p
    (g k (start-checkpoint-helper imp-procs i))
    (g k spec-procs))))

(local-defthm procs-equivalent-p-of-start-checkpoint-helper-left
  (implies
   (procs-equivalent-p ids imp-procs spec-procs)
   (procs-equivalent-p
    ids
    (start-checkpoint-helper imp-procs i)
    spec-procs))
  :hints
  (("Goal"
    :induct (procs-equivalent-p ids imp-procs spec-procs)
    :in-theory
    (disable proc-equivalent-p start-checkpoint-helper))

   ("Subgoal *1/2"
    :cases ((equal (car ids) i)))))

;end checkpoint helper process lemmas


;start checkpoint marker channel lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Checkpoint marker channel lemmas
;; Checkpoint start sends marker messages only on implementation channels.
;; Markers are non-normal, so they are ignored by the channel projection
;; relation.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(local-defthm imp-spec-channel-msgs-equivalent-p-of-snoc-create-marker-message-left
  (implies
   (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
   (imp-spec-channel-msgs-equivalent-p
    (snoc imp-msgs
          (create-marker-message local sid))
    spec-msgs)))

(local-defthm imp-spec-channel-msgs-equivalent-p-of-send-marker-one-channel
  (implies
   (imp-spec-channel-msgs-equivalent-p
    (channel-state src dst imp-channels)
    (channel-state src dst spec-channels))
   (imp-spec-channel-msgs-equivalent-p
    (channel-state
     src dst
     (send-msg-all-outgoing-channels
      (create-marker-message local sid)
      sender
      nbrs
      imp-channels))
    (channel-state
     src dst
     spec-channels)))
  :hints
  (("Goal"
    :in-theory
    (disable create-marker-message))))

(local-defthm incoming-channels-equivalent-for-proc-p-of-send-marker-left
  (implies
   (incoming-channels-equivalent-for-proc-p
    srcs dst imp-channels spec-channels)
   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (send-msg-all-outgoing-channels
     (create-marker-message local sid)
     sender
     nbrs
     imp-channels)
    spec-channels))
  :hints
  (("Goal"
    :induct
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)
    :in-theory
    (disable create-marker-message send-msg-all-outgoing-channels))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-send-marker-left
  (implies
   (imp-spec-channels-equivalent-p-aux
    ids imp-procs imp-channels spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (send-msg-all-outgoing-channels
     (create-marker-message local sid)
     sender
     nbrs
     imp-channels)
    spec-channels))
  :hints
  (("Goal"
    ;; :induct
    :in-theory
    (disable create-marker-message))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-start-checkpoint-helper-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (start-checkpoint-helper imp-procs i)
    imp-channels
    spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    imp-channels
    spec-channels))
  :hints (("Goal"
	   :in-theory (disable start-checkpoint-helper))))

;end checkpoint marker channel lemmas


;start main theorem: checkpoint step preserves full equivalence
;; Main theorem: checkpoint step preserves full equivalence The implementation may install checkpoint metadata and send markers, while the spec state remains unchanged.
(local-defthm imp-spec-equivalent-p-of-step-checkpoint
  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)
    (imp-spec-equivalent-p imp-st spec-st)
    (memberp i (proc-ids imp-st)))
   (imp-spec-equivalent-p
    (step-checkpoint imp-st i)
    spec-st))
  :hints
  (("Goal"
    :in-theory
    (disable
     good-state-p
      good-spec-state-p
      good-proc-p
      good-spec-proc-p
      send-msg-all-outgoing-channels
      create-marker-message
      start-checkpoint-helper))))

;end main theorem: checkpoint step preserves full equivalence


;start recovery-start channel-equivalence lemmas
;; Recovery-start channel-equivalence lemmas Starting recovery may change implementation recovery metadata/local state, so this block proves only channel equivalence.
(local-defthm imp-spec-channel-msgs-equivalent-p-of-snoc-create-recovery-message-left
  (implies
   (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
   (imp-spec-channel-msgs-equivalent-p
    (snoc imp-msgs
          (create-recovery-message local sid))
    spec-msgs)))

(local-defthm imp-spec-channel-msgs-equivalent-p-of-send-recovery-message-left
  (implies
   (imp-spec-channel-msgs-equivalent-p
    (channel-state src dst imp-channels)
    (channel-state src dst spec-channels))
   (imp-spec-channel-msgs-equivalent-p
    (channel-state
     src dst
     (send-msg-all-outgoing-channels
      (create-recovery-message local sid)
      sender
      nbrs
      imp-channels))
    (channel-state src dst spec-channels)))
  :hints
  (("Goal"
    :in-theory
    (disable create-recovery-message))))

(local-defthm incoming-channels-equivalent-for-proc-p-of-send-recovery-message-left
  (implies
   (incoming-channels-equivalent-for-proc-p
    srcs dst imp-channels spec-channels)
   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (send-msg-all-outgoing-channels
     (create-recovery-message local sid)
     sender
     nbrs
     imp-channels)
    spec-channels))
    :hints
  (("Goal"
    :in-theory
    (disable create-recovery-message))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-send-recovery-message-left
  (implies
   (imp-spec-channels-equivalent-p-aux
    ids imp-procs imp-channels spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (send-msg-all-outgoing-channels
     (create-recovery-message local sid)
     sender
     nbrs
     imp-channels)
    spec-channels))
  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)
    :in-theory
    (disable create-recovery-message))))

(local-defthm nbrs-from-of-start-recovery-helper
  (equal
   (nbrs-from
    (g k
       (start-recovery-helper procs i)))
   (nbrs-from
    (g k procs))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-start-recovery-helper-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (start-recovery-helper imp-procs i)
    imp-channels
    spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    imp-channels
    spec-channels))
  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)
    :in-theory
    (disable start-recovery-helper))))

(local-defthm imp-spec-channels-equivalent-p-of-step-recover
  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)
    (imp-spec-equivalent-p imp-st spec-st)
    (memberp i (proc-ids imp-st)))
   (imp-spec-channels-equivalent-p
    (proc-ids imp-st)
    (step-recover imp-st i)
    spec-st))
  :hints
  (("Goal"
    :in-theory
    (disable
     good-state-p
      good-spec-state-p
      good-proc-p
      good-spec-proc-p
      send-msg-all-outgoing-channels
      create-recovery-message
      start-recovery-helper))))

;end recovery-start channel-equivalence lemmas


;start marker receive: proc-id preservation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Marker receive: proc-id preservation
;; Marker handlers do not create or remove processes.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(local-defthm proc-ids-of-handle-first-marker-msg
  (equal
   (proc-ids
    (handle-first-marker-msg st i j msg))
   (proc-ids st)))

(local-defthm proc-ids-of-handle-non-first-marker-msg
  (equal
   (proc-ids
    (handle-non-first-marker-msg st i j msg))
   (proc-ids st)))

(local-defthm proc-ids-of-handle-marker-msg
  (equal
   (proc-ids
    (handle-marker-msg st i j msg))
   (proc-ids st)))

;end marker receive: proc-id preservation


;start non-first marker receive: process equivalence
;; Non-first marker receive: process equivalence Non-first marker handling updates only snapshot bookkeeping for the receiver.
(local-defthm proc-equivalent-p-of-update-proc-for-non-first-marker-msg-left
  (implies
   (proc-equivalent-p imp-p spec-p)
   (proc-equivalent-p
    (update-proc-for-non-first-marker-msg imp-p sid j)
    spec-p)))

(local-defthm procs-equivalent-p-of-set-non-first-marker-proc-left
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (procs-equivalent-p
    ids
    (s i
       (update-proc-for-non-first-marker-msg
        (g i imp-procs)
        sid
        j)
       imp-procs)
    spec-procs))
  :hints
  (("Goal"
    :induct (procs-equivalent-p ids imp-procs spec-procs)
    :in-theory
    (disable update-proc-for-non-first-marker-msg proc-equivalent-p))
   ("Subgoal *1/2"
    :cases ((equal i (car ids))))))

(local-defthm procs-equivalent-p-of-handle-non-first-marker-msg-left
  (implies
   (and
    (procs-equivalent-p ids
                        (procs imp-st)
                        (procs spec-st))
    (memberp i ids))
   (procs-equivalent-p
    ids
    (procs
     (handle-non-first-marker-msg imp-st i j msg))
    (procs spec-st))))

;end non-first marker receive: process equivalence


;start non-first marker receive: channel equivalence
;; Non-first marker receive: channel equivalence The handler removes a marker from j -> i.
(local-defthm imp-spec-channels-equivalent-p-aux-of-handle-non-first-marker-msg-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs
     (handle-non-first-marker-msg st i j msg))
    imp-channels
    spec-channels)

   (imp-spec-channels-equivalent-p-aux
    ids
    (procs st)
    imp-channels
    spec-channels)))

(local-defthm channels-of-handle-non-first-marker-msg
  (equal
   (channels
    (handle-non-first-marker-msg st i j msg))
   (remove-message-from-channel j i (channels st))))

(local-defthm imp-spec-channel-msgs-equivalent-p-of-cdr-left-when-head-non-normal
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
    (consp imp-msgs)
    (not (equal (msg-type (first imp-msgs)) :normal)))
   (imp-spec-channel-msgs-equivalent-p
    (rest imp-msgs)
    spec-msgs)))

(local-defthm imp-spec-channel-msgs-equivalent-p-of-remove-message-from-channel-left
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p
     (channel-state src dst imp-channels)
     (channel-state src dst spec-channels))
    ;; The channel being removed from is nonempty.
    (consp
     (channel-state rm-src rm-dst imp-channels))

    ;; The removed message is non-normal.
    (not
     (equal
      (msg-type
       (get-msg-from-channel rm-src rm-dst imp-channels))
      :normal)))

   (imp-spec-channel-msgs-equivalent-p
    (channel-state
     src dst
     (remove-message-from-channel rm-src rm-dst imp-channels))
    (channel-state src dst spec-channels)))

  :hints
  (("Goal"
    :cases ((and (equal src rm-src)
                 (equal dst rm-dst))))))

(local-defthm incoming-channels-equivalent-for-proc-p-of-remove-message-from-channel-left
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)

    (consp
     (channel-state rm-src rm-dst imp-channels))

    (not
     (equal
      (msg-type
       (get-msg-from-channel rm-src rm-dst imp-channels))
      :normal)))

   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (remove-message-from-channel rm-src rm-dst imp-channels)
    spec-channels)))

(local-defthm imp-spec-channels-equivalent-p-aux-of-remove-message-from-channel-left
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)

    (consp
     (channel-state rm-src rm-dst imp-channels))

    (not
     (equal
      (msg-type
       (get-msg-from-channel rm-src rm-dst imp-channels))
      :normal)))

   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (remove-message-from-channel rm-src rm-dst imp-channels)
    spec-channels))

  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)
    :in-theory
    (disable
     remove-message-from-channel
     incoming-channels-equivalent-for-proc-p))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-channels-handle-non-first-marker-msg-left
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids
     imp-procs
     (channels imp-st)
     spec-channels)
    ;; The channel j -> i has a head message.
    (consp
     (channel-state j i (channels imp-st)))
    ;; The consumed message is that head message.
    (equal
     msg
     (get-msg-from-channel j i (channels imp-st)))

    ;; The head message is a marker, hence non-normal.
    (equal
     (msg-type msg)
     :marker))

   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (channels
     (handle-non-first-marker-msg imp-st i j msg))
    spec-channels))

  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel
     remove-message-from-channel) )))

;end non-first marker receive: channel equivalence


;start first marker receive: process equivalence
;; First marker receive: process equivalence First marker handling creates snapshot metadata but leaves local-state and neighbor fields unchanged.
(local-defthm proc-equivalent-p-of-update-proc-for-first-marker-msg-left
  (implies
   (proc-equivalent-p imp-p spec-p)
   (proc-equivalent-p
    (update-proc-for-first-marker-msg imp-p sid j)
    spec-p)))

(local-defthm procs-equivalent-p-of-set-first-marker-proc-left
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (procs-equivalent-p
    ids
    (s i
       (update-proc-for-first-marker-msg
        (g i imp-procs)
        sid
        j)
       imp-procs)
    spec-procs))
  :hints
  (("Goal"
    :induct (procs-equivalent-p ids imp-procs spec-procs)
    :in-theory
    (disable update-proc-for-first-marker-msg))
   ("Subgoal *1/2"
    :cases ((equal i (car ids))))))

(local-defthm procs-equivalent-p-of-handle-first-marker-msg-left
  (implies
   (and
    (procs-equivalent-p ids
                        (procs imp-st)
                        (procs spec-st))
    (memberp i ids))
   (procs-equivalent-p
    ids
    (procs
     (handle-first-marker-msg imp-st i j msg))
    (procs spec-st)))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-first-marker-msg))))

;end first marker receive: process equivalence


;start reusable non-normal send lemmas
;; Reusable non-normal send lemmas These generic lemmas cover sending any non-normal protocol message on implementation channels only.
(local-defthm imp-spec-channel-msgs-equivalent-p-of-snoc-non-normal-left
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
    (not (equal (msg-type msg) :normal)))
   (imp-spec-channel-msgs-equivalent-p
    (snoc imp-msgs msg)
    spec-msgs)))

(local-defthm imp-spec-channel-msgs-equivalent-p-of-send-non-normal-msg-left
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p
     (channel-state src dst imp-channels)
     (channel-state src dst spec-channels))
    (not (equal (msg-type msg) :normal)))
   (imp-spec-channel-msgs-equivalent-p
    (channel-state
     src dst
     (send-msg-all-outgoing-channels
      msg
      sender
      nbrs
      imp-channels))
    (channel-state src dst spec-channels))))

(local-defthm incoming-channels-equivalent-for-proc-p-of-send-non-normal-msg-left
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)
    (not (equal (msg-type msg) :normal)))
   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (send-msg-all-outgoing-channels
     msg
     sender
     nbrs
     imp-channels)
    spec-channels)))

(local-defthm imp-spec-channels-equivalent-p-aux-of-send-non-normal-msg-left
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)
    (not (equal (msg-type msg) :normal)))
   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (send-msg-all-outgoing-channels
     msg
     sender
     nbrs
     imp-channels)
    spec-channels)))

;end reusable non-normal send lemmas


;start first marker receive: channel/proc helper facts
;; First marker receive: channel/proc helper facts
(local-defthm nbrs-from-of-install-snapshot-entry
  (equal
   (nbrs-from
    (install-snapshot-entry sid entry p))
   (nbrs-from p)))

(local-defthm nbrs-from-of-update-proc-for-first-marker-msg
  (equal
   (nbrs-from
    (update-proc-for-first-marker-msg p sid j))
   (nbrs-from p)))

(local-defthm nbrs-from-of-procs-handle-first-marker-msg
  (equal
   (nbrs-from
    (g k
       (procs
        (handle-first-marker-msg st i j msg))))
   (nbrs-from
    (g k
       (procs st))))
  :hints
  (("Goal"
    :cases ((equal k i)))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-handle-first-marker-msg-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs
     (handle-first-marker-msg st i j msg))
    imp-channels
    spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs st)
    imp-channels
    spec-channels))
  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids
     (procs st)
     imp-channels
     spec-channels)
    :in-theory
    (disable update-proc-for-first-marker-msg))))

(local-defthm channels-of-handle-first-marker-msg
  (equal
   (channels
    (handle-first-marker-msg st i j msg))
   (send-msg-all-outgoing-channels
    msg
    i
    (nbrs-to (g i (procs st)))
    (remove-message-from-channel j i (channels st)))))

;end first marker receive: channel/proc helper facts


;start main theorem: marker receive preserves full equivalence
;; Main theorem: marker receive preserves full equivalence Both first and non-first marker receives preserve visible process equivalence and channel projection equivalence.
(local-defthm imp-spec-equivalent-p-of-step-rcv-marker
  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)
    (imp-spec-equivalent-p imp-st spec-st)

    (memberp i (proc-ids imp-st))
    (memberp j (proc-ids imp-st))

    ;; The implementation receive consumes a marker.
    (consp (channel-state j i (channels imp-st)))
    (equal
     (msg-type
      (get-msg-from-channel j i (channels imp-st)))
     :marker))
   (imp-spec-equivalent-p
    (step-rcv imp-st i j)
    spec-st))
  :hints
  (("Goal"
    :in-theory
    ( disable
      good-state-p
      good-spec-state-p
      good-proc-p
      good-spec-proc-p
      handle-first-marker-msg
      handle-non-first-marker-msg
      send-msg-all-outgoing-channels
      remove-message-from-channel
      create-marker-message
      get-msg-from-channel
      procs-equivalent-p
      imp-spec-channels-equivalent-p-aux))))

;end main theorem: marker receive preserves full equivalence


;start first recovery receive: channel equivalence only
;; First recovery receive: channel equivalence only First recovery may restore implementation local state and set recovery status, so full process equivalence is not expected here.
(local-defthm proc-ids-of-handle-first-recovery-msg
  (equal
   (proc-ids
    (handle-first-recovery-msg st i j msg))
   (proc-ids st)))

(local-defthm nbrs-from-of-procs-handle-first-recovery-msg
  (equal
   (nbrs-from
    (g k
       (procs
        (handle-first-recovery-msg st i j msg))))
   (nbrs-from
    (g k
       (procs st))))
  :hints
  (("Goal"
    :cases ((equal k i))
    :in-theory
    (disable
     replay-channel-snapshots
     replay-msgs-on-channel
     remove-from-list))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-handle-first-recovery-msg-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs
     (handle-first-recovery-msg st i j msg))
    imp-channels
    spec-channels)
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs st)
    imp-channels
    spec-channels))
  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids
     (procs st)
     imp-channels
     spec-channels)
    :in-theory
    (disable
     handle-first-recovery-msg
     replay-channel-snapshots
     replay-msgs-on-channel))))

(local-defthm channels-of-handle-first-recovery-msg
  (equal
   (channels
    (handle-first-recovery-msg st i j msg))
   (send-msg-all-outgoing-channels
    msg
    i
    (nbrs-to (g i (procs st)))
    (remove-message-from-channel j i (channels st)))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-channels-handle-first-recovery-msg-left
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids
     imp-procs
     (channels imp-st)
     spec-channels)

    ;; The channel j -> i has a head message.
    (consp
     (channel-state j i (channels imp-st)))

    ;; The consumed message is that head message.
    (equal
     msg
     (get-msg-from-channel j i (channels imp-st)))

    ;; The head message is a recovery message, hence non-normal.
    (equal
     (msg-type msg)
     :recovery))

   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (channels
     (handle-first-recovery-msg imp-st i j msg))
    spec-channels))

  :hints
  (("Goal"
    :in-theory
    (disable
     handle-first-recovery-msg
     send-msg-all-outgoing-channels
     remove-message-from-channel
     get-msg-from-channel))))

(local-defthm imp-spec-channels-equivalent-p-of-handle-first-recovery-msg
  (implies
   (and
    (imp-spec-channels-equivalent-p
     ids
     imp-st
     spec-st)

    ;; The channel j -> i has a recovery message at the head.
    (consp
     (channel-state j i (channels imp-st)))

    (equal
     msg
     (get-msg-from-channel j i (channels imp-st)))

    (equal
     (msg-type msg)
     :recovery))

   (imp-spec-channels-equivalent-p
    ids
    (handle-first-recovery-msg imp-st i j msg)
    spec-st))

  :hints
  (("Goal"
    :in-theory
    (disable
     handle-first-recovery-msg
     send-msg-all-outgoing-channels
     remove-message-from-channel
     get-msg-from-channel
     imp-spec-channels-equivalent-p-aux))))

(local-defthm imp-spec-channels-equivalent-p-of-step-rcv-first-recovery
  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)
    (imp-spec-equivalent-p imp-st spec-st)

    (memberp i (proc-ids imp-st))
    (memberp j (proc-ids imp-st))

    ;; First recovery message means receiver i is still normal.
    (equal
     (proc-status (g i (procs imp-st)))
     :normal)

    ;; The implementation receive consumes a recovery message.
    (consp
     (channel-state j i (channels imp-st)))

    (equal
     (msg-type
      (get-msg-from-channel j i (channels imp-st)))
     :recovery))

   (imp-spec-channels-equivalent-p
    (proc-ids imp-st)
    (step-rcv imp-st i j)
    spec-st))

  :hints
  (("Goal"
    :in-theory
    (disable
     good-state-p
     good-spec-state-p
     good-proc-p
     good-spec-proc-p
    ; step-rcv
    ; handle-recovery-msg
     handle-first-recovery-msg
     send-msg-all-outgoing-channels
     remove-message-from-channel
     get-msg-from-channel
     replay-channel-snapshots
     replay-msgs-on-channel
     imp-spec-channels-equivalent-p-aux))))

;end first recovery receive: channel equivalence only


;start non-first recovery receive: process equivalence
;; Non-first recovery receive: process equivalence Non-first recovery only updates recovery bookkeeping.
(local-defthm proc-equivalent-p-of-update-proc-for-non-first-recovery-msg-left
  (implies
   (proc-equivalent-p imp-p spec-p)
   (proc-equivalent-p
    (update-proc-for-non-first-recovery-msg imp-p j)
    spec-p))
  :hints
  (("Goal"
    :in-theory
    (disable remove-from-list))))

(local-defthm procs-equivalent-p-of-set-non-first-recovery-proc-left
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (procs-equivalent-p
    ids
    (s i
       (update-proc-for-non-first-recovery-msg
        (g i imp-procs)
        j)
       imp-procs)
    spec-procs))
  :hints
  (("Goal"
    :induct (procs-equivalent-p ids imp-procs spec-procs)
    :in-theory
    (disable
     update-proc-for-non-first-recovery-msg
     proc-equivalent-p))
   ("Subgoal *1/2"
    :cases ((equal i (car ids))))))

(local-defthm procs-equivalent-p-of-handle-non-first-recovery-msg-left
  (implies
   (and
    (procs-equivalent-p ids
                        (procs imp-st)
                        (procs spec-st))
    (memberp i ids))
   (procs-equivalent-p
    ids
    (procs
     (handle-non-first-recovery-msg imp-st i j msg))
    (procs spec-st)))
  :hints
  (("Goal"
    :in-theory
    (disable
     update-proc-for-non-first-recovery-msg
     proc-equivalent-p))))

;end non-first recovery receive: process equivalence


;start non-first recovery receive: channel/proc helper facts
;; Non-first recovery receive: channel/proc helper facts
(local-defthm nbrs-from-of-update-proc-for-non-first-recovery-msg
  (equal
   (nbrs-from
    (update-proc-for-non-first-recovery-msg p j))
   (nbrs-from p))
  :hints
  (("Goal"
    :in-theory
    (disable remove-from-list))))

(local-defthm nbrs-from-of-procs-handle-non-first-recovery-msg
  (equal
   (nbrs-from
    (g k
       (procs
        (handle-non-first-recovery-msg st i j msg))))
   (nbrs-from
    (g k
       (procs st))))
  :hints
  (("Goal"
    :cases ((equal k i))
    :in-theory
    (disable
     update-proc-for-non-first-recovery-msg
     remove-from-list))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-handle-non-first-recovery-msg-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs
     (handle-non-first-recovery-msg st i j msg))
    imp-channels
    spec-channels)

   (imp-spec-channels-equivalent-p-aux
    ids
    (procs st)
    imp-channels
    spec-channels))
  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids
     (procs st)
     imp-channels
     spec-channels)
    :in-theory
    (disable
     handle-non-first-recovery-msg
     update-proc-for-non-first-recovery-msg
     remove-from-list))))

(local-defthm proc-ids-of-handle-non-first-recovery-msg
  (equal
   (proc-ids
    (handle-non-first-recovery-msg st i j msg))
   (proc-ids st)))

(local-defthm channels-of-handle-non-first-recovery-msg
  (equal
   (channels
    (handle-non-first-recovery-msg st i j msg))
   (remove-message-from-channel j i (channels st))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-channels-handle-non-first-recovery-msg-left
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids
     imp-procs
     (channels imp-st)
     spec-channels)

    ;; The channel j -> i has a head message.
    (consp
     (channel-state j i (channels imp-st)))

    ;; The consumed message is that head message.
    (equal
     msg
     (get-msg-from-channel j i (channels imp-st)))

    ;; The head message is recovery, hence non-normal.
    (equal
     (msg-type msg)
     :recovery))

   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (channels
     (handle-non-first-recovery-msg imp-st i j msg))
    spec-channels))

  :hints
  (("Goal"
    :in-theory
    (disable
     handle-non-first-recovery-msg
     get-msg-from-channel
     remove-message-from-channel))))

;end non-first recovery receive: channel/proc helper facts


;start main theorem: non-first recovery receive preserves full equivalence
;; Main theorem: non-first recovery receive preserves full equivalence Because only bookkeeping changes and one non-normal recovery message is removed, the full imp/spec.
(local-defthm imp-spec-equivalent-p-of-handle-non-first-recovery-msg
  (implies
   (and
    (imp-spec-equivalent-p imp-st spec-st)

    ;; Needed because only process i is updated.
    (memberp i (proc-ids imp-st))

    ;; The channel j -> i has a recovery message at the head.
    (consp
     (channel-state j i (channels imp-st)))

    (equal
     msg
     (get-msg-from-channel j i (channels imp-st)))

    (equal
     (msg-type msg)
     :recovery))

   (imp-spec-equivalent-p
    (handle-non-first-recovery-msg imp-st i j msg)
    spec-st))

  :hints
  (("Goal"
    :in-theory
    (disable
     handle-non-first-recovery-msg
     update-proc-for-non-first-recovery-msg
     get-msg-from-channel
     remove-message-from-channel
     imp-spec-channels-equivalent-p-aux
     procs-equivalent-p))))

(local-defthm imp-spec-equivalent-p-of-step-rcv-non-first-recovery
  (implies
   (and
    (good-state-p imp-st)
    (good-spec-state-p spec-st)
    (imp-spec-equivalent-p imp-st spec-st)

    (memberp i (proc-ids imp-st))
    (memberp j (proc-ids imp-st))

    ;; Non-first recovery means receiver i is already not normal.
    (not
     (equal
      (proc-status (g i (procs imp-st)))
      :normal))

    ;; The implementation receive consumes a recovery message.
    (consp
     (channel-state j i (channels imp-st)))

    (equal
     (msg-type
      (get-msg-from-channel j i (channels imp-st)))
     :recovery))

   (imp-spec-equivalent-p
    (step-rcv imp-st i j)
    spec-st))

  :hints
  (("Goal"
    :in-theory
    (disable
     good-state-p
     good-spec-state-p
     good-proc-p
     good-spec-proc-p
     handle-non-first-recovery-msg
     update-proc-for-non-first-recovery-msg
     get-msg-from-channel
     remove-message-from-channel
     remove-from-list
     imp-spec-channels-equivalent-p-aux
     procs-equivalent-p))))

;end main theorem: non-first recovery receive preserves full equivalence


;start normal receive: process equivalence
;; Normal receive: process equivalence A normal receive updates the implementation process using the normal- message core and updates the spec process using spec-step-rcv.
(local-defthm proc-ids-of-handle-normal-msg-core
  (equal
   (proc-ids
    (handle-normal-msg-core st i j msg))
   (proc-ids st)))

(local-defthm proc-equivalent-p-of-update-proc-for-normal-msg-core-left-right
  (implies
   (proc-equivalent-p imp-p spec-p)
   (proc-equivalent-p
    (update-proc-for-normal-msg-core imp-p j msg)
    (update spec-p
            :local-state
            (update-local-state-rcv
             (local-state spec-p)
             msg
             j))))
  :hints
  (("Goal"
    :in-theory
    (disable record-msg-in-snapshots))))

(local-defthm procs-equivalent-p-of-set-normal-msg-core-left-right
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (memberp i ids))
   (procs-equivalent-p
    ids
    (s i
       (update-proc-for-normal-msg-core
        (g i imp-procs)
        j
        msg)
       imp-procs)
    (s i
       (update (g i spec-procs)
               :local-state
               (update-local-state-rcv
                (local-state (g i spec-procs))
                msg
                j))
       spec-procs)))
  :hints
  (("Goal"
    :induct (procs-equivalent-p ids imp-procs spec-procs)
    :in-theory
    (disable
     update-proc-for-normal-msg-core
     LOCAL-STATE-OF-SPEC-PROC-WHEN-PROCS-EQUIVALENT-P
     proc-equivalent-p))
   ("Subgoal *1/2"
    :cases ((equal i (car ids))))))

(local-defthm procs-equivalent-p-of-handle-normal-msg-core-and-spec-step-rcv
  (implies
   (and
    (procs-equivalent-p ids
                        (procs imp-st)
                        (procs spec-st))
    (memberp i ids)

    msg  
    ;; The spec receive must use the same normal application message.
    (equal
     msg
     (get-msg-from-channel j i (channels spec-st))))

   (procs-equivalent-p
    ids
    (procs
     (handle-normal-msg-core imp-st i j msg))
    (procs
     (spec-step-rcv spec-st i j))))

  :hints
  (("Goal"
    :in-theory
    (disable
      LOCAL-STATE-OF-SPEC-PROC-WHEN-PROCS-EQUIVALENT-P
     update-proc-for-normal-msg-core
     procs-equivalent-p))))

(local-defthm proc-ids-of-spec-step-rcv
  (equal
   (proc-ids
    (spec-step-rcv st i j))
   (proc-ids st)))

;end normal receive: process equivalence


;start normal receive: getting the matching spec message
;; Normal receive: getting the matching spec message If the implementation head message is normal, then the corresponding spec channel head is the same message.
(local-defthm imp-spec-channel-msgs-equivalent-p-when-incoming-channels-equivalent-for-proc-p
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)
    (memberp src srcs))
   (imp-spec-channel-msgs-equivalent-p
    (channel-state src dst imp-channels)
    (channel-state src dst spec-channels))))

(local-defthm imp-spec-channel-msgs-equivalent-p-when-imp-spec-channels-equivalent-p-aux
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)
    (memberp dst ids)
    (memberp src (nbrs-from (g dst imp-procs))))
   (imp-spec-channel-msgs-equivalent-p
    (channel-state src dst imp-channels)
    (channel-state src dst spec-channels))))

(local-defthm first-spec-msg-when-left-head-normal-and-msgs-equivalent
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
    (consp imp-msgs)
    (equal (msg-type (first imp-msgs)) :normal))
   (equal (first spec-msgs)
          (first imp-msgs))))

(local-defthm get-msg-from-channel-equal-when-imp-spec-channels-equivalent-p-aux
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids
     imp-procs
     imp-channels
     spec-channels)

    ;; dst must be one of the destinations checked by ids.
    (memberp dst ids)

    ;; src -> dst must be one of dst's checked incoming channels.
    (memberp src
             (nbrs-from
              (g dst imp-procs)))

    ;; Implementation channel has a head message.
    (consp
     (channel-state src dst imp-channels))

    ;; Implementation head message is visible to spec.
    (equal
     (msg-type
      (get-msg-from-channel src dst imp-channels))
     :normal))

   (equal
    (get-msg-from-channel src dst spec-channels)
    (get-msg-from-channel src dst imp-channels)))

  :hints
  (("Goal"
    :use
    ((:instance
      imp-spec-channel-msgs-equivalent-p-when-imp-spec-channels-equivalent-p-aux
      (ids ids)
      (imp-procs imp-procs)
      (imp-channels imp-channels)
      (spec-channels spec-channels)
      (src src)
      (dst dst))

     (:instance
      first-spec-msg-when-left-head-normal-and-msgs-equivalent
      (imp-msgs
       (channel-state src dst imp-channels))
      (spec-msgs
       (channel-state src dst spec-channels))))

    :in-theory
    (disable imp-spec-channel-msgs-equivalent-p
      imp-spec-channel-msgs-equivalent-p-when-imp-spec-channels-equivalent-p-aux
      first-spec-msg-when-left-head-normal-and-msgs-equivalent
      imp-spec-channels-equivalent-p-aux
      incoming-channels-equivalent-for-proc-p))))

;end normal receive: getting the matching spec message


;start normal receive: channel equivalence after consuming normal messages
;; Normal receive: channel equivalence after consuming normal messages For a normal receive, both implementation and spec consume the same visible channel head.
(local-defthm nbrs-from-of-procs-handle-normal-msg-core
  (equal
   (nbrs-from
    (g k
       (procs
        (handle-normal-msg-core st i j msg))))
   (nbrs-from
    (g k
       (procs st))))
  :hints
  (("Goal"
    :cases ((equal k i))
    :in-theory
    (disable
     update-proc-for-normal-msg-core
     record-msg-in-snapshots
     remove-message-from-channel))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-handle-normal-msg-core-procs
  (equal
   (imp-spec-channels-equivalent-p-aux
    ids
    (procs
     (handle-normal-msg-core st i j msg))
    imp-channels
    spec-channels)

   (imp-spec-channels-equivalent-p-aux
    ids
    (procs st)
    imp-channels
    spec-channels))
  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids
     (procs st)
     imp-channels
     spec-channels)
    :in-theory
    (disable
     handle-normal-msg-core
     update-proc-for-normal-msg-core
     record-msg-in-snapshots
     remove-message-from-channel))))

(local-defthm imp-spec-channel-msgs-equivalent-p-of-cdr-both-when-left-head-normal
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p imp-msgs spec-msgs)
    (consp imp-msgs)
    (equal (msg-type (first imp-msgs)) :normal))
   (imp-spec-channel-msgs-equivalent-p
    (rest imp-msgs)
    (rest spec-msgs))))

(local-defthm imp-spec-channel-msgs-equivalent-p-of-remove-message-from-channel-both
  (implies
   (and
    (imp-spec-channel-msgs-equivalent-p
     (channel-state src dst imp-channels)
     (channel-state src dst spec-channels))

    ;; The removed implementation channel is nonempty.
    (consp
     (channel-state rm-src rm-dst imp-channels))

    ;; The removed implementation head is normal.
    (equal
     (msg-type
      (get-msg-from-channel rm-src rm-dst imp-channels))
     :normal))

   (imp-spec-channel-msgs-equivalent-p
    (channel-state
     src dst
     (remove-message-from-channel rm-src rm-dst imp-channels))
    (channel-state
     src dst
     (remove-message-from-channel rm-src rm-dst spec-channels)))))

(local-defthm incoming-channels-equivalent-for-proc-p-of-remove-message-from-channel-both
  (implies
   (and
    (incoming-channels-equivalent-for-proc-p
     srcs dst imp-channels spec-channels)

    (consp
     (channel-state rm-src rm-dst imp-channels))

    (equal
     (msg-type
      (get-msg-from-channel rm-src rm-dst imp-channels))
     :normal))

   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    (remove-message-from-channel rm-src rm-dst imp-channels)
    (remove-message-from-channel rm-src rm-dst spec-channels))))

(local-defthm imp-spec-channels-equivalent-p-aux-of-remove-message-from-channel-both
  (implies
   (and
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)

    (consp
     (channel-state rm-src rm-dst imp-channels))

    (equal
     (msg-type
      (get-msg-from-channel rm-src rm-dst imp-channels))
     :normal))

   (imp-spec-channels-equivalent-p-aux
    ids
    imp-procs
    (remove-message-from-channel rm-src rm-dst imp-channels)
    (remove-message-from-channel rm-src rm-dst spec-channels)))

  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     ids imp-procs imp-channels spec-channels)
    :in-theory
    (disable
     remove-message-from-channel
     get-msg-from-channel
     incoming-channels-equivalent-for-proc-p))))

(local-defthm channels-of-handle-normal-msg-core
  (equal
   (channels
    (handle-normal-msg-core st i j msg))
   (remove-message-from-channel j i (channels st))))

;; (defthm channels-of-spec-step-rcv
;;   (equal
;;    (channels
;;     (spec-step-rcv st i j))
;;    (remove-message-from-channel j i (channels st))))

(local-defthm channels-of-spec-step-rcv-when-msg
  (implies
   (get-msg-from-channel j i (channels st))
   (equal
    (channels
     (spec-step-rcv st i j))
    (remove-message-from-channel j i (channels st)))))

(local-defthm channels-of-spec-step-rcv-when-no-msg
  (implies
   (not (get-msg-from-channel j i (channels st)))
   (equal
    (channels
     (spec-step-rcv st i j))
    (channels st))))

;end normal receive: channel equivalence after consuming normal messages


;start main theorem: normal receive preserves full equivalence
;; Main theorem: normal receive preserves full equivalence The implementation and spec consume the same normal message and update the receiver consistently.
(local-defthm imp-spec-equivalent-p-of-handle-normal-msg-core
  (implies
   (and
    (imp-spec-equivalent-p imp-st spec-st)

    ;; Process i must be checked by process equivalence.
    (memberp i (proc-ids imp-st))

    ;; j -> i must be a checked incoming channel, so the spec receives
    ;; the same normal message as the implementation.
    (memberp j (nbrs-from (g i (procs imp-st))))

    ;; Implementation consumes msg from channel j -> i.
    (consp
     (channel-state j i (channels imp-st)))

    (equal
     msg
     (get-msg-from-channel j i (channels imp-st)))

    (equal
     (msg-type msg)
     :normal))

   (imp-spec-equivalent-p
    (handle-normal-msg-core imp-st i j msg)
    (spec-step-rcv spec-st i j)))

  :hints
  (("Goal"
    :in-theory
    (disable
     handle-normal-msg-core
     spec-step-rcv
     LOCAL-STATE-OF-SPEC-PROC-WHEN-PROCS-EQUIVALENT-P
     update-proc-for-normal-msg-core
     get-msg-from-channel
     remove-message-from-channel
     imp-spec-channels-equivalent-p-aux
     ;procs-equivalent-p
     ))))

;end main theorem: normal receive preserves full equivalence







;start theorem: rep of good implementation state is equivalent
;; REP correctness for a single implementation state


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic subset/list lemmas used to connect good-state neighbor facts to
;; the channel projection proof.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm subset-reflexive-for-rep
;;   (subset x x))

;; (defthm memberp-when-subset-for-rep
;;   (implies
;;    (and
;;     (subset xs ys)
;;     (memberp x xs))
;;    (memberp x ys)))


;; Process part of REP

(local-defthm proc-equivalent-p-of-map-proc-to-spec-proc
  (proc-equivalent-p
   imp-p
   (map-proc-to-spec-proc imp-p)))


(defthm procs-equivalent-p-of-s-irrelevant-spec-procs
  (implies
   (and
    (procs-equivalent-p ids imp-procs spec-procs)
    (not (memberp k ids)))
   (procs-equivalent-p
    ids
    imp-procs
    (s k v spec-procs)))
  :hints
  (("Goal"
    :induct (procs-equivalent-p ids imp-procs spec-procs))))


(local-defthm procs-equivalent-p-of-map-procs-to-spec-procs
  (implies
   (uniquep ids)
   (procs-equivalent-p
    ids
    imp-procs
    (map-procs-to-spec-procs ids imp-procs)))
  :hints
  (("Goal"
    :induct (map-procs-to-spec-procs ids imp-procs))))


;; Channel-message part of REP

(local-defthm imp-spec-channel-msgs-equivalent-p-of-project-channel-msgs-to-spec
  (imp-spec-channel-msgs-equivalent-p
   msgs
   (project-channel-msgs-to-spec msgs))
  :hints
  (("Goal"
    :induct (project-channel-msgs-to-spec msgs))))


;; Channel lookup facts for the channel projection built by REP

(local-defthm g-of-project-channel-row-to-spec
  (implies
   (and
    (uniquep srcs)
    (memberp src srcs))
   (equal
    (g src
       (project-channel-row-to-spec srcs dst imp-channels))
    (project-channel-msgs-to-spec
     (channel-state src dst imp-channels))))
  :hints
  (("Goal"
    :induct (project-channel-row-to-spec srcs dst imp-channels))))

(local-defthm channel-state-of-project-channels-to-spec-aux
  (implies
   (and
    (uniquep dsts)
    (uniquep srcs)
    (memberp dst dsts)
    (memberp src srcs))
   (equal
    (channel-state
     src
     dst
     (project-channels-to-spec-aux dsts srcs imp-channels))
    (project-channel-msgs-to-spec
     (channel-state src dst imp-channels))))
  :hints
  (("Goal"
    :induct (project-channels-to-spec-aux dsts srcs imp-channels))))


(local-defthm channel-state-of-project-channels-to-spec
  (implies
   (and
    (uniquep ids)
    (memberp dst ids)
    (memberp src ids))
   (equal
    (channel-state
     src
     dst
     (project-channels-to-spec ids imp-channels))
    (project-channel-msgs-to-spec
     (channel-state src dst imp-channels)))))


;; Lift channel projection to incoming channels for one destination.

(local-defthm incoming-channels-equivalent-for-proc-p-of-project-channels-to-spec
  (implies
   (and
    (uniquep ids)
    (memberp dst ids)
    (subset srcs ids))
   (incoming-channels-equivalent-for-proc-p
    srcs
    dst
    imp-channels
    (project-channels-to-spec ids imp-channels)))
  :hints
  (("Goal"
    :induct
    (incoming-channels-equivalent-for-proc-p
     srcs
     dst
     imp-channels
     (project-channels-to-spec ids imp-channels)))))


;; Helper predicate:

(defun all-nbrs-from-subset-p (dsts procs ids)
  (if (endp dsts)
      t
    (and
     (subset
      (nbrs-from (g (first dsts) procs))
      ids)
     (all-nbrs-from-subset-p
      (rest dsts)
      procs
      ids))))


(local-defthm all-nbrs-from-subset-p-when-good-procs-p
  (implies
   (good-procs-p dsts procs ids)
   (all-nbrs-from-subset-p dsts procs ids))
  :hints
  (("Goal"
    :induct (good-procs-p dsts procs ids))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lift channel projection to all checked destination processes.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm imp-spec-channels-equivalent-p-aux-of-project-channels-to-spec
  (implies
   (and
    (uniquep ids)
    (subset dsts ids)
    (all-nbrs-from-subset-p dsts imp-procs ids))
   (imp-spec-channels-equivalent-p-aux
    dsts
    imp-procs
    imp-channels
    (project-channels-to-spec ids imp-channels)))
  :hints
  (("Goal"
    :induct
    (imp-spec-channels-equivalent-p-aux
     dsts
     imp-procs
     imp-channels
     (project-channels-to-spec ids imp-channels)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main theorem:
;; A good implementation state is equivalent to its REP.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm imp-spec-equivalent-p-of-rep
  (implies
   (good-state-p imp-st)
   (imp-spec-equivalent-p
    imp-st
    (rep imp-st)))
  :hints
  (("Goal"
    :in-theory
    (disable
     procs-equivalent-p
      imp-spec-channels-equivalent-p-aux
      project-channels-to-spec
      map-procs-to-spec-procs))))

;end theorem: rep of good implementation state is equivalent



(defthm procs-equivalent-p-reflexive
  (procs-equivalent-p
   ids
   procs
   procs))

) ;; end private channel-equivalence proof development
