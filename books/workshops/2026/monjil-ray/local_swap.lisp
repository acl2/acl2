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
(include-book "scan")
(include-book "good_state_inv")
(include-book "channel_equivalence")
(include-book "basic")
(include-book "recovery_inv")
(include-book "cut_meta_inv")

;; Proof roadmap

;; Complete isolated checkpoint segment using the unified cut scan

;; ------------------------------------------------------------------
;; Segment identity and metadata
;; ------------------------------------------------------------------

(defun checkpoint-segment-initiator (input-seg)
  (pid (first input-seg)))

(defun checkpoint-segment-sid (st input-seg)
  (let* ((i (checkpoint-segment-initiator input-seg))
         (p (g i (procs st))))
    (list i (counter p))))

(defun checkpoint-segment-initial-meta (st input-seg)
  (make-cut-meta
   (checkpoint-segment-sid st input-seg)
   (checkpoint-segment-initiator input-seg)
   st))

(defun checkpoint-segment-meta (st input-seg)
  (scan-until-checkpoint-done
   input-seg
   st
   (checkpoint-segment-initial-meta st input-seg)))

(defun checkpoint-segment-completep (st input-seg)
  (checkpoint-collection-complete-p
   (checkpoint-segment-meta st input-seg)))

(defun checkpoint-segment-end-state (st input-seg)
  (run-imp st input-seg))

;; ------------------------------------------------------------------
;; Completion occurs exactly at the segment boundary
;; ------------------------------------------------------------------

(defun checkpoint-completes-at-segment-end-p (inputs st m)
  (declare (xargs :measure (acl2-count inputs)))
  (if (endp inputs)
      (checkpoint-collection-complete-p m)
    (and
     (not (checkpoint-collection-complete-p m))
     (let* ((input   (first inputs))
            (next-m  (process-cut-step input st m))
            (next-st (system-step st input)))
       (checkpoint-completes-at-segment-end-p
        (rest inputs) next-st next-m)))))

;; ------------------------------------------------------------------
;; Recorded before/after partition
;; ------------------------------------------------------------------

(defun checkpoint-segment-before-cut-inputs (st input-seg)
  (cm-before-cut-input-sequence
   (checkpoint-segment-meta st input-seg)))

(defun checkpoint-segment-after-cut-inputs (st input-seg)
  (cm-after-cut-input-sequence
   (checkpoint-segment-meta st input-seg)))

(defun checkpoint-segment-reordered-inputs (st input-seg)
  (append
   (checkpoint-segment-before-cut-inputs st input-seg)
   (checkpoint-segment-after-cut-inputs st input-seg)))

;; ------------------------------------------------------------------
;; Complete checkpoint segment
;; ------------------------------------------------------------------

(defun checkpoint-start-end-segment-p (st input-seg)
  (and
   (consp input-seg)
   (equal (ttype (first input-seg)) :start-checkpoint)
   (true-listp input-seg)
   (cl-checkpoint-body-inputs-p (rest input-seg))
   (good-state-p st)
   (legal-input-sequencep st input-seg)
   (recovery-free-state-p st)
   (checkpoint-segment-completep st input-seg)
   (checkpoint-completes-at-segment-end-p
    input-seg
    st
    (checkpoint-segment-initial-meta st input-seg))))

;; Local two-input independence contract
(defun two-imp-inputs-swappable-p
    (st input-1 input-2)
  (let* ((st-1 (system-step st input-1))
         (st-2 (system-step st input-2)))
    (and
     ;; Preserve each process's local input order.
     (not
      (equal
       (pid input-1)
       (pid input-2)))
     ;; Both inputs are valid checkpoint-segment body inputs.
     ;; This includes checkpoint starts for other SIDs.
     (cl-checkpoint-body-input-p input-1)
     (cl-checkpoint-body-input-p input-2)
     ;; Both execution orders are legal.
     (legal-inputp st input-1)
     (legal-inputp st-1 input-2)
     (legal-inputp st input-2)
     (legal-inputp st-2 input-1)
     ;; Neither execution order performs recovery activity.
     (no-recovery-step-p input-1 st)
     (no-recovery-step-p input-2 st-1)
     (no-recovery-step-p input-2 st)
     (no-recovery-step-p input-1 st-2))))

;; Channel algebra for independent implementation steps

;; This encapsulate exports only the small interface needed by the global reorder proof.
(encapsulate
 ()

;; Updates to rows belonging to distinct senders commute, even when their
;; destination keys happen to be equal.
(local-defthm channel-updates-different-senders-commute
  (implies
   (not (equal i1 i2))
   (equal
    (>channel
     i2 dst2 val2
     (>channel
      i1 dst1 val1
      channels))
    (>channel
     i1 dst1 val1
     (>channel
      i2 dst2 val2
      channels))))
  :hints
  (("Goal"
    :cases
    ((equal dst1 dst2)))))

;; A compute-message send from I2 cannot disturb a separately installed channel value whose sender is I1.
(local-defthm send-compute-message-preserves-other-sender-update
  (implies
   (not (equal i1 i2))
   (equal
    (send-compute-message
     local2
     i2
     nbrs2
     (s dst
        (s i1 val
           (g dst channels))
        channels))
    (s dst
       (s i1 val
          (g dst
             (send-compute-message
              local2
              i2
              nbrs2
              channels)))
       (send-compute-message
        local2
        i2
        nbrs2
        channels)))))

;; Two normal compute sends from different processes may be exchanged
;; without changing the concrete channel table.
(local-defthm send-compute-message-different-senders-commute
  (implies
   (not (equal i1 i2))
   (equal
    (send-compute-message
     local2
     i2
     nbrs2
     (send-compute-message
      local1
      i1
      nbrs1
      channels))
    (send-compute-message
     local1
     i1
     nbrs1
     (send-compute-message
      local2
      i2
      nbrs2
      channels)))))

;; Normal application execution changes process and channel contents but not
;; the universe or order of process identifiers.
(local-defthm proc-ids-of-step-normal
  (equal
   (proc-ids
   (step-normal st i))
   (proc-ids st)))

;; Starting a checkpoint at I2 commutes with replacing the distinct process
;; slot I1.  This isolates the process-table part of mixed normal/start cases.
(local-defthm start-checkpoint-helper-commutes-with-other-proc-update
  (implies
   (not (equal i1 i2))
   (equal
    (start-checkpoint-helper
     (s i1 p1 procs)
     i2)
    (s i1
       p1
       (start-checkpoint-helper
        procs
        i2)))))

;; Projection lemmas for marker traffic

;; Projecting one concrete channel erases a marker appended by broadcast.
(local-defthm project-channel-msgs-marker-send-invisible
  (implies
   (equal (msg-type msg) :marker)
   (equal
    (project-channel-msgs-to-spec
     (channel-state
      src
      dst
      (send-msg-all-outgoing-channels
       msg i nbrs channels)))
    (project-channel-msgs-to-spec
     (channel-state
      src
      dst
     channels)))))

;; Lift marker invisibility from one channel to one destination row.
(local-defthm project-channel-row-marker-send-invisible
  (implies
   (equal (msg-type msg) :marker)
   (equal
    (project-channel-row-to-spec
     srcs
     dst
     (send-msg-all-outgoing-channels
      msg i nbrs channels))
    (project-channel-row-to-spec
     srcs
     dst
     channels))))

;; Lift marker invisibility once more to the complete projected channel map.
(local-defthm project-channels-marker-send-invisible
  (implies
   (equal (msg-type msg) :marker)
   (equal
    (project-channels-to-spec-aux
     dsts
     srcs
     (send-msg-all-outgoing-channels
      msg i nbrs channels))
    (project-channels-to-spec-aux
     dsts
     srcs
     channels))))

;; A broadcast sent by I2 leaves every channel whose sender is I1 unchanged.
(local-defthm channel-state-of-send-msg-all-other-sender
  (implies
   (not (equal i1 i2))
   (equal
    (channel-state
     i1
     dst
     (send-msg-all-outgoing-channels
      msg i2 nbrs2 channels))
    (channel-state
     i1
     dst
     channels))))

;; Consequently, a broadcast by I2 commutes with an explicit update to an
;; I1-originating channel when I1 and I2 are distinct.
(local-defthm send-msg-all-outgoing-commutes-with-other-sender-update
  (implies
   (not (equal i1 i2))
   (equal
    (send-msg-all-outgoing-channels
     msg
     i2
     nbrs2
     (>channel i1 dst val channels))
    (>channel
     i1
     dst
     val
     (send-msg-all-outgoing-channels
      msg
      i2
      nbrs2
      channels)))))

;; A normal send from I1 followed by a marker broadcast from I2 has the same
;; projected destination row as the normal send alone.
(local-defthm project-channel-row-send-compute-marker-invisible
  (implies
   (and
    (not (equal i1 i2))
    (equal (msg-type msg) :marker))
   (equal
    (project-channel-row-to-spec
     srcs dst
     (send-compute-message
      local i1 nbrs1
      (send-msg-all-outgoing-channels
       msg i2 nbrs2 channels)))
    (project-channel-row-to-spec
     srcs dst
     (send-compute-message
      local i1 nbrs1 channels)))))

;; Whole-table version of the preceding row lemma.
(local-defthm project-send-compute-marker-invisible
 (implies
    (and
    (not (equal i1 i2))
    (equal (msg-type msg) :marker))
   (equal
    (project-channels-to-spec-aux
     dsts
     srcs
     (send-compute-message
      local
      i1
      nbrs1
      (send-msg-all-outgoing-channels
       msg i2 nbrs2 channels)))
    (project-channels-to-spec-aux
     dsts
     srcs
     (send-compute-message
      local
      i1
      nbrs1
      channels))))
  :hints (("Goal"
	   :in-theory (disable send-msg-all-outgoing-channels
			       send-compute-message))))

;; At the specification-channel level, a normal send and a marker broadcast by different processes commute.
(local-defthm project-channels-normal-send-marker-send-commute
  (implies
   (and
    (not (equal i1 i2))
    (equal (msg-type msg) :marker))
   (equal
    ;; Normal send from I1 first, then marker sends from I2.
    (project-channels-to-spec-aux
     ids
     ids
     (send-msg-all-outgoing-channels
      msg
      i2
      nbrs2
      (send-compute-message
       local1
       i1
       nbrs1
       channels)))
    ;; Marker sends from I2 first, then normal send from I1.
    (project-channels-to-spec-aux
     ids
     ids
     (send-compute-message
      local1
      i1
      nbrs1
      (send-msg-all-outgoing-channels
       msg
       i2
       nbrs2
       channels))))))

;; FIFO-head and receive-removal facts

;; Appending an element to a nonempty list preserves its existing head.
(defthm car-of-snoc-when-consp
  (implies
   (consp x)
   (equal
    (car (snoc x e))
    (car x))))

;; Hence a compute send cannot change the message currently available on a
;; nonempty channel, whether or not that channel is one of the send targets.
(defthm get-msg-from-channel-of-send-compute-message-when-consp
  (implies
   (consp
    (channel-state src dst channels))
   (equal
    (get-msg-from-channel
     src
     dst
     (send-compute-message
      local i nbrs channels))
    (get-msg-from-channel
     src
     dst
     channels))))

;; Removing the old head and appending compute traffic commute on a nonempty
;; channel.  This is the concrete channel equality needed for normal/receive.
(local-defthm remove-message-from-channel-of-send-compute-message
  (implies
   (consp
    (channel-state sender receiver channels))
   (equal
    (remove-message-from-channel
     sender
     receiver
     (send-compute-message
      local
      normal-i
      nbrs
      channels))
    (send-compute-message
     local
     normal-i
     nbrs
     (remove-message-from-channel
      sender
      receiver
      channels)))))

;; Broadcasting can only append; it cannot make an existing channel empty.
(defthm channel-consp-after-send-msg-all-outgoing
  (implies
   (consp (channel-state src dst channels))
   (consp
    (channel-state
     src
     dst
     (send-msg-all-outgoing-channels
      msg i nbrs channels)))))

;; A marker or recovery broadcast also preserves the head of every channel
;; that was already nonempty.
(defthm get-msg-from-channel-of-send-msg-all-outgoing-when-consp
  (implies
   (consp
    (channel-state
     src
     dst
     channels))
   (equal
    (get-msg-from-channel
     src
     dst
     (send-msg-all-outgoing-channels
      msg
      i
      nbrs
      channels))
    (get-msg-from-channel
     src
     dst
     channels))))

;; Boolean/non-NIL form of nonemptiness preservation, useful after ACL2 has
;; simplified a CONSP fact into a truth test on CHANNEL-STATE.
(local-defthm channel-nonempty-after-send-msg-all-outgoing
  (implies
   (consp
    (channel-state src dst channels))
   (channel-state
    src
    dst
    (send-msg-all-outgoing-channels
     msg i nbrs channels))))

;; Receiving at destination DST commutes with a broadcast originating from a
;; different process I, provided the received channel already has a head.
(local-defthm remove-message-from-channel-of-send-msg-all-outgoing-when-consp
    (implies
     (and
      (not (equal dst i))
      (consp (channel-state src dst channels)))
   (equal
    (remove-message-from-channel
     src
     dst
     (send-msg-all-outgoing-channels
      msg i nbrs channels))
    (send-msg-all-outgoing-channels
     msg
     i
     nbrs
     (remove-message-from-channel
      src dst channels)))))

;; A receive removal at DST1 cannot affect the head observed at DST2.
(defthm get-msg-from-channel-of-remove-message-different-dst
  (implies
   (not (equal dst1 dst2))
   (equal
    (get-msg-from-channel
     src2
     dst2
     (remove-message-from-channel
      src1
      dst1
      channels))
    (get-msg-from-channel
     src2
     dst2
     channels))))

;; Two receives addressed to distinct processes modify distinct destination
;; rows and therefore commute exactly.
(local-defthm remove-message-from-channel-different-dsts-commute
  (implies
   (not (equal dst1 dst2))
   (equal
    (remove-message-from-channel
     src1
     dst1
     (remove-message-from-channel
      src2
      dst2
      channels))
    (remove-message-from-channel
     src2
     dst2
     (remove-message-from-channel
      src1
      dst1
      channels)))))

;; The process-table helper used by two independent checkpoint starts is
;; itself commutative at distinct process identifiers.
(local-defthm start-checkpoint-helper-different-pids-commute
  (implies
   (not (equal i1 i2))
   (equal
    (start-checkpoint-helper
     (start-checkpoint-helper procs i1)
     i2)
    (start-checkpoint-helper
     (start-checkpoint-helper procs i2)
     i1))))


;; Process-side adjacent-swap theorem.
(local-defthm two-imp-inputs-commute-under-procs-equivalence
  (implies
   (two-imp-inputs-swappable-p
    st
    input-1
    input-2)
   (procs-equivalent-p
    (proc-ids st)
    ;; INPUT-1 followed by INPUT-2.
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    ;; INPUT-2 followed by INPUT-1.
    (procs
     (system-step
      (system-step st input-2)
      input-1))))
 ; :otf-flg t
  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel
     remove-message-from-channel
     start-checkpoint-helper
     create-marker-message
     update-proc-for-normal-msg-core)
    :cases
    ((equal (ttype input-1) :nop)
     (equal (ttype input-1) :normal)
     (equal (ttype input-1) :receive)
     (equal (ttype input-1) :start-checkpoint)
     (equal (ttype input-2) :nop)
     (equal (ttype input-2) :normal)
     (equal (ttype input-2) :receive)
     (equal (ttype input-2) :start-checkpoint)))))

;; ------------------------------------------------------------
;; PROCESS-CUT-STEP cannot make a process become pre-cut.
;; ------------------------------------------------------------

(defthm cm-cut-not-taken-p-after-process-cut-step-implies-before
  (implies
   (cm-cut-not-taken-p
    (process-cut-step
     input
     st
     m)
    i)
   (cm-cut-not-taken-p
    m
    i)))

;; Executing a NOP leaves the state unchanged, so it cannot alter whether the next input is legal.
(local-defthm legal-inputp-after-nop-step-iff
  (implies
   (equal
    (ttype input-i)
    :nop)
   (equal
    (legal-inputp
     (system-step st input-i)
     input-j)
    (legal-inputp
     st
     input-j))))

;; NOP itself is always an admissible implementation input.
(defthm legal-inputp-when-nop
  (implies
   (equal
    (ttype input)
    :nop)
   (legal-inputp
    st
    input)))

;; ------------------------------------------------------------
;; SYSTEM-STEP does not change the set of process IDs.
;; ------------------------------------------------------------

(local-defthm legal-normal-input-after-step-implies-before
  (implies
   (and
    (equal
     (ttype input-j)
     :normal)
    (legal-inputp
     (system-step st input-i)
     input-j))
   (legal-inputp
    st
    input-j)))

;; ------------------------------------------------------------
;; A NORMAL input does not change the set of processes that have not yet taken the cut.
;; ------------------------------------------------------------

(local-defthm cm-cut-not-taken-p-of-process-cut-step-when-normal
  (implies
   (equal
    (ttype input)
    :normal)
   (equal
    (cm-cut-not-taken-p
     (process-cut-step
      input
      st
      m)
     i)
    (cm-cut-not-taken-p
     m
     i))))

;; ------------------------------------------------------------
;; If INPUT-I is a NORMAL step, it only sends messages from.
;; ------------------------------------------------------------

(local-defthm channel-state-after-normal-step-when-src-different
  (implies
   (and
    (equal
     (ttype input)
     :normal)
    (not
     (equal
      src
      (pid input))))
   (equal
    (channel-state
     src
     dst
     (channels
      (system-step st input)))
    (channel-state
     src
     dst
     (channels st)))))

;; ------------------------------------------------------------
;; If SRC has already taken the cut and DST has not, and SRC is an incoming neighbor of DST, then the SRC -> DST channel is already nonempty.
;; ------------------------------------------------------------

;; ------------------------------------------------------------
;; Convert the incoming-neighbor view into the outgoing-neighbor view.
;; ------------------------------------------------------------

(local-defthm nbrs-from-src-dst-implies-nbrs-to-src-dst
  (implies
   (and
    (good-state-p st)
    (memberp src
             (proc-ids st))
    (memberp dst
             (proc-ids st))
    (memberp
     src
     (nbrs-from
      (g dst
         (procs st)))))
   (memberp
    dst
    (nbrs-to
     (g src
        (procs st)))))
    :hints
  (("Goal"
    :in-theory
    (enable
     nbrs-from-implies-nbrs-to-when-good-state-p))))

;; Convert topology plus the marker-in-transit invariant into the concrete FIFO fact required by receive commutation: the channel from an already post-cut sender to a.
(local-defthm cut-markers-in-transit-p-implies-channel-consp-from-nbrs-from
  (implies
   (and
    (cut-markers-in-transit-p
     m
     st)
    (good-state-p st)
    (memberp src
             (proc-ids st))
    (memberp dst
             (proc-ids st))
    (memberp
     src
     (nbrs-from
      (g dst
         (procs st))))
    (not
     (cm-cut-not-taken-p
      m
      src))
    (cm-cut-not-taken-p
     m
     dst))
   (consp
    (channel-state
     src
     dst
     (channels st))))
  :hints
  (("Goal"
    :in-theory (disable cut-markers-in-transit-p
			good-state-p
			cm-cut-not-taken)))
    :rule-classes
  ((:rewrite
    :match-free :all)))

;; ------------------------------------------------------------
;; INPUT-I is already post-cut.
;; ------------------------------------------------------------

(local-defthm post-pre-after-process-cut-step-implies-different-pids
  (implies
   (and
    (not
     (cm-cut-not-taken-p
      m
      (pid input-i)))
    (cm-cut-not-taken-p
     (process-cut-step
      input-i
      st
      m)
     (pid input-j)))
   (not
    (equal
     (pid input-i)
     (pid input-j)))))

;; ------------------------------------------------------------
;; A RECEIVE by process I can affect channels in two ways:
;; ------------------------------------------------------------

(local-defthm channel-state-after-receive-step-when-src-and-dst-different
  (implies
   (and
    (equal
     (ttype input)
     :receive)
    (not
     (equal
      src
      (pid input)))
    (not
     (equal
      dst
      (pid input))))
   (equal
    (channel-state
     src
     dst
     (channels
      (system-step st input)))
    (channel-state
     src
     dst
     (channels st)))))

;; ------------------------------------------------------------
;; INPUT-I is a RECEIVE by a post-cut process.
;; ------------------------------------------------------------

(local-defthm receive-channel-consp-before-post-cut-receive-step
  (implies
   (and
    (cut-markers-in-transit-p m st)
    (good-state-p st)
    (equal
     (ttype input-i)
     :receive)
    (equal
     (ttype input-j)
     :receive)
    (memberp
     (pid input-j)
     (proc-ids st))
    (memberp
     (sender input-j)
     (proc-ids st))
    (memberp
     (sender input-j)
     (nbrs-from
      (g (pid input-j)
         (procs st))))
    (consp
     (channel-state
      (sender input-j)
      (pid input-j)
      (channels
       (system-step st input-i))))
    (not
     (cm-cut-not-taken-p
      m
      (pid input-i)))
    (cm-cut-not-taken-p
     (process-cut-step
      input-i
      st
      m)
     (pid input-j)))
   ;; Therefore INPUT-J's channel was already nonempty.
   (consp
    (channel-state
     (sender input-j)
     (pid input-j)
     (channels st))))
  :hints
  (("Goal"
    ;; Is INPUT-I the source of INPUT-J's receive channel?
    :cases
    ((equal
      (sender input-j)
      (pid input-i))))))

;; ------------------------------------------------------------
;; SEND-MSG-ALL-OUTGOING-CHANNELS only changes channels whose source is I.
;; ------------------------------------------------------------

(local-defthm channel-state-of-send-msg-all-outgoing-channels-when-src-different
  (implies
   (not
    (equal src i))
   (equal
    (channel-state
     src
     dst
     (send-msg-all-outgoing-channels
      msg
      i
      nbrs
      channels))
    (channel-state
     src
     dst
     channels)))
  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels
     msg
     i
     nbrs
     channels))))

;; ------------------------------------------------------------
;; A START-CHECKPOINT step sends marker messages only from PID(INPUT) to its outgoing neighbors.
;; ------------------------------------------------------------

(local-defthm channel-state-after-start-checkpoint-step-when-src-different
  (implies
   (and
    (equal
     (ttype input)
     :start-checkpoint)
    (not
     (equal
      src
      (pid input))))
   (equal
    (channel-state
     src
     dst
     (channels
      (system-step st input)))
    (channel-state
     src
     dst
     (channels st)))))

;; ------------------------------------------------------------
;; INPUT-I is a START-CHECKPOINT step by a process that is already post-cut with respect to the target cut M.
;; ------------------------------------------------------------

(local-defthm receive-channel-consp-before-post-cut-start-checkpoint-step
  (implies
   (and
    (cut-markers-in-transit-p
     m st)
    (good-state-p st)
    (equal
     (ttype input-i)
     :start-checkpoint)
    (equal
     (ttype input-j)
     :receive)
    (memberp
     (pid input-j)
     (proc-ids st))
    (memberp
     (sender input-j)
     (proc-ids st))
    (memberp
     (sender input-j)
     (nbrs-from
      (g (pid input-j)
         (procs st))))
    (consp
     (channel-state
      (sender input-j)
      (pid input-j)
      (channels
       (system-step st input-i))))
    (not
     (cm-cut-not-taken-p
      m
      (pid input-i)))
    (cm-cut-not-taken-p
     (process-cut-step
      input-i
      st
      m)
     (pid input-j)))
   ;; Hence INPUT-J's receive channel was already nonempty.
   (consp
    (channel-state
     (sender input-j)
     (pid input-j)
     (channels st))))
  :hints
  (("Goal"
    ;; Split according to whether INPUT-I is the source of
    ;; INPUT-J's receive channel.
    :cases
    ((equal
      (sender input-j)
      (pid input-i))))))

;; ------------------------------------------------------------
;; A NOP step does not change any channel.
;; ------------------------------------------------------------

(local-defthm channel-state-after-nop-step
  (implies
   (equal
    (ttype input)
    :nop)
   (equal
    (channel-state
     src
     dst
     (channels
      (system-step st input)))
    (channel-state
     src
     dst
     (channels st)))))

;; ------------------------------------------------------------
;; INPUT-J is legal before moving it to the left of INPUT-I.
;; ------------------------------------------------------------

(defthm post-pre-input-j-legal-before-input-i
  (let*
      ((m-after-i
        (process-cut-step
         input-i
         st
         m)))
    (implies
     (and
      (cut-markers-in-transit-p
       m
       st)
      (cut-meta-imp-consistent-p
       m
       st)
      (recovery-free-state-p st)
      (good-cut-meta-p m)
      (good-state-p st)
      (legal-input-sequencep
       st
       (list input-i input-j))
      (cl-checkpoint-body-input-p
       input-i)
      (cl-checkpoint-body-input-p
       input-j)
      (not
       (cm-cut-not-taken-p
        m
        (pid input-i)))
      (cm-cut-not-taken-p
       m-after-i
       (pid input-j)))
     (legal-inputp
      st
      input-j)))
  :rule-classes
  ((:rewrite
    :match-free :all))
  :hints
  (("Goal"
    :cases
    ((equal (ttype input-i) :nop)
     (equal (ttype input-i) :normal)
     (equal (ttype input-i) :receive)
     (equal (ttype input-i) :start-checkpoint)
     (equal (ttype input-j) :nop)
     (equal (ttype input-j) :normal)
     (equal (ttype input-j) :receive)
     (equal (ttype input-j) :start-checkpoint))
    :in-theory
    (disable
     good-state-p
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     recovery-free-state-p
     good-cut-meta-p
    ; legal-inputp
     process-cut-step
     system-step
     step-normal
     step-rcv
     step-checkpoint
     get-msg-from-channel
     cm-cut-not-taken-p))
   ("Subgoal 7''"
    :cases
    ((equal
    (sender input-j)
    (pid input-i))))
      ("Subgoal 2.1"
    :cases
    ((equal
    (sender input-j)
    (pid input-i))))))

;; ------------------------------------------------------------
;; If a sequence of inputs is legal from ST, then its first input is legal in ST.
;; ------------------------------------------------------------

(defthm legal-input-sequencep-implies-first-legal
  (implies
   (and
    (consp inputs)
    (legal-input-sequencep st inputs))
   (legal-inputp
    st
    (first inputs))))

;; ------------------------------------------------------------
;; If the two-input sequence (INPUT-I INPUT-J) is legal from ST,
;; then INPUT-I is legal in ST.
;; ------------------------------------------------------------

(defthm legal-input-sequencep-of-two-implies-first-legal
  (implies
   (legal-input-sequencep
    st
    (list input-i input-j))
   (legal-inputp
    st
    input-i))
    :rule-classes
  ((:rewrite
    :match-free :all))
  :hints (("Goal"
	   :in-theory (disable legal-inputp))))

;; ------------------------------------------------------------
;; If the two-input sequence (INPUT-I INPUT-J) is legal from ST, then after executing INPUT-I, INPUT-J is legal.
;; ------------------------------------------------------------

(defthm legal-input-sequencep-of-two-implies-second-legal
  (implies
   (legal-input-sequencep
    st
    (list input-i input-j))
   (legal-inputp
    (system-step st input-i)
    input-j))
    :rule-classes
  ((:rewrite
    :match-free :all))
  :hints (("Goal"
	   :in-theory (disable legal-inputp
			       system-step))))

;; ------------------------------------------------------------
;; SEND-COMPUTE-MESSAGE never makes a nonempty channel empty.
;; ------------------------------------------------------------

(defthm channel-consp-preserved-by-send-compute-message
  (implies
   (consp
    (channel-state
     src
     dst
     channels))
   (consp
    (channel-state
     src
     dst
     (send-compute-message
      local-state
      i
      nbrs
      channels)))))

;; ------------------------------------------------------------
;; A NORMAL step never removes messages from any channel.
;; ------------------------------------------------------------

(local-defthm channel-consp-preserved-by-normal-step
  (implies
   (and
    (equal
     (ttype input)
     :normal)
    (consp
     (channel-state
      src
      dst
      (channels st))))
   (consp
    (channel-state
     src
     dst
     (channels
      (system-step st input))))))

;; ------------------------------------------------------------
;; A START-CHECKPOINT step cannot make an already nonempty channel empty.
;; ------------------------------------------------------------

(local-defthm channel-consp-preserved-by-start-checkpoint-step
  (implies
   (and
    (equal
     (ttype input)
     :start-checkpoint)
    (consp
     (channel-state
      src
      dst
      (channels st))))
   (consp
    (channel-state
     src
     dst
     (channels
      (system-step st input))))))

;; ------------------------------------------------------------
;; A RECEIVE step at process PID(INPUT) cannot make a nonempty channel SRC -> DST empty when DST is a different process.
;; ------------------------------------------------------------

(local-defthm channel-consp-preserved-by-receive-step-when-dst-different
  (implies
   (and
    (equal
     (ttype input)
     :receive)
    (not
     (equal
      dst
      (pid input)))
    (consp
     (channel-state
      src
      dst
      (channels st))))
   (consp
    (channel-state
     src
     dst
     (channels
      (system-step st input))))))

;; ------------------------------------------------------------
;; SWAPPED-ORDER LEGALITY OF INPUT-I
;; ------------------------------------------------------------

(defthm post-pre-input-i-legal-after-input-j
  (implies
   (and
    (cut-markers-in-transit-p
     m st)
    (cut-meta-imp-consistent-p
     m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)
    (legal-input-sequencep
     st
     (list input-i input-j))
    (cl-checkpoint-body-input-p
     input-i)
    (cl-checkpoint-body-input-p
     input-j)
    (not
     (cm-cut-not-taken-p
      m
      (pid input-i)))
    (cm-cut-not-taken-p
     (process-cut-step
      input-i
      st
      m)
     (pid input-j)))
   ;; After moving INPUT-J first, INPUT-I remains legal.
   (legal-inputp
    (system-step st input-j)
    input-i))
    :rule-classes
  ((:rewrite
    :match-free :all))
  :hints
  (("Goal"
    :cases
    ((equal (ttype input-i) :nop)
     (equal (ttype input-i) :normal)
     (equal (ttype input-i) :receive)
     (equal (ttype input-i) :start-checkpoint)
     (equal (ttype input-j) :nop)
     (equal (ttype input-j) :normal)
     (equal (ttype input-j) :receive)
     (equal (ttype input-j) :start-checkpoint))
    :in-theory
    (disable
     good-state-p
     recovery-free-state-p
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     no-recovery-step-p
     good-cut-meta-p
    ; legal-inputp
     process-cut-step
     system-step
     step-normal
     step-rcv
     step-checkpoint
     get-msg-from-channel
     cm-cut-not-taken-p))))

;; ------------------------------------------------------------
;; A POST process and a PRE process cannot be the same process.
;; ------------------------------------------------------------

(local-defthm post-pre-process-cut-step-implies-pids-different
  (implies
   (and
    (not
     (cm-cut-not-taken-p
      m
      (pid input-i)))
    (cm-cut-not-taken-p
     (process-cut-step input-i st m)
     (pid input-j)))
   (not
    (equal
     (pid input-i)
     (pid input-j))))
    :rule-classes
  ((:rewrite
    :match-free :all)))

;; ;; ------------------------------------------------------------ ;; A POST-CUT input followed by a PRE-CUT input is swappable ;; in the implementation.

;; ------------------------------------------------------------
;; Starting condition for a local POST ; PRE swap.
;; ------------------------------------------------------------

(defun post-pre-swap-start-p
    (st m input-1 input-2)
  (let*
      ((m-after-1
        (process-cut-step
         input-1
         st
         m)))
    (and
     ;; Cut / implementation invariants.
     (cut-markers-in-transit-p
      m st)
     (cut-meta-imp-consistent-p
      m st)
     (good-cut-meta-p m)
     (good-state-p st)
     ;; We are outside recovery.
     (recovery-free-state-p st)
     ;; INPUT-1 ; INPUT-2 is the actual legal order.
     (legal-input-sequencep
      st
      (list input-1 input-2))
     ;; Both are checkpoint-body inputs.
     (cl-checkpoint-body-input-p
      input-1)
     (cl-checkpoint-body-input-p
      input-2)
     ;; INPUT-1 is POST-cut.
     (not
      (cm-cut-not-taken-p
       m
       (pid input-1)))
     ;; INPUT-2 is still PRE-cut immediately before it executes.
     (cm-cut-not-taken-p
     m-after-1
     (pid input-2)))))

;; Bridge from the cut-oriented hypothesis used by the global reordering argument to the semantic independence contract used by the local commutation library.
(defthm post-pre-two-imp-inputs-swappable-p
  (implies
   (post-pre-swap-start-p
    st m input-1 input-2)
   (two-imp-inputs-swappable-p
    st input-1 input-2))
  :hints
  (("Goal"
    :in-theory
    (disable
     process-cut-step
     recovery-free-state-p
     good-state-p
     legal-input-sequencep
     legal-inputp
     cm-cut-not-taken-p
     any-process-recovering-p
     append
     any-snapshot-checkpointing-p
     no-recovery-step-p
     system-step
     cl-checkpoint-body-input-p
     cut-markers-in-transit-p
     recovery-free-state-p)))
  :rule-classes
  ((:rewrite
    :match-free :all)))

;; ------------------------------------------------------------
;; A normal-message send by I1 commutes exactly with sending MSG on all outgoing channels of a different process I2.
;; ------------------------------------------------------------

(local-defthm send-compute-message-send-msg-all-outgoing-different-senders-commute
  (implies
   (not
    (equal i1 i2))
   (equal
    (send-msg-all-outgoing-channels
     msg
     i2
     nbrs2
     (send-compute-message
      local1
      i1
      nbrs1
      channels))
    (send-compute-message
     local1
     i1
     nbrs1
     (send-msg-all-outgoing-channels
      msg
      i2
      nbrs2
      channels))))
  :hints
  (("Goal"
    :induct
    (send-compute-message
     local1
     i1
     nbrs1
     channels)
    :in-theory
    (disable
     send-msg-all-outgoing-channels))))

;; ------------------------------------------------------------
;; Sending messages from another source I2 cannot affect the final I1 -> DST channel produced by I1's own outgoing sends.
;; ------------------------------------------------------------

(local-defthm channel-state-of-send-msg-all-after-other-sender
  (implies
   (not
    (equal i1 i2))
   (equal
    (channel-state
     i1
     dst
     (send-msg-all-outgoing-channels
      msg1
      i1
      nbrs1
      (send-msg-all-outgoing-channels
       msg2
       i2
       nbrs2
       channels)))
    (channel-state
     i1
     dst
     (send-msg-all-outgoing-channels
      msg1
      i1
      nbrs1
      channels)))))

;; ------------------------------------------------------------
;; Sending messages from two different source processes commutes exactly at the raw channel level.
;; ------------------------------------------------------------

(local-defthm send-msg-all-outgoing-different-senders-commute
  (implies
   (not
    (equal i1 i2))
   (equal
    (send-msg-all-outgoing-channels
     msg2
     i2
     nbrs2
     (send-msg-all-outgoing-channels
      msg1
      i1
      nbrs1
      channels))
    (send-msg-all-outgoing-channels
     msg1
     i1
     nbrs1
     (send-msg-all-outgoing-channels
      msg2
      i2
      nbrs2
      channels)))))

;; Raw-channel adjacent-swap theorem.
(local-defthm two-imp-inputs-commute-channels
  (implies
   (two-imp-inputs-swappable-p
    st input-1 input-2)
   (equal
    (channels
     (system-step
      (system-step st input-1)
      input-2))
    (channels
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    ;; Split the proof according to the implementation input types and use
    ;; the exact commutation facts established in the channel library.
    :in-theory
    (disable get-msg-from-channel
             remove-message-from-channel
	     start-checkpoint-helper
	     create-marker-message
	     update-proc-for-normal-msg-core
	    ; step-normal
	     )
    :cases
    ((equal (ttype input-1) :nop)
     (equal (ttype input-1) :normal)
     (equal (ttype input-1) :receive)
     (equal (ttype input-1) :start-checkpoint)
     (equal (ttype input-2) :nop)
     (equal (ttype input-2) :normal)
     (equal (ttype input-2) :receive)
     (equal (ttype input-2) :start-checkpoint)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Checkpoint-control commutation by input-type pair
;;
;; CL-CHECKPOINT-CONTROL-EQUIVALENT-P observes each process's COUNTER and
;; SNAPSHOT-IDS.  Unlike the visible-process and channel components, these
;; fields are intentionally modified by :start-checkpoint and marker
;; receives.  We therefore prove the interesting type pairs separately,
;; retain both orientations where a mixed pair is asymmetric syntactically,
;; and finish with one exhaustive dispatcher theorem.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A NOP is operational identity.  This closes every case in which either
;; side of the adjacent transposition is :nop.
(defthm system-step-when-nop
  (implies
   (equal
    (ttype input)
    :nop)
   (equal
    (system-step st input)
    st)))

;; The pointwise checkpoint-control relation is reflexive; it is the terminal
;; fact for cases whose two process tables simplify to the same term.
(defthm checkpoint-control-equivalent-p-reflexive
  (cl-checkpoint-control-equivalent-p
   ids
   procs
   procs))

;; Receive/receive base case under the abstract swappability contract.
(local-defthm checkpoint-control-receive-receive-commute
  (implies
   (and
    (equal (ttype input-1) :receive)
    (equal (ttype input-2) :receive)
    (two-imp-inputs-swappable-p
     st input-1 input-2))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st)
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel
     remove-message-from-channel))))

;; Specialize the abstract receive/receive result to a post-cut/pre-cut pair
;; by deriving TWO-IMP-INPUTS-SWAPPABLE-P from the cut invariants.
(local-defthm post-pre-receive-receive-checkpoint-control
  (implies
   (and
    (equal (ttype input-1) :receive)
    (equal (ttype input-2) :receive)
    (post-pre-swap-start-p
     st m input-1 input-2))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st)
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-two-imp-inputs-swappable-p)
     (:instance
      checkpoint-control-receive-receive-commute))
    :in-theory
    (disable
     post-pre-swap-start-p
     post-pre-two-imp-inputs-swappable-p
     two-imp-inputs-swappable-p
     checkpoint-control-receive-receive-commute
     cl-checkpoint-control-equivalent-p
     system-step))))

;; Two normal inputs do not modify checkpoint counters or snapshot-ID lists,
;; so checkpoint-control equivalence holds without a swappability hypothesis.
(local-defthm checkpoint-control-normal-normal-commute
  (implies
   (and
    (equal (ttype input-1) :normal)
    (equal (ttype input-2) :normal))
   (cl-checkpoint-control-equivalent-p
    ids
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1)))))

;; Mixed normal/receive base case, with normal first in the original order.
(local-defthm checkpoint-control-normal-receive-commute
  (implies
   (and
    (equal (ttype input-1) :normal)
    (equal (ttype input-2) :receive)
    (two-imp-inputs-swappable-p
     st input-1 input-2))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st)
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel))))

;; Cut-oriented wrapper for the normal/receive base case.
(local-defthm post-pre-normal-receive-checkpoint-control
  (implies
   (and
    (equal (ttype input-1) :normal)
    (equal (ttype input-2) :receive)
    (post-pre-swap-start-p
     st m input-1 input-2))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st)
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-two-imp-inputs-swappable-p)
     (:instance
      checkpoint-control-normal-receive-commute)))))

;; Reverse mixed orientation: receive first, then normal.
(local-defthm checkpoint-control-normal-receive-commute2
  (implies
   (and
    (equal (ttype input-1) :receive)
    (equal (ttype input-2) :normal)
    (two-imp-inputs-swappable-p
     st input-1 input-2))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st)
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel))))

;; Cut-oriented wrapper for the receive/normal orientation.
(local-defthm post-pre-normal-receive-checkpoint-control2
  (implies
   (and
    (equal (ttype input-1) :receive)
    (equal (ttype input-2) :normal)
    (post-pre-swap-start-p
     st m input-1 input-2))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st)
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-two-imp-inputs-swappable-p)
     (:instance
      checkpoint-control-normal-receive-commute2)))))

;; A post-cut input and the following still-pre-cut input cannot belong to
;; the same process: PROCESS-CUT-STEP never makes an already-taken cut revert.
(local-defthm post-pre-swap-start-implies-pids-different
  (implies
   (post-pre-swap-start-p
    st m input-1 input-2)
   (not
    (equal
     (pid input-1)
     (pid input-2))))
  :hints
  (("Goal"
    :in-theory
     (disable
      process-cut-step
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-input-sequencep
      legal-inputp
      cl-checkpoint-body-input-p
      cm-cut-not-taken-p
      system-step))))

;; Symmetric spelling of PID disequality, registered only for explicit use.
;; It avoids depending on ACL2 to orient EQUAL in mixed start/normal proofs.
(local-defthm post-pre-swap-start-implies-reversed-pids-different
  (implies
   (post-pre-swap-start-p
    st m input-1 input-2)
   (not
    (equal
     (pid input-2)
     (pid input-1))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-swap-start-implies-pids-different
      (st st)
      (m m)
      (input-1 input-1)
      (input-2 input-2)))
    :cases
    ((equal
      (pid input-2)
      (pid input-1)))
    :in-theory
    (disable
     post-pre-swap-start-p
     post-pre-swap-start-implies-pids-different)))
:rule-classes nil)

;; Exact process-table commutation for checkpoint-start followed by a normal step at a different PID.
(local-defthm start-checkpoint-normal-procs-commute
  (implies
   (and
    (equal (ttype input-1) :start-checkpoint)
    (equal (ttype input-2) :normal)
    (not
     (equal
      (pid input-1)
      (pid input-2))))
   (equal
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    :in-theory
    (disable start-checkpoint-helper
      create-marker-message
      send-compute-message))))

;; Normal/start is the reverse syntactic orientation of the exact theorem
;; above; PID disequality from the post/pre predicate supplies its side case.
(local-defthm post-pre-normal-start-checkpoint-checkpoint-control
  (implies
   (and
    (equal (ttype input-1) :normal)
    (equal (ttype input-2) :start-checkpoint)
    (post-pre-swap-start-p
     st m input-1 input-2))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st)
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-swap-start-implies-reversed-pids-different
      (st st)
      (m m)
      (input-1 input-1)
      (input-2 input-2))
     (:instance
      start-checkpoint-normal-procs-commute
      (st st)
      (input-1 input-2)
      (input-2 input-1)))
    :in-theory
    (disable
     post-pre-swap-start-p
     post-pre-swap-start-implies-pids-different
    ; post-pre-swap-start-implies-reversed-pids-different
     start-checkpoint-normal-procs-commute
     system-step
     cl-checkpoint-control-equivalent-p))))

;; Generic update rules for the checkpoint-control relation

;; If two replacement records agree on the observed control fields, placing
;; them into the same process table at the same key yields equivalent tables.
(local-defthm checkpoint-control-equivalent-p-of-single-proc-update
  (implies
   (and
    (equal
     (counter p1)
     (counter p2))
    (equal
     (snapshot-ids p1)
     (snapshot-ids p2)))
   (cl-checkpoint-control-equivalent-p
    ids
    (s i p1 procs)
    (s i p2 procs)))
  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids procs procs))
   ("Subgoal *1/2"
    :cases
    ((equal
      (car ids)
      i)))))

;; If two tables are already control-equivalent, installing the same process
;; record at the same key on both sides preserves the relation.
(local-defthm checkpoint-control-equivalent-p-preserved-by-same-proc-update
  (implies
   (cl-checkpoint-control-equivalent-p
    ids procs-1 procs-2)
   (cl-checkpoint-control-equivalent-p
    ids
    (s i p procs-1)
    (s i p procs-2)))
  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids procs-1 procs-2))
   ("Subgoal *1/2"
    :cases
    ((equal
      (car ids)
      i)))))

;; Core start/receive theorem.
(local-defthm start-checkpoint-receive-checkpoint-control
  (implies
   (and
    (equal
     (ttype input-1)
     :start-checkpoint)
    (equal
     (ttype input-2)
     :receive)
    (not
     (equal
      (pid input-1)
      (pid input-2)))
    (legal-inputp
     st
     input-1)
    (legal-inputp
     st
     input-2)
    (recovery-free-state-p st))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st)
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1)))))

;; Symmetry is kept as an explicit non-rewrite theorem.  Using it by instance
;; is predictable and avoids rewrite loops on a symmetric relation.
(local-defthm checkpoint-control-equivalent-p-symmetric
  (implies
   (cl-checkpoint-control-equivalent-p
    ids
    procs-1
    procs-2)
   (cl-checkpoint-control-equivalent-p
    ids
    procs-2
    procs-1))
  
  :rule-classes nil)

;; Receive/start wrapper.  Apply the core start/receive theorem in the
;; opposite order, then use symmetry to restore the requested conclusion.
(local-defthm post-pre-receive-start-checkpoint-checkpoint-control
  (implies
   (and
    (post-pre-swap-start-p
     st m input-1 input-2)
    (equal (ttype input-1) :receive)
    (equal
     (ttype input-2)
     :start-checkpoint))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st)
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    :cases
    ((equal
      (pid input-2)
      (pid input-1)))
    :use
    ((:instance
      post-pre-two-imp-inputs-swappable-p)
     (:instance
      start-checkpoint-receive-checkpoint-control
      (input-1 input-2)
      (input-2 input-1))
     (:instance
      checkpoint-control-equivalent-p-symmetric
      (ids (proc-ids st))
      (procs-1
       (procs
        (system-step
         (system-step st input-2)
         input-1)))
      (procs-2
       (procs
        (system-step
         (system-step st input-1)
         input-2)))))
    :in-theory
    (disable post-pre-two-imp-inputs-swappable-p
      start-checkpoint-receive-checkpoint-control
     ; checkpoint-control-equivalent-p-symmetric
      cl-checkpoint-control-equivalent-p
      system-step
      process-cut-step
      legal-input-sequencep
      legal-inputp
      no-recovery-step-p
      recovery-free-state-p
      cl-checkpoint-body-input-p
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p))))

;; Start/receive wrapper in the same orientation as the core theorem.
(local-defthm post-pre-start-checkpoint-receive-checkpoint-control
  (implies
   (and
    (post-pre-swap-start-p
     st m input-1 input-2)
    (equal
     (ttype input-1)
     :start-checkpoint)
    (equal
     (ttype input-2)
     :receive))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st)
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-two-imp-inputs-swappable-p)
     (:instance
      start-checkpoint-receive-checkpoint-control))
    :in-theory
    (disable post-pre-two-imp-inputs-swappable-p
      start-checkpoint-receive-checkpoint-control
      cl-checkpoint-control-equivalent-p
      system-step
      process-cut-step
      legal-input-sequencep
      legal-inputp
      no-recovery-step-p
      recovery-free-state-p
      cl-checkpoint-body-input-p
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p))))

;; Start/normal post-pre case.  The stronger exact process commutation theorem
;; immediately implies checkpoint-control equivalence.
(local-defthm post-pre-start-checkpoint-normal-checkpoint-control
  (implies
   (and
    (post-pre-swap-start-p
     st m input-1 input-2)
    (equal
     (ttype input-1)
     :start-checkpoint)
    (equal
     (ttype input-2)
     :normal))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st)
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-two-imp-inputs-swappable-p)
     (:instance
      start-checkpoint-normal-procs-commute))
    :in-theory
    (disable post-pre-swap-start-p
      post-pre-two-imp-inputs-swappable-p
      start-checkpoint-normal-procs-commute
      cl-checkpoint-control-equivalent-p
      system-step))))

;; Two starts at distinct PIDs commute exactly in the process table: each
;; START-CHECKPOINT-HELPER updates only its designated process slot.
(local-defthm procs-start-checkpoint-start-checkpoint-different-pids-commute
  (implies
   (and
    (equal
     (ttype input-1)
     :start-checkpoint)
    (equal
     (ttype input-2)
     :start-checkpoint)
    (not
     (equal
      (pid input-1)
      (pid input-2))))
   (equal
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1)))))

;; Cut-oriented control-equivalence wrapper for the start/start equality.
(local-defthm post-pre-start-checkpoint-start-checkpoint-checkpoint-control
  (implies
   (and
    (post-pre-swap-start-p
     st m input-1 input-2)
    (equal
     (ttype input-1)
     :start-checkpoint)
    (equal
     (ttype input-2)
     :start-checkpoint))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st)
    (procs
     (system-step
      (system-step st input-1)
      input-2))
    (procs
     (system-step
      (system-step st input-2)
      input-1))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-two-imp-inputs-swappable-p)
     (:instance
      procs-start-checkpoint-start-checkpoint-different-pids-commute))
    :in-theory
    (disable post-pre-swap-start-p
      post-pre-two-imp-inputs-swappable-p
      procs-start-checkpoint-start-checkpoint-different-pids-commute
      cl-checkpoint-control-equivalent-p
      system-step))))

;; Exhaustive checkpoint-control dispatcher.
(local-defthm post-pre-two-imp-inputs-commute-checkpoint-control
    (implies
     (and
   (post-pre-swap-start-p
    st m input-1 input-2)
    (cl-checkpoint-body-input-p input-1)
    (cl-checkpoint-body-input-p input-2))
   (cl-checkpoint-control-equivalent-p
    (proc-ids st)
    (procs
     (run-imp
      st
      (list input-1 input-2)))
    (procs
     (run-imp
      st
      (list input-2 input-1)))))
 :otf-flg t
  :hints
  (("Goal"
    :in-theory
    (disable
     post-pre-swap-start-p
     system-step
      step-rcv
      step-normal
      step-checkpoint
      process-cut-step
     ; recovery-free-state-p
      good-state-p
      good-cut-meta-p
      cut-meta-imp-consistent-p
     ; legal-input-sequencep
      legal-inputp
      cm-cut-not-taken-p
      ;cl-checkpoint-body-input-p
      cut-markers-in-transit-p
     ; cl-checkpoint-control-equivalent-p
      ))))

;; Local swap theorem under implementation-state equivalence

(defthm post-pre-two-imp-inputs-commute-under-state-equivalence
  (implies
   (post-pre-swap-start-p
    st m input-1 input-2)
   (state-equivalent-p
    (run-imp
     st
     (list input-1 input-2))
    (run-imp
     st
     (list input-2 input-1))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-two-imp-inputs-swappable-p)
     (:instance
      two-imp-inputs-commute-under-procs-equivalence)
     (:instance
      two-imp-inputs-commute-channels)
     (:instance
      post-pre-two-imp-inputs-commute-checkpoint-control))
    :in-theory
    (disable
     post-pre-swap-start-p
      post-pre-two-imp-inputs-swappable-p
      system-step
      procs-equivalent-p
      cl-checkpoint-control-equivalent-p
      cl-checkpoint-body-input-p
      legal-inputp
      no-recovery-step-p
      recovery-free-state-p)))
      :rule-classes nil)

) ;; end local two-input commutation proof

;; Single-step preservation support library

;; A nonempty channel in a recovery-free state cannot have a recovery
;; message at its head.  This removes the recovery-message receive branch.
(encapsulate
 ()

(local-defthm no-recovery-msgs-in-state-channels-implies-head-not-recovery
  (implies
   (and
    (no-recovery-msgs-in-channels-p
     (proc-ids st)
     (proc-ids st)
     (channels st))
    (memberp
     src
     (proc-ids st))
    (memberp
     dst
     (proc-ids st))
    (consp
     (channel-state
      src
      dst
      (channels st))))
   (not
    (equal
     (msg-type
      (first
       (channel-state
        src
        dst
        (channels st))))
     :recovery)))
  :hints
  (("Goal"
    :use
    ((:instance
      no-recovery-msgs-in-channels-p-implies-get-msg-not-recovery
      (srcs
       (proc-ids st))
      (dsts
       (proc-ids st))
      (channels
       (channels st))
      (src src)
      (dst dst)))
    :in-theory
    (disable no-recovery-msgs-in-channels-p-implies-get-msg-not-recovery))))

;; LOCAL-STATE is not part of checkpoint control, so independent local-state
;; updates preserve checkpoint-control equivalence.
(local-defthm checkpoint-control-equivalent-p-preserved-by-local-state-updates
  (implies
   (cl-checkpoint-control-equivalent-p
    ids
    procs-1
    procs-2)
   (cl-checkpoint-control-equivalent-p
    ids
    (s i
       (s :local-state
          new-local-1
          (g i procs-1))
       procs-1)
    (s i
       (s :local-state
          new-local-2
          (g i procs-2))
       procs-2)))
  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2))
   ("Subgoal *1/2"
    :cases
    ((equal
      (car ids)
      i)))))

;; A normal receive may record different snapshot bookkeeping on the two sides, but visible-process equivalence is preserved when it installs the same application-visible local state.
(local-defthm procs-equivalent-p-preserved-by-same-local-state-and-snapshots-update
  (implies
   (procs-equivalent-p
    ids
    procs-1
    procs-2)
   (procs-equivalent-p
    ids
    (s i
       (s :snapshots snapshots-1
          (s :local-state new-local
             (g i procs-1)))
       procs-1)
    (s i
       (s :snapshots snapshots-2
          (s :local-state new-local
             (g i procs-2)))
       procs-2)))
  :hints
  (("Goal"
    :induct
    (procs-equivalent-p
     ids
     procs-1
     procs-2))
   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))

;; Both LOCAL-STATE and SNAPSHOTS are invisible to checkpoint control.
;; Consequently, they may be updated independently on the two sides.
(local-defthm checkpoint-control-equivalent-p-preserved-by-local-state-and-snapshots-updates
  (implies
   (cl-checkpoint-control-equivalent-p
    ids
    procs-1
    procs-2)
   (cl-checkpoint-control-equivalent-p
    ids
    (s i
       (s :snapshots snapshots-1
          (s :local-state new-local-1
             (g i procs-1)))
       procs-1)
    (s i
       (s :snapshots snapshots-2
          (s :local-state new-local-2
             (g i procs-2)))
       procs-2)))
  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2))
   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))

;; SNAPSHOTS and SNAPSHOT-IDS are invisible to PROCS-EQUIVALENT-P, whose
;; observations are limited to the three application-visible process fields.
(local-defthm procs-equivalent-p-preserved-by-snapshots-and-snapshot-ids-updates
  (implies
   (procs-equivalent-p
    ids
    procs-1
    procs-2)
   (procs-equivalent-p
    ids
    (s i
       (s :snapshots snapshots-1
          (s :snapshot-ids snapshot-ids-1
             (g i procs-1)))
       procs-1)
    (s i
       (s :snapshots snapshots-2
          (s :snapshot-ids snapshot-ids-2
             (g i procs-2)))
       procs-2)))
  :hints
  (("Goal"
    :induct
    (procs-equivalent-p
     ids
     procs-1
     procs-2))
   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))

;; If no listed process is recovering, a listed process cannot individually
;; have :RECOVERING status.  This closes inconsistent receive branches.
(defthm no-any-proc-recovering-p-implies-member-not-recovering
  (implies
   (and
    (not
     (any-proc-recovering-p
      ids
      procs))
    (memberp i ids))
   (not
    (equal
     (proc-status
      (g i procs))
     :recovering))))

;; Generic checkpoint-control update rule.
(local-defthm checkpoint-control-equivalent-p-preserved-by-related-proc-updates
  (implies
   (and
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2)
    (implies
     (and
      (equal
       (counter (g i procs-1))
       (counter (g i procs-2)))
      (equal
       (snapshot-ids (g i procs-1))
       (snapshot-ids (g i procs-2))))
     (and
      (equal
       (counter new-p-1)
       (counter new-p-2))
      (equal
       (snapshot-ids new-p-1)
       (snapshot-ids new-p-2)))))
   (cl-checkpoint-control-equivalent-p
    ids
    (s i new-p-1 procs-1)
    (s i new-p-2 procs-2)))
  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2))
   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))

;; Pointwise projection of SNAPSHOT-IDS from checkpoint-control equivalence.
(defthm checkpoint-control-equivalent-p-implies-snapshot-ids-equal
  (implies
   (and
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2)
    (memberp i ids))
   (equal
    (snapshot-ids
     (g i procs-1))
    (snapshot-ids
     (g i procs-2))))
  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2))
   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))

;; Process-level field abstraction.
(local-defthm proc-equivalent-p-ignores-non-visible-field-updates
  (implies
   (and
    (not (equal field :local-state))
    (not (equal field :nbrs-to))
    (not (equal field :nbrs-from)))
   (equal
    (proc-equivalent-p
     (s field value-1 p-1)
     (s field value-2 p-2))
    (proc-equivalent-p
     p-1
     p-2))))

;; Lift the preceding field abstraction pointwise over the process table.
(local-defthm procs-equivalent-p-ignores-non-visible-field-updates
  (implies
   (and
    (procs-equivalent-p
     ids
     procs-1
     procs-2)
    (not (equal field :local-state))
    (not (equal field :nbrs-to))
    (not (equal field :nbrs-from)))
   (procs-equivalent-p
    ids
    (s i
       (s field value-1
          (g i procs-1))
       procs-1)
    (s i
       (s field value-2
          (g i procs-2))
       procs-2)))
  :hints
  (("Goal"
    :induct
    (procs-equivalent-p
     ids
     procs-1
     procs-2))
   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))

;; Pointwise projection of COUNTER from checkpoint-control equivalence.  It
;; ensures that both executions create the same checkpoint SID and marker.
(defthm checkpoint-control-equivalent-p-implies-counter-equal
  (implies
   (and
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2)
    (memberp i ids))
   (equal
    (counter
     (g i procs-1))
    (counter
     (g i procs-2))))
  :hints
  (("Goal"
    :induct
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2))
   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))

;; Most general visible-process replacement rule used by the preservation proof.
(local-defthm procs-equivalent-p-preserved-by-invisible-proc-replacements
  (implies
   (and
    (procs-equivalent-p
     ids
     procs-1
     procs-2)
    (equal
     (local-state new-p-1)
     (local-state (g i procs-1)))
    (equal
     (nbrs-to new-p-1)
     (nbrs-to (g i procs-1)))
    (equal
     (nbrs-from new-p-1)
     (nbrs-from (g i procs-1)))
    (equal
     (local-state new-p-2)
     (local-state (g i procs-2)))
    (equal
     (nbrs-to new-p-2)
     (nbrs-to (g i procs-2)))
    (equal
     (nbrs-from new-p-2)
     (nbrs-from (g i procs-2))))
   (procs-equivalent-p
    ids
    (s i new-p-1 procs-1)
    (s i new-p-2 procs-2)))
  :hints
  (("Goal"
    :induct
    (procs-equivalent-p
     ids
     procs-1
     procs-2))
   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))

;; Main single-step preservation theorem

(defthm state-equivalent-p-preserved-by-checkpoint-body-step
  (implies
   (and
    (state-equivalent-p
     st-1
     st-2)
    (cl-checkpoint-body-input-p
     input)
    (recovery-free-state-p
     st-1)
    (recovery-free-state-p
     st-2)
    (legal-inputp
     st-1
     input)
    (legal-inputp
     st-2
     input))
   (state-equivalent-p
   (system-step st-1 input)
   (system-step st-2 input))))

) ;; end local single-step preservation proof

;; ------------------------------------------------------------
;; Equivalent states remain equivalent after executing the
;; same legal, recovery-free checkpoint-body postfix.
;; ------------------------------------------------------------

(defthm state-equivalent-p-preserved-by-checkpoint-body-inputs
  (implies
   (and
    (state-equivalent-p
     st-1
     st-2)
    (good-state-p st-1)
    (good-state-p st-2)
    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)
    (cl-checkpoint-body-inputs-p
     inputs)
    (legal-input-sequencep
     st-1
     inputs)
    (legal-input-sequencep
     st-2
     inputs))
   (state-equivalent-p
    (run-imp st-1 inputs)
    (run-imp st-2 inputs)))
  :hints
  (("Goal"
    :in-theory
    (disable
     system-step
     legal-inputp
     good-state-p
     recovery-free-state-p
     cl-checkpoint-body-input-p
     state-equivalent-p))))

(defthm state-equivalent-p-reflexive
  (state-equivalent-p st st))

;; ------------------------------------------------------------
;; Equivalent process tables have identical incoming-neighbor lists for every process identifier in IDS.
;; ------------------------------------------------------------

(defthm procs-equivalent-p-implies-nbrs-from-equal
  (implies
   (and
    (procs-equivalent-p
     ids
     procs-1
     procs-2)
    (memberp i ids))
   (equal
    (g :nbrs-from
       (g i procs-1))
    (g :nbrs-from
       (g i procs-2)))))

(defthm state-equivalent-p-preserves-legal-body-inputp
  (implies
   (and
    (state-equivalent-p
     st-original
     st-after-swap)
    (recovery-free-state-p
     st-original)
    (recovery-free-state-p
     st-after-swap)
    (cl-checkpoint-body-input-p
     input)
    (legal-inputp
     st-original
     input))
   (legal-inputp
    st-after-swap
    input)))

(defthm state-equivalent-p-preserves-legal-postfix
  (implies
   (and
    (state-equivalent-p
     st-original
     st-after-swap)
    (recovery-free-state-p
     st-original)
    (recovery-free-state-p
     st-after-swap)
    (good-state-p st-original)
    (good-state-p st-after-swap)
    (cl-checkpoint-body-inputs-p
     postfix)
    (legal-input-sequencep
     st-original
     postfix))
   ;; Therefore, the same postfix is legal after the swap.
   (legal-input-sequencep
    st-after-swap
    postfix))
  :hints (("Goal"
	  ; :induct (legal-input-sequencep st-after-swap postfix)
	   :in-theory (disable legal-inputp
			       state-equivalent-p
			       recovery-free-state-p
			       good-state-p
			       system-step
			       cl-checkpoint-body-input-p)))
  :rule-classes
  ((:rewrite
    :match-free :all)))

(defthm state-equivalent-p-preserved-by-postfix
  (implies
   (and
    (state-equivalent-p
     st-original
     st-after-swap)
    (recovery-free-state-p st-original)
    (recovery-free-state-p st-after-swap)
    (good-state-p st-original)
    (good-state-p st-after-swap)
    (cl-checkpoint-body-inputs-p postfix)
    (legal-input-sequencep
     st-original
     postfix))
   (state-equivalent-p
    (run-imp st-original postfix)
    (run-imp st-after-swap postfix)))
  :hints (("Goal"
	  ; :induct (legal-input-sequencep st-after-swap postfix)
	   :in-theory (disable
			       state-equivalent-p
			       recovery-free-state-p
			       good-state-p
			       run-imp
			       cl-checkpoint-body-inputs-p))))

;; ------------------------------------------------------------
;; Legality of a concatenated execution implies legality of its suffix from the state reached after its prefix.
;; ------------------------------------------------------------

(defthm legal-input-sequencep-of-append-implies-second
  (implies
   (legal-input-sequencep
    st
    (append inputs-1 inputs-2))
   (legal-input-sequencep
    (run-imp st inputs-1)
    inputs-2)))

(defthm one-post-pre-swap-with-prefix-and-postfix
  (let*
      (;; State immediately before the adjacent pair.
       (swap-st
        (run-imp st prefix))
       ;; States immediately after the two possible pair orders.
       (original-pair-st
        (run-imp
         swap-st
         (list input-post input-pre)))
       (swapped-pair-st
        (run-imp
         swap-st
         (list input-pre input-post)))
       ;; Complete original and swapped sequences.
       (original-inputs
        (append (append prefix (list input-post input-pre)) postfix))
       (swapped-inputs
        (append (append prefix (list input-pre input-post)) postfix)))
    (implies
     (and
      (legal-input-sequencep
       st
       original-inputs)
      (post-pre-swap-start-p
       swap-st
       m-at-swap
       input-post
       input-pre)
      (cl-checkpoint-body-inputs-p
       postfix)
      (good-state-p original-pair-st)
      (good-state-p swapped-pair-st)
      (recovery-free-state-p original-pair-st)
      (recovery-free-state-p swapped-pair-st))
    ;; Both complete executions end in equivalent states.
    (state-equivalent-p
       (run-imp st original-inputs)
       (run-imp st swapped-inputs))))
  :hints
(("Goal"
  :do-not-induct t
  :use
  ((:instance
    post-pre-two-imp-inputs-commute-under-state-equivalence
    (st
     (run-imp st prefix))
    (m
     m-at-swap)
    (input-1
     input-post)
    (input-2
     input-pre))
   (:instance
    legal-input-sequencep-of-append-implies-second
    (st
     st)
    (inputs-1
     (append
      prefix
      (list input-post input-pre)))
    (inputs-2
     postfix))
   (:instance
    state-equivalent-p-preserved-by-postfix
    (st-original
     (run-imp
      (run-imp st prefix)
      (list input-post input-pre)))
    (st-after-swap
     (run-imp
      (run-imp st prefix)
      (list input-pre input-post)))
    (postfix
     postfix)))
  :in-theory
  (disable append
    run-imp
    recovery-free-state-p
    good-state-p
    cl-checkpoint-body-inputs-p
    post-pre-swap-start-p
    legal-input-sequencep
    state-equivalent-p
;    post-pre-two-imp-inputs-commute-under-state-equivalence
    legal-input-sequencep-of-append-implies-second
    state-equivalent-p-preserved-by-postfix))))

;; ------------------------------------------------------------
;; A swappable pair is legal in its original order.
;; ------------------------------------------------------------

(defthm two-imp-inputs-swappable-p-implies-original-order-legal
  (implies
   (two-imp-inputs-swappable-p
    st input-1 input-2)
   (legal-input-sequencep
    st
    (list input-1 input-2)))
  :hints
  (("Goal"
    :in-theory
    (disable cl-checkpoint-body-input-p
	     legal-inputp
	     system-step))))

;; ------------------------------------------------------------
;; A swappable pair is also legal in the exchanged order.
;; ------------------------------------------------------------

(defthm two-imp-inputs-swappable-p-implies-swapped-order-legal
  (implies
   (two-imp-inputs-swappable-p
    st input-1 input-2)
   (legal-input-sequencep
    st
    (list input-2 input-1)))
    :hints
  (("Goal"
    :in-theory
    (disable cl-checkpoint-body-input-p
	     legal-inputp
	     system-step))))

;; ------------------------------------------------------------
;; The local POST/PRE swap condition is strong enough to establish all state-quality assumptions needed after the adjacent pair, in both execution orders.
;; ------------------------------------------------------------

(defthm post-pre-swap-start-implies-good-state
  (implies
   (post-pre-swap-start-p
    st m input-1 input-2)
   (good-state-p st))
  :rule-classes
  ((:rewrite
    :match-free :all))
  :hints
  (("Goal"
    :in-theory
    (disable good-state-p))))

(defthm post-pre-swap-start-implies-recovery-free-state
  (implies
   (post-pre-swap-start-p
    st m input-1 input-2)
   (recovery-free-state-p st))
  :rule-classes
  ((:rewrite
    :match-free :all))
  :hints
  (("Goal"
    :in-theory
     (disable
   ;  post-pre-swap-start-p
     good-state-p
     cut-markers-in-transit-p
     legal-input-sequencep
     cm-cut-not-taken
     process-cut-step
     good-cut-meta-p
     cut-meta-imp-consistent-p
     cl-checkpoint-body-input-p
     recovery-free-state-p))))

(defthm post-pre-swap-start-implies-cp-inputs
  (implies
   (post-pre-swap-start-p
    st m input-1 input-2)
   (cl-checkpoint-body-inputs-p (list input-1 input-2)))
  :rule-classes
  ((:rewrite
    :match-free :all))
  :hints
  (("Goal"
    :in-theory
     (disable
     good-state-p
     cut-markers-in-transit-p
     legal-input-sequencep
     cm-cut-not-taken
     process-cut-step
     good-cut-meta-p
     cut-meta-imp-consistent-p
     cl-checkpoint-body-input-p
     recovery-free-state-p))))

(defthm post-pre-swap-start-implies-cp-inputs-2
  (implies
   (post-pre-swap-start-p
    st m input-1 input-2)
   (cl-checkpoint-body-inputs-p (list input-2 input-1)))
  :rule-classes
  ((:rewrite
    :match-free :all))
  :hints
  (("Goal"
    :in-theory
     (disable
     good-state-p
     cut-markers-in-transit-p
     legal-input-sequencep
     cm-cut-not-taken
     process-cut-step
     good-cut-meta-p
     cut-meta-imp-consistent-p
     cl-checkpoint-body-input-p
     recovery-free-state-p))))

(defthm post-pre-swap-start-implies-pair-states-good-and-recovery-free
  (implies
   (post-pre-swap-start-p
    st m input-1 input-2)
   (and
    ;; Original order.
    (good-state-p
     (run-imp
      st
      (list input-1 input-2)))
    (recovery-free-state-p
     (run-imp
      st
      (list input-1 input-2)))
    ;; Swapped order.
    (good-state-p
     (run-imp
      st
      (list input-2 input-1)))
    (recovery-free-state-p
     (run-imp
      st
      (list input-2 input-1)))))
  :hints
  (("Goal"
       ; :use ((:instance post-pre-two-imp-inputs-swappable-p ))
    :in-theory
    (disable
     post-pre-swap-start-p
     good-state-p
     cut-markers-in-transit-p
     legal-input-sequencep
     cm-cut-not-taken
     process-cut-step
     good-cut-meta-p
     cut-meta-imp-consistent-p
     cl-checkpoint-body-input-p
     run-imp
     recovery-free-state-p))))

(defthm one-post-pre-swap-with-prefix-and-postfix-final
  (let*
      (;; State immediately before the adjacent pair.
       (swap-st
        (run-imp st prefix))
       ;; Complete original and swapped sequences.
       (original-inputs
        (append
         (append prefix
                 (list input-post input-pre))
         postfix))
       (swapped-inputs
        (append
         (append prefix
                 (list input-pre input-post))
         postfix)))
    (implies
     (and
      (legal-input-sequencep
       st
       original-inputs)
      (post-pre-swap-start-p
       swap-st
       m-at-swap
       input-post
       input-pre)
      (cl-checkpoint-body-inputs-p
       postfix))
     ;; Both complete executions end in equivalent states.
     (state-equivalent-p
      (run-imp st original-inputs)
      (run-imp st swapped-inputs))))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    (;; Local POST/PRE swap preserves state equivalence.
     (:instance
      post-pre-two-imp-inputs-commute-under-state-equivalence
      (st
       (run-imp st prefix))
      (m
       m-at-swap)
      (input-1
       input-post)
      (input-2
       input-pre))
     ;; The swap-start condition also guarantees that both
     ;; pair-result states are good and recovery-free.
     (:instance
      post-pre-swap-start-implies-pair-states-good-and-recovery-free
      (st
       (run-imp st prefix))
      (m
       m-at-swap)
      (input-1
       input-post)
      (input-2
       input-pre))
     ;; Legality of the entire original execution gives legality
     ;; of POSTFIX from the original pair-result state.
     (:instance
      legal-input-sequencep-of-append-implies-second
      (st
       st)
      (inputs-1
       (append
        prefix
        (list input-post input-pre)))
      (inputs-2
       postfix))
     ;; Propagate pair-state equivalence through the common POSTFIX.
     (:instance
      state-equivalent-p-preserved-by-postfix
      (st-original
       (run-imp
        (run-imp st prefix)
        (list input-post input-pre)))
      (st-after-swap
       (run-imp
        (run-imp st prefix)
        (list input-pre input-post)))
      (postfix
       postfix)))
    :in-theory
    (disable append
      run-imp
      recovery-free-state-p
      good-state-p
      cl-checkpoint-body-inputs-p
      post-pre-swap-start-p
      legal-input-sequencep
      state-equivalent-p
      post-pre-swap-start-implies-pair-states-good-and-recovery-free
      legal-input-sequencep-of-append-implies-second
      state-equivalent-p-preserved-by-postfix))))
