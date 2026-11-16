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
(include-book "scan")
(include-book "basic")


(defun cut-meta-imp-procs-consistent-p
    (ids target-sid m imp-procs)

  (declare
   (xargs :measure (acl2-count ids)))

  (if (endp ids)

      t

    (let* ((i       (first ids))
           (p       (g i imp-procs))
           (has-sid (memberp target-sid
                             (snapshot-ids p))))

      (and

       ;; ------------------------------------------------------------
       ;; CUT STATUS
       ;; ------------------------------------------------------------
       (equal
        (cm-cut-not-taken-p m i)
        (not has-sid))


       ;; --------------------------------------------------
       ;; WAITING-MARKER-FROM
       ;; --------------------------------------------------
       (if has-sid

           ;; Once i has taken the cut, the scanner metadata
           ;; must exactly mirror the implementation snapshot.
           (equal
            (g i
               (cm-waiting-marker-from m))

            (snapshot-waiting-marker-from
             (snapshot-entry
              target-sid
              p)))

         ;; Before i takes the cut, it must not yet have an
         ;; open-channel row in the cut metadata.
         (endp
          (g i
             (cm-waiting-marker-from m))))


       (cut-meta-imp-procs-consistent-p
        (rest ids)
        target-sid
        m
        imp-procs)))))



(defun cut-meta-imp-initiator-consistent-p (m imp-st)
  (let* ((target-sid     (cm-sid m))
         (initiator      (first target-sid))
         (target-counter (second target-sid))
         (proc-ids       (proc-ids imp-st))
         (p              (g initiator
                            (procs imp-st))))

    (and
     (memberp initiator proc-ids)

     (if (cm-cut-not-taken-p m initiator)

         ;; Target checkpoint has not started.
         (and
          (equal (counter p)
                 target-counter)

          ;; Before the initiator starts the target checkpoint,
          ;; nobody can have taken this target cut.
          (equal (cm-cut-not-taken m)
                 (cm-proc-ids m)))

       ;; Target checkpoint has started.
       (< target-counter
          (counter p))))))



(defun cut-meta-imp-proc-ids-consistent-p (m imp-st)
  (equal
   (cm-proc-ids m)
   (proc-ids imp-st)))




(defun cut-meta-imp-consistent-p (m imp-st)

  (and

   ;; Metadata and implementation describe the same processes.
   (cut-meta-imp-proc-ids-consistent-p m imp-st)
   ;; The SID initiator/counter agrees with implementation state.
   (cut-meta-imp-initiator-consistent-p
    m
    imp-st)

   ;; Per-process cut status and waiting-marker state agree.
   (cut-meta-imp-procs-consistent-p
    (cm-proc-ids m)
    (cm-sid m)
    m
    (procs imp-st))))





(defun target-sid-absent-from-procs-p
    (ids target-sid procs)

  (declare
   (xargs :measure (acl2-count ids)))

  (if (endp ids)

      t

    (let* ((i (first ids))
           (p (g i procs)))

      (and
       (not
        (memberp
         target-sid
         (snapshot-ids p)))

       (target-sid-absent-from-procs-p
        (rest ids)
        target-sid
        procs)))))




(encapsulate ()

(local-defthm
  cut-meta-imp-proc-ids-consistent-p-of-make-cut-meta

  (cut-meta-imp-proc-ids-consistent-p
   (make-cut-meta sid initiator st)
   st))


(local-defthm
  cut-meta-imp-initiator-consistent-p-of-make-cut-meta

  (implies
   (and
    (memberp
     initiator
     (proc-ids st))

    (equal
     sid
     (list
      initiator
      (counter
       (g initiator
          (procs st))))))

   (cut-meta-imp-initiator-consistent-p
    (make-cut-meta sid initiator st)
    st)))


(local-defthm
  cut-meta-imp-procs-consistent-p-of-make-cut-meta-gen

  (implies
   (and
    (subset
     ids
     (proc-ids st))

    (target-sid-absent-from-procs-p
     ids
     sid
     (procs st)))

   (cut-meta-imp-procs-consistent-p
    ids
    sid
    (make-cut-meta sid initiator st)
    (procs st))))



(local-defthm
  cut-meta-imp-procs-consistent-p-of-make-cut-meta

  (implies
   (target-sid-absent-from-procs-p
    (proc-ids st)
    sid
    (procs st))

   (cut-meta-imp-procs-consistent-p
    (proc-ids st)
    sid
    (make-cut-meta sid initiator st)
    (procs st)))

  :hints
  (("Goal"
    :use
    ((:instance
      cut-meta-imp-procs-consistent-p-of-make-cut-meta-gen
      (ids (proc-ids st)))))))




(defthm
  cut-meta-imp-consistent-p-of-make-cut-meta

  (implies
   (and
    ;; INITIATOR is a real process.
    (memberp
     initiator
     (proc-ids st))

    ;; SID is exactly the checkpoint that INITIATOR
    ;; would start in ST.
    (equal
     sid
     (list
      initiator
      (counter
       (g initiator
          (procs st)))))

    ;; This checkpoint has not started yet.
    (target-sid-absent-from-procs-p
     (proc-ids st)
     sid
     (procs st)))

   (cut-meta-imp-consistent-p
    (make-cut-meta
     sid
     initiator
     st)

    st))

  :hints
  (("Goal"
    :use
    ((:instance
      cut-meta-imp-proc-ids-consistent-p-of-make-cut-meta)

     (:instance
      cut-meta-imp-initiator-consistent-p-of-make-cut-meta)

     (:instance
      cut-meta-imp-procs-consistent-p-of-make-cut-meta)))))



(defun good-cut-meta-sid-p (m)
  (let ((sid (cm-sid m)))
    (and
     (true-listp sid)
     (equal (len sid) 2)

     ;; SID = (initiator counter)
     (memberp
      (first sid)
      (cm-proc-ids m))

     (natp
      (second sid)))))


(defun good-cut-meta-cut-not-taken-p (m)
  (and
   (true-listp
    (cm-cut-not-taken m))

   (uniquep
    (cm-cut-not-taken m))

   (subset
    (cm-cut-not-taken m)
    (cm-proc-ids m))))


(defun good-cut-meta-waiting-for-procs-p (ids m)
  (declare
   (xargs :measure (acl2-count ids)))

  (if (endp ids)

      t

    (let* ((i       (first ids))
           (waiting (g i
                       (g :waiting-marker-from m))))

      (and
       ;; A waiting row is a proper, duplicate-free process list.
       (true-listp waiting)

       (uniquep waiting)

       ;; It cannot mention a process outside this metadata universe.
       (subset
        waiting
        (cm-proc-ids m))

       ;; A process that has not taken its cut should not yet
       ;; be waiting for checkpoint markers.
       (implies
        (cm-cut-not-taken-p m i)
        (endp waiting))

       (good-cut-meta-waiting-for-procs-p
        (rest ids)
        m)))))


(defun good-cut-meta-global-input-sequences-p (m)
  (and
   (true-listp
    (g :before-cut-input-sequence m))

   (true-listp
    (g :after-cut-input-sequence m))))



(defun good-cut-meta-p (m)
  (and
   ;; Process universe.
   (true-listp
    (cm-proc-ids m))

   (uniquep
    (cm-proc-ids m))

   ;; Target checkpoint identifier.
   (good-cut-meta-sid-p m)

   ;; Cut-status set.
   (good-cut-meta-cut-not-taken-p m)

   ;; Per-process waiting-marker rows.
   (good-cut-meta-waiting-for-procs-p
    (cm-proc-ids m)
    m)

   ;; Global stored input sequences.
   (good-cut-meta-global-input-sequences-p m)))




;; ------------------------------------------------------------
;; GOOD-CUT-META-P is invariant under one metadata-processing step, provided the implementation state and metadata are mutually consistent and the concrete input is legal.
;; ------------------------------------------------------------

;; ------------------------------------------------------------
;; FRAME LEMMAS FOR THE TWO GLOBAL INPUT-SEQUENCE FIELDS
;; ------------------------------------------------------------


(defthm
  good-cut-meta-waiting-for-procs-p-of-s-before-cut-input-sequence

  (equal
   (good-cut-meta-waiting-for-procs-p
    ids
    (s :before-cut-input-sequence xs m))

   (good-cut-meta-waiting-for-procs-p
    ids
    m)))


(defthm
  good-cut-meta-waiting-for-procs-p-of-s-after-cut-input-sequence

  (equal
   (good-cut-meta-waiting-for-procs-p
    ids
    (s :after-cut-input-sequence xs m))

   (good-cut-meta-waiting-for-procs-p
    ids
    m)))


;; ------------------------------------------------------------
;; Updating a stored input sequence does not affect the correspondence between the cut-control metadata and the implementation process state.
;; ------------------------------------------------------------


(local-defthm
  cut-meta-imp-procs-consistent-p-of-s-before-cut-input-sequence

  (equal
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    (s :before-cut-input-sequence xs m)
    procs)

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    procs)))


(local-defthm
  cut-meta-imp-procs-consistent-p-of-s-after-cut-input-sequence

  (equal
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    (s :after-cut-input-sequence xs m)
    procs)

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    procs)))


;; ============================================================
;; APPEND-ONE preserves TRUE-LISTP.
;; ============================================================


(local-defthm
  true-listp-of-append-one

  (implies
   (true-listp xs)

   (true-listp
    (append xs
            (list x)))))


;; ============================================================
;; Adding one input to either global sequence preserves the
;; structural invariant for the two stored sequences.
;; ============================================================


(local-defthm
  good-cut-meta-global-input-sequences-p-of-add-before

  (implies
   (good-cut-meta-global-input-sequences-p m)

   (good-cut-meta-global-input-sequences-p
    (cm-add-before-cut-input-sequence
     m
     input))))


(local-defthm
  good-cut-meta-global-input-sequences-p-of-add-after

  (implies
   (good-cut-meta-global-input-sequences-p m)

   (good-cut-meta-global-input-sequences-p
    (cm-add-after-cut-input-sequence
     m
     input))))


;; ============================================================
;; Extract the structural properties of an incoming-neighbor
;; list from GOOD-PROCS-P.
;; ============================================================


(local-defthm
  cl-good-procs-p-implies-good-proc-p

  (implies
   (and
    (good-procs-p ids procs all-ids)
    (memberp i ids))

   (good-proc-p
    (g i procs)
    all-ids)))


(defthm
  good-procs-p-implies-good-nbrs-from

  (implies
   (and
    (good-procs-p
     ids
     procs
     all-ids)

    (memberp i ids))

   (and
    (true-listp
     (g :nbrs-from
        (g i procs)))

    (uniquep
     (g :nbrs-from
        (g i procs)))

    (subset
     (g :nbrs-from
        (g i procs))
     all-ids))))


;; ============================================================
;; Closing one already-open incoming channel preserves the
;; waiting-marker invariant.
;; ============================================================


(local-defthm
  good-cut-meta-waiting-for-procs-p-of-remove-waiting-marker

  (implies
   (good-cut-meta-waiting-for-procs-p
    ids
    m)

   (good-cut-meta-waiting-for-procs-p
    ids

    (s :waiting-marker-from
       (s i
          (remove1-equal
           j
           (g i
              (g :waiting-marker-from m)))

          (g :waiting-marker-from m))

       m)))

  :hints
  (("Goal"
    :induct
    (good-cut-meta-waiting-for-procs-p
     ids
     m))

   ("Subgoal *1/2"
    :cases
    ((equal i
            (car ids))))))


;; ------------------------------------------------------------
;; A first target-marker receive:
;; ------------------------------------------------------------


(local-defthm
  good-cut-meta-waiting-for-procs-p-of-first-marker-update

  (implies
   (and
    (good-cut-meta-waiting-for-procs-p
     ids
     m)

    (uniquep
     (g :cut-not-taken m))

    (true-listp nbrs)

    (uniquep nbrs)

    (subset
     nbrs
     (g :proc-ids m)))

   (good-cut-meta-waiting-for-procs-p
    ids

    (s :cut-not-taken
       (remove1-equal
        i
        (g :cut-not-taken m))

       (s :waiting-marker-from
          (s i
             (remove1-equal j nbrs)
             (g :waiting-marker-from m))

          (s :before-cut-input-sequence
             new-before
             m)))))

  :hints
  (("Goal"
    :induct
    (good-cut-meta-waiting-for-procs-p
     ids
     m))

   ("Subgoal *1/2"
    :cases
    ((equal i
            (car ids))))))



;; ------------------------------------------------------------
;; Starting the target checkpoint:
;; ------------------------------------------------------------


(local-defthm
  good-cut-meta-waiting-for-procs-p-of-start-checkpoint-update

  (implies
   (and
    (good-cut-meta-waiting-for-procs-p
     ids
     m)

    (uniquep
     (g :cut-not-taken m))

    (true-listp nbrs)

    (uniquep nbrs)

    (subset
     nbrs
     (g :proc-ids m)))

   (good-cut-meta-waiting-for-procs-p
    ids

    (s :cut-not-taken
       (remove1-equal
        i
        (g :cut-not-taken m))

       (s :waiting-marker-from
          (s i
             nbrs
             (g :waiting-marker-from m))

          (s :before-cut-input-sequence
             new-before
             m)))))

  :hints
  (("Goal"
    :induct
    (good-cut-meta-waiting-for-procs-p
     ids
     m))

   ("Subgoal *1/2"
    :cases
    ((equal i
            (car ids))))))



;; ------------------------------------------------------------
;; LATER TARGET MARKER
;; ------------------------------------------------------------

(local-defthm
  good-cut-meta-waiting-for-procs-p-of-later-marker

  (implies
   (good-cut-meta-waiting-for-procs-p
    ids
    m)

   (good-cut-meta-waiting-for-procs-p
    ids

    (s :waiting-marker-from
       (s i
          (remove1-equal
           j
           (g i
              (g :waiting-marker-from m)))

          (g :waiting-marker-from m))

       (s :after-cut-input-sequence
          new-after
          m))))

  :hints
  (("Goal"
    :induct
    (good-cut-meta-waiting-for-procs-p
     ids
     m))

   ("Subgoal *1/2"
    :cases
    ((equal i
            (car ids))))))


;; ------------------------------------------------------------
;; TARGET START-CHECKPOINT
;; ------------------------------------------------------------

(local-defthm
  good-cut-meta-waiting-for-procs-p-of-initial-start-checkpoint

  (implies
   (and
    (good-cut-meta-waiting-for-procs-p
     (g :proc-ids m)
     m)

    (uniquep
     (g :proc-ids m))

    (equal
     (g :cut-not-taken m)
     (g :proc-ids m))

    (good-procs-p
     (g :proc-ids m)
     procs
     (g :proc-ids m))

    (memberp
     i
     (g :proc-ids m)))

   (good-cut-meta-waiting-for-procs-p
    (g :proc-ids m)

    (s :cut-not-taken
       (remove1-equal
        i
        (g :proc-ids m))

       (s :waiting-marker-from
          (s i
             (g :nbrs-from
                (g i procs))

             (g :waiting-marker-from m))

          (s :before-cut-input-sequence
             new-before
             m)))))

  :hints
  (("Goal"
    :use
    ((:instance
      good-cut-meta-waiting-for-procs-p-of-start-checkpoint-update

      (ids
       (g :proc-ids m))

      (nbrs
       (g :nbrs-from
          (g i procs))))))))



;; ------------------------------------------------------------
;; FIRST TARGET MARKER
;; ------------------------------------------------------------

(local-defthm
  good-cut-meta-waiting-for-procs-p-of-initial-first-marker

  (implies
   (and
    (good-cut-meta-waiting-for-procs-p
     (g :proc-ids m)
     m)

    (uniquep
     (g :proc-ids m))

    (equal
     (g :cut-not-taken m)
     (g :proc-ids m))

    (good-procs-p
     (g :proc-ids m)
     procs
     (g :proc-ids m))

    (memberp
     i
     (g :proc-ids m)))

   (good-cut-meta-waiting-for-procs-p
    (g :proc-ids m)

    (s :cut-not-taken
       (remove1-equal
        i
        (g :proc-ids m))

       (s :waiting-marker-from
          (s i
             (remove1-equal
              j
              (g :nbrs-from
                 (g i procs)))

             (g :waiting-marker-from m))

          (s :before-cut-input-sequence
             new-before
             m)))))

  :hints
  (("Goal"
    :use
    ((:instance
      good-cut-meta-waiting-for-procs-p-of-first-marker-update

      (ids
       (g :proc-ids m))

      (nbrs
       (g :nbrs-from
          (g i procs))))))))



(defthm
  good-cut-meta-p-preserved-by-process-cut-step

  (implies
   (and
    (good-cut-meta-p m)

    (cut-meta-imp-consistent-p
     m
     st)

    (good-state-p st)

    (legal-inputp
     st
     input))

   (good-cut-meta-p
    (process-cut-step
     input
     st
     m)))
  :otf-flg t
  :hints
  (("Goal"
    :in-theory
    (disable
     cut-meta-imp-procs-consistent-p
     snapshot-counters-good-for-procs-p
     nbrs-from-to-consistent-p
     nbrs-to-from-consistent-p
     good-channels-p))))



(local-defthm remove-from-list-when-not-memberp-and-true-listp
  (implies
   (and
    (true-listp xs)
    (not (memberp x xs)))

   (equal
    (remove-from-list xs x)
    xs)))

(defthm
  remove-from-list-equals-remove1-equal-when-true-listp-and-uniquep

  (implies
   (and
    (true-listp xs)
    (uniquep xs))

   (equal
    (remove-from-list xs x)
    (remove1-equal x xs))))



(local-defthm
  proc-ids-of-cm-add-before-cut-input-sequence

  (equal
   (proc-ids
    (cm-add-before-cut-input-sequence
     m
     input))

   (proc-ids m)))


(local-defthm
  sid-of-cm-add-before-cut-input-sequence

  (equal
   (sid
    (cm-add-before-cut-input-sequence
     m
     input))

   (sid m)))

(local-defthm
  cut-meta-imp-procs-consistent-p-of-cm-add-before-cut-input-sequence

  (equal
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    (cm-add-before-cut-input-sequence m input)
    procs)

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    procs)))

(local-defthm
  cm-cut-not-taken-p-of-cm-add-before-cut-input-sequence

  (equal
   (cm-cut-not-taken-p
    (cm-add-before-cut-input-sequence m input)
    i)

   (cm-cut-not-taken-p
    m
    i)))


(local-defthm
  proc-ids-of-cm-add-after-cut-input-sequence

  (equal
   (proc-ids
    (cm-add-after-cut-input-sequence
     m
     input))

   (proc-ids m)))


(local-defthm
  sid-of-cm-add-after-cut-input-sequence

  (equal
   (sid
    (cm-add-after-cut-input-sequence
     m
     input))

   (sid m)))


(local-defthm
  cut-meta-imp-procs-consistent-p-of-cm-add-after-cut-input-sequence

  (equal
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    (cm-add-after-cut-input-sequence m input)
    procs)

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    procs)))


(local-defthm
  cm-cut-not-taken-p-of-cm-add-after-cut-input-sequence

  (equal
   (cm-cut-not-taken-p
    (cm-add-after-cut-input-sequence m input)
    i)

   (cm-cut-not-taken-p
    m
    i)))


(local-defthm proc-ids-of-step-normal
  (equal
   (proc-ids
    (step-normal st i))

   (proc-ids st)))


(local-defthm counter-of-g-of-procs-of-step-normal
  (equal
   (counter
    (g j
       (procs
        (step-normal st i))))

   (counter
    (g j
       (procs st)))))



(local-defthm
  cut-meta-imp-procs-consistent-p-of-step-normal

  (equal
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    (procs
     (step-normal st i)))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    (procs st))))






(local-defthm
    counter-of-target-proc-unchanged-by-start-checkpoint-on-other-proc
    (implies
     (not (equal i j))
     (equal (g :counter (g i (start-checkpoint-helper procs j)))
	    (g :counter (g i  procs )))))



(local-defthm
  target-counter-bound-preserved-by-start-checkpoint-helper

  (implies
   (< target-counter
      (counter
       (g initiator procs)))

   (< target-counter
      (counter
       (g initiator
          (start-checkpoint-helper
           procs
           i)))))

  :rule-classes
  ((:rewrite :match-free :all))

  :hints
  (("Goal"
    :cases
    ((equal i initiator)))))






(defun target-cut-proc-view (target-sid p)
  (let ((has-sid
         (memberp target-sid
                  (snapshot-ids p))))
    (list
     has-sid
     (if has-sid
         (snapshot-waiting-marker-from
          (snapshot-entry target-sid p))
       nil))))




(local-defthm
  cut-meta-imp-procs-consistent-p-of-proc-update-when-target-view-same

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs)

    (equal
     (target-cut-proc-view
      target-sid
      new-p)

     (target-cut-proc-view
      target-sid
      (g i procs))))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    (s i new-p procs)))

  :hints
  (("Goal"
    :induct
    (len ids))

   ;; The LEN induction has only one nontrivial inductive step.
   ("Subgoal *1/1"
    :cases
    ((equal i
            (car ids))))))

;; Updating the counter does not affect the target-cut view.

(local-defthm target-cut-proc-view-of-counter-update
  (equal
   (target-cut-proc-view
    target-sid
    (s :counter new-counter p))

   (target-cut-proc-view
    target-sid
    p)))

;; Installing an entry for another SID does not affect TARGET-SID.

(local-defthm
  target-cut-proc-view-of-install-snapshot-entry-other-sid

  (implies
   (not (equal target-sid new-sid))

   (equal
    (target-cut-proc-view
     target-sid
     (install-snapshot-entry
      new-sid
      entry
      p))

    (target-cut-proc-view
     target-sid
     p))))


;; Starting another checkpoint preserves the updated process's
;; view of TARGET-SID.

(local-defthm
  target-cut-proc-view-of-g-of-start-checkpoint-helper-other-sid

  (implies
   (not
    (equal
     target-sid
     (list i
           (counter (g i procs)))))

   (equal
    (target-cut-proc-view
     target-sid
     (g i
        (start-checkpoint-helper procs i)))

    (target-cut-proc-view
     target-sid
     (g i procs)))))


(local-defthm
  cut-meta-imp-procs-consistent-p-of-start-checkpoint-helper-other-sid

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs)

    (not
     (equal
      target-sid
      (list i
            (counter (g i procs))))))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    (start-checkpoint-helper procs i)))

  :hints
  (("Goal"
    :do-not-induct t

    :use
    ((:instance
      target-cut-proc-view-of-g-of-start-checkpoint-helper-other-sid)

     (:instance
      cut-meta-imp-procs-consistent-p-of-proc-update-when-target-view-same

      (new-p
       (g i
          (start-checkpoint-helper procs i))))))))


(local-defthm
  proc-ids-of-first-marker-meta-update

  (equal
   (proc-ids
    (cm-set-waiting-marker-for
     (cm-remove-cut-not-taken
      (cm-add-before-cut-input-sequence
       m
       input)
      i)
     i
     waiting))

   (proc-ids m)))


(local-defthm
  sid-of-first-marker-meta-update

  (equal
   (sid
    (cm-set-waiting-marker-for
     (cm-remove-cut-not-taken
      (cm-add-before-cut-input-sequence
       m
       input)
      i)
     i
     waiting))

   (sid m)))


(local-defthm
  counter-of-proc-update-for-normal-msg-core

  (equal
   (counter
    (g j
       (s i
          (update-proc-for-normal-msg-core
           (g i procs)
           sender
           msg)
          procs)))

   (counter
    (g j procs)))

  :hints
  (("Goal"
    :cases
    ((equal i j)))))



(local-defthm
  waiting-marker-from-of-record-msg-in-snapshots

  (equal
   (snapshot-waiting-marker-from
    (g target-sid
       (record-msg-in-snapshots
        snapshots
        snapshot-ids
        sender
        msg)))

   (snapshot-waiting-marker-from
    (g target-sid
       snapshots)))

  :hints
  (("Goal"
    :induct
    (record-msg-in-snapshots
     snapshots
     snapshot-ids
     sender
     msg))))


(local-defthm
  target-cut-proc-view-of-update-proc-for-normal-msg-core

  (equal
   (target-cut-proc-view
    target-sid
    (update-proc-for-normal-msg-core
     p
     sender
     msg))

   (target-cut-proc-view
    target-sid
    p)))


(local-defthm
  cut-meta-imp-procs-consistent-p-of-update-proc-for-normal-msg-core-general

  (implies
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    procs)

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    (s i
       (update-proc-for-normal-msg-core
        (g i procs)
        sender
        msg)
       procs)))

  :hints
  (("Goal"
    :use
    ((:instance
      cut-meta-imp-procs-consistent-p-of-proc-update-when-target-view-same
      (new-p
       (update-proc-for-normal-msg-core
        (g i procs)
        sender
        msg)))

     (:instance
      target-cut-proc-view-of-update-proc-for-normal-msg-core
      (target-sid target-sid)
      (p (g i procs))
      (sender sender)
      (msg msg))))))



(local-defthm
  proc-ids-of-marker-after-cut-meta-update

  (equal
   (proc-ids
    (cm-set-waiting-marker-for
     (cm-add-after-cut-input-sequence
      m
      input)
     i
     waiting))

   (proc-ids m)))


(local-defthm
  sid-of-marker-after-cut-meta-update

  (equal
   (sid
    (cm-set-waiting-marker-for
     (cm-add-after-cut-input-sequence
      m
      input)
     i
     waiting))

   (sid m)))


;; If process I has already taken TARGET-SID, then consistency requires TARGET-SID to be present in I's implementation snapshot list.

(local-defthm
  cut-meta-imp-procs-consistent-p-cut-taken-implies-snapshot

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs)

    (memberp i ids)

    (not
     (cm-cut-not-taken-p m i)))

   (memberp
    target-sid
    (snapshot-ids
     (g i procs)))))


;; Receiving the first marker for NEW-SID does not change the
;; cut-relevant view for TARGET-SID when the two SIDs are different.
(local-defthm
  target-cut-proc-view-of-update-proc-for-first-marker-msg-other-sid

  (implies
   (not
    (equal target-sid new-sid))

   (equal
    (target-cut-proc-view
     target-sid
     (update-proc-for-first-marker-msg
      p
      new-sid
      sender))

    (target-cut-proc-view
     target-sid
     p)))

  :rule-classes nil)


;; Therefore, installing a first marker for another SID preserves
;; process-level consistency for TARGET-SID.
(local-defthm
  cut-meta-imp-procs-consistent-p-of-update-proc-for-first-marker-msg-other-sid

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs)

    (not
     (equal target-sid new-sid)))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    m
    (s i
       (update-proc-for-first-marker-msg
        (g i procs)
        new-sid
        sender)
       procs)))

  :hints
  (("Goal"
    :use
    ((:instance
      target-cut-proc-view-of-update-proc-for-first-marker-msg-other-sid
      (target-sid target-sid)
      (new-sid new-sid)
      (p (g i procs))
      (sender sender))

     (:instance
      cut-meta-imp-procs-consistent-p-of-proc-update-when-target-view-same
      (ids ids)
      (target-sid target-sid)
      (m m)
      (procs procs)
      (i i)
      (new-p
       (update-proc-for-first-marker-msg
        (g i procs)
        new-sid
        sender)))))))






;; Recording INPUT in the before-cut sequence does not affect the cut-control metadata seen by CUT-META-IMP-PROCS-CONSISTENT-P, even after I takes the cut and its waiting-marker.
(local-defthm
  cut-meta-imp-procs-consistent-p-vanish-add-before-cut

  (equal
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    (cm-set-waiting-marker-for
     (cm-remove-cut-not-taken
      (cm-add-before-cut-input-sequence m input)
      i)
     i
     waiting)
    procs)

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    (cm-set-waiting-marker-for
     (cm-remove-cut-not-taken m i)
     i
     waiting)
    procs)))




;; When process I receives the first marker for TARGET-SID:

;; Removing an element from a proper list cannot introduce
;; an element that was not already present.



;;(defthm
  ;; not-memberp-of-remove1-equal-when-not-memberp

  ;; (implies
  ;;  (and
  ;;   (true-listp xs)
  ;;   (not (memberp j xs)))

  ;;  (not
  ;;   (memberp j
  ;;            (remove1-equal i xs)))))


;; Exact metadata-level simplification needed by Subgoal *1/2.2.2''.


(local-defthm
  not-cm-cut-not-taken-p-preserved-by-other-cut-update

  (implies
   (and
    (true-listp (cm-cut-not-taken m))
    (not (cm-cut-not-taken-p m j)))

   (not
    (cm-cut-not-taken-p
     (s :cut-not-taken
        (remove1-equal i (cm-cut-not-taken m))
        (s :waiting-marker-from
           new-waiting
           m))
     j))))


(local-defthm
  cm-cut-not-taken-member-preserved-by-removing-other-proc

  (implies
   (and
    (true-listp (cm-cut-not-taken m))
    (uniquep (cm-cut-not-taken m))
    (memberp j (cm-cut-not-taken m))
    (not (equal i j)))

   (memberp
    j
    (cm-cut-not-taken
     (s :cut-not-taken
        (remove1-equal i (cm-cut-not-taken m))
        (s :waiting-marker-from
           new-waiting
           m))))))


(local-defthm
  memberp-target-sid-of-install-snapshot-entry

  (memberp
   target-sid
   (snapshot-ids
    (install-snapshot-entry
     target-sid
     entry
     p))))


(local-defthm
  waiting-marker-from-of-install-snapshot-entry-same-sid

  (equal
   (snapshot-waiting-marker-from
    (snapshot-entry
     target-sid
     (install-snapshot-entry
      target-sid
      entry
      p)))

   (snapshot-waiting-marker-from
    entry)))

;; When process I takes the cut, removing I from the unique CUT-NOT-TAKEN list guarantees that I is no longer present.

(local-defthm
  not-memberp-self-of-cut-not-taken-after-taking-cut

  (implies
   (and
    (true-listp (cm-cut-not-taken m))
    (uniquep (cm-cut-not-taken m)))

   (not
    (memberp
     i
     (cm-cut-not-taken
      (s :cut-not-taken
         (remove1-equal i
                        (cm-cut-not-taken m))
         (s :waiting-marker-from
            new-waiting-marker-from
            m)))))))


;; MAKE-SNAPSHOT-ENTRY stores WAITING-MARKER-FROM exactly as supplied.
(local-defthm
  waiting-marker-from-of-make-snapshot-entry

  (equal
   (snapshot-waiting-marker-from
    (make-snapshot-entry
     local-state
     waiting
     sender))

   waiting))




;; If process I is not among IDS, then changing only I's cut metadata
;; and implementation process state cannot affect consistency over IDS.
(local-defthm
  cut-meta-imp-procs-consistent-p-of-untracked-proc-cut-update

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs)

    (not
     (memberp i ids)))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    ;; Metadata changes only for I.
    (s :cut-not-taken
       (remove1-equal i
                      (cm-cut-not-taken m))
       (s :waiting-marker-from
          (s i
             waiting
             (g :waiting-marker-from m))
          m))

    ;; Implementation changes only process I.
    (s i
       new-p
       procs)))

  :hints
  (("Goal"
    :induct
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs))))



(local-defthm
  cut-meta-imp-procs-consistent-p-of-first-target-marker

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs)

    (true-listp ids)
    (uniquep ids)

    (memberp i ids)

    (true-listp (cm-cut-not-taken m))
    (uniquep (cm-cut-not-taken m))

    ;; I has not taken TARGET-SID yet.
    (cm-cut-not-taken-p m i)

    ;; This is the first TARGET-SID marker at I.
    (not
     (memberp
      target-sid
      (snapshot-ids
       (g i procs))))

    ;; SENDER is one of I's incoming neighbors.
    (memberp
     sender
     (nbrs-from
      (g i procs)))

    ;; Needed only to relate REMOVE-FROM-LIST in the implementation
    ;; to REMOVE1-EQUAL in the metadata.
    (true-listp
     (nbrs-from
      (g i procs)))

    (uniquep
     (nbrs-from
      (g i procs))))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    (cm-set-waiting-marker-for
     (cm-remove-cut-not-taken
      m
      i)
     i
     (remove1-equal
      sender
      (nbrs-from
       (g i procs))))

    (s i
       (update-proc-for-first-marker-msg
        (g i procs)
        target-sid
        sender)
       procs)))

  :hints
  (("Goal"
    :in-theory
    (disable
     cm-cut-not-taken
     install-snapshot-entry
     make-snapshot-entry)

    :induct
    (cut-meta-imp-procs-consistent-p
     ids
     target-sid
     m
     procs))

   ("Subgoal *1/2"
    :cases
    ((equal i (car ids))))))



(local-defthm cut-meta-imp-procs-consistent-p-of-first-target-marker-good-procs
  (implies
   (and
    (cut-meta-imp-procs-consistent-p ids target-sid m procs)
    (true-listp ids)
    (uniquep ids)
    (good-procs-p ids procs ids)
    (memberp i ids)
    (true-listp (cm-cut-not-taken m))
    (uniquep (cm-cut-not-taken m))
    (cm-cut-not-taken-p m i)
    (not
     (memberp target-sid
              (snapshot-ids (g i procs))))
    ;; Sender must still be an incoming neighbor.
    (memberp sender
             (nbrs-from (g i procs))))
   (cut-meta-imp-procs-consistent-p
    ids target-sid
    (cm-set-waiting-marker-for
     (cm-remove-cut-not-taken m i)
     i
     (remove1-equal sender
                    (nbrs-from (g i procs))))
    (s i
       (update-proc-for-first-marker-msg
        (g i procs)
        target-sid
        sender)
       procs)))
  :hints
  (("Goal"
    :use
    ((:instance
      cut-meta-imp-procs-consistent-p-of-first-target-marker
      (ids ids)
      (target-sid target-sid)
      (m m)
      (procs procs)
      (i i)
      (sender sender)))
    :in-theory
    (disable
     cut-meta-imp-procs-consistent-p
     good-procs-p
     cm-cut-not-taken-p
     update-proc-for-first-marker-msg))))



;; From GOOD-STATE-P ST.
(local-defthm good-state-p-implies-good-procs-p
  (implies
   (good-state-p st)
   (good-procs-p
    (proc-ids st)
    (procs st)
    (proc-ids st))))


(local-defthm good-state-p-implies-true-listp-proc-ids
  (implies
   (good-state-p st)
   (true-listp (proc-ids st))))

(local-defthm good-state-p-implies-uniquep-proc-ids
  (implies
   (good-state-p st)
   (uniquep (proc-ids st))))

;; From GOOD-CUT-META-P M.
(local-defthm good-cut-meta-p-implies-true-listp-cut-not-taken
  (implies
   (good-cut-meta-p m)
   (true-listp (cm-cut-not-taken m))))

(local-defthm good-cut-meta-p-implies-uniquep-cut-not-taken
  (implies
   (good-cut-meta-p m)
   (uniquep (cm-cut-not-taken m))))


;; A before-cut record, cut removal, and waiting-marker update cannot
;; introduce a process that was absent from CUT-NOT-TAKEN.
(local-defthm not-cm-cut-not-taken-p-preserved-by-first-marker-meta-update
  (implies
   (and
    (true-listp (cm-cut-not-taken m))
    (not (cm-cut-not-taken-p m j)))
   (not
    (cm-cut-not-taken-p
     (cm-set-waiting-marker-for
      (cm-remove-cut-not-taken
       (cm-add-before-cut-input-sequence m input)
       i)
      i waiting)
     j))))


;; If I has not yet taken TARGET-SID, consistency requires that
;; TARGET-SID is absent from I's implementation snapshot list.
(local-defthm cut-meta-imp-procs-consistent-p-cut-not-taken-implies-no-snapshot
  (implies
   (and
    (cut-meta-imp-procs-consistent-p ids target-sid m procs)
    (memberp i ids)
    (cm-cut-not-taken-p m i))
   (not
    (memberp target-sid
             (snapshot-ids (g i procs))))))



;; AFTER-CUT bookkeeping does not affect cut consistency.
(local-defthm cut-meta-imp-procs-consistent-p-vanish-add-after-cut
  (equal
   (cut-meta-imp-procs-consistent-p
    ids target-sid
    (cm-set-waiting-marker-for
     (cm-add-after-cut-input-sequence m input)
     i waiting)
    procs)
   (cut-meta-imp-procs-consistent-p
    ids target-sid
    (cm-set-waiting-marker-for
     m i waiting)
    procs)))

;; Metadata consistency gives the current waiting set for an already-taken cut.
(local-defthm cut-meta-imp-procs-consistent-p-cut-taken-implies-waiting-equal
  (implies
   (and
    (cut-meta-imp-procs-consistent-p ids target-sid m procs)
    (memberp i ids)
    (not (cm-cut-not-taken-p m i)))
   (equal
    (cm-waiting-marker-for m i)
    (snapshot-waiting-marker-from
     (snapshot-entry target-sid (g i procs)))))
  :hints
  (("Goal"
    :induct
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs))))

;; Removing the same sender from equal waiting sets preserves equality.
(local-defthm remove1-equal-preserves-equal
  (implies
   (equal x y)
   (equal
    (remove1-equal a x)
    (remove1-equal a y))))

;; Recording an after-cut input does not change any waiting-marker row.
(local-defthm cm-waiting-marker-for-of-cm-add-after-cut-input-sequence
  (equal
   (cm-waiting-marker-for
    (cm-add-after-cut-input-sequence m input)
    i)
   (cm-waiting-marker-for m i)))

;; Receiving another TARGET-SID marker after I has already taken the cut
;; removes SENDER from the same waiting set in metadata and implementation.
(local-defthm cut-meta-imp-procs-consistent-p-of-non-first-target-marker
  (implies
   (and
    (cut-meta-imp-procs-consistent-p ids target-sid m procs)
    (true-listp ids)
    (uniquep ids)
    (memberp i ids)
    ;; I has already taken TARGET-SID.
    (not (cm-cut-not-taken-p m i))
    ;; Needed only for REMOVE-FROM-LIST = REMOVE1-EQUAL.
    (true-listp
     (snapshot-waiting-marker-from
      (snapshot-entry target-sid (g i procs))))
    (uniquep
     (snapshot-waiting-marker-from
      (snapshot-entry target-sid (g i procs)))))
   (cut-meta-imp-procs-consistent-p
    ids target-sid
    (cm-set-waiting-marker-for
     m i
     (remove1-equal
      sender
      (snapshot-waiting-marker-from
       (snapshot-entry target-sid (g i procs)))))
    (s i
       (s :snapshots
          (s target-sid
             (s :status
                (snapshot-status
                 (snapshot-entry target-sid (g i procs)))
                (s :waiting-marker-from
                   (remove-from-list
                    (snapshot-waiting-marker-from
                     (snapshot-entry target-sid (g i procs)))
                    sender)
                   (snapshot-entry target-sid (g i procs))))
             (snapshots (g i procs)))
          (g i procs))
       procs)))
  :hints
  (("Goal"
    :in-theory (disable REMOVE1-EQUAL-PRESERVES-EQUAL)
    :induct
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs))
   ("Subgoal *1/2"
    :cases ((equal i (car ids))))))




;; A stored SID in GOOD-SNAPSHOTS-P has a good snapshot entry.
(local-defthm good-snapshots-p-implies-good-snapshot-entry-p
  (implies
   (and
    (good-snapshots-p snapshot-ids p nbrs ids)
    (memberp sid snapshot-ids))
   (good-snapshot-entry-p
    (snapshot-entry sid p)
    nbrs)))

;; GOOD-STATE-P gives a good stored snapshot entry for any process/SID.
(local-defthm good-state-p-implies-good-snapshot-entry-p
  (implies
   (and
    (good-state-p st)
    (memberp i (proc-ids st))
    (memberp sid
             (snapshot-ids
              (g i (procs st)))))
   (good-snapshot-entry-p
    (snapshot-entry
     sid
     (g i (procs st)))
    (nbrs-from
     (g i (procs st)))))
  :hints
  (("Goal"
    :use
    ((:instance
      good-proc-p-of-g-when-good-procs-p
      (ids (proc-ids st))
      (procs (procs st))
      (all-ids (proc-ids st)))
     (:instance
      good-snapshots-p-implies-good-snapshot-entry-p
      (snapshot-ids
       (snapshot-ids (g i (procs st))))
      (p (g i (procs st)))
      (nbrs
       (nbrs-from (g i (procs st))))
      (ids (proc-ids st))
      (sid sid))))))


;; GOOD-SNAPSHOT-ENTRY-P directly supplies TRUE-LISTP.
(defthm good-state-p-implies-true-listp-snapshot-waiting-marker-from
  (implies
   (and
    (good-state-p st)

    (memberp
     i
     (proc-ids st))

    (memberp
     sid
     (snapshot-ids
      (g i (procs st)))))

   (true-listp
    (snapshot-waiting-marker-from
     (snapshot-entry
      sid
      (g i (procs st))))))

  :hints
  (("Goal"
    :do-not-induct t

    :use
    (good-state-p-implies-good-snapshot-entry-p)

    :in-theory
    (disable
      ;; Keep the large state invariant opaque.
      good-state-p

      ;; Prevent the explicitly used formula from rewriting itself to T.
      good-state-p-implies-good-snapshot-entry-p))))


;; GOOD-SNAPSHOT-ENTRY-P also directly supplies UNIQUEP.
(defthm good-state-p-implies-uniquep-snapshot-waiting-marker-from
  (implies
   (and
    (good-state-p st)

    (memberp
     i
     (proc-ids st))

    (memberp
     sid
     (snapshot-ids
      (g i (procs st)))))

   (uniquep
    (snapshot-waiting-marker-from
     (snapshot-entry
      sid
      (g i (procs st))))))

  :hints
  (("Goal"
    :do-not-induct t

    :use
    (good-state-p-implies-good-snapshot-entry-p)

    :in-theory
    (disable
      ;; Keep the large state invariant opaque.
      good-state-p

      ;; Prevent the explicitly used formula from rewriting itself to T.
      good-state-p-implies-good-snapshot-entry-p))))




;; GOOD-STATE-P supplies:


;; Generalized GOOD-STATE version:
(local-defthm
  cut-meta-imp-procs-consistent-p-of-non-first-target-marker-good-state-gen

  (implies
   (and
    (good-state-p st)

    (equal ids
           (proc-ids st))

    (equal procs
           (procs st))

    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (memberp i ids)

    ;; I has already taken TARGET-SID.
    (not
     (cm-cut-not-taken-p m i)))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    (cm-set-waiting-marker-for
     m
     i
     (remove1-equal
      sender
      (snapshot-waiting-marker-from
       (snapshot-entry
        target-sid
        (g i procs)))))

    (s i
       (s :snapshots
          (s target-sid
             (s :status
                (snapshot-status
                 (snapshot-entry
                  target-sid
                  (g i procs)))

                (s :waiting-marker-from
                   (remove1-equal
                    sender
                    (snapshot-waiting-marker-from
                     (snapshot-entry
                      target-sid
                      (g i procs))))

                   (snapshot-entry
                    target-sid
                    (g i procs))))

             (snapshots
              (g i procs)))

          (g i procs))

       procs)))

  :hints
  (("Goal"
    :do-not-induct t

    ;; Variables align directly; no explicit instance is needed.
    :use
    (cut-meta-imp-procs-consistent-p-of-non-first-target-marker)

    :in-theory
    (disable
      ;; Do not let the explicitly used theorem rewrite itself away.
      cut-meta-imp-procs-consistent-p-of-non-first-target-marker

      ;; Keep large predicates and updates opaque.
      cut-meta-imp-procs-consistent-p
      good-state-p
      good-procs-p
      good-snapshots-p
      good-snapshot-entry-p
      cm-cut-not-taken-p
      cm-set-waiting-marker-for
      remove-from-list))))


(local-defthm
  cm-cut-not-taken-p-of-non-first-target-meta-update

  (equal
   (cm-cut-not-taken-p
    (cm-set-waiting-marker-for
     (cm-add-after-cut-input-sequence m input)
     waiting-pid
     waiting-for)
    queried-pid)

   (cm-cut-not-taken-p
    m
    queried-pid))
  )


;; Changing the status of TARGET-SID does not affect process/cut consistency, provided the snapshot membership and waiting row remain unchanged.


;; Stop the old nonterminating rewrite rule.

;; Remove a :STATUS update completely.  The right-hand side is
;; structurally smaller and therefore cannot recreate the same redex.
(local-defthm
  cut-meta-imp-procs-consistent-p-removes-target-snapshot-status

  (equal
   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    meta

    (s i
       (s :snapshots
          (s target-sid
             (s :status
                new-status
                entry)
             (snapshots (g i procs)))
          (g i procs))
       procs))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid
    meta

    (s i
       (s :snapshots
          (s target-sid
             entry
             (snapshots (g i procs)))
          (g i procs))
       procs)))

  :hints
  (("Goal"
    :induct (len ids))

   ("Subgoal *1/1"
    :cases
    ((equal i (car ids))))))


;; Normalized GOOD-STATE theorem.  The target entry contains only
;; the updated waiting row; its status is irrelevant.
(local-defthm
  cut-meta-imp-procs-consistent-p-of-non-first-target-marker-good-state-normalized

  (implies
   (and
    (good-state-p st)

    (equal ids
           (proc-ids st))

    (equal procs
           (procs st))

    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (memberp i ids)

    (not
     (cm-cut-not-taken-p m i)))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    (cm-set-waiting-marker-for
     m
     i
     (remove1-equal
      sender
      (snapshot-waiting-marker-from
       (snapshot-entry
        target-sid
        (g i procs)))))

    (s i
       (s :snapshots
          (s target-sid

             ;; No redundant :STATUS update.
             (s :waiting-marker-from
                (remove1-equal
                 sender
                 (snapshot-waiting-marker-from
                  (snapshot-entry
                   target-sid
                   (g i procs))))

                (snapshot-entry
                 target-sid
                 (g i procs)))

             (snapshots
              (g i procs)))

          (g i procs))

       procs)))

  :hints
  (("Goal"
    :do-not-induct t

    :use
    (cut-meta-imp-procs-consistent-p-of-non-first-target-marker-good-state-gen)

    :in-theory
    (disable
      ;; Do not rewrite the explicitly used theorem away.
      cut-meta-imp-procs-consistent-p-of-non-first-target-marker-good-state-gen


      cut-meta-imp-procs-consistent-p
      good-state-p
      cm-set-waiting-marker-for))))




;; Updating one process's recovery-control fields preserves the
;; counter of every queried process, including the updated process.
(local-defthm
  counter-of-g-of-recovery-control-update

  (equal
   (counter
    (g queried-pid
       (s updated-pid

          (s :local-state
             new-local-state

             (s :proc-status
                new-proc-status

                (s :waiting-recovery-from
                   new-waiting-recovery-from

                   (g updated-pid procs))))

          procs)))

   (counter
    (g queried-pid procs)))

  :hints
  (("Goal"
    :cases
    ((equal queried-pid updated-pid)))))


;; Replacing UPDATED-PID by NEW-P preserves every process counter
;; whenever NEW-P preserves the updated process's own counter.
(defthm
  counter-of-g-of-proc-update-when-counter-unchanged

  (implies
   (equal
    (counter new-p)

    (counter
     (g updated-pid procs)))

   (equal
    (counter
     (g queried-pid
        (s updated-pid
           new-p
           procs)))

    (counter
     (g queried-pid procs))))

  :hints
  (("Goal"
    :cases
    ((equal queried-pid updated-pid)))))



;; Recording an input in the before-cut sequence preserves the
;; complete CUT-NOT-TAKEN list.
(local-defthm cm-cut-not-taken-of-cm-add-before-cut-input-sequence
  (equal
   (cm-cut-not-taken
    (cm-add-before-cut-input-sequence m input))

   (cm-cut-not-taken m)))

;; Recording an input in the after-cut sequence preserves the
;; complete CUT-NOT-TAKEN list.
(local-defthm cm-cut-not-taken-of-cm-add-after-cut-input-sequence
  (equal
   (cm-cut-not-taken
    (cm-add-after-cut-input-sequence m input))

   (cm-cut-not-taken m)))






;; Functional theorem with a clean induction only over IDS.
(local-defthm
  cl-cut-meta-imp-procs-consistent-p-of-target-start-checkpoint

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (true-listp
     (cm-cut-not-taken m))

    (uniquep
     (cm-cut-not-taken m))

    (cm-cut-not-taken-p m i)

    (equal
     target-sid
     (list i
           (counter (g i procs)))))

   (cut-meta-imp-procs-consistent-p
    ids
    target-sid

    (cm-set-waiting-marker-for
     (cm-remove-cut-not-taken m i)
     i
     (nbrs-from (g i procs)))

    (start-checkpoint-helper
     procs
     i)))

  :hints
  (("Goal"
    :induct (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    :in-theory
    (disable
      install-snapshot-entry
      add-snapshot-id))

   ("Subgoal *1/2"
    :cases
    ((equal i (car ids))))))



;; START-CHECKPOINT-HELPER increments the selected process's counter
;; and leaves every other process's counter unchanged.
(local-defthm counter-of-start-checkpoint-helper
  (equal
   (counter
    (g j
       (start-checkpoint-helper procs i)))

   (if (equal j i)
       (+ 1
          (counter
           (g i procs)))
     (counter
      (g j procs))))

  :hints
  (("Goal"
    :cases
    ((equal j i))

    :in-theory
     ;; These do not need to be opened to establish the counter field.
    (disable
     install-snapshot-entry
      add-snapshot-id))))


;; Specialized SID form needed by Subgoal 28.2.3:
(local-defthm target-sid-counter-less-after-start-checkpoint-helper
  (implies
   (equal
    (list
     i
     (counter
      (g i procs)))
    target-sid)

   (<
    (cadr target-sid)

    (counter
     (g (car target-sid)
        (start-checkpoint-helper
         procs i))))))



;; A start-checkpoint metadata update removes I from CUT-NOT-TAKEN.
(local-defthm
  cm-cut-not-taken-p-false-after-start-checkpoint-meta-update

  (implies
   (good-cut-meta-p m)

   (not
    (cm-cut-not-taken-p

     (cm-set-waiting-marker-for

      (cm-remove-cut-not-taken

       (cm-add-before-cut-input-sequence
        m input)

       i)

      i
      waiting)

     i))))


(local-defthm true-listp-len-2-with-known-first
  (implies
   (and
    (true-listp sid)

    (equal
     (len sid)
     2)

    (equal
     (car sid)
     i))

   (equal
    (list i
          (cadr sid))
    sid)))


(local-defthm good-cut-meta-p-implies-len-sid-equal-2
  (implies
   (good-cut-meta-p m)

   (equal
    (len (cm-sid m))
    2)))

(local-defthm good-cut-meta-p-implies-true-listp-sid
  (implies
   (good-cut-meta-p m)

   (true-listp
    (cm-sid m))))



;; ------------------------------------------------------------
;; If every IDS process is still in CUT-NOT-TAKEN, then no
;; process in IDS can already store TARGET-SID.
;; ------------------------------------------------------------

(local-defthm
  cut-meta-consistency-all-cut-not-taken-implies-no-snapshot-holder

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (subset
     ids
     (cm-cut-not-taken m)))

   (not
    (some-proc-has-snapshot-id-p
     target-sid ids procs)))

  :hints
  (("Goal"
    :induct
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs))))


;; ------------------------------------------------------------
;; A marker at the head of a well-formed channel must have an SID stored by some process.
;; ------------------------------------------------------------

(local-defthm
  marker-head-sid-cannot-equal-unstarted-target-sid

  (implies
   (and
    ;; The target cut has not started anywhere.
    (equal
     (cm-cut-not-taken m)
     (proc-ids st))

    (cut-meta-imp-procs-consistent-p
     (proc-ids st)
     (sid m)
     m
     (procs st))

    ;; The channel and its marker are well formed.
    (good-state-p st)

    (memberp i
             (proc-ids st))

    (memberp j
             (proc-ids st))

    (memberp j
             (nbrs-from
              (g i (procs st))))

    (equal
     (msg-type
      (get-msg-from-channel
       j i (channels st)))
     :marker))

   (not
    (equal
     (sid
      (get-msg-from-channel
       j i (channels st)))
     (sid m))))

  :hints
  (("Goal"
    :use
    (good-state-p-implies-marker-head-sid-known-somewhere)

    :in-theory
    (disable
     good-state-p
     get-msg-from-channel
     some-proc-has-snapshot-id-p))))


(defthm cut-meta-imp-consistent-p-preserved-by-step
  (implies
   (and
    (cut-meta-imp-consistent-p m st)
    (good-state-p st)
    (good-cut-meta-p m)
    (legal-inputp st input))

   (cut-meta-imp-consistent-p
    (process-cut-step input st m)
    (system-step st input)))
  :hints
  (("Goal"
    :in-theory
    (disable step-normal
	     start-checkpoint-helper
	     cm-cut-not-taken-p
	     get-msg-from-channel
	     update-proc-for-first-marker-msg
	     update-proc-for-normal-msg-core
	          cm-cut-not-taken
		  good-state-p
		  good-cut-meta-p
		  get-msg-from-channel
		  remove-message-from-channel
		  legal-input-sequencep
		 ; current-msg-for-receive
		 ; legal-inputp
		  cm-cut-not-taken-p
		  cm-remove-cut-not-taken
		  cm-waiting-marker-for
		  cm-set-waiting-marker-for
		  cm-remove-cut-not-taken
		  cm-add-after-cut-input-sequence
		  cm-add-before-cut-input-sequence
		  cm-after-cut-input-sequence
		  cm-before-cut-input-sequence
		  cm-waiting-marker-from
		  ))))





(defun marker-for-sid-in-channel-p (target-sid channel)
  (declare
   (xargs :measure (acl2-count channel)))

  (if (endp channel)
      nil

    (or
     (and
      (equal
       (msg-type (first channel))
       :marker)

      (equal
       (sid (first channel))
       target-sid))

     (marker-for-sid-in-channel-p
      target-sid
      (rest channel)))))


(defun cut-marker-in-transit-for-outgoing-nbrs-p
    (src outgoing-nbrs target-sid m channels)

  (declare
   (xargs :measure (acl2-count outgoing-nbrs)))

  ;; If SRC has not taken its cut yet, it has not sent the target checkpoint marker, so there is no in-transit marker obligation from SRC.
  (if (cm-cut-not-taken-p m src)
      t

    ;; SRC has taken its cut.
    (if (endp outgoing-nbrs)
        t

      (let ((out-nbr (first outgoing-nbrs)))

        (and
         ;; If OUT-NBR has not taken its cut yet, then the target checkpoint marker sent by SRC must still be in transit on channel SRC -> OUT-NBR.
         (if (cm-cut-not-taken-p m out-nbr)

             (marker-for-sid-in-channel-p
              target-sid
              (channel-state
               src
               out-nbr
               channels))

           ;; OUT-NBR has already taken its cut, so there is
           ;; no longer an in-transit obligation.
           t)

         (cut-marker-in-transit-for-outgoing-nbrs-p
          src
          (rest outgoing-nbrs)
          target-sid
          m
          channels))))))


(defun cut-markers-in-transit-for-srcs-p
    (srcs target-sid m procs channels)

  (declare
   (xargs :measure (acl2-count srcs)))

  (if (endp srcs)
      t

    (let ((src (first srcs)))

      (and
       ;; Check every outgoing channel of SRC.
       (cut-marker-in-transit-for-outgoing-nbrs-p
        src
        (nbrs-to
         (g src procs))
        target-sid
        m
        channels)

       ;; Check the remaining source processes.
       (cut-markers-in-transit-for-srcs-p
        (rest srcs)
        target-sid
        m
        procs
        channels)))))


(defun cut-markers-in-transit-p (m st)
  ;; Global invariant:
  (cut-markers-in-transit-for-srcs-p
   (proc-ids st)
   (cm-sid m)
   m
   (procs st)
   (channels st)))

;; ------------------------------------------------------------
;; Base case for the invariant.
;; ------------------------------------------------------------



(local-defthm
  cut-markers-in-transit-for-srcs-p-when-all-cut-not-taken

  (implies
   (subset
    srcs
    (cm-cut-not-taken m))

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)))

;; ------------------------------------------------------------
;; Initial marker-in-transit invariant.
;; ------------------------------------------------------------



(defthm cut-markers-in-transit-p-of-make-cut-meta
  (cut-markers-in-transit-p
   (make-cut-meta
    target-sid
    initiator
    st)
   st))






(local-defthm cut-marker-in-transit-for-outgoing-nbrs-p-of-before-cut-input-sequence-update
  (equal
   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    (s :before-cut-input-sequence val m)
    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    channels)))


(local-defthm cut-markers-in-transit-for-srcs-p-of-before-cut-input-sequence-update
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    (s :before-cut-input-sequence val m)
    procs
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)))


(local-defthm cut-marker-in-transit-for-outgoing-nbrs-p-of-after-cut-input-sequence-update
  (equal
   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    (s :after-cut-input-sequence val m)
    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    channels)))


(local-defthm cut-markers-in-transit-for-srcs-p-of-after-cut-input-sequence-update
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    (s :after-cut-input-sequence val m)
    procs
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)))


;; (defthm
;;   cut-marker-in-transit-for-outgoing-nbrs-p-of-inputs-before-cut-update

;; (equal

;; (cut-marker-in-transit-for-outgoing-nbrs-p


;; (defthm
;;   cut-markers-in-transit-for-srcs-p-of-inputs-before-cut-update

;; (equal

;; (cut-markers-in-transit-for-srcs-p


(local-defthm cut-markers-in-transit-for-srcs-p-of-local-state-update
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (s i
       (s :local-state val
          (g i procs))
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)))



(local-defthm marker-for-sid-in-channel-p-of-snoc
  (implies
   (marker-for-sid-in-channel-p
    target-sid
    channel)

   (marker-for-sid-in-channel-p
    target-sid
    (snoc channel msg))))

;; ------------------------------------------------------------
;; Ordinary sends cannot destroy an existing target marker.
;; ------------------------------------------------------------



(local-defthm marker-for-sid-in-channel-p-preserved-by-send-compute-message
  (implies
   (marker-for-sid-in-channel-p
    target-sid
    (channel-state src dst channels))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src
     dst
     (send-compute-message
      local-state
      i
      nbrs
      channels)))))


(local-defthm cut-marker-in-transit-for-outgoing-nbrs-p-preserved-by-send-compute-message
  (implies
   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    (send-compute-message
     local-state
     i
     nbrs
     channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src
     outgoing-nbrs
     target-sid
     m
     channels))))

;; ------------------------------------------------------------
;; Lift ordinary-send preservation to the global source list.
;; ------------------------------------------------------------



(local-defthm cut-markers-in-transit-for-srcs-p-preserved-by-send-compute-message
  (implies
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    (send-compute-message
     local-state
     i
     nbrs
     channels)))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels))))

;; ------------------------------------------------------------
;; START-CHECKPOINT-HELPER is invisible to this invariant.
;; ------------------------------------------------------------


(local-defthm cut-markers-in-transit-for-srcs-p-of-start-checkpoint-helper
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (start-checkpoint-helper procs i)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)

    :in-theory
    (disable start-checkpoint-helper))))

(local-defthm marker-for-sid-in-channel-p-preserved-by-send-msg-all-outgoing
  (implies
   (marker-for-sid-in-channel-p
    target-sid
    (channel-state src dst channels))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src
     dst
     (send-msg-all-outgoing-channels
      msg
      i
      nbrs
      channels))))

  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels
     msg i nbrs channels))))

(local-defthm cut-marker-in-transit-for-outgoing-nbrs-p-preserved-by-send-msg-all-outgoing
  (implies
   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    (send-msg-all-outgoing-channels
     msg
     i
     nbrs
     channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src outgoing-nbrs target-sid m channels))))

;; ------------------------------------------------------------
;; Broadcasting a message preserves all already-existing target marker obligations.
;; ------------------------------------------------------------



(local-defthm cut-markers-in-transit-for-srcs-p-preserved-by-send-msg-all-outgoing
  (implies
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    (send-msg-all-outgoing-channels
     msg
     i
     nbrs
     channels)))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs target-sid m procs channels))))


(local-defthm cut-markers-in-transit-for-srcs-p-of-proc-status-update
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (s i
       (s :proc-status val
          (g i procs))
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels)))

;; ------------------------------------------------------------
;; Normal-message process updates are invisible to the invariant.
;; ------------------------------------------------------------



(local-defthm cut-markers-in-transit-for-srcs-p-of-update-proc-for-normal-msg-core
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (s i
       (update-proc-for-normal-msg-core
        (g i procs)
        j
        msg)
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)
    :in-theory
    (disable update-proc-for-normal-msg-core))))


;; (defthm
;;   cut-marker-in-transit-for-outgoing-nbrs-p-of-inputs-after-cut-update

;; (equal

;; (cut-marker-in-transit-for-outgoing-nbrs-p

;;   :hints
;;   (("Goal"
;;     :induct
;;     (cut-marker-in-transit-for-outgoing-nbrs-p
;;      src
;;      outgoing-nbrs
;;      target-sid
;;      m
;;      channels))))


;; (defthm cut-markers-in-transit-for-srcs-p-of-cm-after-cut-append
;;   (equal
;;    (cut-markers-in-transit-for-srcs-p
;;     srcs target-sid
;;     (cm-after-cut-append m i j input)
;;     procs channels)

;; (cut-markers-in-transit-for-srcs-p

;; (defthm
;;   cut-marker-in-transit-for-outgoing-nbrs-p-of-after-cut-msgs-update

;; (equal

;; (cut-marker-in-transit-for-outgoing-nbrs-p

;;   :hints
;;   (("Goal"
;;     :induct
;;     (cut-marker-in-transit-for-outgoing-nbrs-p
;;      src
;;      outgoing-nbrs
;;      target-sid
;;      m
;;      channels))))


;; (defthm cut-markers-in-transit-for-srcs-p-of-cm-after-cut-msg-append
;;   (equal
;;    (cut-markers-in-transit-for-srcs-p
;;     srcs target-sid
;;     (cm-after-cut-msg-append m i j msg)
;;     procs channels)

;; (cut-markers-in-transit-for-srcs-p

;; (defthm sid-of-cm-after-cut-append
;;   (equal
;;    (g :sid
;;       (cm-after-cut-append m i j input))
;;    (g :sid m)))

;; (defthm sid-of-cm-after-cut-msg-append
;;   (equal
;;    (g :sid
;;       (cm-after-cut-msg-append m i j msg))
;;    (g :sid m)))


;; (defthm cut-not-taken-of-cm-after-cut-append
;;   (equal
;;    (g :cut-not-taken
;;       (cm-after-cut-append m i j input))
;;    (g :cut-not-taken m)))


;; (defthm cut-not-taken-of-cm-after-cut-msg-append
;;   (equal
;;    (g :cut-not-taken
;;       (cm-after-cut-msg-append m i j msg))
;;    (g :cut-not-taken m)))




(local-defthm
  marker-for-sid-in-channel-p-preserved-by-remove-normal-message

  (implies
   (and

    (equal
     (msg-type
      (get-msg-from-channel j i channels))
     :normal)

    (marker-for-sid-in-channel-p
     target-sid
     (channel-state src dst channels)))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src
     dst
     (remove-message-from-channel
      j i channels))))

  :hints
  (("Goal"
    :cases
    ((equal src j)
     (equal dst i))
    :in-theory
    (disable 
             remove-message-from-channel))))


(local-defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-preserved-by-remove-normal-message

  (implies
   (and
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src
     outgoing-nbrs
     target-sid
     m
     channels)

    ;; (consp
    ;;  (channel-state j i channels))

    (equal
     (msg-type
      (get-msg-from-channel j i channels))
     :normal))

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src
     outgoing-nbrs
     target-sid
     m
     channels))))



(local-defthm
  cut-markers-in-transit-for-srcs-p-preserved-by-remove-normal-message

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)

    (equal
     (msg-type
      (get-msg-from-channel j i channels))
     :normal))

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :in-theory (disable remove-message-from-channel)
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels))))

;; ------------------------------------------------------------
;; Metadata/implementation consistency: cut already taken.
;; ------------------------------------------------------------



(local-defthm
  cut-meta-imp-procs-consistent-p-cut-taken-implies-has-snapshot

  (implies
   (and
    (cut-meta-imp-procs-consistent-p
     ids target-sid m procs)

    (memberp i ids)

    (not
     (cm-cut-not-taken-p m i)))

   (memberp
    target-sid
    (snapshot-ids (g i procs)))))


(local-defthm marker-for-sid-in-channel-p-of-cdr-when-head-not-marker
  (implies
   (and
    (consp channel)

    (not
     (equal (msg-type (car channel))
            :marker))

    (marker-for-sid-in-channel-p
     target-sid
     channel))

   (marker-for-sid-in-channel-p
    target-sid
    (cdr channel))))

;; ------------------------------------------------------------
;; Removing a non-marker head preserves a target marker.
;; ------------------------------------------------------------


(local-defthm
  marker-for-sid-in-channel-p-preserved-by-remove-non-marker-message

  (implies
   (and
    (consp
     (channel-state j i channels))

    (not
     (equal
      (msg-type
       (get-msg-from-channel j i channels))
      :marker))

    (marker-for-sid-in-channel-p
     target-sid
     (channel-state src dst channels)))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src
     dst
     (remove-message-from-channel
      j i channels)))))

(local-defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-preserved-by-remove-non-marker-message

  (implies
   (and
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src outgoing-nbrs target-sid m channels)

    (consp
     (channel-state j i channels))

    (not
     (equal
      (msg-type
       (get-msg-from-channel j i channels))
      :marker)))

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src
    outgoing-nbrs
    target-sid
    m
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src outgoing-nbrs target-sid m channels))))


(local-defthm
  cut-markers-in-transit-for-srcs-p-of-first-recovery-proc-update

  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (s i
       (update-proc-for-first-recovery-msg
        (g i procs)
        sid
        j)
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs target-sid m procs channels)
    :in-theory
    (disable update-proc-for-first-recovery-msg))))


(local-defthm get-msg-recovery-implies-not-marker
  (implies
   (equal
    (msg-type
     (get-msg-from-channel j i channels))
    :recovery)
   (not
    (equal
     (msg-type
      (get-msg-from-channel j i channels))
     :marker))))

(defthm recovery-msg-implies-channel-consp
  (implies
   (equal
    (msg-type
     (get-msg-from-channel j i channels))
    :recovery)

   (consp
    (channel-state j i channels))))

;; ------------------------------------------------------------
;; Global lift of non-marker removal preservation.
;; ------------------------------------------------------------




  (local-defthm
  cut-markers-in-transit-for-srcs-p-preserved-by-remove-non-marker-message

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)

    (consp
     (channel-state j i channels))

    (not
     (equal
      (msg-type
       (get-msg-from-channel j i channels))
      :marker)))

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)

    :in-theory
    (disable remove-message-from-channel
             get-msg-from-channel))))
  


  (local-defthm
  cut-markers-in-transit-for-srcs-p-of-non-first-recovery-proc-update

  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (s i
       (update-proc-for-non-first-recovery-msg
        (g i procs)
        j)
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)

    :in-theory
    (disable
     update-proc-for-non-first-recovery-msg))))


(local-defthm
  cut-markers-in-transit-for-srcs-p-of-first-marker-proc-update

  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    (s i
       (update-proc-for-first-marker-msg
        (g i procs)
        sid
        j)
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    srcs
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     srcs target-sid m procs channels)
    :in-theory
    (disable update-proc-for-first-marker-msg))))


(local-defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-of-waiting-marker-from-update
  (equal
   (cut-marker-in-transit-for-outgoing-nbrs-p
    src outgoing-nbrs target-sid
    (s :waiting-marker-from val m)
    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    src outgoing-nbrs target-sid
    m
    channels)))

(local-defthm
  cut-markers-in-transit-for-srcs-p-of-waiting-marker-from-update
  (equal
   (cut-markers-in-transit-for-srcs-p
    srcs target-sid
    (s :waiting-marker-from val m)
    procs channels)

   (cut-markers-in-transit-for-srcs-p
    srcs target-sid
    m
    procs channels)))




;; ------------------------------------------------------------
;; I takes its cut by receiving a marker from J.
;; ------------------------------------------------------------

;; ------------------------------------------------------------
;; Preserve obligations of an OLD source when I takes the cut.
;; ------------------------------------------------------------


(local-defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-preserved-when-i-takes-cut

  (implies
   (and
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p
     nbrs
     target-sid
     m
     channels)

    ;; I has not taken the cut yet.
    (memberp i
             (cm-cut-not-taken m))

    ;; Removing I once really removes it.
    (uniquep
     (cm-cut-not-taken m))

    ;; P is not the process taking the cut now.
    (not (equal p i)))

   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    nbrs
    target-sid

    ;; I takes the cut.
    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))
       m)

    ;; I consumed the message received from J.
    (remove-message-from-channel
     j
     i
     channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p nbrs target-sid m channels)

    :in-theory
    (disable remove-message-from-channel))))



;; ------------------------------------------------------------
;; Source-level preservation when I takes its cut.
;; ------------------------------------------------------------

;; ------------------------------------------------------------
;; Source-list lift for the "I takes the cut" transition.
;; ------------------------------------------------------------


(local-defthm
  cut-markers-in-transit-for-srcs-p-preserved-when-i-takes-cut

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     m
     procs
     channels)

    ;; I has not taken the cut before this step.
    (memberp i
             (cm-cut-not-taken m))

    (uniquep
     (cm-cut-not-taken m))

    ;; PIDS contains only the processes other than I.
    (not (memberp i pids)))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    ;; I now takes the cut.
    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))
       m)

    procs

    ;; I consumes the message received from J.
    (remove-message-from-channel
     j
     i
     channels)))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     m
     procs
     channels)

    :in-theory
    (disable remove-message-from-channel
	     cm-cut-not-taken))))






(local-defthm marker-for-sid-in-channel-p-of-snoc-marker
  (implies
   (equal (msg-type msg) :marker)

   (marker-for-sid-in-channel-p
    (sid msg)
    (snoc channel msg))))

;; ------------------------------------------------------------
;; Marker broadcast CREATES the required marker.
;; ------------------------------------------------------------




(local-defthm
  target-marker-present-after-send-to-all-outgoing-nbrs

  (implies
   (and
    (memberp out-nbr outgoing-nbrs)

    (equal (msg-type msg)
           :marker)

    (equal (sid msg)
           target-sid))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     i
     out-nbr
     (send-msg-all-outgoing-channels
      msg
      i
      outgoing-nbrs
      channels))))

  :hints
  (("Goal"
    :induct
    (send-msg-all-outgoing-channels
     msg i outgoing-nbrs channels))))




;; ------------------------------------------------------------
;; I has just taken the cut.
;; ------------------------------------------------------------

;; ------------------------------------------------------------
;; Establish I's NEW outgoing obligations when I takes the cut.
;; ------------------------------------------------------------


(local-defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-when-i-takes-cut

  (implies
   (and
    ;; I has not taken the cut before this step.
    (memberp i
             (cm-cut-not-taken m))

    ;; Removing I once makes I definitely cut.
    (uniquep
     (cm-cut-not-taken m))

    ;; The message being broadcast is the target marker.
    (equal (msg-type msg)
           :marker)

    (equal (sid msg)
           target-sid))

   (cut-marker-in-transit-for-outgoing-nbrs-p
    i
    outgoing-nbrs
    target-sid

    ;; I now takes the cut.
    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))
       m)

    ;; I broadcasts the target marker.
    (send-msg-all-outgoing-channels
     msg
     i
     outgoing-nbrs
     channels))))



(local-defthm
  cut-markers-in-transit-for-srcs-p-from-i-and-rest

  (implies
   (and
    (uniquep pids)

    (memberp i pids)

    ;; I's own outgoing obligations.
    (cut-marker-in-transit-for-outgoing-nbrs-p
     i
     (nbrs-to (g i procs))
     target-sid
     m
     channels)

    ;; Obligations for every other process.
    (cut-markers-in-transit-for-srcs-p
     (remove1-equal i pids)
     target-sid
     m
     procs
     channels))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    procs
    channels)))


;; Removing one PID from the list of source processes cannot create any new marker obligation.

(local-defthm
  cut-markers-in-transit-for-srcs-p-of-remove1-equal

  (implies
   (cut-markers-in-transit-for-srcs-p
    pids target-sid m procs channels)

   (cut-markers-in-transit-for-srcs-p
    (remove1-equal i pids)
    target-sid
    m
    procs
    channels)))


;; If:

(local-defthm
  cut-markers-in-transit-for-srcs-p-from-i-and-other-pids

  (implies
   (and
    (uniquep pids)

    (memberp i pids)

    ;; I itself.
    (cut-marker-in-transit-for-outgoing-nbrs-p
     i
     (nbrs-to (g i procs))
     target-sid
     m
     channels)

    ;; Every process other than I.
    (cut-markers-in-transit-for-srcs-p
     (remove1-equal i pids)
     target-sid
     m
     procs
     channels))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    procs
    channels)))

;; ------------------------------------------------------------
;; Complete first-target-marker transition.
;; ------------------------------------------------------------



(local-defthm
  cut-markers-in-transit-for-srcs-p-after-i-takes-cut-and-sends-marker

  (implies
   (and
    ;; Old invariant.
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     m
     procs
     channels)

    ;; I has not taken the cut before this step.
    (memberp i
             (cm-cut-not-taken m))

    (uniquep
     (cm-cut-not-taken m))

    (uniquep pids)

    ;; The broadcast message is the target marker.
    (equal (msg-type msg) :marker)

    (equal (sid msg) target-sid))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    ;; I takes the cut.
    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))
       m)

    procs

    ;; First consume J -> I, then I broadcasts the marker.
    (send-msg-all-outgoing-channels
     msg
     i
     (nbrs-to (g i procs))
     (remove-message-from-channel
      j i channels))))

  :hints
  (("Goal"
    :in-theory (disable remove-message-from-channel
			cm-cut-not-taken)
    :cases ((memberp i pids)))))


(local-defthm cm-cut-not-taken-of-cut-not-taken-update
  (equal
   (cm-cut-not-taken
    (s :cut-not-taken val m))
   val))



(local-defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-of-cut-update-over-waiting-and-after-cut

  (equal
   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    outgoing-nbrs
    target-sid

    (s :cut-not-taken
       cut-not-taken
       (s :waiting-marker-from
          waiting
          (s :after-cut-input-sequence
             after-cut
             m)))

    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    outgoing-nbrs
    target-sid

    (s :cut-not-taken
       cut-not-taken
       m)

    channels))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p
     outgoing-nbrs
     target-sid
     (s :cut-not-taken cut-not-taken m)
     channels))))



(local-defthm
  cut-markers-in-transit-for-srcs-p-of-cut-update-over-waiting-and-after-cut

  (equal
   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    (s :cut-not-taken
       cut-not-taken
       (s :waiting-marker-from
          waiting
          (s :after-cut-input-sequence
             after-cut
             m)))

    procs
    channels)

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    (s :cut-not-taken
       cut-not-taken
       m)

    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     (s :cut-not-taken cut-not-taken m)
     procs
     channels))))

(local-defthm cm-cut-not-taken-of-waiting-marker-from-update
  (equal
   (cm-cut-not-taken
    (s :waiting-marker-from val m))
   (cm-cut-not-taken m)))



;; ------------------------------------------------------------
;; I has already taken the cut.
;; ------------------------------------------------------------

;; ------------------------------------------------------------
;; Later target-marker receive.
;; ------------------------------------------------------------


(local-defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-preserved-by-remove-message-when-i-already-cut

  (implies
   (and
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p
     outgoing-nbrs
     target-sid
     m
     channels)

    (not
     (memberp i
              (cm-cut-not-taken m))))

   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    outgoing-nbrs
    target-sid
    m
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p outgoing-nbrs target-sid m channels)

    :in-theory
    (disable remove-message-from-channel))))

;; ------------------------------------------------------------
;; Global lift for a later marker received by an already-cut I.
;; ------------------------------------------------------------



(local-defthm
  cut-markers-in-transit-for-srcs-p-preserved-by-remove-message-when-i-already-cut

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     m
     procs
     channels)

    (not
     (memberp i
              (cm-cut-not-taken m))))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    procs
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids target-sid m procs channels)

    :in-theory
    (disable remove-message-from-channel))))

(local-defthm
  cut-markers-in-transit-for-srcs-p-of-snapshots-update

  (equal
   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    (s i
       (s :snapshots val
          (g i procs))
       procs)
    channels)

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids target-sid m procs channels))))

;; ------------------------------------------------------------
;; Removing a marker for a DIFFERENT checkpoint is safe.
;; ------------------------------------------------------------




(local-defthm
  marker-for-sid-in-channel-p-preserved-by-remove-non-target-marker

  (implies
   (and
    (consp
     (channel-state j i channels))

    ;; The consumed message is not the marker for TARGET-SID.
    (not
     (and
      (equal
       (msg-type
        (get-msg-from-channel j i channels))
       :marker)

      (equal
       (sid
        (get-msg-from-channel j i channels))
       target-sid)))

    (marker-for-sid-in-channel-p
     target-sid
     (channel-state p q channels)))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     p q
     (remove-message-from-channel
      j i channels))))

  :hints
  (("Goal"
    :cases
    ((equal p j)
     (equal q i))
    :in-theory
    (disable remove-message-from-channel))))


(local-defthm
  different-sid-marker-implies-not-target-marker

  (implies
   (and
    (equal
     (msg-type msg)
     :marker)

    (not
     (equal
      (sid msg)
      target-sid)))

   (not
    (and
     (equal
      (msg-type msg)
      :marker)

     (equal
      (sid msg)
      target-sid)))))

(local-defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-preserved-by-remove-non-target-marker

  (implies
   (and
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p outgoing-nbrs target-sid m channels)

    (consp
     (channel-state j i channels))

    (not
     (and
      (equal
       (msg-type
        (get-msg-from-channel j i channels))
       :marker)

      (equal
       (sid
        (get-msg-from-channel j i channels))
       target-sid))))

   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    outgoing-nbrs
    target-sid
    m
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p outgoing-nbrs target-sid m channels))))

;; ------------------------------------------------------------
;; Global preservation when a different-SID marker is consumed.
;; ------------------------------------------------------------



(local-defthm
  cut-markers-in-transit-for-srcs-p-preserved-by-remove-non-target-marker

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
     pids target-sid m procs channels)

    (consp
     (channel-state j i channels))

    (not
     (and
      (equal
       (msg-type
        (get-msg-from-channel j i channels))
       :marker)

      (equal
       (sid
        (get-msg-from-channel j i channels))
       target-sid))))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    procs
    (remove-message-from-channel
     j i channels)))

  :hints
  (("Goal"
    :in-theory (disable remove-message-from-channel
			get-msg-from-channel)
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids target-sid m procs channels))))


;; ------------------------------------------------------------
;; START-RECOVERY-HELPER changes recovery-related process fields, but it does not change any process's outgoing-neighbor list.
;; ------------------------------------------------------------

(local-defthm
  cut-markers-in-transit-for-srcs-p-of-start-recovery-helper

  (equal
   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    (start-recovery-helper procs i)
    channels)

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid
    m
    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     m
     procs
     channels)

    :in-theory
    (disable start-recovery-helper))))






;; ------------------------------------------------------------
;; I initiates the target checkpoint.
;; ------------------------------------------------------------

;; ------------------------------------------------------------
;; Initiator starts the target checkpoint.
;; ------------------------------------------------------------


(local-defthm
  cut-markers-in-transit-for-srcs-p-after-i-starts-checkpoint

  (implies
   (and
    (equal
     (cm-cut-not-taken m)
     pids)

    (uniquep pids)

    (memberp i pids)

    (equal (msg-type msg)
           :marker)

    (equal (sid msg)
           target-sid))

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    (s :cut-not-taken
       (remove1-equal
        i
        (cm-cut-not-taken m))
       m)

    procs

    (send-msg-all-outgoing-channels
     msg
     i
     (nbrs-to (g i procs))
     channels)))

  :hints
  (("Goal"
    :in-theory (disable cm-cut-not-taken)
    :cases ((memberp i pids)))))

(defthm cm-cut-not-taken-of-before-cut-input-sequence-update
  (equal
   (cm-cut-not-taken
    (s :before-cut-input-sequence val m))
   (cm-cut-not-taken m)))



(local-defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-of-cut-update-over-waiting-and-before-cut

  (equal
   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    outgoing-nbrs
    target-sid

    (s :cut-not-taken
       cut-not-taken
       (s :waiting-marker-from
          waiting
          (s :before-cut-input-sequence
             before-cut
             m)))

    channels)

   (cut-marker-in-transit-for-outgoing-nbrs-p
    p
    outgoing-nbrs
    target-sid

    (s :cut-not-taken
       cut-not-taken
       m)

    channels))

  :hints
  (("Goal"
    :induct
    (cut-marker-in-transit-for-outgoing-nbrs-p
     p
     outgoing-nbrs
     target-sid
     (s :cut-not-taken cut-not-taken m)
     channels))))


(local-defthm
  cut-markers-in-transit-for-srcs-p-of-cut-update-over-waiting-and-before-cut

  (equal
   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    (s :cut-not-taken
       cut-not-taken
       (s :waiting-marker-from
          waiting
          (s :before-cut-input-sequence
             before-cut
             m)))

    procs
    channels)

   (cut-markers-in-transit-for-srcs-p
    pids
    target-sid

    (s :cut-not-taken
       cut-not-taken
       m)

    procs
    channels))

  :hints
  (("Goal"
    :induct
    (cut-markers-in-transit-for-srcs-p
     pids
     target-sid
     (s :cut-not-taken cut-not-taken m)
     procs
     channels))))


(defthm cm-cut-not-taken-of-after-cut-input-sequence-update
  (equal
   (cm-cut-not-taken
    (s :after-cut-input-sequence val m))
   (cm-cut-not-taken m)))

;; ------------------------------------------------------------
;; MAIN ONE-STEP PRESERVATION THEOREM
;; ------------------------------------------------------------






(defthm cut-markers-in-transit-p-preserved-by-step
  (implies
   (and
    (cut-markers-in-transit-p
     m
     st)

    (cut-meta-imp-consistent-p
     m
     st)

    (good-state-p st)
    (good-cut-meta-p m)
    (legal-inputp
     st
     input))

   (cut-markers-in-transit-p
    (process-cut-step
     input
     st
     m)

    (system-step
     st
     input)))
  :hints (("Goal"
	   :in-theory (disable record-msg-in-snapshots
			       update-proc-for-first-marker-msg
			       
			      update-proc-for-first-recovery-msg
			      update-proc-for-non-first-recovery-msg
			      start-recovery-helper
			       start-checkpoint-helper
			       create-marker-message
			       create-recovery-message
			       remove-message-from-channel
			       get-msg-from-channel
			       update-proc-for-normal-msg-core
			       cm-cut-not-taken
			       true-listp
			       REMOVE1-EQUAL-PRESERVES-EQUAL
			     ;  cm-after-cut-append
					; cm-after-cut-msg-append
			       ))))





;; ------------------------------------------------------------
;; Marker-in-transit preservation over an entire input segment.
;; ------------------------------------------------------------






(local-defthm
  cut-marker-in-transit-for-outgoing-nbrs-p-implies-marker

  (implies
   (and
    (cut-marker-in-transit-for-outgoing-nbrs-p
     src
     outgoing-nbrs
     target-sid
     m
     channels)

    (memberp dst outgoing-nbrs)

    ;; SRC is post-cut.
    (not
     (cm-cut-not-taken-p m src))

    ;; DST is pre-cut.
    (cm-cut-not-taken-p m dst))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src
     dst
     channels)))
  :rule-classes
((:rewrite
  :match-free :all)))


(local-defthm
  cut-markers-in-transit-for-srcs-p-implies-marker

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)

    (memberp src srcs)

    (memberp
     dst
     (nbrs-to
      (g src procs)))

    (not
     (cm-cut-not-taken-p m src))

    (cm-cut-not-taken-p m dst))

   (marker-for-sid-in-channel-p
    target-sid
    (channel-state
     src
     dst
     channels)))
    :rule-classes
((:rewrite
  :match-free :all)))


;; ------------------------------------------------------------
;; Global marker consequence of CUT-MARKERS-IN-TRANSIT-P.
;; ------------------------------------------------------------

(local-defthm
  cut-markers-in-transit-p-implies-marker

  (implies
   (and
    (cut-markers-in-transit-p
     m
     st)

    (memberp
     src
     (proc-ids st))

    (memberp
     dst
     (nbrs-to
      (g src
         (procs st))))

    (not
     (cm-cut-not-taken-p
      m
      src))

    (cm-cut-not-taken-p
     m
     dst))

   (marker-for-sid-in-channel-p
    (cm-sid m)
    (channel-state
     src
     dst
     (channels st))))
    :rule-classes
((:rewrite
  :match-free :all)))


(local-defthm marker-for-sid-in-channel-p-implies-consp
  (implies
   (marker-for-sid-in-channel-p
    target-sid
    channel)

   (consp channel))
      :rule-classes
((:rewrite
  :match-free :all)))

;; ------------------------------------------------------------
;; If SRC is post-cut and DST is still pre-cut, the target marker must be somewhere on SRC -> DST.
;; ------------------------------------------------------------
(defthm
  cut-markers-in-transit-for-srcs-p-implies-channel-consp

  (implies
   (and
    (cut-markers-in-transit-for-srcs-p
     srcs
     target-sid
     m
     procs
     channels)

    (memberp src srcs)

    (memberp
     dst
     (nbrs-to
      (g src procs)))

    (not
     (cm-cut-not-taken-p m src))

    (cm-cut-not-taken-p m dst))

   (consp
    (channel-state
     src
     dst
     channels)))
  :rule-classes
  ((:rewrite
    :match-free :all))
  :hints
  (("Goal"
    :in-theory
    (disable
     cm-cut-not-taken-p))))



;; ------------------------------------------------------------
;; Global version of the FOR-SRCS channel-nonempty theorem.
;; ------------------------------------------------------------

(defthm
  cut-markers-in-transit-p-implies-channel-consp

  (implies
   (and
    (cut-markers-in-transit-p
     m
     st)

    (memberp
     src
     (proc-ids st))

    (memberp
     dst
     (nbrs-to
      (g src
         (procs st))))

    ;; SRC has already taken the cut.
    (not
     (cm-cut-not-taken-p
      m
      src))

    ;; DST has not yet taken the cut.
    (cm-cut-not-taken-p
     m
     dst))

   (consp
    (channel-state
     src
     dst
     (channels st))))

  :rule-classes
  ((:rewrite
    :match-free :all)))










;; ------------------------------------------------------------
;; GOOD-CUT-META and CUT-META/IMPLEMENTATION CONSISTENCY are preserved together over an entire legal input segment.
;; ------------------------------------------------------------


;; ------------------------------------------------------------
;; GOOD-CUT-META preservation over a complete input segment.
;; ------------------------------------------------------------

(defthm
  good-cut-meta-p-over-process-cut-segment

  (implies
   (and
    (good-cut-meta-p m)

    (cut-meta-imp-consistent-p
     m
     st)

    (good-state-p st)

    (legal-input-sequencep
     st
     inputs))

   (good-cut-meta-p
    (process-cut-segment
     inputs
     st
     m)))

    :hints
  (("Goal"
    :induct
    (process-cut-segment
     inputs
     st
     m)

    :in-theory
    (disable
     good-state-p
     good-cut-meta-p
     cut-meta-imp-consistent-p
     cut-markers-in-transit-p
     process-cut-step
     system-step
     legal-inputp))))








;; ------------------------------------------------------------
;; Metadata/implementation consistency over a complete segment.
;; ------------------------------------------------------------

(defthm
  cut-meta-imp-consistent-p-over-process-cut-segment

  (implies
   (and
    (cut-meta-imp-consistent-p
     m
     st)

    (good-cut-meta-p m)

    (good-state-p st)

    (legal-input-sequencep
     st
     inputs))

   (cut-meta-imp-consistent-p
    (process-cut-segment
     inputs
     st
     m)

    (run-imp
     st
     inputs)))

    :hints
  (("Goal"
    :induct
    (process-cut-segment
     inputs
     st
     m)

    :in-theory
    (disable
     good-state-p
     good-cut-meta-p
     cut-meta-imp-consistent-p
     cut-markers-in-transit-p
     process-cut-step
     system-step
     legal-inputp))))


;; ------------------------------------------------------------
;; Marker-in-transit preservation over an entire input segment.
;; ------------------------------------------------------------

(defthm cut-markers-in-transit-p-preserved-by-segment
  (implies
   (and
    (cut-markers-in-transit-p m st)

    (cut-meta-imp-consistent-p m st)

    (good-state-p st)

    (good-cut-meta-p m)

    (legal-input-sequencep st inputs))

   (cut-markers-in-transit-p
    (process-cut-segment inputs st m)
    (run-imp st inputs)))

  :hints
  (("Goal"
    :induct
    (process-cut-segment
     inputs
     st
     m)

    :in-theory
    (disable
     good-state-p
     good-cut-meta-p
     cut-meta-imp-consistent-p
     cut-markers-in-transit-p
     process-cut-step
     system-step
     legal-inputp))))


) ;; end private proof development
