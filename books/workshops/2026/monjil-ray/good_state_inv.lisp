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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Book import
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(in-package "ACL2")
(include-book "model")
(include-book "basic")




;start definitions: status-and-snapshot-id-predicates
;; Basic recognizers for allowed process statuses, snapshot statuses, and snapshot identifiers.

(defun good-proc-status-p (x)
  (or (equal x :normal)
      (equal x :crashed)
      (equal x :recovering)))

(defun good-snapshot-status-p (x)
  (or (equal x :checkpointing)
      (equal x :done)))

(defun good-snapshot-id-p (sid ids)
  (or (equal sid :init)
      (and (consp sid)
           (consp (cdr sid))
           (endp (cddr sid))
           (memberp (car sid) ids)
           (natp (cadr sid)))))

(defun good-snapshot-ids-p (snapshot-ids ids)
  (if (endp snapshot-ids)
      t
    (and (good-snapshot-id-p (first snapshot-ids) ids)
         (good-snapshot-ids-p (rest snapshot-ids) ids))))

(defun good-snapshot-ids-list-p (snapshot-ids ids)
  (and (true-listp snapshot-ids)
       (uniquep snapshot-ids)
       (memberp :init snapshot-ids)
       (good-snapshot-ids-p snapshot-ids ids)))

;end definitions: status-and-snapshot-id-predicates


;start definitions: message-well-formedness
;; Marker and recovery messages have different sid-knowledge requirements:


(defun good-msg-p (msg ids procs)
  (let ((tp (msg-type msg)))
    (cond ((equal tp :normal)
           t)
          ((equal tp :marker)
           (some-proc-has-snapshot-id-p (sid msg) ids procs))
          ((equal tp :recovery)
           (all-procs-have-snapshot-id-p (sid msg) ids procs))
          (t nil))))

(defun good-msg-list-p (msgs ids procs)
  (if (endp msgs)
      t
    (and (good-msg-p (first msgs) ids procs)
         (good-msg-list-p (rest msgs) ids procs))))

(defthm good-msg-p-of-create-marker-message
  (implies (some-proc-has-snapshot-id-p sid ids procs)
           (good-msg-p (create-marker-message local-state sid)
                       ids
                       procs)))

(defthm good-msg-p-of-create-recovery-message
  (implies (all-procs-have-snapshot-id-p sid ids procs)
           (good-msg-p (create-recovery-message local-state sid)
                       ids
                       procs)))

;end definitions: message-well-formedness


;start definitions: snapshot-entry-well-formedness
;; Channel snapshots contain only normal messages, and each snapshot entry keeps
;; its waiting-marker list inside the process's incoming-neighbor list.

(defun good-normal-msg-p (msg)
  (equal (msg-type msg) :normal))

(defthm good-normal-msg-p-of-create-compute-message
  (good-normal-msg-p (create-compute-message local-state nbr)))

(defun good-normal-msg-list-p (msgs)
  (if (endp msgs)
      t
    (and (good-normal-msg-p (first msgs))
         (good-normal-msg-list-p (rest msgs)))))

(defun good-channel-snapshot-record-p (nbrs-from-i cs)
  (if (endp nbrs-from-i)
      t
    (and (good-normal-msg-list-p (g (first nbrs-from-i) cs))
         (good-channel-snapshot-record-p (rest nbrs-from-i) cs))))

(defun good-snapshot-entry-p (entry nbrs-from-i)
  (and (good-snapshot-status-p (snapshot-status entry))
       (true-listp (snapshot-waiting-marker-from entry))
       (uniquep (snapshot-waiting-marker-from entry))
       (subset (snapshot-waiting-marker-from entry) nbrs-from-i)
       (good-channel-snapshot-record-p nbrs-from-i
                                       (snapshot-channel-snapshots entry))))

(defun good-snapshots-p (snapshot-ids p nbrs-from-i ids)
  (declare (irrelevant ids))
  (if (endp snapshot-ids)
      t
    (let* ((sid   (first snapshot-ids))
           (entry (snapshot-entry sid p)))
      (and
           (good-snapshot-entry-p entry nbrs-from-i)
           (good-snapshots-p (rest snapshot-ids)
                             p
                             nbrs-from-i
                             ids)))))

;end definitions: snapshot-entry-well-formedness




;start definitions: process-channel-state-well-formedness
;; Lift the local predicates to processes, process tables, channel rows,
;; full channel tables, and finally the top-level implementation state.

;; (defun good-proc-p ( p ids)
;;   (let* ((nbrs-in  (nbrs-from p))
;;          (nbrs-out (nbrs-to p)))
;;     (and (true-listp nbrs-in)
;;          (true-listp nbrs-out)
;;          (subset nbrs-in ids)
;;          (subset nbrs-out ids)
;;          (good-proc-status-p (proc-status p))
;;          (natp (counter p))
;;          (true-listp (waiting-recovery-from p))
;;          (subset (waiting-recovery-from p) nbrs-in)
;; 	 (good-snapshot-ids-list-p (snapshot-ids p) ids)
;;          (good-snapshots-p (snapshot-ids p) p nbrs-in ids)  )))

(defun good-proc-p (p ids)
  (let* ((nbrs-in  (nbrs-from p))
         (nbrs-out (nbrs-to p)))
    (and
     ;; Neighbor rows are finite set-like lists.
     (true-listp nbrs-in)
     (true-listp nbrs-out)
     (uniquep nbrs-in)
     (uniquep nbrs-out)

     ;; Every neighbor is a process in the system.
     (subset nbrs-in ids)
     (subset nbrs-out ids)

     (good-proc-status-p (proc-status p))
     (natp (counter p))
     (true-listp (waiting-recovery-from p))
     (subset (waiting-recovery-from p) nbrs-in)
     (good-snapshot-ids-list-p (snapshot-ids p) ids)
     (good-snapshots-p
      (snapshot-ids p)
      p
      nbrs-in
      ids))))

(defun good-procs-p (ids procs all-ids)
  (if (endp ids)
      t
    (let* ((i (first ids))
           (p (g i procs)))
      (and (good-proc-p  p  all-ids)
           (good-procs-p (rest ids) procs all-ids)))))

(defun good-channel-p (src dst channels ids procs)
  (let ((p (g src procs)))
    (if (memberp dst (nbrs-to p))
        (good-msg-list-p (channel-state src dst channels) ids procs)
      (equal (channel-state src dst channels) nil))))

(defun good-channel-row-p (src dsts channels ids procs)
  (if (endp dsts)
      t
    (and (good-channel-p src (first dsts) channels ids procs)
         (good-channel-row-p src (rest dsts) channels ids procs))))

(defun good-channels-p (srcs dsts channels ids procs)
  (if (endp srcs)
      t
    (and (good-channel-row-p (first srcs) dsts channels ids procs)
         (good-channels-p (rest srcs) dsts channels ids procs))))

(defun nbrs-from-to-consistent-for-one-dst-p (i srcs procs)
  (if (endp srcs)
      t
    (and
     (implies
      (memberp (first srcs)
               (nbrs-from (g i procs)))
      (memberp i
               (nbrs-to (g (first srcs) procs))))
     (nbrs-from-to-consistent-for-one-dst-p
      i
      (rest srcs)
      procs))))

(defun nbrs-from-to-consistent-p (dsts srcs procs)
  (if (endp dsts)
      t
    (and
     (nbrs-from-to-consistent-for-one-dst-p
      (first dsts)
      srcs
      procs)
     (nbrs-from-to-consistent-p
      (rest dsts)
      srcs
      procs))))

(defun nbrs-to-from-consistent-for-one-src-p (j dsts procs)
  (if (endp dsts)
      t
    (and
     (implies
      (memberp (first dsts)
               (nbrs-to (g j procs)))
      (memberp j
               (nbrs-from (g (first dsts) procs))))
     (nbrs-to-from-consistent-for-one-src-p
      j
      (rest dsts)
      procs))))

(defun nbrs-to-from-consistent-p (srcs dsts procs)
  (if (endp srcs)
      t
    (and
     (nbrs-to-from-consistent-for-one-src-p
      (first srcs)
      dsts
      procs)
     (nbrs-to-from-consistent-p
      (rest srcs)
      dsts
      procs))))


(defun checkpoint-sid-p (x)
  (and
   (consp x)
   (consp (cdr x))
   (endp (cddr x))))


(defun own-checkpoint-sids-before-counter-p
    (i ctr sids)

  (if (endp sids)
      t

    (let ((x (first sids)))
      (and
       (implies
        (and
         (checkpoint-sid-p x)
         (equal (first x) i))

        (< (second x)
           ctr))

       (own-checkpoint-sids-before-counter-p
        i
        ctr
        (rest sids))))))


(defun proc-snapshot-counter-good-p
    (i p)

  (own-checkpoint-sids-before-counter-p
   i
   (counter p)
   (snapshot-ids p)))


(defun snapshot-counters-good-for-procs-p
    (ids procs)

  (if (endp ids)
      t

    (and
     (proc-snapshot-counter-good-p
      (first ids)
      (g (first ids) procs))

     (snapshot-counters-good-for-procs-p
      (rest ids)
      procs))))


;; ============================================================ 
;; CHECK ONE SNAPSHOT-ID LIST FOR ONE INITIATOR 
;; ============================================================ 

;; We call this function with a process id (initiator), counter value stored in that initiator and
;; a list of snapshot-ids stored in another process. We check for each snapshot id, if the
;; car(sid) matches the initiator id then cadr(sid) must be smaller than the initiator counter

(defun stored-sids-for-initiator-have-smaller-counters-p 
  (initiator initiator-counter sids) 
 
 (declare 
  (xargs :measure (acl2-count sids))) 
 
 (if (endp sids) 
 
     t 
 
  (let ((sid (first sids))) 
 
     (and 
      (cond 
       ;; :INIT contains no initiator/counter pair. 
       ((equal sid :init) 
        t) 
 
       ;; Every other SID must be a checkpoint SID. 
       ((not (checkpoint-sid-p sid)) 
        nil) 
 
       ;; If this SID belongs to INITIATOR, its stored counter must be smaller than the initiator's current counter.
       ((equal (first sid) initiator) 
        (< (second sid) 
           initiator-counter)) 
 
       ;; This SID belongs to another initiator. 
       (t 
        t)) 
 
      (stored-sids-for-initiator-have-smaller-counters-p 
       initiator 
       initiator-counter 
       (rest sids))))))


;; ============================================================ 
;; CHECK ALL STORED SIDS FOR ONE INITIATOR 
;; ============================================================ 
;; Take one initiator, compare snapshot-id list for process-ids
;;  using stored-sids-for-initiator-have-smaller-counters-p

(defun all-stored-sids-for-initiator-have-smaller-counters-p 
   (initiator ids procs) 
 
 (declare 
  (xargs :measure (acl2-count ids))) 
 
 (if (endp ids) 
 
     t 
 
   (let* ((holder            (first ids)) 
          (holder-p          (g holder procs)) 
          (initiator-p       (g initiator procs)) 
          (initiator-counter (counter initiator-p))) 
 
     (and 
      (stored-sids-for-initiator-have-smaller-counters-p 
       initiator 
       initiator-counter 
       (snapshot-ids holder-p)) 
 
      (all-stored-sids-for-initiator-have-smaller-counters-p 
       initiator 
       (rest ids) 
       procs)))))


;; ============================================================ 
;; CHECK THE CONDITION FOR EVERY INITIATOR 
;; ============================================================ 
 
(defun all-initiators-stored-sids-have-smaller-counters-p 
   (initiators ids procs) 
 
 (declare 
  (xargs :measure (acl2-count initiators))) 
 
 (if (endp initiators) 
 
     t 
 
   (and 
    (all-stored-sids-for-initiator-have-smaller-counters-p 
     (first initiators) 
     ids 
     procs) 
 
    (all-initiators-stored-sids-have-smaller-counters-p 
     (rest initiators) 
     ids 
     procs))))


(defun good-state-p (st)
  (let* ((ids      (proc-ids st))
         (procs    (procs st))
         (channels (channels st)))
    (and (true-listp ids)
         (uniquep ids)

	 ;; Second element(counter) of all snapshot ids stored in all process
	 ;; must be smaller than counter counter value in all processes if
	 ;; the process id matches with first element of sid
	 (all-initiators-stored-sids-have-smaller-counters-p 
	  ids 
	  ids 
	  procs) 
         (good-procs-p ids procs ids)

         ;; Direction 1:
         ;; j in nbrs-from(i) ==> i in nbrs-to(j)
         (nbrs-from-to-consistent-p ids ids procs)

         ;; Direction 2:
         ;; i in nbrs-to(j) ==> j in nbrs-from(i)
         (nbrs-to-from-consistent-p ids ids procs)

         (good-channels-p ids ids channels ids procs))))


(defthm 
 stored-sids-for-initiator-have-smaller-counters-p-implies-current-sid-absent 
 
 (implies 
  (stored-sids-for-initiator-have-smaller-counters-p 
   initiator 
   initiator-counter 
   sids) 
 
  (not 
  (memberp 
    (list initiator initiator-counter) 
    sids))) 
 
 :hints 
 (("Goal" 
   :induct 
  (stored-sids-for-initiator-have-smaller-counters-p 
    initiator 
    initiator-counter 
    sids) 
 
   :in-theory 
  (enable 
    checkpoint-sid-p)))) 
;end definitions: process-channel-state-well-formedness

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;DONT TOUCH START;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm nbrs-to-from-consistent-for-one-src-p-when-memberp-dst
  (implies
   (and
    (nbrs-to-from-consistent-for-one-src-p src dsts procs)
    (memberp dst dsts)
    (memberp dst (nbrs-to (g src procs))))
   (memberp src
            (nbrs-from (g dst procs))))
  :hints
  (("Goal"
    :induct
    (nbrs-to-from-consistent-for-one-src-p src dsts procs))))


(defthm nbrs-to-from-consistent-p-when-memberp-src
  (implies
   (and
    (nbrs-to-from-consistent-p srcs dsts procs)
    (memberp src srcs)
    (memberp dst dsts)
    (memberp dst (nbrs-to (g src procs))))
   (memberp src
            (nbrs-from (g dst procs))))
  :hints
  (("Goal"
    :induct
    (nbrs-to-from-consistent-p srcs dsts procs))))

(defthm nbrs-from-to-consistent-for-one-dst-p-when-memberp-src
  (implies
   (and
    (nbrs-from-to-consistent-for-one-dst-p dst srcs procs)
    (memberp src srcs)
    (memberp src (nbrs-from (g dst procs))))
   (memberp dst
            (nbrs-to (g src procs))))
  :hints
  (("Goal"
    :induct
    (nbrs-from-to-consistent-for-one-dst-p dst srcs procs))))

(defthm nbrs-from-to-consistent-p-when-memberp-dst
  (implies
   (and
    (nbrs-from-to-consistent-p dsts srcs procs)
    (memberp dst dsts)
    (memberp src srcs)
    (memberp src (nbrs-from (g dst procs))))
   (memberp dst
            (nbrs-to (g src procs))))
  :hints
  (("Goal"
    :induct
    (nbrs-from-to-consistent-p dsts srcs procs))))

(defthm nbrs-to-implies-nbrs-from-when-good-state-p
  (implies
   (and
    (good-state-p st)
    (memberp j (proc-ids st))
    (memberp i (proc-ids st))
    (memberp i (nbrs-to (g j (procs st)))))
   (memberp j (nbrs-from (g i (procs st))))))

(defthm nbrs-from-implies-nbrs-to-when-good-state-p
  (implies
   (and
    (good-state-p st)
    (memberp i (proc-ids st))
    (memberp j (proc-ids st))
    (memberp j (nbrs-from (g i (procs st)))))
   (memberp i (nbrs-to (g j (procs st))))))

(defthm good-channel-p-when-good-channels-p
  (implies
   (and
    (good-channels-p srcs dsts channels ids procs)
    (memberp src srcs)
    (memberp dst dsts))
   (good-channel-p src dst channels ids procs)))

(defthm good-channels-p-when-memberp-src
  (implies
   (and
    (good-channels-p srcs dsts channels ids procs)
    (memberp src srcs))
   (good-channel-row-p src dsts channels ids procs)))

(defthm good-channel-row-p-when-memberp-dst
  (implies
   (and
    (good-channel-row-p src dsts channels ids procs)
    (memberp dst dsts))
   (good-channel-p src dst channels ids procs)))

(defthm good-msg-list-p-of-channel-state-when-good-channel-p
  (implies
   (and
    (good-channel-p src dst channels ids procs)
    (memberp dst (nbrs-to (g src procs))))
   (good-msg-list-p
    (channel-state src dst channels)
    ids
    procs)))

(defthm good-msg-list-p-of-channel-state-when-good-state-p-nbrs-to
  (implies
   (and
    (good-state-p st)

    ;; Legal channel j -> i.
    (memberp j (proc-ids st))
    (memberp i (proc-ids st))
    (memberp i (nbrs-to (g j (procs st)))))
   (good-msg-list-p
    (channel-state j i (channels st))
    (proc-ids st)
    (procs st))))

(defthm good-msg-list-p-of-channel-state-when-good-state-p-nbrs-from
  (implies
   (and
    (good-state-p st)

    ;; Legal channel j -> i.
    (memberp j (proc-ids st))
    (memberp i (proc-ids st))
    (memberp j (nbrs-from (g i (procs st)))))
   (good-msg-list-p
    (channel-state  j i (channels st))
    (proc-ids st)
    (procs st))))


(defthm good-msg-p-of-get-msg-from-channel-when-good-msg-list-p
  (implies
   (and
    (good-msg-list-p
     (channel-state src dst channels)
     ids
     procs)
    (equal (msg-type
            (get-msg-from-channel src dst channels))
           :marker))
   (good-msg-p
    (get-msg-from-channel src dst channels)
    ids
    procs)))

(defthm good-msg-p-marker-implies-some-proc-has-snapshot-id-p
  (implies
   (and
    (good-msg-p msg ids procs)
    (equal (msg-type msg) :marker))
   (some-proc-has-snapshot-id-p
    (sid msg)
    ids
    procs)))


(defthm good-state-p-implies-marker-head-sid-known-somewhere
  (implies
   (and
    (good-state-p st)

    ;; Legal channel j -> i.
    (memberp j (proc-ids st))
    (memberp i (proc-ids st))
    (memberp j (nbrs-from (g i (procs st))))

    ;; The head message on channel j -> i is a marker.
    (equal (msg-type
            (get-msg-from-channel j i (channels st)))
           :marker))
   (some-proc-has-snapshot-id-p
    (sid (get-msg-from-channel j i (channels st)))
    (proc-ids st)
    (procs st)))
  :hints
  (("Goal"
    :in-theory
    (disable good-state-p
             get-msg-from-channel
             some-proc-has-snapshot-id-p))))

(defthm good-msg-p-of-get-msg-from-channel-when-good-msg-list-p-recovery
  (implies
   (and
    (good-msg-list-p
     (channel-state src dst channels)
     ids
     procs)
    (equal (msg-type
            (get-msg-from-channel src dst channels))
           :recovery))
   (good-msg-p
    (get-msg-from-channel src dst channels)
    ids
    procs)))


(defthm good-msg-p-recovery-implies-all-procs-have-snapshot-id-p
  (implies
   (and
    (good-msg-p msg ids procs)
    (equal (msg-type msg) :recovery))
   (all-procs-have-snapshot-id-p
    (sid msg)
    ids
    procs)))


(defthm good-state-p-implies-recovery-head-sid-known-by-all-procs
  (implies
   (and
    (good-state-p st)

    ;; Legal channel j -> i.
    (memberp j (proc-ids st))
    (memberp i (proc-ids st))
    (memberp j (nbrs-from (g i (procs st))))
    (equal (msg-type
            (get-msg-from-channel j i (channels st)))
           :recovery))
   (all-procs-have-snapshot-id-p
    (sid (get-msg-from-channel j i (channels st)))
    (proc-ids st)
    (procs st)))
  :hints
  (("Goal"
    :in-theory
    (disable good-state-p
             get-msg-from-channel
             all-procs-have-snapshot-id-p))))

(in-theory
 (disable
  ;; Neighbor-consistency accessors.
  nbrs-to-from-consistent-for-one-src-p-when-memberp-dst
  nbrs-to-from-consistent-p-when-memberp-src
  nbrs-from-to-consistent-for-one-dst-p-when-memberp-src
  nbrs-from-to-consistent-p-when-memberp-dst

  ;; Good-state neighbor-consistency consequences.
  nbrs-to-implies-nbrs-from-when-good-state-p
  nbrs-from-implies-nbrs-to-when-good-state-p

  ;; Channel/message extraction helpers.
  good-channel-p-when-good-channels-p
  good-channels-p-when-memberp-src
  good-channel-row-p-when-memberp-dst
  good-msg-list-p-of-channel-state-when-good-channel-p
  good-msg-list-p-of-channel-state-when-good-state-p-nbrs-to
  good-msg-list-p-of-channel-state-when-good-state-p-nbrs-from

  ;; Marker head-message helpers.
  good-msg-p-of-get-msg-from-channel-when-good-msg-list-p
  good-msg-p-marker-implies-some-proc-has-snapshot-id-p
  good-state-p-implies-marker-head-sid-known-somewhere

  ;; Recovery head-message helpers.
  good-msg-p-of-get-msg-from-channel-when-good-msg-list-p-recovery
  good-msg-p-recovery-implies-all-procs-have-snapshot-id-p
  good-state-p-implies-recovery-head-sid-known-by-all-procs))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;DONT TOUCH END;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Small reusable helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; General process-table/list lemmas used by several preservation proofs.


;start support: generic-process-and-list-helpers
;; Small rewrite/helper facts used across many preservation proofs.  These keep
;; membership/subset obligations from being reproved in every major case.

(defthm good-proc-p-of-g-when-good-procs-p
  (implies (and (good-procs-p ids procs all-ids)
                (memberp i ids))
           (good-proc-p (g i procs)
                        all-ids)))

(defthm not-memberp-when-subset-and-not-memberp
  (implies (and (subset xs ys)
                (not (memberp a ys)))
           (not (memberp a xs))))

(defthm memberp-of-cons-right
  (implies (memberp e xs)
           (memberp e (cons a xs))))

(defthm subset-of-cons
  (implies (subset xs ys)
           (subset xs (cons a ys))))

(defthm subset-reflexive
    (subset x x))

(defthm all-procs-have-snapshot-id-p-when-memberp
  (implies
   (and (all-procs-have-snapshot-id-p sid ids procs)
        (memberp i ids))
   (memberp sid (snapshot-ids (g i procs)))))

(defthm all-procs-have-snapshot-id-p-of-same-snapshot-ids-update
  (implies
   (and (all-procs-have-snapshot-id-p sid ids procs)
        (equal (snapshot-ids new-p)
               (snapshot-ids (g k procs))))
   (all-procs-have-snapshot-id-p
    sid
    ids
    (s k new-p procs)))
  :hints
  (("Goal"
    :induct (all-procs-have-snapshot-id-p sid ids procs))
   ("Subgoal *1/2"
    :cases ((equal k (car ids))))))

(defthm all-procs-have-init-snapshot-id-p-when-good-procs-p
  (implies
   (good-procs-p ids procs all-ids)
   (all-procs-have-snapshot-id-p :init ids procs)))


;end support: generic-process-and-list-helpers


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Initial-state preservation support
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Shows that the initial process table and channel table satisfy good-state-p.


;start support: initial-empty-message-and-snapshot-records
;; Empty channels and empty channel-snapshot records are well-formed.  The
;; initial snapshot entry is also structurally good for any incoming-neighbor list.

(defthm good-normal-msg-list-p-of-nil
  (good-normal-msg-list-p nil))

(defthm good-msg-list-p-of-nil
  (good-msg-list-p nil ids procs))

(defthm good-channel-snapshot-record-p-of-nil
  (good-channel-snapshot-record-p nbrs-from-i nil))

(defthm good-snapshot-entry-p-of-make-init-snapshot-entry
  (good-snapshot-entry-p (make-init-snapshot-entry init-local-state)
                         nbrs-from-i))

(defthm good-proc-p-of-install-initial-snapshot-on-make-one-proc
  (good-proc-p
   (install-initial-snapshot (make-one-proc i all-ids))
   all-ids))

;end support: initial-empty-message-and-snapshot-records


;start support: initial-process-table-construction
;; Show that make-procs-aux installs the expected process at every valid id, and
;; that installing the initial snapshot produces a good process table.

(defthm g-of-make-procs-aux
  (implies (and (memberp i ids)
                (uniquep ids))
           (equal (g i (make-procs-aux ids all-ids))
                  (make-one-proc i all-ids))))

(defthm g-of-s-diff
  (implies (not (equal k1 k2))
           (equal (g k1 (s k2 v r))
                  (g k1 r))))

(defthm g-of-install-initial-snapshots-when-not-member
  (implies (not (memberp k ids))
           (equal (g k (install-initial-snapshots ids procs))
                  (g k procs))))

(defthm g-of-install-initial-snapshots
  (implies (and (memberp i ids)
                (uniquep ids))
           (equal (g i (install-initial-snapshots ids procs))
                  (install-initial-snapshot (g i procs)))))

(defthm g-of-install-initial-snapshots-of-make-procs-aux
  (implies (and (memberp i ids)
                (uniquep ids))
           (equal (g i
                     (install-initial-snapshots ids
                                                (make-procs-aux ids all-ids)))
                  (install-initial-snapshot
                   (make-one-proc i all-ids)))))

(defthm good-proc-p-of-g-of-install-initial-snapshots-of-make-procs-aux
  (implies (and (memberp i ids)
                (uniquep ids))
           (good-proc-p
            (g i
               (install-initial-snapshots ids
                                          (make-procs-aux ids all-ids)))
            all-ids)))

(defthm good-procs-p-of-install-initial-snapshots-of-make-procs-aux
  (implies (uniquep ids)
           (good-procs-p ids
                         (install-initial-snapshots ids
                                                    (make-procs-aux ids all-ids))
                         all-ids)))

;end support: initial-process-table-construction


;start support: initial-channel-table-construction
;; Build the initial channel table one destination column at a time.  Freshness
;; and uniqueness keep old rows from being disturbed by the new destination.

(defthm good-channel-row-p-preserved-by-adding-fresh-dst
  (implies (and (good-channel-row-p src dsts channels ids procs)
                (not (memberp new-dst dsts)))
           (good-channel-row-p src dsts
                               (s new-dst row channels)
                               ids procs)))

(defthm good-channels-p-of-cons-new-dst
  (implies (and (good-channels-p srcs dsts channels ids procs)
                (not (memberp dst dsts))
		(uniquep dsts)
		(uniquep srcs))
           (good-channels-p srcs
                            (cons dst dsts)
                            (s dst (make-channel-row srcs) channels)
                            ids
                            procs)))

(defthm good-channels-p-of-make-channels-aux
    (implies (and (uniquep dsts)
		  (uniquep srcs))
           (good-channels-p srcs
                            dsts
                            (make-channels-aux srcs dsts)
                            ids
                            procs)))

(defthm good-channels-p-of-make-channels
    (implies (uniquep ids)
	     (good-channels-p ids ids (make-channels ids) ids procs)))

;end support: initial-channel-table-construction

(defthm nbrs-from-to-consistent-for-one-dst-p-of-make-procs-aux
  (implies
   (and
    (memberp i ids)
    (subset srcs ids)
    (uniquep ids))
   (nbrs-from-to-consistent-for-one-dst-p
    i
    srcs
    (make-procs-aux ids ids))))

(defthm nbrs-from-to-consistent-p-of-make-procs-aux
  (implies
   (and
    (subset dsts ids)
    (subset srcs ids)
    (uniquep ids))
   (nbrs-from-to-consistent-p
    dsts
    srcs
    (make-procs-aux ids ids))))

(defthm nbrs-to-of-install-initial-snapshot
  (equal (nbrs-to (install-initial-snapshot p))
         (nbrs-to p)))

(defthm nbrs-from-of-install-initial-snapshot
  (equal (nbrs-from (install-initial-snapshot p))
         (nbrs-from p)))

(defthm nbrs-to-of-g-of-s-install-initial-snapshot
  (equal
   (g :nbrs-to
      (g k
         (s a
            (install-initial-snapshot (g a procs))
            procs)))
   (g :nbrs-to
      (g k procs)))
  :hints
  (("Goal"
    :cases ((equal k a)))))

(defthm nbrs-to-of-g-of-install-initial-snapshots
  (equal
   (nbrs-to
    (g k (install-initial-snapshots ids procs)))
   (nbrs-to
    (g k procs))))

(defthm nbrs-from-of-g-of-s-install-initial-snapshot
  (equal
   (g :nbrs-from
      (g k
         (s a
            (install-initial-snapshot (g a procs))
            procs)))
   (g :nbrs-from
      (g k procs)))
  :hints
  (("Goal"
    :cases ((equal k a)))))

(defthm nbrs-from-of-g-of-install-initial-snapshots
  (equal
   (nbrs-from
    (g k (install-initial-snapshots ids procs)))
   (nbrs-from
    (g k procs))))

(defthm nbrs-from-to-consistent-for-one-dst-p-of-install-initial-snapshots
  (implies
   (nbrs-from-to-consistent-for-one-dst-p i srcs procs)
   (nbrs-from-to-consistent-for-one-dst-p
    i
    srcs
    (install-initial-snapshots ids procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-from-to-consistent-for-one-dst-p i srcs procs))))

(defthm nbrs-from-to-consistent-p-of-install-initial-snapshots
  (implies
   (nbrs-from-to-consistent-p dsts srcs procs)
   (nbrs-from-to-consistent-p
    dsts
    srcs
    (install-initial-snapshots ids procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-from-to-consistent-p dsts srcs procs))))

 
(defthm nbrs-from-to-consistent-p-of-make-initial-state
  (nbrs-from-to-consistent-p
   (proc-ids (make-initial-state))
   (proc-ids (make-initial-state))
   (procs (make-initial-state))))



(defthm nbrs-to-from-consistent-for-one-src-p-of-make-procs-aux
  (implies
   (and
    (memberp j ids)
    (subset dsts ids)
    (uniquep ids))
   (nbrs-to-from-consistent-for-one-src-p
    j
    dsts
    (make-procs-aux ids ids))))


(defthm nbrs-to-from-consistent-p-of-make-procs-aux
  (implies
   (and
    (subset srcs ids)
    (subset dsts ids)
    (uniquep ids))
   (nbrs-to-from-consistent-p
    srcs
    dsts
    (make-procs-aux ids ids))))


(defthm nbrs-to-from-consistent-for-one-src-p-of-install-initial-snapshots
  (implies
   (nbrs-to-from-consistent-for-one-src-p j dsts procs)
   (nbrs-to-from-consistent-for-one-src-p
    j
    dsts
    (install-initial-snapshots ids procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-to-from-consistent-for-one-src-p j dsts procs))))


(defthm nbrs-to-from-consistent-p-of-install-initial-snapshots
  (implies
   (nbrs-to-from-consistent-p srcs dsts procs)
   (nbrs-to-from-consistent-p
    srcs
    dsts
    (install-initial-snapshots ids procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-to-from-consistent-p srcs dsts procs))))


(defthm nbrs-to-from-consistent-p-of-make-initial-state
  (nbrs-to-from-consistent-p
   (proc-ids (make-initial-state))
   (proc-ids (make-initial-state))
   (procs (make-initial-state))))



;start target: initial-state-is-good-state
;; Main target for initialization: the state produced by make-initial-state
;; satisfies the global structural invariant good-state-p.




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Every initialized process stores exactly the distinguished :INIT SID.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm snapshot-ids-of-install-initial-snapshot
  (equal
   (snapshot-ids
    (install-initial-snapshot p))
   (list :init))
  :hints
  (("Goal"
    :in-theory
    (enable
     install-initial-snapshot
     add-snapshot-id
     snoc
     memberp))))


;; :INIT is explicitly accepted by the stored-SID predicate, independently
;; of the initiator and its current counter.
(defthm stored-sids-for-initiator-have-smaller-counters-p-of-init
  (stored-sids-for-initiator-have-smaller-counters-p
   initiator
   initiator-counter
   (list :init))
  :hints
  (("Goal"
    :in-theory
    (enable
     stored-sids-for-initiator-have-smaller-counters-p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Every initialized holder satisfies the condition for one initiator.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  all-stored-sids-for-initiator-have-smaller-counters-p-of-initial-procs

  (implies
   (and
    (true-listp holders)
    (subset holders all-ids)
    (uniquep all-ids))

   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    holders
    (install-initial-snapshots
     all-ids
     (make-procs-aux all-ids all-ids))))

  :hints
  (("Goal"
    :induct (len holders)

    :in-theory
    (e/d
     (all-stored-sids-for-initiator-have-smaller-counters-p
      subset)

     (install-initial-snapshots
      install-initial-snapshot
      make-procs-aux
      stored-sids-for-initiator-have-smaller-counters-p)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lift the result over every initiator.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-initial-procs-aux

  (implies
   (and
    (true-listp initiators)
    (true-listp holders)
    (subset holders all-ids)
    (uniquep all-ids))

   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    holders
    (install-initial-snapshots
     all-ids
     (make-procs-aux all-ids all-ids))))

  :hints
  (("Goal"
    :induct (len initiators)

    :in-theory
    (e/d
     (all-initiators-stored-sids-have-smaller-counters-p)

     (all-stored-sids-for-initiator-have-smaller-counters-p
      install-initial-snapshots
      install-initial-snapshot
      make-procs-aux)))

   ("Subgoal *1/1"
    :use
    ((:instance
      all-stored-sids-for-initiator-have-smaller-counters-p-of-initial-procs
      (initiator (car initiators)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Specialize both lists to the full process-ID list.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-initial-procs

  (implies
   (and
    (true-listp ids)
    (uniquep ids))

   (all-initiators-stored-sids-have-smaller-counters-p
    ids
    ids
    (install-initial-snapshots
     ids
     (make-procs-aux ids ids))))

  :hints
  (("Goal"
    :use
    ((:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-initial-procs-aux
      (initiators ids)
      (holders ids)
      (all-ids ids)))

    :in-theory
    (disable
     all-initiators-stored-sids-have-smaller-counters-p))))


(defthm initial-state-is-good-state
  (good-state-p
   (make-initial-state))

  :hints
  (("Goal"
    :use
    ((:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-initial-procs
      (ids (make-proc-ids))))

    :in-theory
    (e/d
     (good-state-p
      make-initial-state
      make-procs)

     (all-initiators-stored-sids-have-smaller-counters-p)))))

;end target: initial-state-is-good-state


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NOP preservation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A nop input leaves the state structurally unchanged.


;start target: good-state-p-preserved-by-nop
;; Main target for :nop inputs.  Since system-step does not change the state in
;; the nop case, good-state-p is preserved directly.

(defthm good-state-p-preserved-by-nop
  (implies (and (good-state-p st)
                (equal (ttype input) :nop))
           (good-state-p (system-step st input))))


;end target: good-state-p-preserved-by-nop


;; Crash preservation


;start support: crash-process-update-preservation
;; A crash changes only :proc-status.  Since :crashed is an allowed status and
;; snapshot data is untouched, the updated process remains good.

(defthm good-snapshots-p-of-set-proc-status-crashed
  (implies (good-snapshots-p snapshot-ids
                             p
                             nbrs-from
                             ids)
           (good-snapshots-p snapshot-ids
                             (s :proc-status :crashed p)
                             nbrs-from
                             ids)))

(defthm good-proc-p-of-set-proc-status-crashed
  (implies (good-proc-p p ids)
           (good-proc-p (s :proc-status :crashed p)
                        ids)))

(defthm good-proc-p-of-crashed-g-when-good-procs-p
  (implies (and (good-procs-p ids procs all-ids)
                (memberp i ids))
           (good-proc-p (s :proc-status
                           :crashed
                           (g i procs))
                        all-ids)))

(defthm g-of-crash-updated-procs
  (equal (g k
            (s i
               (s :proc-status :crashed (g i procs))
               procs))
         (if (equal k i)
             (s :proc-status :crashed (g i procs))
           (g k procs))))

(defthm good-procs-p-of-crash-update
  (implies (and (true-listp ids)
                (uniquep ids)
                (true-listp all-ids)
                (uniquep all-ids)
                (good-procs-p ids procs all-ids))
           (good-procs-p ids
                         (s i
                            (s :proc-status
                               :crashed
                               (g i procs))
                            procs)
                         all-ids)))

;end support: crash-process-update-preservation


;start support: crash-channel-preservation
;; Channels are unchanged by a crash, and message goodness is independent of the
;; crashed process's status.  Lift this fact from message lists to all channels.

(defthm good-msg-list-p-of-crash-update
  (implies (good-msg-list-p msgs ids procs)
           (good-msg-list-p msgs ids
                            (s i
                               (s :proc-status :crashed (g i procs))
                               procs))))

(defthm good-channel-p-of-crash-update
  (implies (good-channel-p src dst channels ids procs)
           (good-channel-p src dst channels ids
                           (s i
                              (s :proc-status :crashed (g i procs))
                              procs))))

(defthm good-channel-row-p-of-crash-update
  (implies (good-channel-row-p src dsts channels ids procs)
           (good-channel-row-p src dsts channels ids
                               (s i
                                  (s :proc-status :crashed (g i procs))
                                  procs))))

(defthm good-channels-p-of-crash-update
  (implies (good-channels-p srcs dsts channels ids procs)
           (good-channels-p srcs dsts channels ids
                            (s i
                               (s :proc-status :crashed (g i procs))
                               procs))))

;end support: crash-channel-preservation

(defthm nbrs-to-of-g-of-crash-update
  (equal
   (nbrs-to
    (g k
       (s i
          (s :proc-status
             :crashed
             (g i procs))
          procs)))
   (nbrs-to
    (g k procs)))
  :hints
  (("Goal"
    :cases ((equal k i)))))


(defthm nbrs-from-of-g-of-crash-update
  (equal
   (nbrs-from
    (g k
       (s i
          (s :proc-status
             :crashed
             (g i procs))
          procs)))
   (nbrs-from
    (g k procs)))
  :hints
  (("Goal"
    :cases ((equal k i)))))


(defthm nbrs-from-to-consistent-for-one-dst-p-of-crash-update
  (implies
   (nbrs-from-to-consistent-for-one-dst-p i srcs procs)
   (nbrs-from-to-consistent-for-one-dst-p
    i
    srcs
    (s k
       (s :proc-status
          :crashed
          (g k procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-from-to-consistent-for-one-dst-p i srcs procs))))


(defthm nbrs-from-to-consistent-p-of-crash-update
  (implies
   (nbrs-from-to-consistent-p dsts srcs procs)
   (nbrs-from-to-consistent-p
    dsts
    srcs
    (s k
       (s :proc-status
          :crashed
          (g k procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-from-to-consistent-p dsts srcs procs))))


(defthm nbrs-to-from-consistent-for-one-src-p-of-crash-update
  (implies
   (nbrs-to-from-consistent-for-one-src-p j dsts procs)
   (nbrs-to-from-consistent-for-one-src-p
    j
    dsts
    (s k
       (s :proc-status
          :crashed
          (g k procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-to-from-consistent-for-one-src-p j dsts procs))))


(defthm nbrs-to-from-consistent-p-of-crash-update
  (implies
   (nbrs-to-from-consistent-p srcs dsts procs)
   (nbrs-to-from-consistent-p
    srcs
    dsts
    (s k
       (s :proc-status
          :crashed
          (g k procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-to-from-consistent-p srcs dsts procs))))

;start target: good-state-p-of-system-step-crash
;; Main target for :crash inputs: combine the process-table update proof with
;; the channel-table preservation proof.

;; (defthm good-state-p-of-system-step-crash
;;   (implies (and (good-state-p st)
;;                 (equal (ttype input) :crash))
;;            (good-state-p (system-step st input))))


;end target: good-state-p-of-system-step-crash


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Normal-step process update preservation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Local-state updates preserve process and channel well-formedness.


;start support: normal-process-local-state-update
;; A normal computation step may update only :local-state.  This does not change
;; status, neighbor lists, snapshot ids, counters, or snapshot entries.

(defthm good-snapshots-p-of-set-proc-update-normal
  (implies (good-snapshots-p snapshot-ids
                             p
                             nbrs-from
                             ids)
           (good-snapshots-p snapshot-ids
                             (s :local-state val p)
                             nbrs-from
                             ids)))

(defthm good-proc-p-of-set-proc-update-normal
  (implies (good-proc-p p ids)
           (good-proc-p (s :local-state val p)
                        ids)))

(defthm good-proc-p-of-update-normal-g-when-good-procs-p
  (implies (and (good-procs-p ids procs all-ids)
                (memberp i ids))
           (good-proc-p (s :local-state val
                           (g i procs))
                        all-ids)))

(defthm good-proc-p-of-g-when-good-procs-p-update-normal
  (implies (and (good-procs-p ids procs all-ids)
                (memberp i ids))
           (good-proc-p (g i procs)
                        all-ids)))

(defthm g-of-update-normal-updated-procs
  (equal (g k
            (s i
               (s :local-state val (g i procs))
               procs))
         (if (equal k i)
             (s :local-state val (g i procs))
           (g k procs))))

(defthm good-procs-p-of-normal-update
  (implies (and (true-listp ids)
                (uniquep ids)
                (true-listp all-ids)
                (uniquep all-ids)
                (good-procs-p ids procs all-ids))
           (good-procs-p ids
                         (s i
                            (s :local-state
                               val
                               (g i procs))
                            procs)
                         all-ids)))

;end support: normal-process-local-state-update


;start support: normal-channel-preservation-under-proc-update
;; The channel contents do not change when only a process local state changes.
;; Lift preservation from message lists to rows and then to the whole channel table.

(defthm good-msg-list-p-of-normal-update
  (implies (good-msg-list-p msgs ids procs)
           (good-msg-list-p msgs ids
                            (s i
                               (s :local-state val (g i procs))
                               procs))))

(defthm good-channel-p-of-normal-update
  (implies (good-channel-p src dst channels ids procs)
           (good-channel-p src dst channels ids
                           (s i
                              (s :local-state val (g i procs))
                              procs))))

(defthm good-channel-row-p-of-normal-update
  (implies (good-channel-row-p src dsts channels ids procs)
           (good-channel-row-p src dsts channels ids
                               (s i
                                  (s  :local-state val (g i procs))
                                  procs))))

(defthm good-channels-p-of-normal-update
  (implies (good-channels-p srcs dsts channels ids procs)
           (good-channels-p srcs dsts channels ids
                            (s i
                               (s :local-state val (g i procs))
                               procs))))


;end support: normal-channel-preservation-under-proc-update


;; Compute-message channel preservation


;start support: compute-message-goodness
;; Compute messages are normal messages, so appending a freshly created compute
;; message preserves good-msg-list-p.

(defthm good-msg-p-of-create-compute-message
  (good-msg-p (create-compute-message local-state nbr)
              ids
              procs))

(defthm good-msg-list-p-of-snoc-create-compute-message
  (implies (good-msg-list-p msgs ids procs)
           (good-msg-list-p
            (snoc msgs (create-compute-message local-state nbr))
            ids
            procs)))

;end support: compute-message-goodness


;start support: one-compute-channel-update
;; These lemmas reason about a single channel-table update.  They separate the
;; same-channel case from different-source/different-destination cases.

(defthm channel-lookup-after-send-compute-message-when-dst-not-in-nbrs
  (implies (not (memberp dst nbrs))
           (equal (g src
                     (g dst
                        (send-compute-message local-state i nbrs channels)))
                  (g src
                     (g dst channels)))))

(defthm good-msg-list-p-preserved-by-setting-different-dst
    (implies (and (memberp dst dsts)
		  (not (memberp dst2 dsts))
                (good-msg-list-p (g src (g dst channels))
                                 ids procs))
           (good-msg-list-p
            (g src
               (g dst
                  (s dst2 row channels)))
            ids procs)))

(defthm good-msg-list-p-preserved-by-setting-different-src
  (implies (and (not (equal src src2))
                (good-msg-list-p (g src (g dst channels))
                                 ids procs))
           (good-msg-list-p
            (g src
               (g dst
                  (s dst
                     (s src2 val (g dst channels))
                     channels)))
            ids procs)))

(defthm good-msg-list-p-of-setting-channel-src-entry-val
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)
        (good-msg-list-p val ids procs))
   (good-msg-list-p
    (g src
       (s i
          val
          (g dst channels)))
    ids procs))
  :hints (("Goal"
           :cases ((equal i src)))))

(defthm good-msg-list-p-of-setting-channel-dst-entry-val
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)

        (good-msg-list-p val ids procs))
   (good-msg-list-p
    (g src
       (g dst
          (s j
             (s i val (g j channels))
             channels)))
    ids procs))
  :hints (("Goal"
           :cases ((equal dst j)))))

(defthm g-of-s-different-src
  (implies (not (equal src i))
           (equal (g src (s i val row))
                  (g src row))))

(defthm g-g-of-s-different-dst
  (implies (not (equal dst j))
           (equal (g src
                     (g dst
                        (s j row channels)))
                  (g src
                     (g dst channels)))))

(defthm channel-lookup-of-setting-different-channel
  (implies (or (not (equal dst j))
               (not (equal src i)))
           (equal
            (g src
               (g dst
                  (s j
                     (s i val (g j channels))
                     channels)))
            (g src
               (g dst channels))))
  :hints (("Goal"
           :do-not '(generalize fertilize)
           :cases ((equal dst j)))))

(defthm good-msg-list-p-of-setting-different-channel
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)
        (or (not (equal dst j))
            (not (equal src i))))
   (good-msg-list-p
    (g src
       (g dst
          (s j
             (s i val (g j channels))
             channels)))
    ids procs)))

(defthm good-msg-list-p-of-setting-channel-combined
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)
        (or (not (equal dst j))
            (not (equal src i))
            (good-msg-list-p val ids procs)))
   (good-msg-list-p
    (g src
       (g dst
          (s j
             (s i val (g j channels))
             channels)))
    ids procs))
  :hints (("Goal"
           :do-not '(generalize fertilize)
           :cases ((equal dst j)
                   (equal src i)))))

(defthm good-msg-list-p-of-snoc-create-compute-message-same-channel
  (implies
   (and (equal src i)
        (equal dst j)
        (good-msg-list-p (g src (g dst channels))
                         ids procs))
   (good-msg-list-p
    (snoc (g i (g j channels))
          (create-compute-message local-state j))
    ids procs)))

(defthm one-compute-send-update-disjunct
  (implies
   (good-msg-list-p (g src (g dst channels))
                    ids procs)
   (or (not (equal dst j))
       (not (equal src i))
       (good-msg-list-p
        (snoc (g i (g j channels))
              (create-compute-message local-state j))
        ids procs))))

(defthm good-msg-list-p-of-one-compute-send-update
  (implies
   (good-msg-list-p (g src (g dst channels))
                    ids procs)
   (good-msg-list-p
    (g src
       (g dst
          (s j
             (s i
                (snoc (g i (g j channels))
                      (create-compute-message local-state j))
                (g j channels))
             channels)))
    ids procs))
  :hints (("Goal"
           :do-not '(generalize fertilize)
           :use ((:instance good-msg-list-p-of-setting-channel-combined
                            (src src)
                            (dst dst)
                            (i i)
                            (j j)
                            (channels channels)
                            (ids ids)
                            (procs procs)
                            (val (snoc (g i (g j channels))
                                       (create-compute-message local-state j))))
                 (:instance one-compute-send-update-disjunct
                            (src src)
                            (dst dst)
                            (i i)
                            (j j)
                            (channels channels)
                            (ids ids)
                            (procs procs)
                            (local-state local-state))))))

;end support: one-compute-channel-update


;start support: send-compute-message-channel-lookup
;; After send-compute-message, either the target channel receives a good normal
;; message or unrelated/nil channels stay unchanged.

(defthm good-msg-list-p-of-channel-after-send-compute-message
  (implies
   (good-msg-list-p (g src (g dst channels)) ids procs)
   (good-msg-list-p
    (g src
       (g dst
          (send-compute-message local-state i nbrs channels)))
    ids procs)))

(defthm channel-nil-after-send-compute-message-when-dst-not-in-nbrs-2
    (implies (and (not (memberp dst  nbrs-to))
		  (subset nbrs nbrs-to )
                (not (g src (g dst channels))))
           (not (g src
                   (g dst
                      (send-compute-message local-state i nbrs channels))))))

(defthm channel-lookup-after-send-compute-message-when-src-not-i
  (implies (not (equal src i))
           (equal (g src
                     (g dst
                        (send-compute-message local-state i nbrs channels)))
                  (g src
                     (g dst channels)))))

(defthm channel-nil-after-send-compute-message-when-src-not-i
  (implies (and (not (equal src i))
                (not (g src (g dst channels))))
           (not
            (g src
               (g dst
                  (send-compute-message local-state i nbrs channels))))))

;end support: send-compute-message-channel-lookup


;start support: lift-send-compute-message-to-channel-table
;; Lift the compute-send preservation theorem from one channel to one row and
;; then to the full channel table.

(defthm good-channel-p-of-send-compute-message
  (implies (and (good-channel-p src dst channels ids procs)
                (subset nbrs (nbrs-to (g i procs))))
           (good-channel-p
            src
            dst
            (send-compute-message local-state i nbrs channels)
            ids
            procs))
  :hints (("Goal'"
           :cases ((equal src i)))))

(defthm good-channel-row-p-of-send-compute-message
  (implies (and (good-channel-row-p src dsts channels ids procs)
                (subset nbrs (nbrs-to (g i procs))))
           (good-channel-row-p
            src
            dsts
            (send-compute-message local-state i nbrs channels)
            ids
            procs))
    :hints (("Goal"
           :induct (good-channel-row-p src dsts channels ids procs))))

(defthm good-channels-p-of-send-compute-message
  (implies (and (good-channels-p srcs dsts channels ids procs)
                (subset nbrs (nbrs-to (g i procs))))
           (good-channels-p
            srcs
            dsts
            (send-compute-message local-state i nbrs channels)
            ids
            procs))
      :hints (("Goal"
           :induct (good-channels-p srcs dsts channels ids procs))))


;end support: lift-send-compute-message-to-channel-table


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Normal system-step preservation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Combines the local-state update and compute-send preservation lemmas.

(defthm nbrs-to-of-g-of-normal-update
  (equal
   (nbrs-to
    (g k
       (s i
          (s :local-state
             val
             (g i procs))
          procs)))
   (nbrs-to
    (g k procs)))
  :hints
  (("Goal"
    :cases ((equal k i)))))


(defthm nbrs-from-of-g-of-normal-update
  (equal
   (nbrs-from
    (g k
       (s i
          (s :local-state
             val
             (g i procs))
          procs)))
   (nbrs-from
    (g k procs)))
  :hints
  (("Goal"
    :cases ((equal k i)))))


(defthm nbrs-from-to-consistent-for-one-dst-p-of-normal-update
  (implies
   (nbrs-from-to-consistent-for-one-dst-p i srcs procs)
   (nbrs-from-to-consistent-for-one-dst-p
    i
    srcs
    (s k
       (s :local-state
          val
          (g k procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-from-to-consistent-for-one-dst-p i srcs procs))))


(defthm nbrs-from-to-consistent-p-of-normal-update
  (implies
   (nbrs-from-to-consistent-p dsts srcs procs)
   (nbrs-from-to-consistent-p
    dsts
    srcs
    (s k
       (s :local-state
          val
          (g k procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-from-to-consistent-p dsts srcs procs))))


(defthm nbrs-to-from-consistent-for-one-src-p-of-normal-update
  (implies
   (nbrs-to-from-consistent-for-one-src-p j dsts procs)
   (nbrs-to-from-consistent-for-one-src-p
    j
    dsts
    (s k
       (s :local-state
          val
          (g k procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-to-from-consistent-for-one-src-p j dsts procs))))


(defthm nbrs-to-from-consistent-p-of-normal-update
  (implies
   (nbrs-to-from-consistent-p srcs dsts procs)
   (nbrs-to-from-consistent-p
    srcs
    dsts
    (s k
       (s :local-state
          val
          (g k procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-to-from-consistent-p srcs dsts procs))))

;start target: good-state-p-of-system-step-normal
;; Main target for :normal inputs: combine the local-state process update with
;; the preservation of outgoing compute-message sends.

;; (defthm good-state-p-of-system-step-normal
;;   (implies (and (good-state-p st)
;;                 (equal (ttype input) :normal))
;;            (good-state-p (system-step st input))))


;end target: good-state-p-of-system-step-normal


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Checkpoint-entry/process-table support
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Snapshot-entry construction and process-table update lemmas used when starting
;; a checkpoint.


;start support: checkpoint-snapshot-entry-construction
;; Starting a checkpoint creates a new snapshot entry.  These lemmas show that
;; the new entry and the modified snapshot table preserve good-snapshots-p.

(defthm g-of-s-nil-nil
  (equal (g k (s j nil nil))
         nil)
  :hints (("Goal"
           :cases ((equal k j)))))

(defthm good-normal-msg-list-p-of-g-of-s-nil-nil
  (good-normal-msg-list-p (g k (s j nil nil))))

;; (defthm good-snapshot-entry-p-of-make-snapshot-entry
;;   (implies (and (true-listp waiting-marker-from)
;;                 (subset waiting-marker-from nbrs-from-i))
;;            (good-snapshot-entry-p
;;             (make-snapshot-entry local-snap-shot
;;                                  waiting-marker-from
;;                                  j)
;;             nbrs-from-i)))

(defthm good-snapshot-entry-p-of-make-snapshot-entry
  (implies
   (and
    (true-listp waiting-marker-from)
    (uniquep waiting-marker-from)
    (subset waiting-marker-from nbrs-from-i))
   (good-snapshot-entry-p
    (make-snapshot-entry
     local-snap-shot
     waiting-marker-from
     j)
    nbrs-from-i)))


(defthm good-snapshots-p-of-set-snapshot-entry-general
  (implies
   (and (good-snapshots-p snapshot-ids
                          p
                          nbrs-from-i
                          ids)
        (good-snapshot-entry-p entry nbrs-from-i))
   (good-snapshots-p
    snapshot-ids
    (s :snapshots
       (s sid entry (snapshots p))
       p)
    nbrs-from-i
    ids))
  :hints (("Goal"

           :in-theory (disable good-snapshot-entry-p))

          ("Subgoal *1/4''"
           :cases ((equal sid (car snapshot-ids))))))

(defthm good-snapshots-p-of-set-snapshot-ids-field
  (implies
   (good-snapshots-p snapshot-ids
                     p
                     nbrs-from-i
                     ids)
   (good-snapshots-p snapshot-ids
                     (s :snapshot-ids new-snapshot-ids p)
                     nbrs-from-i
                     ids)))

(defthm good-snapshots-p-of-set-snapshot-entry-after-set-snapshot-ids
  (implies
   (and (good-snapshots-p snapshot-ids
                          p
                          nbrs-from-i
                          ids)
        (good-snapshot-entry-p entry nbrs-from-i))
   (good-snapshots-p
    snapshot-ids
    (s :snapshots
       (s sid entry (g :snapshots p))
       (s :snapshot-ids new-snapshot-ids p))
    nbrs-from-i
    ids))
  :hints
  (("Goal"
    :use ((:instance good-snapshots-p-of-set-snapshot-ids-field
                     (snapshot-ids snapshot-ids)
                     (p p)
                     (new-snapshot-ids new-snapshot-ids)
                     (nbrs-from-i nbrs-from-i)
                     (ids ids))

          (:instance good-snapshots-p-of-set-snapshot-entry-general
                     (snapshot-ids snapshot-ids)
                     (p (s :snapshot-ids new-snapshot-ids p))
                     (sid sid)
                     (entry entry)
                     (nbrs-from-i nbrs-from-i)
                     (ids ids)))
    :in-theory (disable good-snapshot-entry-p))))

(defthm good-snapshots-p-of-install-snapshot-entry
  (implies
   (and (good-snapshots-p (snapshot-ids p)
                          p
                          nbrs-from-i
                          ids)
        (good-snapshot-entry-p entry nbrs-from-i))
   (good-snapshots-p
    (snapshot-ids (install-snapshot-entry sid entry p))
    (install-snapshot-entry sid entry p)
    nbrs-from-i
    ids))
  :hints (("Goal"
	   :in-theory (disable good-snapshot-entry-p))))

;end support: checkpoint-snapshot-entry-construction


;start support: checkpoint-updated-process-goodness
;; start-checkpoint-helper increments the counter and installs a snapshot entry.
;; These lemmas show the selected process remains good after that update.

(defthm good-snapshots-p-of-set-counter
  (implies (good-snapshots-p snapshot-ids
                             p
                             nbrs-from-i
                             ids)
           (good-snapshots-p snapshot-ids
                             (s :counter val p)
                             nbrs-from-i
                             ids)))

(defthm good-proc-p-of-increment-counter
  (implies (good-proc-p p ids)
           (good-proc-p
            (s :counter
               (+ 1 (counter p))
               p)
            ids)))

(defthm good-proc-p-of-start-checkpoint-helper-updated-proc
  (implies
   (and (good-proc-p (g i procs) ids)
	(memberp i ids))
   (good-proc-p
    (g i (start-checkpoint-helper procs i))
    ids)))

;end support: checkpoint-updated-process-goodness


;start support: checkpoint-process-table-lift
;; Lift the updated-process proof to the whole process table.  The key split is
;; whether the current id in the induction is the process that started checkpointing.

(defthm good-procs-p-of-set-good-proc
  (implies (and (good-procs-p ids procs all-ids)
                (good-proc-p new-p all-ids))
           (good-procs-p ids
                         (s i new-p procs)
                         all-ids))
  :hints (("Goal"
           :induct (good-procs-p ids procs all-ids))
          ("Subgoal *1/2"
           :cases ((equal i (car ids))))))

(defthm g-of-start-checkpoint-helper-diff
  (implies
   (not (equal k i))
   (equal (g k (start-checkpoint-helper procs i))
          (g k procs))))

(defthm good-procs-p-of-start-checkpoint-helper-when-not-member
  (implies
   (not (memberp i ids))
   (equal (good-procs-p ids
                        (start-checkpoint-helper procs i)
                        all-ids)
          (good-procs-p ids procs all-ids))))

(defthm good-procs-p-of-start-checkpoint-helper
  (implies
   (and (good-procs-p ids procs all-ids)
        (memberp i ids)
	(subset ids all-ids)
        (true-listp ids)
        (uniquep ids))
   (good-procs-p
    ids
    (start-checkpoint-helper procs i)
    all-ids))
  :hints
  (("Goal"
    :in-theory (disable start-checkpoint-helper good-proc-p)
    :induct (good-procs-p ids procs all-ids))
      ("Subgoal *1/2"
    :cases ((equal i (car ids))))))


;end support: checkpoint-process-table-lift


;; Generic outgoing-message send preservation


;start definitions: process-table-compatibility-predicates
;; Compatibility predicates for comparing an old process table with an updated
;; one.  They are used when channels are preserved across process-table changes.

(defun snapshot-ids-subset-procs-p (ids procs1 procs2)
  (if (endp ids)
      t
    (and (subset (snapshot-ids (g (car ids) procs1))
                 (snapshot-ids (g (car ids) procs2)))
         (snapshot-ids-subset-procs-p (cdr ids) procs1 procs2))))

(defun same-nbrs-to-p (srcs procs1 procs2)
  (if (endp srcs)
      t
    (and (equal (nbrs-to (g (car srcs) procs1))
                (nbrs-to (g (car srcs) procs2)))
         (same-nbrs-to-p (cdr srcs) procs1 procs2))))

;end definitions: process-table-compatibility-predicates


;start support: change-procs-preserves-message-and-channel-goodness
;; If the updated process table keeps enough snapshot ids and the same outgoing
;; neighbors, then existing good messages/channels remain good under the new table.

(defthm some-proc-has-snapshot-id-p-monotone
  (implies
   (and (snapshot-ids-subset-procs-p ids procs1 procs2)
        (some-proc-has-snapshot-id-p sid ids procs1))
   (some-proc-has-snapshot-id-p sid ids procs2)))

(defthm all-procs-have-snapshot-id-p-monotone
  (implies
   (and (snapshot-ids-subset-procs-p ids procs1 procs2)
        (all-procs-have-snapshot-id-p sid ids procs1))
   (all-procs-have-snapshot-id-p sid ids procs2)))

(defthm good-msg-p-change-procs
  (implies
   (and (good-msg-p msg ids procs1)
        (snapshot-ids-subset-procs-p ids procs1 procs2))
   (good-msg-p msg ids procs2)))

(defthm good-msg-list-p-change-procs
  (implies
   (and (good-msg-list-p msgs ids procs1)
        (snapshot-ids-subset-procs-p ids procs1 procs2))
   (good-msg-list-p msgs ids procs2)))

(defthm good-channel-p-change-procs
  (implies
   (and (good-channel-p src dst channels ids procs1)
        (equal (nbrs-to (g src procs1))
               (nbrs-to (g src procs2)))
        (snapshot-ids-subset-procs-p ids procs1 procs2))
   (good-channel-p src dst channels ids procs2)))

(defthm good-channel-row-p-change-procs
  (implies
   (and (good-channel-row-p src dsts channels ids procs1)
        (equal (nbrs-to (g src procs1))
               (nbrs-to (g src procs2)))
        (snapshot-ids-subset-procs-p ids procs1 procs2))
   (good-channel-row-p src dsts channels ids procs2)))

(defthm good-channels-p-change-procs
  (implies
   (and (good-channels-p srcs dsts channels ids procs1)
        (same-nbrs-to-p srcs procs1 procs2)
        (snapshot-ids-subset-procs-p ids procs1 procs2))
   (good-channels-p srcs dsts channels ids procs2)))

;end support: change-procs-preserves-message-and-channel-goodness


;start support: one-generic-channel-send
;; General one-channel send lemma for any already-good message.  This reuses the
;; same combined channel-update reasoning developed for compute messages.

(defthm good-msg-list-p-of-snoc-good-msg
  (implies (and (good-msg-list-p msgs ids procs)
                (good-msg-p msg ids procs))
           (good-msg-list-p (snoc msgs msg)
                            ids
                            procs))
  :hints (("Goal"
           :induct (snoc msgs msg))))

(defthm one-generic-send-update-disjunct
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)
        (good-msg-p msg ids procs))
   (or (not (equal dst j))
       (not (equal src i))
       (good-msg-list-p
        (snoc (g i (g j channels)) msg)
        ids procs))))

(defthm good-msg-list-p-of-one-generic-send-update
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)
        (good-msg-p msg ids procs))
   (good-msg-list-p
    (g src
       (g dst
          (s j
             (s i
                (snoc (g i (g j channels)) msg)
                (g j channels))
             channels)))
    ids procs))
  :hints
  (("Goal"
    :do-not '(generalize fertilize)
    :use ((:instance good-msg-list-p-of-setting-channel-combined
                     (src src)
                     (dst dst)
                     (i i)
                     (j j)
                     (channels channels)
                     (ids ids)
                     (procs procs)
                     (val (snoc (g i (g j channels)) msg)))

          (:instance one-generic-send-update-disjunct
                     (src src)
                     (dst dst)
                     (i i)
                     (j j)
                     (channels channels)
                     (ids ids)
                     (procs procs)
                     (msg msg))))))

;end support: one-generic-channel-send


;start support: lift-generic-send-to-channel-table
;; Lift send-msg-all-outgoing-channels from message lists to channel rows and
;; the full channel table.  The two-procs version supports send-after-update cases.

(defthm good-msg-list-p-of-channel-after-send-msg-all-outgoing-channels
  (implies
   (and (good-msg-list-p (g src (g dst channels))
                         ids procs)
        (good-msg-p msg ids procs))
   (good-msg-list-p
    (g src
       (g dst
          (send-msg-all-outgoing-channels msg i nbrs channels)))
    ids procs))
  :hints (("Goal"
           :induct (send-msg-all-outgoing-channels msg i nbrs channels))))

(defthm channel-lookup-after-send-msg-all-outgoing-channels-when-src-not-i
  (implies
   (not (equal src i))
   (equal
    (g src
       (g dst
          (send-msg-all-outgoing-channels msg i nbrs channels)))
    (g src
       (g dst channels))))
  :hints (("Goal"
           :induct (send-msg-all-outgoing-channels msg i nbrs channels))))

(defthm channel-lookup-after-send-msg-all-outgoing-channels-when-dst-not-in-nbrs
  (implies
   (not (memberp dst nbrs))
   (equal
    (g src
       (g dst
          (send-msg-all-outgoing-channels msg i nbrs channels)))
    (g src
       (g dst channels))))
  :hints (("Goal"
           :induct (send-msg-all-outgoing-channels msg i nbrs channels))))

(defthm channel-nil-after-send-msg-all-outgoing-channels-when-dst-not-in-nbrs-to
  (implies
   (and (not (memberp dst nbrs-to))
        (subset nbrs nbrs-to)
        (not (g src (g dst channels))))
   (not
    (g src
       (g dst
          (send-msg-all-outgoing-channels msg i nbrs channels)))))
  :hints
  (("Goal"
    :use ((:instance not-memberp-when-subset-and-not-memberp
                     (xs nbrs)
                     (ys nbrs-to)
                     (a dst))

          (:instance channel-lookup-after-send-msg-all-outgoing-channels-when-dst-not-in-nbrs
                     (src src)
                     (dst dst)
                     (msg msg)
                     (i i)
                     (nbrs nbrs)
                     (channels channels))))))

(defthm good-channel-p-of-send-msg-all-outgoing-channels
  (implies
   (and (good-channel-p src dst channels ids procs)
        (good-msg-p msg ids procs)
        (subset nbrs (nbrs-to (g i procs))))
   (good-channel-p
    src
    dst
    (send-msg-all-outgoing-channels msg i nbrs channels)
    ids
    procs))
  :hints (("Goal"
           :cases ((equal src i)))))

(defthm good-channel-row-p-of-send-msg-all-outgoing-channels
  (implies
   (and (good-channel-row-p src dsts channels ids procs)
        (good-msg-p msg ids procs)
        (subset nbrs (nbrs-to (g i procs))))
   (good-channel-row-p
    src
    dsts
    (send-msg-all-outgoing-channels msg i nbrs channels)
    ids
    procs))
  :hints (("Goal"
           :induct (good-channel-row-p src dsts channels ids procs))))

(defthm good-channels-p-of-send-msg-all-outgoing-channels
  (implies
   (and (good-channels-p srcs dsts channels ids procs)
        (good-msg-p msg ids procs)
        (subset nbrs (nbrs-to (g i procs))))
   (good-channels-p
    srcs
    dsts
    (send-msg-all-outgoing-channels msg i nbrs channels)
    ids
    procs))
  :hints (("Goal"
           :induct (good-channels-p srcs dsts channels ids procs))))

(defthm good-channels-p-of-send-msg-all-outgoing-channels-two-procs
  (implies
   (and (good-channels-p srcs dsts channels ids procs1)

        ;; the new message must be good under the final procs
        (good-msg-p msg ids procs2)

        ;; procs2 keeps same outgoing-neighbor structure
        (same-nbrs-to-p srcs procs1 procs2)

        ;; procs2 contains at least all snapshot ids from procs1
        (snapshot-ids-subset-procs-p ids procs1 procs2)

        ;; sends only go to legal outgoing neighbors under procs2
        (subset nbrs (nbrs-to (g i procs2))))

   (good-channels-p
    srcs
    dsts
    (send-msg-all-outgoing-channels msg i nbrs channels)
    ids
    procs2)))


;end support: lift-generic-send-to-channel-table


;; Start-checkpoint preservation


;start support: marker-message-goodness-after-start-checkpoint
;; After start-checkpoint-helper installs the new sid at process i, the marker
;; message carrying that sid is good under the updated process table.

(defthm good-msg-p-of-create-marker-message-after-start-checkpoint-helper
  (implies (memberp i ids)
           (good-msg-p
            (create-marker-message
             local-state
             (list i (counter (g i procs))))
            ids
            (start-checkpoint-helper procs i))))

;end support: marker-message-goodness-after-start-checkpoint


;start support: start-checkpoint-neighbor-preservation
;; Installing snapshot data and incrementing the counter do not change outgoing
;; neighbors.  This discharges the same-nbrs-to-p requirement for channel sends.

(defthm nbrs-to-of-install-snapshot-entry
  (equal (nbrs-to (install-snapshot-entry sid entry p))
         (nbrs-to p)))

(defthm nbrs-to-of-set-counter
  (equal (nbrs-to (s :counter val p))
         (nbrs-to p)))

(defthm nbrs-to-of-set-snapshots
  (equal (nbrs-to (s :snapshots val p))
         (nbrs-to p)))

(defthm nbrs-to-of-set-snapshot-ids
  (equal (nbrs-to (s :snapshot-ids val p))
         (nbrs-to p)))

(defthm nbrs-to-of-g-of-start-checkpoint-helper
  (equal (nbrs-to (g src (start-checkpoint-helper procs i)))
         (nbrs-to (g src procs)))
  :hints
  (("Goal"
    :cases ((equal src i)))))

(defthm same-nbrs-to-p-of-start-checkpoint-helper
  (same-nbrs-to-p srcs procs
        (start-checkpoint-helper procs i))
  :hints
  (("Goal"
    :induct (same-nbrs-to-p srcs procs
                            (start-checkpoint-helper procs i))
    :in-theory (disable start-checkpoint-helper))))

;end support: start-checkpoint-neighbor-preservation


;start support: start-checkpoint-snapshot-id-monotonicity
;; start-checkpoint-helper only adds the new snapshot id; it does not remove old
;; ids.  This provides the snapshot-id monotonicity needed by the two-procs lemma.

(defthm subset-snapshot-ids-of-g-of-start-checkpoint-helper
  (subset (snapshot-ids (g k procs))
          (snapshot-ids (g k (start-checkpoint-helper procs i))))
  :hints
  (("Goal"
    :cases ((equal k i)))))

(defthm snapshot-ids-subset-procs-p-of-start-checkpoint-helper
  (snapshot-ids-subset-procs-p
   ids
   procs
   (start-checkpoint-helper procs i))
  :hints
  (("Goal"
    :induct (snapshot-ids-subset-procs-p
             ids
             procs
             (start-checkpoint-helper procs i))
    :in-theory (disable start-checkpoint-helper))))

;end support: start-checkpoint-snapshot-id-monotonicity


;start target: good-state-p-of-system-step-start-checkpoint
;; Main target for :start-checkpoint inputs: update the initiating process, prove
;; the marker message is good, and preserve the outgoing marker sends.

(defthm nbrs-from-of-install-snapshot-entry
  (equal (nbrs-from (install-snapshot-entry sid entry p))
         (nbrs-from p)))

(defthm nbrs-from-of-set-counter
  (equal (nbrs-from (s :counter val p))
         (nbrs-from p)))

(defthm nbrs-from-of-set-snapshots
  (equal (nbrs-from (s :snapshots val p))
         (nbrs-from p)))

(defthm nbrs-from-of-set-snapshot-ids
  (equal (nbrs-from (s :snapshot-ids val p))
         (nbrs-from p)))

(defthm nbrs-from-of-g-of-start-checkpoint-helper
  (equal
   (nbrs-from (g src (start-checkpoint-helper procs i)))
   (nbrs-from (g src procs)))
  :hints
  (("Goal"
    :cases ((equal src i)))))

(defthm nbrs-from-to-consistent-for-one-dst-p-of-start-checkpoint-helper
  (implies
   (nbrs-from-to-consistent-for-one-dst-p i srcs procs)
   (nbrs-from-to-consistent-for-one-dst-p
    i
    srcs
    (start-checkpoint-helper procs k)))
  :hints
  (("Goal"
    :in-theory (disable start-checkpoint-helper)
    :induct
    (nbrs-from-to-consistent-for-one-dst-p i srcs procs))))

(defthm nbrs-from-to-consistent-p-of-start-checkpoint-helper
  (implies
   (nbrs-from-to-consistent-p dsts srcs procs)
   (nbrs-from-to-consistent-p
    dsts
    srcs
    (start-checkpoint-helper procs k)))
  :hints
  (("Goal"
    :in-theory (disable start-checkpoint-helper)
    :induct
    (nbrs-from-to-consistent-p dsts srcs procs))))

(defthm nbrs-to-from-consistent-for-one-src-p-of-start-checkpoint-helper
  (implies
   (nbrs-to-from-consistent-for-one-src-p j dsts procs)
   (nbrs-to-from-consistent-for-one-src-p
    j
    dsts
    (start-checkpoint-helper procs k)))
  :hints
  (("Goal"
    :in-theory (disable start-checkpoint-helper)
    :induct
    (nbrs-to-from-consistent-for-one-src-p j dsts procs))))

(defthm nbrs-to-from-consistent-p-of-start-checkpoint-helper
  (implies
   (nbrs-to-from-consistent-p srcs dsts procs)
   (nbrs-to-from-consistent-p
    srcs
    dsts
    (start-checkpoint-helper procs k)))
  :hints
  (("Goal"
    :in-theory (disable start-checkpoint-helper)
    :induct
    (nbrs-to-from-consistent-p srcs dsts procs))))



;; (defthm good-state-p-of-system-step-start-checkpoint
;;   (implies (and (good-state-p st)
;;                 (equal (ttype input) :start-checkpoint)
;; 		(memberp (pid input) (proc-ids st)))
;;            (good-state-p (system-step st input)))
;;   :hints
;;   (("Goal"
;;     :in-theory (disable good-proc-p
;; 			start-checkpoint-helper
;;                         make-snapshot-entry
;;                         install-snapshot-entry
;; 			create-marker-message))))


;end target: good-state-p-of-system-step-start-checkpoint


;; Start-recovery preservation


;start support: start-recovery-field-preservation
;; start-recovery-helper changes only recovery-control fields.  Snapshot tables,
;; neighbor lists, snapshot ids, and counters remain unchanged.

(defthm snapshots-of-g-of-start-recovery-helper
  (equal
   (snapshots (g src (start-recovery-helper procs i)))
   (snapshots (g src procs)))
  :hints
  (("Goal"
    :cases ((equal src i)))))

(defthm good-snapshots-p-of-g-of-start-recovery-helper-general
  (implies
   (good-snapshots-p snapshot-ids
                     (g src procs)
                     nbrs-from
                     ids)
   (good-snapshots-p snapshot-ids
                     (g src (start-recovery-helper procs i))
                     nbrs-from
                     ids))
  :hints
  (("Goal"
    :in-theory (disable start-recovery-helper)
    :cases ((equal src i)))))

(defthm nbrs-from-of-g-of-start-recovery-helper
  (equal
   (nbrs-from (g src (start-recovery-helper procs i)))
   (nbrs-from (g src procs)))
  :hints
  (("Goal"
    :cases ((equal src i))
    :in-theory (enable start-recovery-helper))))

(defthm nbrs-to-of-g-of-start-recovery-helper
  (equal
   (nbrs-to (g src (start-recovery-helper procs i)))
   (nbrs-to (g src procs)))
  :hints
  (("Goal"
    :cases ((equal src i))
    :in-theory (enable start-recovery-helper))))

(defthm snapshot-ids-of-g-of-start-recovery-helper
  (equal
   (snapshot-ids (g src (start-recovery-helper procs i)))
   (snapshot-ids (g src procs)))
  :hints
  (("Goal"
    :cases ((equal src i)))))

(defthm subset-waiting-recovery-from-of-g-i-of-start-recovery-helper
  (subset
   (waiting-recovery-from
    (g i (start-recovery-helper procs i)))
   (nbrs-from (g i procs))))

(defthm counter-of-g-of-start-recovery-helper
  (equal
   (counter (g src (start-recovery-helper procs i)))
   (counter (g src procs)))
  :hints
  (("Goal"
    :cases ((equal src i)))))

(defthm proc-status-of-g-i-of-start-recovery-helper
  (equal
   (proc-status
    (g i (start-recovery-helper procs i)))
   :recovering))

(defthm waiting-recovery-from-of-g-i-of-start-recovery-helper
  (equal
   (waiting-recovery-from
    (g i (start-recovery-helper procs i)))
   (nbrs-from (g i procs))))

;end support: start-recovery-field-preservation


;start support: start-recovery-process-table-lift
;; The recovering process remains good, and all other processes are unchanged.
;; Lift this to good-procs-p for the whole process table.

(defthm good-proc-p-of-start-recover-helper-updated-proc
  (implies
   (and (good-proc-p (g i procs) ids)
	(memberp i ids))
   (good-proc-p
    (g i (start-recovery-helper procs i))
    ids))
    :hints
  (("Goal"
    :in-theory (disable start-recovery-helper))))

(defthm g-of-start-recovery-helper-when-not-equal
  (implies
   (not (equal k i))
   (equal
    (g k (start-recovery-helper procs i))
    (g k procs))))

(defthm good-procs-p-of-start-recovery-helper
  (implies
   (and (good-procs-p ids procs all-ids)
        (true-listp ids)
	(subset ids all-ids)
        (uniquep ids)
        (memberp i ids))
   (good-procs-p
    ids
    (start-recovery-helper procs i)
    all-ids))
  :hints
  (("Goal"
    :in-theory (disable good-proc-p start-recovery-helper)
    :induct (good-procs-p ids procs all-ids))
   ("Subgoal *1/2"
    :cases ((equal i (car ids))))))

;end support: start-recovery-process-table-lift


;start support: start-recovery-neighbor-and-snapshot-compatibility
;; Prove the compatibility facts required when recovery messages are sent under
;; the updated process table: same outgoing neighbors and preserved snapshot ids.

(defthm same-nbrs-to-p-of-start-recovery-helper
  (same-nbrs-to-p srcs procs
        (start-recovery-helper procs i))
  :hints
  (("Goal"
    :induct (same-nbrs-to-p srcs procs
                            (start-recovery-helper procs i))
    :in-theory (disable start-recovery-helper))))

(defthm subset-snapshot-ids-of-g-of-start-recovery-helper
  (subset (snapshot-ids (g k procs))
          (snapshot-ids (g k (start-recovery-helper procs i))))
  :hints
  (("Goal"
    :cases ((equal k i)))))

(defthm snapshot-ids-subset-procs-p-of-start-recovery-helper
  (snapshot-ids-subset-procs-p
   ids
   procs
   (start-recovery-helper procs i))
  :hints
  (("Goal"
    :induct (snapshot-ids-subset-procs-p
             ids
             procs
             (start-recovery-helper procs i))
    :in-theory (disable start-recovery-helper))))

;end support: start-recovery-neighbor-and-snapshot-compatibility


;start support: recovery-message-goodness-after-start-recovery
;; A recovery message uses an existing snapshot id from the recovering process.
;; These lemmas establish that the sid exists before and after the helper update.

(defthm memberp-snapshot-ids-of-start-recovery-helper
  (equal
   (memberp sid
            (snapshot-ids
             (g src (start-recovery-helper procs i))))
   (memberp sid
            (snapshot-ids
             (g src procs)))))

(defthm some-proc-has-snapshot-id-p-of-start-recovery-helper
  (implies
   (and (memberp i ids)
        (some-proc-has-snapshot-id-p sid ids procs))
   (some-proc-has-snapshot-id-p
    sid
    ids
    (start-recovery-helper procs i)))
  :hints
  (("Goal"
    :in-theory (disable start-recovery-helper))))

(defthm all-procs-have-snapshot-id-p-of-start-recovery-helper
  (implies
   (all-procs-have-snapshot-id-p sid ids procs)
   (all-procs-have-snapshot-id-p
    sid
    ids
    (start-recovery-helper procs i)))
  :hints
  (("Goal"
    :in-theory (disable start-recovery-helper))))

(defthm some-proc-has-car-snapshot-id-before-recovery
  (implies
   (and (memberp i ids)
        (consp (snapshot-ids (g i procs))))
   (some-proc-has-snapshot-id-p
    (car (snapshot-ids (g i procs)))
    ids
    procs))
  :hints
  (("Goal"
    :induct (some-proc-has-snapshot-id-p
             (car (snapshot-ids (g i procs)))
             ids
             procs))
   ("Subgoal *1/2"
    :cases ((equal i (car ids))))))

(defthm some-proc-has-car-snapshot-id-after-recovery
  (implies
   (and (memberp i ids)
        (consp (snapshot-ids (g i procs))))
   (some-proc-has-snapshot-id-p
    (car (snapshot-ids (g i procs)))
    ids
     (start-recovery-helper procs i))))

(defthm good-msg-p-of-create-recovery-message-after-start-recovery-helper
  (implies
   (and (memberp i ids)
        (consp (snapshot-ids (g i procs)))
        ;; New recovery-message invariant:
        ;; the selected recovery sid must be globally known.
        (all-procs-have-snapshot-id-p
         (car (snapshot-ids (g i procs)))
         ids
         procs))
   (good-msg-p
    (create-recovery-message
     local-state
     (car (snapshot-ids (g i procs))))
    ids
    (start-recovery-helper procs i)))
    :hints
  (("Goal"
    :in-theory (disable start-recovery-helper
			create-recovery-message))))

;end support: recovery-message-goodness-after-start-recovery


;start support: nonempty-snapshot-ids-for-recovery
;; good-proc-p requires :init to be present in the snapshot-id list, so any good
;; process has a nonempty snapshot-id list for choosing a recovery sid.

(defthm consp-snapshot-ids-of-g-when-good-procs-p
  (implies
   (and (good-procs-p ids procs all-ids)
        (memberp i ids))
   (consp (snapshot-ids (g i procs)))))

;end support: nonempty-snapshot-ids-for-recovery


;start target: good-state-p-of-system-step-recover
;; Main target for :recover inputs: update the initiating process to recovering,
;; create a good recovery message, and preserve all outgoing recovery sends.

(defthm nbrs-from-to-consistent-for-one-dst-p-of-start-recovery-helper
  (implies
   (nbrs-from-to-consistent-for-one-dst-p i srcs procs)
   (nbrs-from-to-consistent-for-one-dst-p
    i
    srcs
    (start-recovery-helper procs k)))
  :hints
  (("Goal"
    :in-theory (disable start-recovery-helper)
    :induct
    (nbrs-from-to-consistent-for-one-dst-p i srcs procs))))


(defthm nbrs-from-to-consistent-p-of-start-recovery-helper
  (implies
   (nbrs-from-to-consistent-p dsts srcs procs)
   (nbrs-from-to-consistent-p
    dsts
    srcs
    (start-recovery-helper procs k)))
  :hints
  (("Goal"
    :in-theory (disable start-recovery-helper)
    :induct
    (nbrs-from-to-consistent-p dsts srcs procs))))


(defthm nbrs-to-from-consistent-for-one-src-p-of-start-recovery-helper
  (implies
   (nbrs-to-from-consistent-for-one-src-p j dsts procs)
   (nbrs-to-from-consistent-for-one-src-p
    j
    dsts
    (start-recovery-helper procs k)))
  :hints
  (("Goal"
    :in-theory (disable start-recovery-helper)
    :induct
    (nbrs-to-from-consistent-for-one-src-p j dsts procs))))


(defthm nbrs-to-from-consistent-p-of-start-recovery-helper
  (implies
   (nbrs-to-from-consistent-p srcs dsts procs)
   (nbrs-to-from-consistent-p
    srcs
    dsts
    (start-recovery-helper procs k)))
  :hints
  (("Goal"
    :in-theory (disable start-recovery-helper)
    :induct
    (nbrs-to-from-consistent-p srcs dsts procs))))

;; (defthm good-state-p-of-system-step-recover
;;   (implies (and (good-state-p st)
;;                 (equal (ttype input) :recover)
;; 		(memberp (pid input) (proc-ids st))
;;                 ;; A recovery message is now good only if its sid is known
;;                 ;; by every process.  This should normally come from a
;;                 ;; stronger legal-input/global recovery invariant.
;;                 (all-procs-have-snapshot-id-p
;;                  (car (snapshot-ids
;;                        (g (pid input) (procs st))))
;;                  (proc-ids st)
;;                  (procs st)))
;;            (good-state-p (system-step st input)))
;;   :hints
;;   (("Goal"
;;     :in-theory (disable good-proc-p
;; 			start-recovery-helper
;; 			create-recovery-message))))

;end target: good-state-p-of-system-step-recover


;; First-recovery-message preservation support


;start support: first-recovery-process-field-preservation
;; These lemmas say that update-proc-for-first-recovery-msg only changes recovery-related fields.

(defthm nbrs-from-of-update-proc-for-first-recovery-msg
  (equal (g :nbrs-from
            (update-proc-for-first-recovery-msg p sid j))
         (g :nbrs-from p)))

(defthm waiting-recovery-from-of-update-proc-for-first-recovery-msg
  (equal (g :waiting-recovery-from
            (update-proc-for-first-recovery-msg p sid j))
         (remove-from-list (g :nbrs-from p) j)))

(defthm subset-of-remove-from-list
  (subset (remove-from-list xs a)
          xs))

(defthm nbrs-to-of-update-proc-for-first-recovery-msg
  (equal (g :nbrs-to
            (update-proc-for-first-recovery-msg p sid j))
         (g :nbrs-to p)))

(defthm snapshot-ids-of-update-proc-for-first-recovery-msg
  (equal (g :snapshot-ids
            (update-proc-for-first-recovery-msg p sid j))
         (g :snapshot-ids p)))

(defthm counter-of-update-proc-for-first-recovery-msg
  (equal (g :counter
            (update-proc-for-first-recovery-msg p sid j))
         (g :counter p)))

(defthm proc-status-of-update-proc-for-first-recovery-msg
  (equal (g :proc-status
            (update-proc-for-first-recovery-msg p sid j))
         :recovering))
;end support: first-recovery-process-field-preservation


;start support: first-recovery-process-goodness
;; Once the basic fields are controlled, prove that the updated receiver process still satisfies good-proc-p.

(defthm good-snapshots-p-of-update-proc-for-first-recovery-msg
  (implies
   (good-snapshots-p snapshot-ids p nbrs-from ids)
   (good-snapshots-p
    snapshot-ids
    (update-proc-for-first-recovery-msg p sid j)
    nbrs-from
    ids)))

(defthm good-proc-p-of-update-proc-for-first-recovery-msg
  (implies
   (and (good-proc-p p ids)

        ;; sid must refer to an existing snapshot entry of p.
        (memberp sid (snapshot-ids p))

        ;; j is the sender of the recovery message.
        (memberp j (nbrs-from p)))
   (good-proc-p
    (update-proc-for-first-recovery-msg p sid j)
    ids))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-first-recovery-msg))))
;end support: first-recovery-process-goodness


;start support: remove-consumed-recovery-message
;; Handling a recovery message first removes the head message from channel j -> i.

(defthm channel-state-of-remove-message-from-channel
  (equal (g src
            (g dst
               (remove-message-from-channel j i channels)))
         (if (and (equal src j)
                  (equal dst i))
             (cdr (g src (g dst channels)))
           (g src (g dst channels)))))

(defthm good-msg-list-p-of-cdr
  (implies
   (good-msg-list-p msgs ids procs)
   (good-msg-list-p (cdr msgs) ids procs)))

(defthm good-channel-row-p-of-remove-message-from-channel
  (implies
   (good-channel-row-p src dsts channels ids procs)
   (good-channel-row-p
    src
    dsts
    (remove-message-from-channel j i channels)
    ids
    procs))
  :hints
  (("Goal"
    :induct (good-channel-row-p src dsts channels ids procs)
    :in-theory (disable remove-message-from-channel))))

(defthm good-channels-p-of-remove-message-from-channel
  (implies
   (good-channels-p srcs dsts channels ids procs)
   (good-channels-p
    srcs
    dsts
    (remove-message-from-channel j i channels)
    ids
    procs))
  :hints
  (("Goal"
    :induct (good-channels-p srcs dsts channels ids procs)
    :in-theory (disable remove-message-from-channel))))
;end support: remove-consumed-recovery-message


;start support: recovery-message-goodness
;; A recovery message is good when its sid is known by every process.

(defthm good-msg-p-of-get-msg-from-channel-when-recovery
  (implies
   (and (equal (msg-type (get-msg-from-channel j i channels))
               :recovery)
        (all-procs-have-snapshot-id-p
         (sid (get-msg-from-channel j i channels))
         ids
         procs))
   (good-msg-p
    (get-msg-from-channel j i channels)
    ids
    procs)))

(defthm good-msg-p-of-get-msg-from-channel-when-recovery-after-first-recovery-update
  (implies
   (and (equal (msg-type (get-msg-from-channel j i channels))
               :recovery)
        (all-procs-have-snapshot-id-p
         (sid (get-msg-from-channel j i channels))
         ids
         procs))
   (good-msg-p
    (get-msg-from-channel j i channels)
    ids
    (s i
       (update-proc-for-first-recovery-msg
        (g i procs)
        (sid (get-msg-from-channel j i channels))
        j)
       procs))))
;end support: recovery-message-goodness


;start support: updated-procs-compatible-with-channel-preservation
;; The generic two-process channel-send lemma needs two compatibility facts:

(defthm nbrs-to-of-g-of-s-update-proc-for-first-recovery-msg
  (equal
   (g :nbrs-to
      (g x
         (s k
            (update-proc-for-first-recovery-msg
             (g k procs)
             sid
             j)
            procs)))
   (g :nbrs-to
      (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))

(defthm same-nbrs-to-p-of-update-proc-for-first-recovery-msg
  (same-nbrs-to-p
   srcs
   procs
   (s k
      (update-proc-for-first-recovery-msg
       (g k procs)
       sid
       j)
      procs))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-first-recovery-msg))))

(defthm same-nbrs-to-p-commutative
  (implies
   (same-nbrs-to-p ids procs1 procs2)
   (same-nbrs-to-p ids procs2 procs1))
  :hints
  (("Goal"
    :induct (same-nbrs-to-p ids procs1 procs2))))

(defthm snapshot-ids-of-g-of-s-update-proc-for-first-recovery-msg
  (equal
   (g :snapshot-ids
      (g x
         (s k
            (update-proc-for-first-recovery-msg
             (g k procs)
             sid
             j)
            procs)))
   (g :snapshot-ids
      (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))

(defthm snapshot-ids-subset-procs-p-of-update-proc-for-first-recovery-msg
  (snapshot-ids-subset-procs-p
   ids
   procs
   (s k
      (update-proc-for-first-recovery-msg
       (g k procs)
       sid
       j)
      procs))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-first-recovery-msg))))

(defthm snapshot-ids-subset-procs-p-of-update-proc-for-first-recovery-msg-reverse
  (snapshot-ids-subset-procs-p
   ids
   (s k
      (update-proc-for-first-recovery-msg
       (g k procs)
       sid
       j)
      procs)
   procs)
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-first-recovery-msg))))

(defthm all-procs-have-snapshot-id-p-of-update-proc-for-first-recovery-msg
  (implies
   (all-procs-have-snapshot-id-p sid0 ids procs)
   (all-procs-have-snapshot-id-p
    sid0
    ids
    (s k
       (update-proc-for-first-recovery-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-first-recovery-msg))))
;end support: updated-procs-compatible-with-channel-preservation


;start target: good-state-p-of-handle-first-recovery-msg
;; Main target theorem for the first recovery-message case.

(defthm nbrs-from-of-g-of-s-update-proc-for-first-recovery-msg
  (equal
   (nbrs-from
    (g x
       (s k
          (update-proc-for-first-recovery-msg
           (g k procs)
           sid
           j)
          procs)))
   (nbrs-from
    (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))


(defthm nbrs-to-of-g-of-s-update-proc-for-first-recovery-msg
  (equal
   (nbrs-to
    (g x
       (s k
          (update-proc-for-first-recovery-msg
           (g k procs)
           sid
           j)
          procs)))
   (nbrs-to
    (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))


(defthm nbrs-from-to-consistent-for-one-dst-p-of-update-proc-for-first-recovery-msg
  (implies
   (nbrs-from-to-consistent-for-one-dst-p i srcs procs)
   (nbrs-from-to-consistent-for-one-dst-p
    i
    srcs
    (s k
       (update-proc-for-first-recovery-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-first-recovery-msg)
    :induct
    (nbrs-from-to-consistent-for-one-dst-p i srcs procs))))


(defthm nbrs-from-to-consistent-p-of-update-proc-for-first-recovery-msg
  (implies
   (nbrs-from-to-consistent-p dsts srcs procs)
   (nbrs-from-to-consistent-p
    dsts
    srcs
    (s k
       (update-proc-for-first-recovery-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-first-recovery-msg)
    :induct
    (nbrs-from-to-consistent-p dsts srcs procs))))


(defthm nbrs-to-from-consistent-for-one-src-p-of-update-proc-for-first-recovery-msg
  (implies
   (nbrs-to-from-consistent-for-one-src-p x dsts procs)
   (nbrs-to-from-consistent-for-one-src-p
    x
    dsts
    (s k
       (update-proc-for-first-recovery-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-first-recovery-msg)
    :induct
    (nbrs-to-from-consistent-for-one-src-p x dsts procs))))


(defthm nbrs-to-from-consistent-p-of-update-proc-for-first-recovery-msg
  (implies
   (nbrs-to-from-consistent-p srcs dsts procs)
   (nbrs-to-from-consistent-p
    srcs
    dsts
    (s k
       (update-proc-for-first-recovery-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-first-recovery-msg)
    :induct
    (nbrs-to-from-consistent-p srcs dsts procs))))

;; (defthm good-state-p-of-handle-first-recovery-msg
;;   (implies
;;    (and (good-state-p st)

;;         ;; Valid receiver and sender.
;;         (memberp i (proc-ids st))
;;         (memberp j (proc-ids st))
;;         (memberp j (nbrs-from (g i (procs st))))

;; ;; msg is the first message on channel j -> i.

;;         ;; This is really a recovery message.
;;         (equal (msg-type msg) :recovery)

;;         ;; First recovery-message case: receiver has not started recovery yet.
;;         (equal (proc-status (g i (procs st))) :normal)

;; ;; The receiver has the snapshot being recovered.

;;         ;; New recovery-message invariant: the sid must be known by all
;;         ;; processes, because this message may be forwarded.
;;         (all-procs-have-snapshot-id-p
;;          (sid msg)
;;          (proc-ids st)
;;          (procs st)))
;;    (good-state-p
;;     (handle-first-recovery-msg st i j msg)))
;;   :hints
;;   (("Goal"
;;     :in-theory (disable good-proc-p
;;                         remove-message-from-channel
;;                         get-msg-from-channel
;;                         update-proc-for-first-recovery-msg))))
;; ;end target: good-state-p-of-handle-first-recovery-msg


;; Non-first recovery-message preservation

;start support: non-first-recovery-process-field-preservation
;; Field-level facts about update-proc-for-non-first-recovery-msg.

(defthm nbrs-from-of-update-proc-for-non-first-recovery-msg
  (equal (g :nbrs-from
            (update-proc-for-non-first-recovery-msg p j))
         (g :nbrs-from p)))

(defthm nbrs-to-of-update-proc-for-non-first-recovery-msg
  (equal (g :nbrs-to
            (update-proc-for-non-first-recovery-msg p j))
         (g :nbrs-to p)))

(defthm waiting-recovery-from-of-update-proc-for-non-first-recovery-msg
  (equal (g :waiting-recovery-from
            (update-proc-for-non-first-recovery-msg p j))
         (remove-from-list (g :waiting-recovery-from p) j)))

(defthm snapshot-ids-of-update-proc-for-non-first-recovery-msg
  (equal (g :snapshot-ids
            (update-proc-for-non-first-recovery-msg p j))
         (g :snapshot-ids p)))

(defthm counter-of-update-proc-for-non-first-recovery-msg
  (equal (g :counter
            (update-proc-for-non-first-recovery-msg p j))
         (g :counter p)))

(defthm local-state-of-update-proc-for-non-first-recovery-msg
  (equal (g :local-state
            (update-proc-for-non-first-recovery-msg p j))
         (g :local-state p)))

;; The only status change is controlled by the remaining wait list.
(defthm proc-status-of-update-proc-for-non-first-recovery-msg
  (equal (g :proc-status
            (update-proc-for-non-first-recovery-msg p j))
         (if (endp (remove-from-list (g :waiting-recovery-from p) j))
             :normal
             :recovering)))

;; Removing an element from a list cannot introduce a new element outside ys.
(defthm subset-of-remove-from-list-when-subset
  (implies
   (subset xs ys)
   (subset (remove-from-list xs a)
           ys)))

;end support: non-first-recovery-process-field-preservation


;start support: non-first-recovery-process-wellformedness
;; Lift the field-level facts to the full process invariant.

(defthm good-snapshots-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (good-snapshots-p snapshot-ids p nbrs-from ids)
   (good-snapshots-p
    snapshot-ids
    (update-proc-for-non-first-recovery-msg p j)
    nbrs-from
    ids)))

(defthm good-proc-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (good-proc-p p ids)
   (good-proc-p
    (update-proc-for-non-first-recovery-msg p j)
    ids))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-recovery-msg))))

;end support: non-first-recovery-process-wellformedness


;start support: non-first-recovery-updated-procs-field-compatibility
;; Facts about reading fields from the process table after updating one process.

(defthm nbrs-to-of-g-of-s-update-proc-for-non-first-recovery-msg
  (equal
   (g :nbrs-to
      (g x
         (s k
            (update-proc-for-non-first-recovery-msg
             (g k procs)
             j)
            procs)))
   (g :nbrs-to
      (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))

(defthm snapshot-ids-of-g-of-s-update-proc-for-non-first-recovery-msg
  (equal
   (g :snapshot-ids
      (g x
         (s k
            (update-proc-for-non-first-recovery-msg
             (g k procs)
             j)
            procs)))
   (g :snapshot-ids
      (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))

;end support: non-first-recovery-updated-procs-field-compatibility


;start support: non-first-recovery-message-goodness-preservation
;; Updating a process for a non-first recovery message does not change any process's snapshot-id list.

(defthm some-proc-has-snapshot-id-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (some-proc-has-snapshot-id-p sid ids procs)
   (some-proc-has-snapshot-id-p
    sid
    ids
    (s k
       (update-proc-for-non-first-recovery-msg
        (g k procs)
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-recovery-msg))))

(defthm all-procs-have-snapshot-id-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (all-procs-have-snapshot-id-p sid ids procs)
   (all-procs-have-snapshot-id-p
    sid
    ids
    (s k
       (update-proc-for-non-first-recovery-msg
        (g k procs)
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-recovery-msg))))

(defthm good-msg-list-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (good-msg-list-p msgs ids procs)
   (good-msg-list-p
    msgs
    ids
    (s k
       (update-proc-for-non-first-recovery-msg
        (g k procs)
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-recovery-msg))))

;end support: non-first-recovery-message-goodness-preservation


;start support: non-first-recovery-channel-table-preservation
;; Lift message-goodness preservation to channel rows and then to the whole channel table.

(defthm good-channel-row-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (good-channel-row-p src dsts channels ids procs)
   (good-channel-row-p
    src
    dsts
    channels
    ids
    (s k
       (update-proc-for-non-first-recovery-msg
        (g k procs)
        j)
       procs)))
  :hints
  (("Goal"
    :induct (good-channel-row-p src dsts channels ids procs)
    :in-theory
    (disable update-proc-for-non-first-recovery-msg))))

(defthm good-channels-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (good-channels-p srcs dsts channels ids procs)
   (good-channels-p
    srcs
    dsts
    channels
    ids
    (s k
       (update-proc-for-non-first-recovery-msg
        (g k procs)
        j)
       procs)))
  :hints
  (("Goal"
    :induct (good-channels-p srcs dsts channels ids procs)
    :in-theory (disable update-proc-for-non-first-recovery-msg))))

;end support: non-first-recovery-channel-table-preservation


;start target: good-state-p-of-handle-non-first-recovery-msg
;; Target theorem for the non-first recovery-message handler.

(defthm nbrs-from-of-g-of-s-update-proc-for-non-first-recovery-msg
  (equal
   (nbrs-from
    (g x
       (s k
          (update-proc-for-non-first-recovery-msg
           (g k procs)
           j)
          procs)))
   (nbrs-from
    (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))


(defthm nbrs-to-of-g-of-s-update-proc-for-non-first-recovery-msg
  (equal
   (nbrs-to
    (g x
       (s k
          (update-proc-for-non-first-recovery-msg
           (g k procs)
           j)
          procs)))
   (nbrs-to
    (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))


(defthm nbrs-from-to-consistent-for-one-dst-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (nbrs-from-to-consistent-for-one-dst-p i srcs procs)
   (nbrs-from-to-consistent-for-one-dst-p
    i
    srcs
    (s k
       (update-proc-for-non-first-recovery-msg
        (g k procs)
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-recovery-msg)
    :induct
    (nbrs-from-to-consistent-for-one-dst-p i srcs procs))))


(defthm nbrs-from-to-consistent-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (nbrs-from-to-consistent-p dsts srcs procs)
   (nbrs-from-to-consistent-p
    dsts
    srcs
    (s k
       (update-proc-for-non-first-recovery-msg
        (g k procs)
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-recovery-msg)
    :induct
    (nbrs-from-to-consistent-p dsts srcs procs))))


(defthm nbrs-to-from-consistent-for-one-src-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (nbrs-to-from-consistent-for-one-src-p x dsts procs)
   (nbrs-to-from-consistent-for-one-src-p
    x
    dsts
    (s k
       (update-proc-for-non-first-recovery-msg
        (g k procs)
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-recovery-msg)
    :induct
    (nbrs-to-from-consistent-for-one-src-p x dsts procs))))


(defthm nbrs-to-from-consistent-p-of-update-proc-for-non-first-recovery-msg
  (implies
   (nbrs-to-from-consistent-p srcs dsts procs)
   (nbrs-to-from-consistent-p
    srcs
    dsts
    (s k
       (update-proc-for-non-first-recovery-msg
        (g k procs)
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-recovery-msg)
    :induct
    (nbrs-to-from-consistent-p srcs dsts procs))))

;; (defthm good-state-p-of-handle-non-first-recovery-msg
;;   (implies
;;    (and (good-state-p st)

;;         ;; Valid receiver and sender.
;;         (memberp i (proc-ids st))
;;         (memberp j (proc-ids st))
;;         (memberp j (nbrs-from (g i (procs st))))

;; ;; msg is the first message on channel j -> i.

;;         ;; This is really a recovery message.
;;         (equal (msg-type msg) :recovery)

;;         ;; Non-first recovery-message case:
;;         ;; receiver is already recovering or crashed, but not normal.
;;         (not (equal (proc-status (g i (procs st))) :normal)))
;;    (good-state-p
;;     (handle-non-first-recovery-msg st i j msg)))
;;   :hints
;;   (("Goal"
;;     :in-theory (disable good-proc-p
;;                         remove-message-from-channel
;;                         get-msg-from-channel
;;                         update-proc-for-non-first-recovery-msg))))

;end target: good-state-p-of-handle-non-first-recovery-msg


;start target: good-state-p-of-handle-recovery-msg
;; Dispatcher theorem for handle-recovery-msg.

;; (defthm good-state-p-of-handle-recovery-msg
;;   (implies
;;    (and (good-state-p st)

;;         ;; Valid receiver and sender.
;;         (memberp i (proc-ids st))
;;         (memberp j (proc-ids st))
;;         (memberp j (nbrs-from (g i (procs st))))

;; ;; msg is the first message on channel j -> i.

;;         ;; This is really a recovery message.
;;         (equal (msg-type msg) :recovery)

;;         ;; Strengthened recovery-message side condition:
;;         ;; recovery sid must be known by every process.
;;         (all-procs-have-snapshot-id-p
;;          (sid msg)
;;          (proc-ids st)
;;          (procs st)))
;;    (good-state-p
;;     (handle-recovery-msg st i j msg)))
;;   :hints
;;   (("Goal"
;;     :in-theory
;;     (disable good-state-p
;;              good-proc-p
;;              handle-first-recovery-msg
;;              handle-non-first-recovery-msg
;;              remove-message-from-channel
;;              get-msg-from-channel
;;              update-proc-for-first-recovery-msg
;;              update-proc-for-non-first-recovery-msg))))

;end target: good-state-p-of-handle-recovery-msg


(defthm nbrs-to-of-update-proc-for-first-marker-msg
  (equal (g :nbrs-to
            (update-proc-for-first-marker-msg p sid j))
         (g :nbrs-to p)))

(defthm nbrs-from-of-update-proc-for-first-marker-msg
  (equal (g :nbrs-from
            (update-proc-for-first-marker-msg p sid j))
         (g :nbrs-from p)))

(defthm good-snapshot-ids-p-of-update-proc-for-first-marker-msg
  (implies
   (and
    (good-snapshot-ids-p (g :snapshot-ids p) ids)
    (good-snapshot-id-p sid ids))
   (good-snapshot-ids-p
    (g :snapshot-ids
       (update-proc-for-first-marker-msg p sid j))
    ids)))

(defthm waiting-recovery-from-of-update-proc-for-first-marker-msg
  (equal (g :waiting-recovery-from
            (update-proc-for-first-marker-msg p sid j))
         (g :waiting-recovery-from p)))

(defthm counter-of-update-proc-for-first-marker-msg
  (equal (g :counter
            (update-proc-for-first-marker-msg p sid j))
         (g :counter p)))



(defthm good-snapshots-p-of-update-proc-for-first-marker-msg
  (implies
   (and
    (good-snapshots-p (snapshot-ids p)
                      p
                      (nbrs-from p)
                      ids)
    (true-listp (nbrs-from p))
    (uniquep (nbrs-from p)))
   (good-snapshots-p
    (snapshot-ids
     (update-proc-for-first-marker-msg p sid j))
    (update-proc-for-first-marker-msg p sid j)
    (nbrs-from p)
    ids))
    :hints
  (("Goal"
    :in-theory
    (disable 
             install-snapshot-entry
             make-snapshot-entry
             good-snapshot-entry-p))))

(defthm true-listp-snapshot-ids-of-update-proc-for-first-marker-msg
  (implies
   (true-listp (snapshot-ids p))
   (true-listp
    (snapshot-ids
     (update-proc-for-first-marker-msg p sid j)))))

(defthm uniquep-snapshot-ids-of-update-proc-for-first-marker-msg
  (implies
   (and (uniquep (snapshot-ids p))
        (not (memberp sid (snapshot-ids p))))
   (uniquep
    (snapshot-ids
     (update-proc-for-first-marker-msg p sid j)))))

(defthm memberp-init-snapshot-ids-of-update-proc-for-first-marker-msg
  (implies
   (memberp :init (snapshot-ids p))
   (memberp
    :init
    (snapshot-ids
     (update-proc-for-first-marker-msg p sid j)))))

(defthm proc-status-of-update-proc-for-first-marker-msg
  (equal (proc-status
          (update-proc-for-first-marker-msg p sid j))
         (proc-status p)))

(defthm good-proc-p-of-update-proc-for-first-marker-msg
  (implies
   (and
    (good-proc-p p ids)
    ;; First-marker case: this process does not already know sid.
    (not (memberp sid (snapshot-ids p)))
    ;; The sid carried by the marker is structurally valid.
    (good-snapshot-id-p sid ids))
   (good-proc-p
    (update-proc-for-first-marker-msg p sid j)
    ids))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-first-marker-msg
             make-snapshot-entry
             install-snapshot-entry
             good-snapshot-entry-p
	     good-snapshot-id-p
             good-snapshots-p))))

(defthm good-procs-p-of-update-proc-for-first-marker-msg-from-some-proc-has-sid
  (implies
   (and
    (good-procs-p ids procs ids)
    (memberp i ids)
    (not (memberp sid
                  (snapshot-ids (g i procs))))
    (good-snapshot-id-p sid ids))
   (good-procs-p
    ids
    (s i
       (update-proc-for-first-marker-msg
        (g i procs)
        sid
        j)
       procs)
    ids))
  :hints
  (("Goal"
    :in-theory
    (disable good-proc-p
             update-proc-for-first-marker-msg))))







(defthm good-snapshot-id-p-when-memberp-good-snapshot-ids-p
  (implies
   (and (memberp sid snapshot-ids)
        (good-snapshot-ids-p snapshot-ids ids))
   (good-snapshot-id-p sid ids)))

(defthm good-snapshot-ids-p-of-snapshot-ids-when-good-proc-p
  (implies
   (good-proc-p p ids)
   (good-snapshot-ids-p (snapshot-ids p) ids)))

(defthm good-snapshot-ids-p-of-snapshot-ids-when-good-proc-p
  (implies
   (good-proc-p p ids)
   (good-snapshot-ids-p (snapshot-ids p) ids)))

(defthm good-snapshot-id-p-when-memberp-snapshot-ids-of-good-proc
  (implies
   (and (good-proc-p p ids)
        (memberp sid (snapshot-ids p)))
   (good-snapshot-id-p sid ids))
  :hints (("Goal"
	   :in-theory (disable good-snapshot-id-p))))

(defun first-proc-with-snapshot-id (sid ids procs)
  (if (endp ids)
      nil
    (let* ((i (first ids))
           (p (g i procs)))
      (if (memberp sid (snapshot-ids p))
          i
        (first-proc-with-snapshot-id sid
                                     (rest ids)
                                     procs)))))


(defthm memberp-of-first-proc-with-snapshot-id
  (implies
   (some-proc-has-snapshot-id-p sid ids procs)
   (memberp
    (first-proc-with-snapshot-id sid ids procs)
    ids)))

(defthm good-first-proc-with-snapshot-id-when-some-proc-has-snapshot-id-p
  (implies
   (and (some-proc-has-snapshot-id-p sid ids procs)
         (good-procs-p ids procs ids))
   (good-proc-p (g (first-proc-with-snapshot-id sid ids procs) procs) ids)))

(defthm first-proc-with-snapshot-id-has-sid
  (implies
   (some-proc-has-snapshot-id-p sid ids procs)
   (memberp
    sid
    (snapshot-ids
     (g (first-proc-with-snapshot-id sid ids procs)
        procs)))))


(defthm good-snapshot-id-p-when-some-proc-has-snapshot-id-p
  (implies
   (and
    (some-proc-has-snapshot-id-p sid ids procs)
    (good-procs-p ids procs ids))
   (good-snapshot-id-p sid ids))
  :hints
  (("Goal"
    :use
    ((:instance good-snapshot-id-p-when-memberp-snapshot-ids-of-good-proc
                (p (g (first-proc-with-snapshot-id sid ids procs)
                      procs))
                (sid sid)
                (ids ids))

     (:instance good-first-proc-with-snapshot-id-when-some-proc-has-snapshot-id-p
                (sid sid)
                (ids ids)
                (procs procs))

     (:instance first-proc-with-snapshot-id-has-sid
                (sid sid)
                (ids ids)
                (procs procs))))))



(defthm memberp-snapshot-ids-of-g-after-update-proc-for-first-marker-msg
  (implies
   (memberp sid0
            (snapshot-ids (g k procs)))
   (memberp sid0
            (snapshot-ids
             (g k
                (s i
                   (update-proc-for-first-marker-msg
                    (g i procs)
                    sid
                    j)
                   procs)))))
  :hints
  (("Goal"
    :cases ((equal k i)))))

(defthm good-msg-p-of-get-msg-from-channel-when-marker-after-first-marker-update
  (implies
   (and (equal (msg-type (get-msg-from-channel j i channels))
               :marker)
        (some-proc-has-snapshot-id-p
         (sid (get-msg-from-channel j i channels))
         ids
         procs))
   (good-msg-p
    (get-msg-from-channel j i channels)
    ids
    (s i
       (update-proc-for-first-marker-msg
        (g i procs)
        (sid (get-msg-from-channel j i channels))
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory
    (disable get-msg-from-channel update-proc-for-first-marker-msg))))








(defthm memberp-snapshot-ids-of-g-of-s-update-proc-for-first-marker-msg
  (implies
   (memberp sid0
            (g :snapshot-ids
               (g x procs)))
   (memberp sid0
            (g :snapshot-ids
               (g x
                  (s k
                     (update-proc-for-first-marker-msg
                      (g k procs)
                      sid
                      j)
                     procs)))))
  :hints
  (("Goal"
    :cases ((equal x k)))))

(defthm some-proc-has-snapshot-id-p-of-update-proc-for-first-marker-msg
  (implies
   (some-proc-has-snapshot-id-p sid0 ids procs)
   (some-proc-has-snapshot-id-p
    sid0
    ids
    (s k
       (update-proc-for-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :induct (some-proc-has-snapshot-id-p sid0 ids procs)
    :in-theory
    (disable update-proc-for-first-marker-msg))))

(defthm all-procs-have-snapshot-id-p-of-update-proc-for-first-marker-msg
  (implies
   (all-procs-have-snapshot-id-p sid0 ids procs)
   (all-procs-have-snapshot-id-p
    sid0
    ids
    (s k
       (update-proc-for-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-first-marker-msg))))

(defthm nbrs-to-of-g-of-s-update-proc-for-first-marker-msg
  (equal
   (g :nbrs-to
      (g x
         (s k
            (update-proc-for-first-marker-msg
             (g k procs)
             sid
             j)
            procs)))
   (g :nbrs-to
      (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))

(defthm same-nbrs-to-p-of-update-proc-for-first-marker-msg
  (same-nbrs-to-p
   srcs
   procs
   (s k
      (update-proc-for-first-marker-msg
       (g k procs)
       sid
       j)
      procs))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-first-marker-msg))))

(defthm snapshot-ids-of-g-of-s-update-proc-for-first-marker-msg
  (equal
   (g :snapshot-ids
      (g x
         (s k
            (update-proc-for-first-marker-msg
             (g k procs)
             sid
             j)
            procs)))
   (if (equal x k)
       (add-snapshot-id sid
                        (g :snapshot-ids
                           (g k procs)))
     (g :snapshot-ids
        (g x procs))))
  :hints
  (("Goal"
    :cases ((equal x k)))))

(defthm subset-snapshot-ids-of-g-of-s-update-proc-for-first-marker-msg
  (subset
   (g :snapshot-ids
      (g x procs))
   (g :snapshot-ids
      (g x
         (s k
            (update-proc-for-first-marker-msg
             (g k procs)
             sid
             j)
            procs))))
  :hints
  (("Goal"
    :cases ((equal x k)))))

(defthm snapshot-ids-subset-procs-p-of-update-proc-for-first-marker-msg
  (snapshot-ids-subset-procs-p
   ids
   procs
   (s k
      (update-proc-for-first-marker-msg
       (g k procs)
       sid
       j)
      procs))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-first-marker-msg))))

(defthm snapshot-ids-subset-procs-p-of-update-proc-for-first-marker-msg
  (snapshot-ids-subset-procs-p
   ids
   procs
   (s k
      (update-proc-for-first-marker-msg
       (g k procs)
       sid
       j)
      procs))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-first-marker-msg))))



(defthm nbrs-from-of-g-of-s-update-proc-for-first-marker-msg
  (equal
   (nbrs-from
    (g x
       (s k
          (update-proc-for-first-marker-msg
           (g k procs)
           sid
           j)
          procs)))
   (nbrs-from
    (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))


(defthm nbrs-to-of-g-of-s-update-proc-for-first-marker-msg
  (equal
   (nbrs-to
    (g x
       (s k
          (update-proc-for-first-marker-msg
           (g k procs)
           sid
           j)
          procs)))
   (nbrs-to
    (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))


(defthm nbrs-from-to-consistent-for-one-dst-p-of-update-proc-for-first-marker-msg
  (implies
   (nbrs-from-to-consistent-for-one-dst-p i srcs procs)
   (nbrs-from-to-consistent-for-one-dst-p
    i
    srcs
    (s k
       (update-proc-for-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-first-marker-msg)
    :induct
    (nbrs-from-to-consistent-for-one-dst-p i srcs procs))))


(defthm nbrs-from-to-consistent-p-of-update-proc-for-first-marker-msg
  (implies
   (nbrs-from-to-consistent-p dsts srcs procs)
   (nbrs-from-to-consistent-p
    dsts
    srcs
    (s k
       (update-proc-for-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-first-marker-msg)
    :induct
    (nbrs-from-to-consistent-p dsts srcs procs))))


(defthm nbrs-to-from-consistent-for-one-src-p-of-update-proc-for-first-marker-msg
  (implies
   (nbrs-to-from-consistent-for-one-src-p x dsts procs)
   (nbrs-to-from-consistent-for-one-src-p
    x
    dsts
    (s k
       (update-proc-for-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-first-marker-msg)
    :induct
    (nbrs-to-from-consistent-for-one-src-p x dsts procs))))


(defthm nbrs-to-from-consistent-p-of-update-proc-for-first-marker-msg
  (implies
   (nbrs-to-from-consistent-p srcs dsts procs)
   (nbrs-to-from-consistent-p
    srcs
    dsts
    (s k
       (update-proc-for-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-first-marker-msg)
    :induct
    (nbrs-to-from-consistent-p srcs dsts procs))))


;; (defthm good-state-p-of-handle-first-marker-msg
;;   (implies
;;    (and
;;     (good-state-p st)

;;     ;; valid receiver and sender
;;     (memberp i (proc-ids st))
;;     (memberp j (proc-ids st))
;;     (memberp j (nbrs-from (g i (procs st))))

;; ;; msg is the head of channel j -> i

;;     ;; marker-message case
;;     (equal (msg-type msg) :marker)

;; ;; first-marker case: receiver i does not yet know this sid

;;     ;; the marker sid is already known somewhere in the system
;;     (some-proc-has-snapshot-id-p
;;      (sid msg)
;;      (proc-ids st)
;;      (procs st)))
;;    (good-state-p
;;     (handle-first-marker-msg st i j msg)))
;;   :hints
;;   (("Goal"
;;     :in-theory
;;     (disable good-proc-p
;;              update-proc-for-first-marker-msg
;;              get-msg-from-channel
;;              remove-message-from-channel
;;              send-msg-all-outgoing-channels
;;              install-snapshot-entry
;;              make-snapshot-entry))))












(defthm nbrs-from-of-update-proc-for-non-first-marker-msg
  (equal (g :nbrs-from
            (update-proc-for-non-first-marker-msg p sid j))
         (g :nbrs-from p)))

(defthm waiting-recovery-from-of-update-proc-for-non-first-marker-msg
  (equal (g :waiting-recovery-from
            (update-proc-for-non-first-marker-msg p sid j))
         (g :waiting-recovery-from p)))

(defthm nbrs-to-of-update-proc-for-non-first-marker-msg
  (equal (g :nbrs-to
            (update-proc-for-non-first-marker-msg p sid j))
         (g :nbrs-to p)))

(defthm counter-of-update-proc-for-non-first-marker-msg
  (equal (g :counter
            (update-proc-for-non-first-marker-msg p sid j))
         (g :counter p)))

(defthm snapshot-ids-of-update-proc-for-non-first-marker-msg
  (equal (g :snapshot-ids
            (update-proc-for-non-first-marker-msg p sid j))
         (g :snapshot-ids p)))

(defthm good-snapshot-ids-p-of-update-proc-for-non-first-marker-msg
  (implies
   (good-snapshot-ids-p (g :snapshot-ids p) ids)
   (good-snapshot-ids-p
    (g :snapshot-ids
       (update-proc-for-non-first-marker-msg p sid j))
    ids)))




(defthm good-snapshots-p-of-set-sid-done-waiting-nil
  (implies
   (and
    (good-snapshots-p snapshot-ids p nbrs-from ids)
    (memberp sid snapshot-ids))
   (good-snapshots-p
    snapshot-ids
    (s :snapshots
       (s sid
          (s :status
             :done
             (s :waiting-marker-from
                nil
                (g sid (g :snapshots p))))
          (g :snapshots p))
       p)
    nbrs-from
    ids))
  :hints
  (("Goal"
    :induct (good-snapshots-p snapshot-ids p nbrs-from ids))
   ("Subgoal *1/2"
    :cases ((equal sid (car snapshot-ids))))))

(defthm good-snapshots-p-of-set-sid-waiting-marker-from-remove
  (implies
   (and
    (good-snapshots-p snapshot-ids p nbrs-from ids)
    (memberp sid snapshot-ids))
   (good-snapshots-p
    snapshot-ids
    (s :snapshots
       (s sid
          (s :status
             (g :status (g sid (g :snapshots p)))
             (s :waiting-marker-from
                (remove-from-list
                 (g :waiting-marker-from
                    (g sid (g :snapshots p)))
                 j)
                (g sid (g :snapshots p))))
          (g :snapshots p))
       p)
    nbrs-from
    ids))
  :hints
  (("Goal"
    :induct (good-snapshots-p snapshot-ids p nbrs-from ids))
   ("Subgoal *1/2"
    :cases ((equal sid (car snapshot-ids))))))

(defthm good-snapshots-p-of-update-proc-for-non-first-marker-msg
  (implies
   (and
    (good-snapshots-p snapshot-ids
                      p
                      nbrs-from
                      ids)
    (memberp sid snapshot-ids))
   (good-snapshots-p
    snapshot-ids
    (update-proc-for-non-first-marker-msg p sid j)
    nbrs-from
    ids)))


(defthm proc-status-of-update-proc-for-non-first-marker-msg
  (equal (g :proc-status
            (update-proc-for-non-first-marker-msg p sid j))
         (g :proc-status p)))

(defthm good-proc-p-of-update-proc-for-non-first-marker-msg
  (implies
   (and
    (good-proc-p p ids)

    ;; Non-first marker case:
    ;; this process already has an entry for sid.
    (memberp sid (snapshot-ids p)))
   (good-proc-p
    (update-proc-for-non-first-marker-msg p sid j)
    ids))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-non-first-marker-msg
             set-snapshot-entry
             good-snapshot-entry-p
             good-snapshots-p))))




(defthm good-procs-p-of-update-proc-for-non-first-marker-msg
  (implies
   (and
    (good-procs-p ids procs all-ids)
    (memberp i ids)

    ;; sid already exists at process i
    (memberp sid
             (snapshot-ids (g i procs))))
   (good-procs-p
    ids
    (s i
       (update-proc-for-non-first-marker-msg
        (g i procs)
        sid
        j)
       procs)
    all-ids))
  :hints
  (("Goal"
    :in-theory
    (disable
             good-procs-p
             update-proc-for-non-first-marker-msg
            ))))




;start support: non-first-marker-updated-procs-field-compatibility
;; Facts about reading fields from the process table after updating one process.

(defthm nbrs-to-of-g-of-s-update-proc-for-non-first-marker-msg
  (equal
   (g :nbrs-to
      (g x
         (s k
            (update-proc-for-non-first-marker-msg
             (g k procs)
             sid
             j)
            procs)))
   (g :nbrs-to
      (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))

(defthm snapshot-ids-of-g-of-s-update-proc-for-non-first-marker-msg
  (equal
   (g :snapshot-ids
      (g x
         (s k
            (update-proc-for-non-first-marker-msg
             (g k procs)
             sid
             j)
            procs)))
   (g :snapshot-ids
      (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k))
   )))

;end support: non-first-marker-updated-procs-field-compatibility


;start support: non-first-marker-message-goodness-preservation
;; Updating a process for a non-first marker message does not change any process's snapshot-id list.

(defthm some-proc-has-snapshot-id-p-of-update-proc-for-non-first-marker-msg
  (implies
   (some-proc-has-snapshot-id-p sid0 ids procs)
   (some-proc-has-snapshot-id-p
    sid0
    ids
    (s k
       (update-proc-for-non-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-non-first-marker-msg))))

(defthm all-procs-have-snapshot-id-p-of-update-proc-for-non-first-marker-msg
  (implies
   (all-procs-have-snapshot-id-p sid0 ids procs)
   (all-procs-have-snapshot-id-p
    sid0
    ids
    (s k
       (update-proc-for-non-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-non-first-marker-msg))))

(defthm good-msg-p-of-update-proc-for-non-first-marker-msg
  (implies
   (good-msg-p msg ids procs)
   (good-msg-p
    msg
    ids
    (s k
       (update-proc-for-non-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-non-first-marker-msg))))

(defthm good-msg-list-p-of-update-proc-for-non-first-marker-msg
  (implies
   (good-msg-list-p msgs ids procs)
   (good-msg-list-p
    msgs
    ids
    (s k
       (update-proc-for-non-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-non-first-marker-msg))))

;end support: non-first-marker-message-goodness-preservation


;start support: non-first-marker-channel-table-preservation
;; Lift message-goodness preservation to channel rows and then to the whole channel table.

(defthm good-channel-row-p-of-update-proc-for-non-first-marker-msg
  (implies
   (good-channel-row-p src dsts channels ids procs)
   (good-channel-row-p
    src
    dsts
    channels
    ids
    (s k
       (update-proc-for-non-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :induct (good-channel-row-p src dsts channels ids procs)
    :in-theory
    (disable update-proc-for-non-first-marker-msg))))

(defthm good-channels-p-of-update-proc-for-non-first-marker-msg
  (implies
   (good-channels-p srcs dsts channels ids procs)
   (good-channels-p
    srcs
    dsts
    channels
    ids
    (s k
       (update-proc-for-non-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :induct (good-channels-p srcs dsts channels ids procs)
    :in-theory
    (disable update-proc-for-non-first-marker-msg))))

;end support: non-first-marker-channel-table-preservation



(defthm nbrs-from-of-g-of-s-update-proc-for-non-first-marker-msg
  (equal
   (nbrs-from
    (g x
       (s k
          (update-proc-for-non-first-marker-msg
           (g k procs)
           sid
           j)
          procs)))
   (nbrs-from
    (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))


(defthm nbrs-to-of-g-of-s-update-proc-for-non-first-marker-msg
  (equal
   (nbrs-to
    (g x
       (s k
          (update-proc-for-non-first-marker-msg
           (g k procs)
           sid
           j)
          procs)))
   (nbrs-to
    (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))


(defthm nbrs-from-to-consistent-for-one-dst-p-of-update-proc-for-non-first-marker-msg
  (implies
   (nbrs-from-to-consistent-for-one-dst-p i srcs procs)
   (nbrs-from-to-consistent-for-one-dst-p
    i
    srcs
    (s k
       (update-proc-for-non-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-marker-msg)
    :induct
    (nbrs-from-to-consistent-for-one-dst-p i srcs procs))))


(defthm nbrs-from-to-consistent-p-of-update-proc-for-non-first-marker-msg
  (implies
   (nbrs-from-to-consistent-p dsts srcs procs)
   (nbrs-from-to-consistent-p
    dsts
    srcs
    (s k
       (update-proc-for-non-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-marker-msg)
    :induct
    (nbrs-from-to-consistent-p dsts srcs procs))))


(defthm nbrs-to-from-consistent-for-one-src-p-of-update-proc-for-non-first-marker-msg
  (implies
   (nbrs-to-from-consistent-for-one-src-p x dsts procs)
   (nbrs-to-from-consistent-for-one-src-p
    x
    dsts
    (s k
       (update-proc-for-non-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-marker-msg)
    :induct
    (nbrs-to-from-consistent-for-one-src-p x dsts procs))))


(defthm nbrs-to-from-consistent-p-of-update-proc-for-non-first-marker-msg
  (implies
   (nbrs-to-from-consistent-p srcs dsts procs)
   (nbrs-to-from-consistent-p
    srcs
    dsts
    (s k
       (update-proc-for-non-first-marker-msg
        (g k procs)
        sid
        j)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-non-first-marker-msg)
    :induct
    (nbrs-to-from-consistent-p srcs dsts procs))))


;; (defthm good-state-p-of-handle-non-first-marker-msg
;;   (implies
;;    (and
;;     (good-state-p st)

;;     ;; Valid receiver and sender.
;;     (memberp i (proc-ids st))
;;     (memberp j (proc-ids st))
;;     (memberp j (nbrs-from (g i (procs st))))

;; ;; msg is the first message on channel j -> i.

;;     ;; This is really a marker message.
;;     (equal (msg-type msg) :marker)

;;     ;; Non-first marker case:
;;     ;; receiver i already knows this snapshot id.
;;     (memberp (sid msg)
;;              (snapshot-ids (g i (procs st)))))
;;    (good-state-p
;;     (handle-non-first-marker-msg st i j msg)))
;;   :hints
;;   (("Goal"
;;     :in-theory
;;     (disable good-proc-p
;;              get-msg-from-channel
;;              remove-message-from-channel
;;              update-proc-for-non-first-marker-msg
;;              set-snapshot-entry))))



;; (defthm good-state-p-of-handle-marker-msg
;;   (implies
;;    (and
;;     (good-state-p st)

;;     ;; Valid receiver and sender.
;;     (memberp i (proc-ids st))
;;     (memberp j (proc-ids st))
;;     (memberp j (nbrs-from (g i (procs st))))
;;     ;; msg is the head of channel j -> i.
;;     (equal msg
;;            (get-msg-from-channel j i (channels st)))
;;     ;; This is really a marker message.
;;     (equal (msg-type msg) :marker)
;;      (some-proc-has-snapshot-id-p
;;       (sid msg)
;;       (proc-ids st)
;;       (procs st)))
;;    (good-state-p
;;     (handle-marker-msg st i j msg)))
;;   :hints
;;   (("Goal"
;;     :cases ((memberp (sid msg)
;;                      (snapshot-ids (g i (procs st)))))
;;     :in-theory
;;     (disable good-state-p
;;              handle-first-marker-msg
;;              handle-non-first-marker-msg))))




;; (defthm good-state-p-of-ignore-normal-msg
;;   (implies
;;    (good-state-p st)
;;    (good-state-p
;;     (ignore-normal-msg st i j msg)))
;;   :hints
;;   (("Goal"
;;     :in-theory
;;     (disable remove-message-from-channel
;;              good-proc-p))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Normal-message-core preservation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Normal-message process update preservation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;start support: normal-msg-core-field-preservation

(defthm nbrs-from-of-update-proc-for-normal-msg-core
  (equal (g :nbrs-from
            (update-proc-for-normal-msg-core p j msg))
         (g :nbrs-from p)))

(defthm nbrs-to-of-update-proc-for-normal-msg-core
  (equal (g :nbrs-to
            (update-proc-for-normal-msg-core p j msg))
         (g :nbrs-to p)))

(defthm proc-status-of-update-proc-for-normal-msg-core
  (equal (g :proc-status
            (update-proc-for-normal-msg-core p j msg))
         (g :proc-status p)))

(defthm waiting-recovery-from-of-update-proc-for-normal-msg-core
  (equal (g :waiting-recovery-from
            (update-proc-for-normal-msg-core p j msg))
         (g :waiting-recovery-from p)))

(defthm counter-of-update-proc-for-normal-msg-core
  (equal (g :counter
            (update-proc-for-normal-msg-core p j msg))
(g :counter p)))

(defthm snapshot-ids-of-update-proc-for-normal-msg-core
  (equal (g :snapshot-ids
            (update-proc-for-normal-msg-core p j msg))
         (g :snapshot-ids p)))

;end support: normal-msg-core-field-preservation

(defthm good-normal-msg-list-p-of-append-normal-msg
  (implies
   (and (good-normal-msg-list-p xs)
        (good-normal-msg-p msg))
   (good-normal-msg-list-p
    (append xs (list msg)))))



(defthm g-of-record-msg-in-snapshots-when-not-member
  (implies
   (not (memberp sid snapshot-ids))
   (equal
    (g sid
       (record-msg-in-snapshots snapshots
                                snapshot-ids
                                j
                                msg))
    (g sid snapshots))))

(defthm good-snapshot-entry-p-of-g-record-msg-in-snapshots-when-not-member
  (implies
   (and
    (not (memberp sid snapshot-ids))
    (good-snapshot-entry-p (g sid snapshots)
                           nbrs-from))
   (good-snapshot-entry-p
    (g sid
       (record-msg-in-snapshots snapshots
                                snapshot-ids
                                j
                                msg))
    nbrs-from)))

(defthm memberp-when-subset
  (implies
   (and (subset xs ys)
        (memberp a xs))
   (memberp a ys)))

(defthm good-channel-snapshot-record-p-of-s-append-normal-msg
  (implies
   (and
    (good-channel-snapshot-record-p nbrs-from cs)
    (memberp j nbrs-from)
    (equal (msg-type msg) :normal))
   (good-channel-snapshot-record-p
    nbrs-from
    (s j
       (append (g j cs)
               (list msg))
       cs)))
  :hints
  (("Goal"
    :induct (good-channel-snapshot-record-p nbrs-from cs))
   ("Subgoal *1/2"
    :cases ((equal j (car nbrs-from))))))


(defthm good-snapshot-entry-p-of-s-channel-snapshots-append-normal-msg
  (implies
   (and
    (good-snapshot-entry-p entry nbrs-from)
    (memberp j (snapshot-waiting-marker-from entry))
    (equal (msg-type msg) :normal))
   (good-snapshot-entry-p
    (s :channel-snapshots
       (s j
          (append (g j (snapshot-channel-snapshots entry))
                  (list msg))
          (snapshot-channel-snapshots entry))
       entry)
    nbrs-from)))


(defthm good-snapshots-p-of-record-msg-in-snapshots
  (implies
   (and
    (good-snapshots-p snapshot-ids p nbrs-from ids)
    (uniquep snapshot-ids)
    (equal (msg-type msg) :normal))
   (good-snapshots-p
    snapshot-ids
    (s :snapshots
       (record-msg-in-snapshots
        (snapshots p)
        snapshot-ids
        j
        msg)
       p)
    nbrs-from
    ids))
  :hints
  (("Goal"
    :induct (record-msg-in-snapshots
             (snapshots p)
             snapshot-ids
             j
             msg)
    :in-theory
    (disable good-snapshot-entry-p))))


(defthm good-snapshots-p-of-set-snapshots-after-set-local-state
  (implies
   (good-snapshots-p snapshot-ids
                     (s :snapshots snaps p)
                     nbrs-from
                     ids)
   (good-snapshots-p snapshot-ids
                     (s :snapshots snaps
                        (s :local-state val p))
                     nbrs-from
                     ids))
  :hints
  (("Goal"
    :induct (good-snapshots-p snapshot-ids p nbrs-from ids))))


(defthm good-snapshots-p-of-update-proc-for-normal-msg-core
  (implies
   (and
    (good-snapshots-p (snapshot-ids p)
                      p
                      (nbrs-from p)
                      ids)
    (equal (msg-type msg) :normal)
    (uniquep (snapshot-ids p)))
   (good-snapshots-p
    (snapshot-ids p)
    (update-proc-for-normal-msg-core p j msg)
    (nbrs-from p)
    ids))
  :hints
  (("Goal"
    :in-theory
    (disable record-msg-in-snapshots))))
;start target: good-proc-p-of-update-proc-for-normal-msg-core


(defthm good-proc-p-of-update-proc-for-normal-msg-core
  (implies
   (and
    (good-proc-p p ids)
    ;; handle-normal-msg-core only records normal/application messages
    ;; into open channel snapshots.
    (equal (msg-type msg) :normal))
   (good-proc-p
    (update-proc-for-normal-msg-core p j msg)
    ids))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-normal-msg-core
             record-msg-in-snapshots
             good-snapshots-p
             good-snapshot-entry-p))))

;end target: good-proc-p-of-update-proc-for-normal-msg-core

(defthm good-procs-p-of-update-proc-for-normal-msg-core
  (implies
   (and
    (good-procs-p ids procs all-ids)
    (memberp i ids)
    (equal (msg-type msg) :normal))
   (good-procs-p
    ids
    (s i
       (update-proc-for-normal-msg-core
        (g i procs)
        j
        msg)
       procs)
    all-ids))
   :hints
  (("Goal"
    :in-theory
    (disable good-proc-p
             update-proc-for-normal-msg-core
             record-msg-in-snapshots))))



(defthm nbrs-to-of-g-of-s-update-proc-for-normal-msg-core
  (equal
   (g :nbrs-to
      (g x
         (s k
            (update-proc-for-normal-msg-core
             (g k procs)
             j
             msg)
            procs)))
   (g :nbrs-to
      (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))


(defthm memberp-snapshot-ids-of-update-proc-for-normal-msg-core
  (equal
   (memberp sid0
            (g :snapshot-ids
               (update-proc-for-normal-msg-core p j msg)))
   (memberp sid0
            (g :snapshot-ids p))))

(defthm memberp-snapshot-ids-of-g-of-s-update-proc-for-normal-msg-core
  (equal
   (memberp sid0
            (g :snapshot-ids
               (g x
                  (s k
                     (update-proc-for-normal-msg-core
                      (g k procs)
                      j
                      msg)
                     procs))))
   (memberp sid0
            (g :snapshot-ids
               (g x procs))))
  :hints
  (("Goal"
    :cases ((equal x k)))))

(defthm some-proc-has-snapshot-id-p-of-update-proc-for-normal-msg-core
  (implies
   (some-proc-has-snapshot-id-p sid0 ids procs)
   (some-proc-has-snapshot-id-p
    sid0
    ids
    (s k
       (update-proc-for-normal-msg-core
        (g k procs)
        j
        msg)
       procs)))
    :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-normal-msg-core))))

(defthm all-procs-have-snapshot-id-p-of-update-proc-for-normal-msg-core
  (implies
   (all-procs-have-snapshot-id-p sid0 ids procs)
   (all-procs-have-snapshot-id-p
    sid0
    ids
    (s k
       (update-proc-for-normal-msg-core
        (g k procs)
        j
        msg)
       procs)))
    :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-normal-msg-core))))

(defthm good-msg-list-p-of-update-proc-for-normal-msg-core
  (implies
   (good-msg-list-p msgs ids procs)
   (good-msg-list-p
    msgs
    ids
    (s k
       (update-proc-for-normal-msg-core
        (g k procs)
        j
        rcv-msg)
       procs)))
  :hints
  (("Goal"
    :induct (good-msg-list-p msgs ids procs)
    :in-theory
    (disable update-proc-for-normal-msg-core))))

;; ;start support: normal-msg-core-channel-table-preservation
;; ;; Lift preservation from channel rows to the whole channel table.

(defthm good-channel-p-of-update-proc-for-normal-msg-core
  (implies
   (good-channel-p src dst channels ids procs)
   (good-channel-p
    src
    dst
    channels
    ids
    (s k
       (update-proc-for-normal-msg-core
        (g k procs)
        j
        msg)
       procs)))
  :hints
  (("Goal"
    :in-theory
    (disable update-proc-for-normal-msg-core))))


(defthm good-channel-row-p-of-update-proc-for-normal-msg-core
  (implies
   (good-channel-row-p src dsts channels ids procs)
   (good-channel-row-p
    src
    dsts
    channels
    ids
    (s k
       (update-proc-for-normal-msg-core
        (g k procs)
        j
        msg)
       procs)))
  :hints
  (("Goal"
    :induct (good-channel-row-p src dsts channels ids procs)
    :in-theory
    (disable update-proc-for-normal-msg-core))))

(defthm good-channels-p-of-update-proc-for-normal-msg-core
  (implies
   (good-channels-p srcs dsts channels ids procs)
   (good-channels-p
    srcs
    dsts
    channels
    ids
    (s k
       (update-proc-for-normal-msg-core
        (g k procs)
        j
        msg)
       procs)))
  :hints
  (("Goal"
    :induct (good-channels-p srcs dsts channels ids procs)
    :in-theory
    (disable update-proc-for-normal-msg-core))))


(defthm nbrs-from-of-g-of-s-update-proc-for-normal-msg-core
  (equal
   (nbrs-from
    (g x
       (s k
          (update-proc-for-normal-msg-core
           (g k procs)
           j
           msg)
          procs)))
   (nbrs-from
    (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))


(defthm nbrs-to-of-g-of-s-update-proc-for-normal-msg-core
  (equal
   (nbrs-to
    (g x
       (s k
          (update-proc-for-normal-msg-core
           (g k procs)
           j
           msg)
          procs)))
   (nbrs-to
    (g x procs)))
  :hints
  (("Goal"
    :cases ((equal x k)))))


(defthm nbrs-from-to-consistent-for-one-dst-p-of-update-proc-for-normal-msg-core
  (implies
   (nbrs-from-to-consistent-for-one-dst-p i srcs procs)
   (nbrs-from-to-consistent-for-one-dst-p
    i
    srcs
    (s k
       (update-proc-for-normal-msg-core
        (g k procs)
        j
        msg)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-normal-msg-core)
    :induct
    (nbrs-from-to-consistent-for-one-dst-p i srcs procs))))


(defthm nbrs-from-to-consistent-p-of-update-proc-for-normal-msg-core
  (implies
   (nbrs-from-to-consistent-p dsts srcs procs)
   (nbrs-from-to-consistent-p
    dsts
    srcs
    (s k
       (update-proc-for-normal-msg-core
        (g k procs)
        j
        msg)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-normal-msg-core)
    :induct
    (nbrs-from-to-consistent-p dsts srcs procs))))


(defthm nbrs-to-from-consistent-for-one-src-p-of-update-proc-for-normal-msg-core
  (implies
   (nbrs-to-from-consistent-for-one-src-p x dsts procs)
   (nbrs-to-from-consistent-for-one-src-p
    x
    dsts
    (s k
       (update-proc-for-normal-msg-core
        (g k procs)
        j
        msg)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-normal-msg-core)
    :induct
    (nbrs-to-from-consistent-for-one-src-p x dsts procs))))


(defthm nbrs-to-from-consistent-p-of-update-proc-for-normal-msg-core
  (implies
   (nbrs-to-from-consistent-p srcs dsts procs)
   (nbrs-to-from-consistent-p
    srcs
    dsts
    (s k
       (update-proc-for-normal-msg-core
        (g k procs)
        j
        msg)
       procs)))
  :hints
  (("Goal"
    :in-theory (disable update-proc-for-normal-msg-core)
    :induct
    (nbrs-to-from-consistent-p srcs dsts procs))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A local-state update does not change any process counter.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  counter-of-g-of-procs-after-local-state-update

  (equal
   (counter
    (g k
       (s i
          (s :local-state
             val
             (g i procs))
          procs)))

   (counter
    (g k procs)))

  :hints
  (("Goal"
    :cases
    ((equal k i)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A local-state update does not change any process's snapshot-ID list.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  snapshot-ids-of-g-of-procs-after-local-state-update

  (equal
   (snapshot-ids
    (g k
       (s i
          (s :local-state
             val
             (g i procs))
          procs)))

   (snapshot-ids
    (g k procs)))

  :hints
  (("Goal"
    :cases
    ((equal k i)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For one initiator, every stored SID retains the same comparison
;; against that initiator's counter.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  all-stored-sids-for-initiator-preserved-by-local-state-update

  (equal
   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids

    (s i
       (s :local-state
          val
          (g i procs))
       procs))

   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    procs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lift the result across every initiator.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  all-initiators-stored-sids-preserved-by-local-state-update

  (equal
   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids

    (s i
       (s :local-state
          val
          (g i procs))
       procs))

   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    procs)))

;; Exact STEP-NORMAL process-table update.

(defthm
  all-initiators-stored-sids-preserved-by-step-normal-procs-update

  (implies
   (good-state-p st)

   (all-initiators-stored-sids-have-smaller-counters-p
    (proc-ids st)
    (proc-ids st)

    (s i
       (s :local-state

          (update-local-state-normal
           (local-state
            (g i (procs st))))

          (g i (procs st)))

       (procs st)))))


(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-step-normal

  (implies
   (and
    (good-state-p st)
    (memberp i (proc-ids st)))

   (all-initiators-stored-sids-have-smaller-counters-p
    (proc-ids
     (step-normal st i))

    (proc-ids
     (step-normal st i))

    (procs
     (step-normal st i)))))



(defthm
  all-stored-sids-for-initiator-have-smaller-counters-p-of-normal-msg-core

  (implies
   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    procs)

   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    (s i
       (update-proc-for-normal-msg-core
        (g i procs)
        j
        msg)
       procs)))

  :hints
  (("Goal"
    :induct
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator
     ids
     procs))

   ("Subgoal *1/2"
    :cases
    ((equal initiator i)
     (equal (car ids) i)))

   ;; Here INITIATOR has already become I.
   ;; Split whether the current holder is also I.
   ("Subgoal *1/2.2"
    :cases
    ((equal (car ids) i)))

   ;; Here I has already become (CAR IDS).
   ;; Split whether the initiator is that same process.
   ("Subgoal *1/2.1"
    :cases
    ((equal initiator (car ids))))))



(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-normal-msg-core

  (implies
   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    procs)

   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    (s i
       (update-proc-for-normal-msg-core
        (g i procs)
        j
        msg)
       procs)))

  :hints
  (("Goal"
    :induct
    (all-initiators-stored-sids-have-smaller-counters-p
     initiators
     ids
     procs)

    :in-theory
    (disable
     update-proc-for-normal-msg-core))))


(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-handle-normal-msg

  (implies
   (all-initiators-stored-sids-have-smaller-counters-p
    ids ids (procs st))

   (all-initiators-stored-sids-have-smaller-counters-p
    ids ids
    (procs
     (handle-normal-msg st i j msg))))
  :hints (("Goal"
	   :in-theory (disable update-proc-for-normal-msg-core
			       remove-message-from-channel))))




(defthm
  all-stored-sids-for-initiator-have-smaller-counters-p-of-first-recovery-msg

  (implies
   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator ids procs)

   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    (s i
       (update-proc-for-first-recovery-msg
        (g i procs)
        sid
        j)
       procs)))

  :hints
  (("Goal"
    :induct
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator ids procs))

   ("Subgoal *1/2"
    :cases
    ((equal initiator i)
     (equal (car ids) i)))

   ("Subgoal *1/2.2"
    :cases
    ((equal (car ids) i)))

   ("Subgoal *1/2.1"
    :cases
    ((equal initiator (car ids))))))


(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-first-recovery-msg

  (implies
   (all-initiators-stored-sids-have-smaller-counters-p
    initiators ids procs)

   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    (s i
       (update-proc-for-first-recovery-msg
        (g i procs)
        sid
        j)
       procs)))

  :hints
  (("Goal"
    :induct
    (all-initiators-stored-sids-have-smaller-counters-p
     initiators ids procs)

    :in-theory
    (disable
     update-proc-for-first-recovery-msg
     all-stored-sids-for-initiator-have-smaller-counters-p))))


(defthm
  all-stored-sids-for-initiator-have-smaller-counters-p-of-non-first-recovery-msg

  (implies
   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator ids procs)

   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    (s i
       (update-proc-for-non-first-recovery-msg
        (g i procs)
        j)
       procs)))

  :hints
  (("Goal"
    :induct
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator ids procs))

   ("Subgoal *1/2"
    :cases
    ((equal initiator i)
     (equal (car ids) i)))

   ("Subgoal *1/2.2"
    :cases
    ((equal (car ids) i)))

   ("Subgoal *1/2.1"
    :cases
    ((equal initiator (car ids))))))





(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-non-first-recovery-msg

  (implies
   (all-initiators-stored-sids-have-smaller-counters-p
    initiators ids procs)

   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    (s i
       (update-proc-for-non-first-recovery-msg
        (g i procs)
        j)
       procs)))

  :hints
  (("Goal"
    :induct
    (all-initiators-stored-sids-have-smaller-counters-p
     initiators ids procs)

    :in-theory
    (disable
     update-proc-for-non-first-recovery-msg
     all-stored-sids-for-initiator-have-smaller-counters-p))))


(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-handle-non-first-recovery-msg

  (implies
   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    (procs st))

   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    (procs
     (handle-non-first-recovery-msg
      st i j msg))))

  :hints
  (("Goal"
    :use
    ((:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-non-first-recovery-msg

      (initiators initiators)
      (ids ids)
      (procs (procs st))
      (i i)
      (j j))))))

(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-handle-first-recovery-msg

  (implies
   (all-initiators-stored-sids-have-smaller-counters-p
    ids ids (procs st))

   (all-initiators-stored-sids-have-smaller-counters-p
    ids
    ids
    (procs
     (handle-first-recovery-msg st i j msg))))

  :hints
  (("Goal"
    :use
    ((:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-first-recovery-msg

      (initiators ids)
      (ids ids)
      (procs (procs st))
      (i i)
      (sid (sid msg))
      (j j)))

    :in-theory
    (e/d
     (handle-first-recovery-msg
      update-proc-for-first-recovery-msg)

     (all-initiators-stored-sids-have-smaller-counters-p)))))



(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-handle-recovery-msg

  (implies
   (all-initiators-stored-sids-have-smaller-counters-p
    ids
    ids
    (procs st))

   (all-initiators-stored-sids-have-smaller-counters-p
    ids
    ids
    (procs
     (handle-recovery-msg st i j msg))))

  :hints
  (("Goal"
    :in-theory 
    (disable
     handle-first-recovery-msg
      handle-non-first-recovery-msg))))






(defthm
  all-stored-sids-for-initiator-have-smaller-counters-p-of-non-first-marker-msg

  (implies
   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    procs)

   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    (s i
       (update-proc-for-non-first-marker-msg
        (g i procs)
        sid
        j)
       procs)))

  :hints
  (("Goal"
    :induct
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator
     ids
     procs)

    :in-theory
    (disable
     update-proc-for-non-first-marker-msg))

   ("Subgoal *1/2"
    :cases
    ((equal initiator i)
     (equal (car ids) i)))

   ("Subgoal *1/2.2"
    :cases
    ((equal (car ids) i)))

   ("Subgoal *1/2.1"
    :cases
    ((equal initiator (car ids))))))



(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-update-proc-for-non-first-marker-msg

  (implies
   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    procs)

   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    (s i
       (update-proc-for-non-first-marker-msg
        (g i procs)
        sid
        j)
       procs)))

  :hints
  (("Goal"
    :induct
    (all-initiators-stored-sids-have-smaller-counters-p
     initiators
     ids
     procs)

    :in-theory
    (disable
     update-proc-for-non-first-marker-msg
     all-stored-sids-for-initiator-have-smaller-counters-p))

   ("Subgoal *1/2"
    :use
    ((:instance
      all-stored-sids-for-initiator-have-smaller-counters-p-of-non-first-marker-msg

      (initiator
       (car initiators))

      (ids ids)
      (procs procs)
      (i i)
      (sid sid)
      (j j))))))



(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-handle-non-first-marker-msg

  (implies
   (all-initiators-stored-sids-have-smaller-counters-p
    ids ids (procs st))

   (all-initiators-stored-sids-have-smaller-counters-p
    ids
    ids
    (procs
     (handle-non-first-marker-msg
      st i j msg))))

  :hints
  (("Goal"
    :in-theory
    (disable
     remove-message-from-channel
     update-proc-for-non-first-marker-msg))))



(defthm
  stored-sids-for-initiator-memberp-implies-singleton

  (implies
   (and
    (stored-sids-for-initiator-have-smaller-counters-p
     initiator counter sids)

    (memberp sid sids))

   (stored-sids-for-initiator-have-smaller-counters-p
    initiator counter (list sid))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Extract the invariant for one holder.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  all-stored-sids-for-initiator-when-holder-memberp

  (implies
   (and
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator ids procs)

    (memberp holder ids))

   (stored-sids-for-initiator-have-smaller-counters-p
    initiator

    (counter
     (g initiator procs))

    (snapshot-ids
     (g holder procs))))

  :hints
  (("Goal"
    :induct
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator ids procs))

   ("Subgoal *1/2"
    :cases
    ((equal holder (car ids))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; If SID occurs somewhere, the invariant establishes the required
;; counter property for SID.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  all-stored-sids-and-some-proc-has-sid-implies-singleton

  (implies
   (and
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator ids procs)

    (some-proc-has-snapshot-id-p
     sid ids procs))

   (stored-sids-for-initiator-have-smaller-counters-p
    initiator
    (counter
     (g initiator procs))
    (list sid))))



(defthm
  stored-sids-for-initiator-of-snoc

  (equal
   (stored-sids-for-initiator-have-smaller-counters-p
    initiator counter
    (snoc sids sid))

   (and
    (stored-sids-for-initiator-have-smaller-counters-p
     initiator counter sids)

    (stored-sids-for-initiator-have-smaller-counters-p
     initiator counter (list sid))))

  :hints
  (("Goal"
    :induct (len sids))))


(defthm
  stored-sids-for-initiator-of-add-snapshot-id

  (implies
   (and
    (stored-sids-for-initiator-have-smaller-counters-p
     initiator counter sids)

    (stored-sids-for-initiator-have-smaller-counters-p
     initiator counter (list sid)))

   (stored-sids-for-initiator-have-smaller-counters-p
    initiator counter
    (add-snapshot-id sid sids))))



(defthm
  counter-of-g-of-s-update-proc-for-first-marker-msg

  (equal
   (counter
    (g x
       (s i
          (update-proc-for-first-marker-msg
           (g i procs)
           sid
           j)
          procs)))

   (counter
    (g x procs)))

  :hints
  (("Goal"
    :cases
    ((equal x i)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; First-marker snapshot-ID update.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm snapshot-ids-of-update-proc-for-first-marker-msg
  (equal
   (snapshot-ids
    (update-proc-for-first-marker-msg p sid j))

   (add-snapshot-id sid
                    (snapshot-ids p)))

  :hints
  (("Goal"
    :in-theory
    (enable update-proc-for-first-marker-msg
            install-snapshot-entry))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Preserve the invariant for one initiator using a stable SID condition.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm all-stored-sids-for-initiator-of-first-marker-when-sid-small
  (implies
   (and
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator ids procs)

    (stored-sids-for-initiator-have-smaller-counters-p
     initiator
     (counter (g initiator procs))
     (list sid)))

   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    (s i
       (update-proc-for-first-marker-msg
        (g i procs) sid j)
       procs)))

  :hints
  (("Goal"
    :induct
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator ids procs)

    :in-theory
    (disable update-proc-for-first-marker-msg))

   ("Subgoal *1/2"
    :cases
    ((equal (car ids) i)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A SID already stored somewhere satisfies the stable SID condition.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm all-stored-sids-for-initiator-of-first-marker-when-sid-known
  (implies
   (and
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator ids procs)

    (some-proc-has-snapshot-id-p
     sid ids procs))

   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    (s i
       (update-proc-for-first-marker-msg
        (g i procs) sid j)
       procs)))

  :hints
  (("Goal"
    :use
    (all-stored-sids-and-some-proc-has-sid-implies-singleton
     all-stored-sids-for-initiator-of-first-marker-when-sid-small)

    :in-theory
    (disable update-proc-for-first-marker-msg
             some-proc-has-snapshot-id-p
             all-stored-sids-for-initiator-have-smaller-counters-p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lift over all initiators.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm all-initiators-stored-sids-have-smaller-counters-p-of-first-marker-msg
  (implies
   (and
    (all-initiators-stored-sids-have-smaller-counters-p
     initiators ids procs)

    (some-proc-has-snapshot-id-p
     sid ids procs))

   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    (s i
       (update-proc-for-first-marker-msg
        (g i procs) sid j)
       procs)))

  :hints
  (("Goal"
    :induct
    (all-initiators-stored-sids-have-smaller-counters-p
     initiators ids procs)

    :in-theory
    (disable update-proc-for-first-marker-msg
             some-proc-has-snapshot-id-p
             all-stored-sids-for-initiator-have-smaller-counters-p))

   ("Subgoal *1/2"
    :use
    ((:instance
      all-stored-sids-for-initiator-of-first-marker-when-sid-known
      (initiator (car initiators)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lift to HANDLE-FIRST-MARKER-MSG.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm all-initiators-stored-sids-have-smaller-counters-p-of-handle-first-marker-msg
  (implies
   (and
    (all-initiators-stored-sids-have-smaller-counters-p
     ids ids (procs st))

    (some-proc-has-snapshot-id-p
     (sid msg) ids (procs st)))

   (all-initiators-stored-sids-have-smaller-counters-p
    ids
    ids
    (procs
     (handle-first-marker-msg st i j msg))))

  :hints
  (("Goal"
    :use
    ((:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-first-marker-msg
      (initiators ids)
      (procs (procs st))
      (sid (sid msg))))

    :in-theory
    (e/d
     (handle-first-marker-msg
      update-proc-for-first-marker-msg)

     (remove-message-from-channel
      send-msg-all-outgoing-channels
      install-snapshot-entry
      make-snapshot-entry
      some-proc-has-snapshot-id-p
      all-initiators-stored-sids-have-smaller-counters-p)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Extract the invariant from GOOD-STATE-P.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-implies-all-initiators-stored-sids-have-smaller-counters-p
  (implies
   (good-state-p st)

   (all-initiators-stored-sids-have-smaller-counters-p
    (proc-ids st)
    (proc-ids st)
    (procs st)))

  :hints
  (("Goal"
    :in-theory
    (enable good-state-p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Preserve the invariant through the marker dispatcher.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm all-initiators-stored-sids-have-smaller-counters-p-of-handle-marker-head
  (implies
   (and
    (good-state-p st)

    (memberp i (proc-ids st))
    (memberp j (proc-ids st))

    (memberp j
             (nbrs-from
              (g i (procs st))))

    (equal
     (msg-type
      (get-msg-from-channel j i (channels st)))
     :marker))

   (all-initiators-stored-sids-have-smaller-counters-p
    (proc-ids st)
    (proc-ids st)
    (procs
     (handle-marker-msg
      st i j
      (get-msg-from-channel j i (channels st))))))

  :hints
  (("Goal"
    :cases
    ((memberp
      (sid
       (get-msg-from-channel j i (channels st)))
      (snapshot-ids
       (g i (procs st)))))

    :use
    (good-state-p-implies-all-initiators-stored-sids-have-smaller-counters-p
     good-state-p-implies-marker-head-sid-known-somewhere

     (:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-handle-first-marker-msg
      (ids (proc-ids st))
      (msg (get-msg-from-channel j i (channels st))))

     (:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-handle-non-first-marker-msg
      (ids (proc-ids st))
      (msg (get-msg-from-channel j i (channels st)))))

    :in-theory
    (e/d
     (handle-marker-msg)

     (good-state-p
      handle-first-marker-msg
      handle-non-first-marker-msg
      get-msg-from-channel
      some-proc-has-snapshot-id-p
      all-initiators-stored-sids-have-smaller-counters-p)))))



(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-step-rcv

  (implies
   (and
    (good-state-p st)

    ;; Valid receiver and sender.
    (memberp i
             (proc-ids st))

    (memberp j
             (proc-ids st))

    (memberp j
             (nbrs-from
              (g i (procs st)))))

   (all-initiators-stored-sids-have-smaller-counters-p
    (proc-ids st)
    (proc-ids st)
    (procs
     (step-rcv st i j))))
  :hints (("Goal"
        :in-theory
    (disable
     handle-normal-msg
     get-msg-from-channel
     handle-marker-msg
     handle-recovery-msg))))


















;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; STEP-RECOVER preserves the counter and snapshot-ID view of every process.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm counter-of-g-of-procs-of-step-recover
  (equal
   (counter
    (g k
       (procs
        (step-recover st i))))

   (counter
    (g k (procs st))))

  :hints
  (("Goal"
    :cases
    ((equal k i))

    :in-theory
    (e/d
     (step-recover)

     (replay-channel-snapshots
      send-msg-all-outgoing-channels
      create-recovery-message)))))


(defthm snapshot-ids-of-g-of-procs-of-step-recover
  (equal
   (snapshot-ids
    (g k
       (procs
        (step-recover st i))))

   (snapshot-ids
    (g k (procs st))))

  :hints
  (("Goal"
    :cases
    ((equal k i))

    :in-theory
    (e/d
     (step-recover)

     (replay-channel-snapshots
      send-msg-all-outgoing-channels
      create-recovery-message)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Preserve the invariant for one initiator.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm all-stored-sids-for-initiator-have-smaller-counters-p-of-step-recover
  (implies
   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    (procs st))

   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    (procs
     (step-recover st i))))

  :hints
  (("Goal"
    :induct
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator
     ids
     (procs st))

    :in-theory
    (disable step-recover))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lift over all initiators.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm all-initiators-stored-sids-have-smaller-counters-p-preserved-by-step-recover
  (implies
   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    (procs st))

   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    (procs
     (step-recover st i))))

  :hints
  (("Goal"
    :induct
    (all-initiators-stored-sids-have-smaller-counters-p
     initiators
     ids
     (procs st))

    :in-theory
    (disable
     step-recover
     all-stored-sids-for-initiator-have-smaller-counters-p))

   ("Subgoal *1/2"
    :use
    ((:instance
      all-stored-sids-for-initiator-have-smaller-counters-p-of-step-recover

      (initiator
       (car initiators)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GOOD-STATE-P form used by the main good-state preservation proof.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm all-initiators-stored-sids-have-smaller-counters-p-of-step-recover
  (implies
   (and
    (good-state-p st)
    (memberp i (proc-ids st)))

   (all-initiators-stored-sids-have-smaller-counters-p
    (proc-ids st)
    (proc-ids st)
    (procs
     (step-recover st i))))

  :hints
  (("Goal"
    :use
    (good-state-p-implies-all-initiators-stored-sids-have-smaller-counters-p

     (:instance
      all-initiators-stored-sids-have-smaller-counters-p-preserved-by-step-recover

      (initiators
       (proc-ids st))

      (ids
       (proc-ids st))))

    :in-theory
    (disable
     good-state-p
     step-recover
     all-initiators-stored-sids-have-smaller-counters-p))))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; STEP-CHECKPOINT installs (I, old-counter) and increments I's counter.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Increasing an initiator counter preserves all previously stored SIDs.

(defthm stored-sids-for-initiator-have-smaller-counters-p-of-increment
  (implies
   (and
    (natp counter)

    (stored-sids-for-initiator-have-smaller-counters-p
     initiator counter sids))

   (stored-sids-for-initiator-have-smaller-counters-p
    initiator
    (+ 1 counter)
    sids))

  :hints
  (("Goal"
    :induct
    (stored-sids-for-initiator-have-smaller-counters-p
     initiator counter sids))))


;; The newly created SID is smaller than its initiator's incremented counter.
;; For every other initiator, the SID belongs to a different process.

(defthm stored-sids-for-initiator-of-new-checkpoint-sid
  (implies
   (natp counter)

   (stored-sids-for-initiator-have-smaller-counters-p
    initiator

    (if (equal initiator i)
        (+ 1 counter)
      other-counter)

    (list
     (list i counter))))

  :hints
  (("Goal"
    :cases
    ((equal initiator i)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Counter and snapshot-ID views after STEP-CHECKPOINT.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm counter-of-g-of-procs-of-step-checkpoint
  (equal
   (counter
    (g k
       (procs
        (step-checkpoint st i))))

   (if (equal k i)
       (+ 1
          (counter
           (g i (procs st))))
     (counter
      (g k (procs st)))))

  :hints
  (("Goal"
    :cases
    ((equal k i))

    :in-theory
    (e/d
     (step-checkpoint
      install-snapshot-entry)

     (make-snapshot-entry
      create-marker-message
      send-msg-all-outgoing-channels)))))


(defthm snapshot-ids-of-g-of-procs-of-step-checkpoint
  (equal
   (snapshot-ids
    (g k
       (procs
        (step-checkpoint st i))))

   (if (equal k i)
       (add-snapshot-id
        (list i
              (counter
               (g i (procs st))))
        (snapshot-ids
         (g i (procs st))))

     (snapshot-ids
      (g k (procs st)))))

  :hints
  (("Goal"
    :cases
    ((equal k i))

    :in-theory
    (e/d
     (step-checkpoint
      install-snapshot-entry)

     (make-snapshot-entry
      create-marker-message
      send-msg-all-outgoing-channels)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Preserve one holder's stored-SID condition.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm stored-sids-for-initiator-view-of-step-checkpoint
  (implies
   (and
    (natp
     (counter
      (g i (procs st))))

    (stored-sids-for-initiator-have-smaller-counters-p
     initiator

     (counter
      (g initiator (procs st)))

     (snapshot-ids
      (g holder (procs st)))))

   (stored-sids-for-initiator-have-smaller-counters-p
    initiator

    (counter
     (g initiator
        (procs
         (step-checkpoint st i))))

    (snapshot-ids
     (g holder
        (procs
         (step-checkpoint st i))))))

  :hints
  (("Goal"
    :cases
    ((equal initiator i)))

   ("Subgoal 2"
    :cases
    ((equal holder i)))

   ("Subgoal 1"
    :cases
    ((equal holder i)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lift over every holder for one initiator.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm all-stored-sids-for-initiator-have-smaller-counters-p-of-step-checkpoint
  (implies
   (and
    (natp
     (counter
      (g i (procs st))))

    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator
     ids
     (procs st)))

   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    (procs
     (step-checkpoint st i))))

  :hints
  (("Goal"
    :induct
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator ids (procs st))

    :in-theory
    (disable
     step-checkpoint
     stored-sids-for-initiator-have-smaller-counters-p))

   ("Subgoal *1/2"
    :use
    ((:instance
      stored-sids-for-initiator-view-of-step-checkpoint
      (holder (car ids)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lift over all initiators.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm all-initiators-stored-sids-have-smaller-counters-p-preserved-by-step-checkpoint
  (implies
   (and
    (natp
     (counter
      (g i (procs st))))

    (all-initiators-stored-sids-have-smaller-counters-p
     initiators
     ids
     (procs st)))

   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    (procs
     (step-checkpoint st i))))

  :hints
  (("Goal"
    :induct
    (all-initiators-stored-sids-have-smaller-counters-p
     initiators ids (procs st))

    :in-theory
    (disable
     step-checkpoint
     all-stored-sids-for-initiator-have-smaller-counters-p))

   ("Subgoal *1/2"
    :use
    ((:instance
      all-stored-sids-for-initiator-have-smaller-counters-p-of-step-checkpoint
      (initiator (car initiators)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A valid process in a good state has a natural-number counter.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-implies-natp-counter
  (implies
   (and
    (good-state-p st)
    (memberp i (proc-ids st)))

   (natp
    (counter
     (g i (procs st)))))

  :hints
  (("Goal"
    :use
    ((:instance
      good-proc-p-of-g-when-good-procs-p

      (ids
       (proc-ids st))

      (procs
       (procs st))

      (all-ids
       (proc-ids st))))

    :in-theory
    (enable
     good-state-p
     good-proc-p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GOOD-STATE-P form.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm all-initiators-stored-sids-have-smaller-counters-p-of-step-checkpoint
  (implies
   (and
    (good-state-p st)
    (memberp i (proc-ids st)))

   (all-initiators-stored-sids-have-smaller-counters-p
    (proc-ids st)
    (proc-ids st)
    (procs
     (step-checkpoint st i))))

  :hints
  (("Goal"
    :use
    (good-state-p-implies-all-initiators-stored-sids-have-smaller-counters-p
     good-state-p-implies-natp-counter

     (:instance
      all-initiators-stored-sids-have-smaller-counters-p-preserved-by-step-checkpoint

      (initiators
       (proc-ids st))

      (ids
       (proc-ids st))))

    :in-theory
    (disable
     good-state-p
     step-checkpoint
     all-initiators-stored-sids-have-smaller-counters-p))))















(defthm good-state-p-of-handle-normal-msg-core
  (implies
   (and
    (good-state-p st)

    ;; Valid receiver and sender.
    (memberp i (proc-ids st))
    (memberp j (proc-ids st))
    (memberp j (nbrs-from (g i (procs st))))

    ;; msg is the first message on channel j -> i.
    (equal msg
           (get-msg-from-channel j i (channels st)))

    ;; This is really a normal/application message.
    (equal (msg-type msg) :normal))
   (good-state-p
    (handle-normal-msg-core st i j msg)))
  :hints
  (("Goal"
    :in-theory
    (disable good-proc-p
             get-msg-from-channel
             remove-message-from-channel
             update-proc-for-normal-msg-core
             record-msg-in-snapshots))))



(defthm good-state-p-of-ignore-normal-msg
  (implies
   (good-state-p st)

   (good-state-p
    (ignore-normal-msg st i j msg)))

  :hints
  (("Goal"
    :in-theory
    (disable
     remove-message-from-channel
     good-proc-p

     ;; IGNORE-NORMAL-MSG does not modify PROC-IDS or PROCS,
     ;; so the old and new occurrences are syntactically equal.
     all-initiators-stored-sids-have-smaller-counters-p))))


(defthm good-state-p-of-handle-normal-msg
  (implies
   (and
    (good-state-p st)
    (memberp i (proc-ids st))
    (memberp j (proc-ids st))
    (memberp j
             (nbrs-from
              (g i (procs st))))
    (equal msg
           (get-msg-from-channel
            j i (channels st)))
    (equal (msg-type msg)
           :normal))

   (good-state-p
    (handle-normal-msg st i j msg)))

  :hints
  (("Goal"
    :cases
    ((and
      (equal
       (proc-status
        (g i (procs st)))
       :recovering)

      (memberp
       j
       (waiting-recovery-from
        (g i (procs st))))))

    :use
    (good-state-p-of-ignore-normal-msg
     good-state-p-of-handle-normal-msg-core)

    :in-theory
    (disable
     good-state-p
     good-proc-p
     get-msg-from-channel
     handle-normal-msg-core
     ignore-normal-msg
     update-proc-for-normal-msg-core
     remove-message-from-channel
     record-msg-in-snapshots))))


;; (defthm good-state-p-of-handle-normal-msg
;;   (implies
;;    (and
;;     (good-state-p st)
;;     (memberp i (proc-ids st))
;;     (memberp j (proc-ids st))
;;     (memberp j (nbrs-from (g i (procs st))))
;;     (equal msg
;;            (get-msg-from-channel j i (channels st)))
;;     (equal (msg-type msg) :normal))
;;    (good-state-p
;;     (handle-normal-msg st i j msg)))
;;   :hints
;;   (("Goal"
;;     :cases ((and (equal (proc-status (g i (procs st))) :recovering)
;;                  (memberp j
;;                           (waiting-recovery-from
;;                            (g i (procs st))))))
;;     :in-theory
;;     (disable good-state-p
;;              good-proc-p
;;              get-msg-from-channel
;;              handle-normal-msg-core
;;              ignore-normal-msg
;;              update-proc-for-normal-msg-core
;;              remove-message-from-channel
;;              record-msg-in-snapshots))))













;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Complete first-marker preservation, including the new counter invariant.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-of-handle-first-marker-msg-with-counter-invariant
  (implies
   (and
    (good-state-p st)

    (memberp i (proc-ids st))
    (memberp j (proc-ids st))
    (memberp j
             (nbrs-from
              (g i (procs st))))

    (equal msg
           (get-msg-from-channel j i (channels st)))

    (equal (msg-type msg) :marker)

    (not
     (memberp
      (sid msg)
      (snapshot-ids
       (g i (procs st)))))

    (some-proc-has-snapshot-id-p
     (sid msg)
     (proc-ids st)
     (procs st)))

   (good-state-p
    (handle-first-marker-msg st i j msg)))

  :hints
  (("Goal"
    :use
    (good-state-p-implies-all-initiators-stored-sids-have-smaller-counters-p

     (:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-handle-first-marker-msg
      (ids (proc-ids st))))

    :in-theory
    (disable
     good-proc-p
     update-proc-for-first-marker-msg
     get-msg-from-channel
     remove-message-from-channel
     send-msg-all-outgoing-channels
     install-snapshot-entry
     make-snapshot-entry
     some-proc-has-snapshot-id-p
     all-initiators-stored-sids-have-smaller-counters-p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Complete non-first-marker preservation, including the new invariant.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-of-handle-non-first-marker-msg-with-counter-invariant
  (implies
   (and
    (good-state-p st)

    (memberp i (proc-ids st))
    (memberp j (proc-ids st))
    (memberp j
             (nbrs-from
              (g i (procs st))))

    (equal msg
           (get-msg-from-channel j i (channels st)))

    (equal (msg-type msg) :marker)

    (memberp
     (sid msg)
     (snapshot-ids
      (g i (procs st)))))

   (good-state-p
    (handle-non-first-marker-msg st i j msg)))

  :hints
  (("Goal"
    :use
    (good-state-p-implies-all-initiators-stored-sids-have-smaller-counters-p

     (:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-handle-non-first-marker-msg
      (ids (proc-ids st))))

    :in-theory
    (disable
     good-proc-p
     get-msg-from-channel
     remove-message-from-channel
     update-proc-for-non-first-marker-msg
     set-snapshot-entry
     all-initiators-stored-sids-have-smaller-counters-p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Re-admit the missing marker dispatcher theorem.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-of-handle-marker-msg
  (implies
   (and
    (good-state-p st)

    (memberp i (proc-ids st))
    (memberp j (proc-ids st))
    (memberp j
             (nbrs-from
              (g i (procs st))))

    (equal msg
           (get-msg-from-channel j i (channels st)))

    (equal (msg-type msg) :marker)

    (some-proc-has-snapshot-id-p
     (sid msg)
     (proc-ids st)
     (procs st)))

   (good-state-p
    (handle-marker-msg st i j msg)))

  :hints
  (("Goal"
    :cases
    ((memberp
      (sid msg)
      (snapshot-ids
       (g i (procs st)))))

    :use
    (good-state-p-of-handle-first-marker-msg-with-counter-invariant
     good-state-p-of-handle-non-first-marker-msg-with-counter-invariant)

    :in-theory
    (disable
     good-state-p
     handle-first-marker-msg
     handle-non-first-marker-msg
     some-proc-has-snapshot-id-p))))












;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Complete first-recovery preservation with the new counter invariant.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-of-handle-first-recovery-msg-with-counter-invariant
  (implies
   (and
    (good-state-p st)

    (memberp i (proc-ids st))
    (memberp j (proc-ids st))
    (memberp j
             (nbrs-from
              (g i (procs st))))

    (equal msg
           (get-msg-from-channel j i (channels st)))

    (equal (msg-type msg) :recovery)

    (equal
     (proc-status
      (g i (procs st)))
     :normal)

    (memberp
     (sid msg)
     (snapshot-ids
      (g i (procs st))))

    (all-procs-have-snapshot-id-p
     (sid msg)
     (proc-ids st)
     (procs st)))

   (good-state-p
    (handle-first-recovery-msg st i j msg)))

  :hints
  (("Goal"
    :use
    (good-state-p-implies-all-initiators-stored-sids-have-smaller-counters-p

     (:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-handle-first-recovery-msg
      (ids (proc-ids st))))

    :in-theory
    (disable
     good-proc-p
     remove-message-from-channel
     get-msg-from-channel
     update-proc-for-first-recovery-msg
     all-initiators-stored-sids-have-smaller-counters-p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Complete non-first-recovery preservation with the new invariant.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-of-handle-non-first-recovery-msg-with-counter-invariant
  (implies
   (and
    (good-state-p st)

    (memberp i (proc-ids st))
    (memberp j (proc-ids st))
    (memberp j
             (nbrs-from
              (g i (procs st))))

    (equal msg
           (get-msg-from-channel j i (channels st)))

    (equal (msg-type msg) :recovery)

    (not
     (equal
      (proc-status
       (g i (procs st)))
      :normal)))

   (good-state-p
    (handle-non-first-recovery-msg st i j msg)))

  :hints
  (("Goal"
    :use
    (good-state-p-implies-all-initiators-stored-sids-have-smaller-counters-p

     (:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-handle-non-first-recovery-msg
      (initiators (proc-ids st))
      (ids (proc-ids st))))

    :in-theory
    (disable
     good-proc-p
     remove-message-from-channel
     get-msg-from-channel
     update-proc-for-non-first-recovery-msg
     all-initiators-stored-sids-have-smaller-counters-p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Re-admit the recovery dispatcher theorem.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-of-handle-recovery-msg
  (implies
   (and
    (good-state-p st)

    (memberp i (proc-ids st))
    (memberp j (proc-ids st))
    (memberp j
             (nbrs-from
              (g i (procs st))))

    (equal msg
           (get-msg-from-channel j i (channels st)))

    (equal (msg-type msg) :recovery)

    (all-procs-have-snapshot-id-p
     (sid msg)
     (proc-ids st)
     (procs st)))

   (good-state-p
    (handle-recovery-msg st i j msg)))

  :hints
  (("Goal"
    :cases
    ((equal
      (proc-status
       (g i (procs st)))
      :normal))

    :use
    ((:instance
      all-procs-have-snapshot-id-p-when-memberp
      (sid (sid msg))
      (ids (proc-ids st))
      (procs (procs st)))

     good-state-p-of-handle-first-recovery-msg-with-counter-invariant

     good-state-p-of-handle-non-first-recovery-msg-with-counter-invariant)

    :in-theory
    (disable
     good-state-p
     handle-first-recovery-msg
     handle-non-first-recovery-msg
     all-procs-have-snapshot-id-p))))










(defthm good-state-p-of-step-rcv
  (implies
   (and
    (good-state-p st)
    (memberp i (proc-ids st))
    (memberp j (proc-ids st))
    (memberp j (nbrs-from (g i (procs st)))))
   (good-state-p
    (step-rcv st i j)))
  :hints
  (("Goal"
    :cases
    ((equal (msg-type (get-msg-from-channel j i (channels st))) :normal)
     (equal (msg-type (get-msg-from-channel j i (channels st))) :marker)
     (equal (msg-type (get-msg-from-channel j i (channels st))) :recovery))
    :in-theory
    (e/d
     ;; Enable only the two bridge lemmas needed to recover the removed
     ;; marker/recovery side conditions.
     (good-state-p-implies-marker-head-sid-known-somewhere
      good-state-p-implies-recovery-head-sid-known-by-all-procs)

     (good-state-p
      good-proc-p
      get-msg-from-channel
      some-proc-has-snapshot-id-p
      all-procs-have-snapshot-id-p
      handle-normal-msg
      handle-marker-msg
      handle-recovery-msg)))))









;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Re-admit the full :START-CHECKPOINT system-step theorem.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-of-system-step-start-checkpoint
  (implies
   (and
    (good-state-p st)

    (equal
     (ttype input)
     :start-checkpoint)

    (memberp
     (pid input)
     (proc-ids st)))

   (good-state-p
    (system-step st input)))

  :hints
  (("Goal"
    :use
    ((:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-step-checkpoint
      (i (pid input))))

    :in-theory
    (e/d
     (system-step)

     (good-proc-p
      start-checkpoint-helper
      make-snapshot-entry
      install-snapshot-entry
      create-marker-message
      all-initiators-stored-sids-have-smaller-counters-p)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; STEP-CHECKPOINT wrapper.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-of-step-checkpoint
  (implies
   (and
    (good-state-p st)
    (memberp i (proc-ids st)))

   (good-state-p
    (step-checkpoint st i)))

  :hints
  (("Goal"
    :use
    ((:instance
      good-state-p-of-system-step-start-checkpoint

      (input
       (>_ :ttype :start-checkpoint
           :pid i)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Re-admit the full :RECOVER system-step theorem.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-of-system-step-recover
  (implies
   (and
    (good-state-p st)

    (equal
     (ttype input)
     :recover)

    (memberp
     (pid input)
     (proc-ids st))

    (all-procs-have-snapshot-id-p
     (car
      (snapshot-ids
       (g (pid input)
          (procs st))))
     (proc-ids st)
     (procs st)))

   (good-state-p
    (system-step st input)))

  :hints
  (("Goal"
    :use
    ((:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-step-recover
      (i (pid input))))

    :in-theory
    (e/d
     (system-step)

     (good-proc-p
      start-recovery-helper
      create-recovery-message
      all-initiators-stored-sids-have-smaller-counters-p)))))


(defthm good-state-p-of-step-recover
  (implies
   (and
    (good-state-p st)

    (memberp i
             (proc-ids st))

    (all-procs-have-snapshot-id-p
     (car
      (snapshot-ids
       (g i (procs st))))
     (proc-ids st)
     (procs st)))

   (good-state-p
    (step-recover st i)))

  :hints
  (("Goal"
    :use
    ((:instance
      good-state-p-of-system-step-recover

      (input
       (>_ :ttype :recover
           :pid i)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Re-admit the full :NORMAL system-step theorem.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-of-system-step-normal
  (implies
   (and
    (good-state-p st)

    (equal
     (ttype input)
     :normal)

    (memberp
     (pid input)
     (proc-ids st)))

   (good-state-p
    (system-step st input)))

  :hints
  (("Goal"
    :use
    ((:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-step-normal
      (i (pid input))))

    :in-theory
    (e/d
     (system-step)

     (all-initiators-stored-sids-have-smaller-counters-p)))))


(defthm good-state-p-of-step-normal
  (implies
   (and
    (good-state-p st)
    (memberp i (proc-ids st)))

   (good-state-p
    (step-normal st i)))

  :hints
  (("Goal"
    :use
    ((:instance
      good-state-p-of-system-step-normal

      (input
       (>_ :ttype :normal
           :pid i)))))))








;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; STEP-CRASH changes only PROC-STATUS.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm counter-of-g-of-procs-of-step-crash
  (equal
   (counter
    (g k
       (procs
        (step-crash st i))))
   (counter
    (g k (procs st))))
  :hints
  (("Goal"
    :cases ((equal k i))
    :in-theory (enable step-crash))))


(defthm snapshot-ids-of-g-of-procs-of-step-crash
  (equal
   (snapshot-ids
    (g k
       (procs
        (step-crash st i))))
   (snapshot-ids
    (g k (procs st))))
  :hints
  (("Goal"
    :cases ((equal k i))
    :in-theory (enable step-crash))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Preserve the property for one initiator.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  all-stored-sids-for-initiator-have-smaller-counters-p-of-step-crash

  (implies
   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    (procs st))

   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator
    ids
    (procs
     (step-crash st i))))

  :hints
  (("Goal"
    :induct
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator
     ids
     (procs st))

    :in-theory
    (disable step-crash))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lift preservation over all initiators.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  all-initiators-stored-sids-have-smaller-counters-p-of-step-crash

  (implies
   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    (procs st))

   (all-initiators-stored-sids-have-smaller-counters-p
    initiators
    ids
    (procs
     (step-crash st i))))

  :hints
  (("Goal"
    :induct
    (all-initiators-stored-sids-have-smaller-counters-p
     initiators
     ids
     (procs st))

    :in-theory
    (disable
     step-crash
     all-stored-sids-for-initiator-have-smaller-counters-p))

   ("Subgoal *1/2"
    :use
    ((:instance
      all-stored-sids-for-initiator-have-smaller-counters-p-of-step-crash
      (initiator (car initiators)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GOOD-STATE-P supplies the old invariant.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  good-state-p-implies-invariant-of-step-crash

  (implies
   (good-state-p st)

   (all-initiators-stored-sids-have-smaller-counters-p
    (proc-ids st)
    (proc-ids st)
    (procs
     (step-crash st i))))

  :hints
  (("Goal"
    :use
    ((:instance
      good-state-p-implies-all-initiators-stored-sids-have-smaller-counters-p)

     (:instance
      all-initiators-stored-sids-have-smaller-counters-p-of-step-crash
      (initiators (proc-ids st))
      (ids        (proc-ids st))))

    :in-theory
    (disable
     good-state-p
     step-crash
     all-initiators-stored-sids-have-smaller-counters-p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Restore GOOD-STATE-P preservation for STEP-CRASH.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-state-p-of-step-crash
  (implies
   (and
    (good-state-p st)
    (memberp i (proc-ids st)))

   (good-state-p
    (step-crash st i)))

  :hints
  (("Goal"
    :use
    ((:instance
      good-state-p-implies-invariant-of-step-crash))

    :in-theory
    (disable
     all-initiators-stored-sids-have-smaller-counters-p))))





(defthm good-state-p-of-system-step-when-legal-inputp
  (implies
   (and
    (good-state-p st)
    (legal-inputp st input))
   (good-state-p
    (system-step st input)))
  :hints
  (("Goal"
    :cases
    ((equal (ttype input) :receive)
     (equal (ttype input) :normal)
     (equal (ttype input) :start-checkpoint)
     (equal (ttype input) :crash)
     (equal (ttype input) :recover)
     (equal (ttype input) :nop))
    :in-theory
    (e/d
     (legal-inputp
      system-step)

     (good-state-p
      good-proc-p
      step-rcv
      step-normal
      step-checkpoint
      step-crash
      step-recover
      get-msg-from-channel
      start-checkpoint-helper
      start-recovery-helper
      create-marker-message
      create-recovery-message)))))



;; Legal input sequence preserves good-state-p

(defthm good-state-p-of-run-imp-when-legal-input-sequencep
  (implies
   (and
    (good-state-p st)
    (legal-input-sequencep st inputs))
   (good-state-p
    (run-imp st inputs)))
  :hints
  (("Goal"
    :induct (legal-input-sequencep st inputs)
    :in-theory
    (e/d
     (legal-input-sequencep
      run-imp)
     (good-state-p
      system-step)))))










;start definitions: spec-state-well-formedness

(defun good-spec-proc-p (p ids)
  ;; A spec process only needs the visible structural fields.
  (and
   (true-listp (nbrs-from p))
   (true-listp (nbrs-to p))
   (subset (nbrs-from p) ids)
   (subset (nbrs-to p) ids)))


(defun good-spec-procs-p (ids spec-procs all-ids)
  (if (endp ids)
      t
    (and
     (good-spec-proc-p
      (g (first ids) spec-procs)
      all-ids)
     (good-spec-procs-p
      (rest ids)
      spec-procs
      all-ids))))

 
;; Good spec channels

(defun good-spec-channel-p (src dst channels procs)
  ;; If dst is an outgoing neighbor of src, then channel src -> dst must contain only normal messages.
  (if (memberp dst (nbrs-to (g src procs)))
      (good-normal-msg-list-p
       (channel-state src dst channels))
    (equal
     (channel-state src dst channels)
     nil)))


(defun good-spec-channel-row-p (src dsts channels procs)
  ;; Check all destination channels for fixed source SRC.
  (if (endp dsts)
      t
    (and
     (good-spec-channel-p src
                          (first dsts)
                          channels
                          procs)
     (good-spec-channel-row-p src
                              (rest dsts)
                              channels
                              procs))))


(defun good-spec-channels-p (srcs dsts channels procs)
  ;; Check all source rows.
  (if (endp srcs)
      t
    (and
     (good-spec-channel-row-p (first srcs)
                              dsts
                              channels
                              procs)
     (good-spec-channels-p (rest srcs)
                           dsts
                           channels
                           procs))))


(defun good-spec-state-p (spec-st)
  (let* ((ids           (proc-ids spec-st))
         (spec-procs    (procs spec-st))
         (spec-channels (channels spec-st)))
    (and
     (true-listp ids)
     (uniquep ids)
     (good-spec-procs-p ids spec-procs ids)

     ;; Same neighbor-consistency conditions as good-state-p,
     ;; but over the projected spec processes.
     (nbrs-from-to-consistent-p ids ids spec-procs)
     (nbrs-to-from-consistent-p ids ids spec-procs)

     ;; Spec channels contain only normal messages.
     (good-spec-channels-p
      ids
      ids
      spec-channels
      spec-procs))))

;end definitions: spec-state-well-formedness

;start support: spec-normal-step-process-preservation

(defthm good-spec-proc-p-of-local-state-update
  (implies
   (good-spec-proc-p p ids)
   (good-spec-proc-p
    (s :local-state val p)
    ids)))


(defthm good-spec-procs-p-of-normal-update
  (implies
   (good-spec-procs-p ids procs all-ids)
   (good-spec-procs-p
    ids
    (s i
       (s :local-state val
          (g i procs))
       procs)
    all-ids))
  :hints
  (("Goal"
    :induct
    (good-spec-procs-p ids procs all-ids))))

;end support: spec-normal-step-process-preservation


;start support: spec-neighbor-consistency-preserved-by-local-state-update

(defthm nbrs-from-to-consistent-for-one-dst-p-of-spec-normal-update
  (implies
   (nbrs-from-to-consistent-for-one-dst-p dst srcs procs)
   (nbrs-from-to-consistent-for-one-dst-p
    dst
    srcs
    (s i
       (s :local-state val
          (g i procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-from-to-consistent-for-one-dst-p dst srcs procs))))


(defthm nbrs-from-to-consistent-p-of-spec-normal-update
  (implies
   (nbrs-from-to-consistent-p dsts srcs procs)
   (nbrs-from-to-consistent-p
    dsts
    srcs
    (s i
       (s :local-state val
          (g i procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-from-to-consistent-p dsts srcs procs))))


(defthm nbrs-to-from-consistent-for-one-src-p-of-spec-normal-update
  (implies
   (nbrs-to-from-consistent-for-one-src-p src dsts procs)
   (nbrs-to-from-consistent-for-one-src-p
    src
    dsts
    (s i
       (s :local-state val
          (g i procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-to-from-consistent-for-one-src-p src dsts procs))))


(defthm nbrs-to-from-consistent-p-of-spec-normal-update
  (implies
   (nbrs-to-from-consistent-p srcs dsts procs)
   (nbrs-to-from-consistent-p
    srcs
    dsts
    (s i
       (s :local-state val
          (g i procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (nbrs-to-from-consistent-p srcs dsts procs))))

;end support: spec-neighbor-consistency-preserved-by-local-state-update


;start support: spec-normal-step-channel-preservation

(defthm good-normal-msg-list-p-of-snoc-normal-msg
  (implies
   (and
    (good-normal-msg-list-p xs)
    (good-normal-msg-p msg))
   (good-normal-msg-list-p
    (snoc xs msg)))
  :hints
  (("Goal"
    :induct
    (good-normal-msg-list-p xs))))


(defthm good-normal-msg-list-p-of-snoc-create-compute-message
  (implies
   (good-normal-msg-list-p xs)
   (good-normal-msg-list-p
    (snoc xs
          (create-compute-message local-state nbr)))))


(defthm channel-state-of-setting-channel
  (equal
   (channel-state src dst
                  (>channel i j val channels))
   (if (and (equal src i)
            (equal dst j))
       val
     (channel-state src dst channels)))
  :hints
  (("Goal"
    :do-not-induct t
    :cases ((equal dst j)
            (equal src i)))))


(defthm good-normal-msg-list-p-of-setting-channel-combined
  (implies
   (and
    (good-normal-msg-list-p
     (channel-state src dst channels))

    ;; If this is the updated channel, VAL must be good.
    ;; Otherwise, the old channel goodness is enough.
    (or
     (not (equal src i))
     (not (equal dst j))
     (good-normal-msg-list-p val)))

   (good-normal-msg-list-p
    (channel-state src dst
                   (>channel i j val channels))))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance channel-state-of-setting-channel
                (src src)
                (dst dst)
                (i i)
                (j j)
                (val val)
                (channels channels)))
    :in-theory
    (disable channel-state-of-setting-channel))))


(defthm good-normal-msg-list-p-of-one-compute-send-update
  (implies
   (good-normal-msg-list-p
    (channel-state src dst channels))
   (good-normal-msg-list-p
    (channel-state
     src
     dst
     (>channel i j
               (snoc
                (channel-state i j channels)
                (create-compute-message local-state j))
               channels))))
  :hints
  (("Goal"
    :use
    ((:instance good-normal-msg-list-p-of-setting-channel-combined
                (src src)
                (dst dst)
                (i i)
                (j j)
                (channels channels)
                (val
                 (snoc
                  (channel-state i j channels)
                  (create-compute-message local-state j))))))))


(defthm good-normal-msg-list-p-of-channel-after-send-compute-message
  (implies
   (good-normal-msg-list-p
    (channel-state src dst channels))
   (good-normal-msg-list-p
    (channel-state
     src
     dst
     (send-compute-message local-state i nbrs channels))))
  :hints
  (("Goal"
    :induct
    (send-compute-message local-state i nbrs channels))))



;start replacement: channel-nil-after-send-compute-message

(defthm channel-state-after-send-compute-message-when-dst-not-in-nbrs
  (implies
   (not (memberp dst nbrs))
   (equal
    (channel-state
     src
     dst
     (send-compute-message local-state i nbrs channels))
    (channel-state src dst channels)))
  :hints
  (("Goal"
    :induct
    (send-compute-message local-state i nbrs channels))))


(defthm channel-nil-after-send-compute-message-when-dst-not-in-nbrs
  (implies
   (and
    (not (memberp dst nbrs))
    (not (channel-state src dst channels)))
   (not
    (channel-state
     src
     dst
     (send-compute-message local-state i nbrs channels))))
  :hints
  (("Goal"
    :use
    ((:instance channel-state-after-send-compute-message-when-dst-not-in-nbrs
                (src src)
                (dst dst)
                (local-state local-state)
                (i i)
                (nbrs nbrs)
                (channels channels)))
    :in-theory
    (disable channel-state-after-send-compute-message-when-dst-not-in-nbrs))))


(defthm channel-state-after-send-compute-message-when-src-not-i
  (implies
   (not (equal src i))
   (equal
    (channel-state
     src
     dst
     (send-compute-message local-state i nbrs channels))
    (channel-state src dst channels)))
  :hints
  (("Goal"
    :induct
    (send-compute-message local-state i nbrs channels))))


(defthm channel-nil-after-send-compute-message-when-src-not-i
  (implies
   (and
    (not (equal src i))
    (not (channel-state src dst channels)))
   (not
    (channel-state
     src
     dst
     (send-compute-message local-state i nbrs channels))))
  :hints
  (("Goal"
    :use
    ((:instance channel-state-after-send-compute-message-when-src-not-i
                (src src)
                (dst dst)
                (local-state local-state)
                (i i)
                (nbrs nbrs)
                (channels channels)))
    :in-theory
    (disable channel-state-after-send-compute-message-when-src-not-i))))

					;end replacement: channel-nil-after-send-compute-message





(defthm good-spec-channel-p-of-send-compute-message
  (implies
   (and
    (good-spec-channel-p src dst channels procs)
    (subset nbrs (nbrs-to (g i procs))))
   (good-spec-channel-p
    src
    dst
    (send-compute-message local-state i nbrs channels)
    procs))
  :hints
  (("Goal"
    :in-theory
    (enable good-spec-channel-p)
    :cases ((equal src i)))))


(defthm good-spec-channel-row-p-of-send-compute-message
  (implies
   (and
    (good-spec-channel-row-p src dsts channels procs)
    (subset nbrs (nbrs-to (g i procs))))
   (good-spec-channel-row-p
    src
    dsts
    (send-compute-message local-state i nbrs channels)
    procs))
  :hints
  (("Goal"
    :induct
    (good-spec-channel-row-p src dsts channels procs))))


(defthm good-spec-channels-p-of-send-compute-message
  (implies
   (and
    (good-spec-channels-p srcs dsts channels procs)
    (subset nbrs (nbrs-to (g i procs))))
   (good-spec-channels-p
    srcs
    dsts
    (send-compute-message local-state i nbrs channels)
    procs))
  :hints
  (("Goal"
    :induct
    (good-spec-channels-p srcs dsts channels procs))))

;end support: spec-normal-step-channel-preservation


;start support: spec-channels-preserved-by-local-state-update

(defthm good-spec-channel-p-of-normal-proc-update
  (implies
   (good-spec-channel-p src dst channels procs)
   (good-spec-channel-p
    src
    dst
    channels
    (s i
       (s :local-state val
          (g i procs))
       procs)))
  :hints
  (("Goal"
    :in-theory
    (enable good-spec-channel-p)
    :cases ((equal src i)))))


(defthm good-spec-channel-row-p-of-normal-proc-update
  (implies
   (good-spec-channel-row-p src dsts channels procs)
   (good-spec-channel-row-p
    src
    dsts
    channels
    (s i
       (s :local-state val
          (g i procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (good-spec-channel-row-p src dsts channels procs))))


(defthm good-spec-channels-p-of-normal-proc-update
  (implies
   (good-spec-channels-p srcs dsts channels procs)
   (good-spec-channels-p
    srcs
    dsts
    channels
    (s i
       (s :local-state val
          (g i procs))
       procs)))
  :hints
  (("Goal"
    :induct
    (good-spec-channels-p srcs dsts channels procs))))

;end support: spec-channels-preserved-by-local-state-update


;start target: good-spec-state-p-of-spec-step-normal

(defthm good-spec-state-p-of-spec-step-normal
  (implies
   (and
    (good-spec-state-p st)
    (memberp i (proc-ids st)))
   (good-spec-state-p
    (spec-step-normal st i)))
  :hints
  (("Goal"
    :in-theory
    (enable spec-step-normal))))

;end target: good-spec-state-p-of-spec-step-normal


;start target: good-spec-state-p-of-spec-step-when-normal

(defthm good-spec-state-p-of-spec-step-when-normal
  (implies
   (and
    (good-spec-state-p st)
    (equal (ttype input) :normal))
   (good-spec-state-p
    (spec-step st input)))
  :hints
  (("Goal"
    :in-theory
    (enable spec-step))))

;end target: good-spec-state-p-of-spec-step-when-normal








;start support: remove-consumed-recovery-message
;; Handling a recovery message first removes the head message from channel j -> i.

(defthm good-normal-msg-list-p-of-cdr
  (implies
   (good-normal-msg-list-p msgs)
   (good-normal-msg-list-p (cdr msgs))))

(defthm good-spec-channel-row-p-of-remove-message-from-channel
  (implies
   (good-spec-channel-row-p src dsts channels procs)
   (good-spec-channel-row-p
    src
    dsts
    (remove-message-from-channel j i channels)
    procs))
  :hints
  (("Goal"
    :induct (good-spec-channel-row-p src dsts channels procs)
    :in-theory (disable remove-message-from-channel))))

(defthm good-spec-channels-p-of-remove-message-from-channel
  (implies
   (good-spec-channels-p srcs dsts channels procs)
   (good-spec-channels-p
    srcs
    dsts
    (remove-message-from-channel j i channels)
    procs))
  :hints
  (("Goal"
    :induct (good-spec-channels-p srcs dsts channels procs)
    :in-theory (disable remove-message-from-channel))))




(defthm good-spec-state-p-of-spec-step-rcv
  (implies
   (good-spec-state-p st)
   (good-spec-state-p
    (spec-step-rcv st i j)))
  :hints
  (("Goal"
    :in-theory
    (e/d
     (spec-step-rcv)
     (good-spec-channels-p
      good-spec-procs-p
      remove-message-from-channel
      get-msg-from-channel)))))

;end target: good-spec-state-p-of-spec-step-rcv


;start target: good-spec-state-p-of-spec-step-when-receive
;; Dispatcher theorem for spec-step in the :receive case.


(defthm good-spec-state-p-of-system-step-with-inputp
  (implies
   (good-spec-state-p st)
   (good-spec-state-p
    (spec-step st input)))
  :hints
  (("Goal"
    :cases
    ((equal (ttype input) :receive)
     (equal (ttype input) :normal))
    :in-theory
    (e/d
     (legal-inputp
      spec-step)

     (good-spec-state-p
      good-proc-p
      spec-step-rcv
      spec-step-normal
      get-msg-from-channel
      start-checkpoint-helper
      start-recovery-helper
      create-marker-message
      create-recovery-message)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Legal input sequence preserves good-spec-state-p
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm good-spec-state-p-of-run-spec-when-input-sequencep
  (implies
   (good-spec-state-p st)
   (good-spec-state-p
    (run-spec st inputs)))
  :hints
  (("Goal"
    :in-theory
    (e/d
     (legal-input-sequencep
      run-spec)
     (good-spec-state-p
      spec-step)))))
