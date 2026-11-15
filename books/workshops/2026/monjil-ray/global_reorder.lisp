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
(include-book "local_swap")
;; RETIRE COMPLETED LOW-LEVEL COMMUTATION PHASE

(in-theory
 (disable
  state-equivalent-p-preserved-by-checkpoint-body-inputs
  one-post-pre-swap-with-prefix-and-postfix))



;; DYNAMIC INVERSION COUNT

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; COUNT BEFORE-CUT INPUTS IN AN EXECUTION
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun number-of-before-cut-inputs
    (st m inputs)
  (declare
   (xargs
    :measure
    (acl2-count inputs)))
  (if (endp inputs)
      0
    (let* ((input
            (first inputs))
           ;; Classify INPUT before executing it.
           (before-cut-input-p
            (cm-cut-not-taken-p
             m
             (g :pid input)))
           (next-st
            (system-step
             st
             input))
           (next-m
            (process-cut-step
             input
             st
             m)))
      (if before-cut-input-p
          (+
           1
           (number-of-before-cut-inputs
            next-st
            next-m
            (rest inputs)))
        (number-of-before-cut-inputs
         next-st
         next-m
         (rest inputs))))))

;; COUNT AFTER-CUT / BEFORE-CUT INVERSIONS

(defun inversion-count
    (st m inputs)
  (declare
   (xargs
    :measure
    (acl2-count inputs)))
  (if (endp inputs)
      0
    (let* ((input
            (first inputs))
           ;; Classify INPUT before executing it.
           (before-cut-input-p
            (cm-cut-not-taken-p
             m
             (g :pid input)))
           (next-st
            (system-step
             st
             input))
           (next-m
            (process-cut-step
             input
             st
             m))
           (suffix
            (rest inputs)))
      (+
       ;; If INPUT is after-cut, count all later before-cut inputs.
       (if before-cut-input-p
           0
         (number-of-before-cut-inputs
          next-st
          next-m
          suffix))
       ;; Count inversions whose first input occurs in the suffix.
       (inversion-count
        next-st
        next-m
        suffix)))))

(defthm natp-of-inversion-count
  (natp
   (inversion-count
    st
    m
    inputs))
  :hints
  (("Goal"
    :induct
    (inversion-count
     st
     m
     inputs))))
;; SWAP THE FIRST ADJACENT POST/PRE PAIR

(defun swap-first-after-before
    (st m inputs)
  (declare
   (xargs
    :measure
    (acl2-count inputs)))
  ;; Fewer than two inputs means no adjacent pair exists.
  (if (or
       (endp inputs)
       (endp (rest inputs)))
      inputs
    (let* ((input-post
            (first inputs))
           (input-pre
            (second inputs))
           (postfix
            (rest
             (rest inputs))))
      (if
       (post-pre-swap-start-p
        st
        m
        input-post
        input-pre)
       (append
        (list input-pre input-post)
        postfix)
       (append
        (list input-post)
        (swap-first-after-before
         (system-step
          st
          input-post)
         (process-cut-step
          input-post
          st
          m)
         (rest inputs)))))))

;; REPEATEDLY REORDER THE COMPLETE RAW INPUT SEQUENCE

(defun reorder-inputs
    (st m inputs)
  (declare
   (xargs
    :measure
    (inversion-count
     st m inputs)
    :hints
    (("Goal"
      :in-theory
      (disable
       inversion-count
       swap-first-after-before)))))
  (let ((current-count
         (inversion-count
          st m inputs)))
    (if (zp current-count)
        inputs
      (let* ((next-inputs
              (swap-first-after-before
               st m inputs))
             (next-count
              (inversion-count
               st m next-inputs)))
        (if (< next-count current-count)
            (reorder-inputs
             st m next-inputs)
          inputs)))))

;; SWAPPING PRESERVES TRUE-LISTP

(defthm true-listp-of-swap-first-after-before
  (implies
   (true-listp inputs)
   (true-listp
    (swap-first-after-before
     st m inputs)))
  :hints
  (("Goal"
    :induct
    (swap-first-after-before
     st m inputs)
    :in-theory
    (disable post-pre-swap-start-p
      system-step
      process-cut-step))))

;; SWAPPING PRESERVES CHECKPOINT-BODY INPUTS

(defthm checkpoint-body-inputs-p-of-swap-first-after-before
  (implies
   (cl-checkpoint-body-inputs-p
    inputs)
   (cl-checkpoint-body-inputs-p
    (swap-first-after-before
     st m inputs)))
  :hints
  (("Goal"
    :induct
    (swap-first-after-before
     st m inputs)
    :in-theory
    (disable post-pre-swap-start-p
      system-step
      process-cut-step))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FRONT POST/PRE PAIR PRODUCES EQUIVALENT STATES IN EITHER ORDER
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm front-post-pre-swap-start-implies-state-equivalent
  (implies
   (post-pre-swap-start-p
    st
    m
    (first inputs)
    (second inputs))
   (state-equivalent-p
    ;; Original order: POST, PRE.
    (run-imp
     st
     (list
      (first inputs)
      (second inputs)))
    ;; Swapped order: PRE, POST.
    (run-imp
     st
     (list
      (second inputs)
      (first inputs)))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-two-imp-inputs-commute-under-state-equivalence
      (st st)
      (m m)
      (input-1
       (first inputs))
      (input-2
       (second inputs))))
    :in-theory
    (disable
     post-pre-swap-start-p
     state-equivalent-p
     run-imp)))
    :rule-classes
  ((:rewrite
    :match-free :all)))

(defthm front-post-pre-swap-start-implies-swapped-pair-legal
  (implies
   (post-pre-swap-start-p
    st
    m
    (first inputs)
    (second inputs))
   (legal-input-sequencep
    st
    (list
     (second inputs)
     (first inputs))))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    (;; Swap-start implies the pair is swappable.
     (:instance
      post-pre-two-imp-inputs-swappable-p
      (st st)
      (m m)
      (input-1
       (first inputs))
      (input-2
       (second inputs)))
     ;; A swappable pair is legal in the exchanged order.
     (:instance
      two-imp-inputs-swappable-p-implies-swapped-order-legal
      (st st)
      (input-1
       (first inputs))
      (input-2
       (second inputs))))
    :in-theory
    (disable
     post-pre-swap-start-p
     two-imp-inputs-swappable-p
     legal-input-sequencep
     legal-inputp
     system-step
     post-pre-two-imp-inputs-swappable-p
     two-imp-inputs-swappable-p-implies-swapped-order-legal))))

(defthm front-post-pre-swap-start-implies-swapped-postfix-legal
  (implies
   (and
    (consp inputs)
    (consp (rest inputs))
    (post-pre-swap-start-p
     st
     m
     (first inputs)
     (second inputs))
    (legal-input-sequencep
     st inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (legal-input-sequencep
    ;; State after executing the swapped pair.
    (run-imp
     st
     (list
      (second inputs)
      (first inputs)))
    ;; Common postfix.
    (rest
     (rest inputs))))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    (;; The original and swapped pair-result states are equivalent.
     (:instance
      front-post-pre-swap-start-implies-state-equivalent
      (st st)
      (m m)
      (inputs inputs))
     ;; Both pair-result states are good and recovery-free.
     (:instance
      post-pre-swap-start-implies-pair-states-good-and-recovery-free
      (st st)
      (m m)
      (input-1
       (first inputs))
      (input-2
       (second inputs)))
     ;; Original complete legality gives postfix legality after
     ;; executing the original pair.
     (:instance
      legal-input-sequencep-of-append-implies-second
      (st st)
      (inputs-1
       (list
        (first inputs)
        (second inputs)))
      (inputs-2
       (rest
        (rest inputs))))
     ;; Transfer postfix legality to the swapped pair-result state.
     (:instance
      state-equivalent-p-preserves-legal-postfix
      (st-original
       (run-imp
        st
        (list
         (first inputs)
         (second inputs))))
      (st-after-swap
       (run-imp
        st
        (list
         (second inputs)
         (first inputs))))
      (postfix
       (rest
        (rest inputs)))))
    :in-theory
    (disable
      ;; Keep semantic definitions closed.
      post-pre-swap-start-p
      state-equivalent-p
      good-state-p
      recovery-free-state-p
      legal-input-sequencep
      legal-inputp
      run-imp
      system-step
      process-cut-step
      ;; These rules are instantiated explicitly above.
      front-post-pre-swap-start-implies-state-equivalent
      post-pre-swap-start-implies-pair-states-good-and-recovery-free
      legal-input-sequencep-of-append-implies-second
      state-equivalent-p-preserves-legal-postfix))))

;; COMBINE LEGALITY OF A PREFIX AND ITS POSTFIX

(defthm legal-input-sequencep-of-append-if
  (implies
   (and
    (legal-input-sequencep
     st
     inputs-1)
    (legal-input-sequencep
     (run-imp st inputs-1)
     inputs-2))
   (legal-input-sequencep
    st
    (append inputs-1 inputs-2)))
  :hints
  (("Goal"
    :induct
    (run-imp
     st
     inputs-1)
    :in-theory
    (disable legal-inputp
      system-step))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; LEGALITY OF A SELECTED PAIR AT THE FRONT
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm front-post-pre-swap-preserves-legal-input-sequencep
  (implies
   (and
    (consp inputs)
    (consp (rest inputs))
    (post-pre-swap-start-p
     st
     m
     (first inputs)
     (second inputs))
    (legal-input-sequencep
     st inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (legal-input-sequencep
    st
    (append
     (list
      (second inputs)
      (first inputs))
     (rest
      (rest inputs)))))
    :hints
  (("Goal"
    :do-not-induct t
    :use
    (;; Legality of the swapped two-input prefix.
     (:instance
      front-post-pre-swap-start-implies-swapped-pair-legal
      (st st)
      (m m)
      (inputs inputs))
     ;; Legality of the postfix from the state reached after
     ;; executing the swapped pair.
     (:instance
      front-post-pre-swap-start-implies-swapped-postfix-legal
      (st st)
      (m m)
      (inputs inputs))
     ;; Combine the legal swapped pair and legal postfix.
     (:instance
      legal-input-sequencep-of-append-if
      (st st)
      (inputs-1
       (list
        (second inputs)
        (first inputs)))
      (inputs-2
       (rest
        (rest inputs)))))
    :in-theory
    (disable
     cl-checkpoint-body-inputs-p
     legal-input-sequencep
     post-pre-swap-start-p
     run-imp
     front-post-pre-swap-start-implies-swapped-pair-legal
     front-post-pre-swap-start-implies-swapped-postfix-legal
     legal-input-sequencep-of-append-if)))
    :rule-classes
  ((:rewrite
    :match-free :all)))

(defthm legal-input-sequencep-implies-rest-legal
  (implies
   (and
    (consp inputs)
    (legal-input-sequencep
     st inputs))
   (legal-input-sequencep
    (system-step
     st
     (first inputs))
    (rest inputs)))
  :hints
  (("Goal"
    :in-theory
    (disable
     legal-inputp
      system-step))))

(defthm checkpoint-body-inputs-p-implies-rest
  (implies
   (and
    (consp inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (cl-checkpoint-body-inputs-p
    (rest inputs))))

(defthm legal-input-sequencep-of-cons-if
  (implies
   (and
    (legal-inputp
     st input)
    (legal-input-sequencep
     (system-step st input)
     inputs))
   (legal-input-sequencep
    st
    (cons input inputs)))
  :hints
  (("Goal"
    :in-theory
    (disable
     legal-inputp
      system-step))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; THE COMPLETE ONE-SWAP SCAN PRESERVES LEGALITY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm legal-input-sequencep-of-swap-first-after-before
  (implies
   (and
    (legal-input-sequencep
     st inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (legal-input-sequencep
    st
    (swap-first-after-before
     st m inputs)))
:hints
(("Goal"
  :induct
  (swap-first-after-before
   st m inputs)
  :in-theory
  (disable post-pre-swap-start-p
    legal-input-sequencep
    cl-checkpoint-body-inputs-p
    legal-inputp
    system-step
    process-cut-step))
 ("Subgoal *1/2"
  :use
  ((:instance
    front-post-pre-swap-preserves-legal-input-sequencep
    (st st)
    (m m)
    (inputs inputs)))
  :in-theory
  (disable
   front-post-pre-swap-preserves-legal-input-sequencep
   post-pre-swap-start-p
   legal-input-sequencep
   cl-checkpoint-body-inputs-p))))

(defthm run-imp-when-consp
  (implies
   (consp inputs)
   (equal
    (run-imp
     st
     inputs)
    (run-imp
     (system-step
      st
      (car inputs))
     (cdr inputs))))
  :hints
  (("Goal"
    :in-theory
    (disable system-step))))

(defthm swap-first-after-before-preserves-run
  (implies
   (and
    (legal-input-sequencep
     st inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (state-equivalent-p
    (run-imp
     st inputs)
    (run-imp
     st
     (swap-first-after-before
      st m inputs))))
  :hints
  (
   ("Subgoal *1/2"
 :use
 (;; Obtain the checkpoint-body property of CDR INPUTS.
  (:instance
   checkpoint-body-inputs-p-implies-rest
   (inputs inputs))
  ;; Obtain the checkpoint-body property of CDDR INPUTS.
  (:instance
   checkpoint-body-inputs-p-implies-rest
   (inputs
    (rest inputs)))
  ;; The selected POST/PRE pair is at the front, so PREFIX is NIL.
  (:instance
   one-post-pre-swap-with-prefix-and-postfix-final
   (st st)
   (prefix nil)
   (m-at-swap m)
   (input-post
    (first inputs))
   (input-pre
    (second inputs))
   (postfix
    (rest
     (rest inputs)))))
 ;; The swap state for an empty prefix is ST.
 :expand
 ((run-imp st nil))
 :in-theory
 (disable
  one-post-pre-swap-with-prefix-and-postfix-final
  checkpoint-body-inputs-p-implies-rest
  post-pre-swap-start-p
  cl-checkpoint-body-inputs-p
  legal-input-sequencep
  state-equivalent-p
  run-imp
  system-step
  process-cut-step))
   ("Subgoal *1/3"
     :in-theory
    (disable post-pre-swap-start-p
     ; run-imp-when-consp
      legal-input-sequencep
      cl-checkpoint-body-inputs-p
      state-equivalent-p
      legal-inputp
      system-step
      run-imp
      process-cut-step))
   ("Goal"
    :induct
    (swap-first-after-before
     st m inputs)
    :in-theory
    (disable post-pre-swap-start-p
      run-imp-when-consp
      legal-input-sequencep
      cl-checkpoint-body-inputs-p
      state-equivalent-p
      legal-inputp
      system-step
      run-imp
      process-cut-step)))
        :rule-classes
  ((:rewrite
    :match-free :all)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; TRANSITIVITY OF VISIBLE-PROCESS EQUIVALENCE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm procs-equivalent-p-transitive
  (implies
   (and
    (procs-equivalent-p
     ids
     procs-1
     procs-2)
    (procs-equivalent-p
     ids
     procs-2
     procs-3))
   (procs-equivalent-p
    ids
    procs-1
    procs-3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; TRANSITIVITY OF CHECKPOINT-CONTROL EQUIVALENCE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm checkpoint-control-equivalent-p-transitive
  (implies
   (and
    (cl-checkpoint-control-equivalent-p
     ids
     procs-1
     procs-2)
    (cl-checkpoint-control-equivalent-p
     ids
     procs-2
     procs-3))
   (cl-checkpoint-control-equivalent-p
    ids
    procs-1
    procs-3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; TRANSITIVITY OF STATE-EQUIVALENT-P
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm state-equivalent-p-transitive
  (implies
   (and
    (state-equivalent-p
     st-1
     st-2)
    (state-equivalent-p
     st-2
     st-3))
   (state-equivalent-p
    st-1
    st-3))
      :rule-classes
  ((:rewrite
    :match-free :all)))

;; MAIN REORDER THEOREM

(defthm reorder-inputs-preserves-run
  (implies
   (and
    (true-listp inputs)
    (cut-markers-in-transit-p
     m st)
    (cut-meta-imp-consistent-p
     m st)
    (good-cut-meta-p
     m)
    (good-state-p
     st)
    (recovery-free-state-p
     st)
    (legal-input-sequencep
     st inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (state-equivalent-p
    (run-imp
     st inputs)
    (run-imp
     st
     (reorder-inputs
      st m inputs))))
  :hints
  (("Goal"
    :induct
    (reorder-inputs
     st m inputs)
    :in-theory
    (disable
     inversion-count
     swap-first-after-before
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     good-cut-meta-p
     good-state-p
     recovery-free-state-p
     legal-input-sequencep
     cl-checkpoint-body-inputs-p
     state-equivalent-p))
   ("Subgoal *1/2''"
    :do-not-induct t
    :use
    (;; Original execution is equivalent to the once-swapped execution.
     (:instance
      swap-first-after-before-preserves-run)
     ;; Combine the one-swap result with the induction hypothesis.
     (:instance
      state-equivalent-p-transitive
      (st-1
       (run-imp
	st inputs))
      (st-2
       (run-imp
	st
	(swap-first-after-before
	 st m inputs)))
      (st-3
       (run-imp
	st
	(reorder-inputs
	 st
	 m
	 (swap-first-after-before
	  st m inputs))))))
    ;; Keep this as a purely propositional transitivity step.
    :in-theory
    (theory
     'minimal-theory))))

;; COLLECT THE BEFORE-CUT INPUTS

(defun before-cut-inputs (st m inputs)
  (declare
   (xargs
    :measure
    (acl2-count inputs)))
  (if (endp inputs)
      nil
    (let* ((input
            (first inputs))
           ;; Classify INPUT before advancing the metadata.
           (before-cut-p
            (cm-cut-not-taken-p
             m
             (pid input)))
           (next-st
            (system-step
             st
             input))
           (next-m
            (process-cut-step
             input
             st
             m))
           (remaining-before-cut-inputs
            (before-cut-inputs
             next-st
             next-m
             (rest inputs))))
      (if before-cut-p
          (cons
           input
           remaining-before-cut-inputs)
        remaining-before-cut-inputs))))

;; COLLECT THE AFTER-CUT INPUTS

(defun after-cut-inputs (st m inputs)
  (declare
   (xargs
    :measure
    (acl2-count inputs)))
  (if (endp inputs)
      nil
    (let* ((input
            (first inputs))
           ;; Classify INPUT before advancing the metadata.
           (before-cut-p
            (cm-cut-not-taken-p
             m
             (pid input)))
           (next-st
            (system-step
             st
             input))
           (next-m
            (process-cut-step
             input
             st
             m))
           (remaining-after-cut-inputs
            (after-cut-inputs
             next-st
             next-m
             (rest inputs))))
      (if before-cut-p
          remaining-after-cut-inputs
        (cons
         input
         remaining-after-cut-inputs)))))

(defthm checkpoint-body-inputs-p-implies-first-is-body-input
  (implies
   (and
    (consp inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (cl-checkpoint-body-input-p
    (first inputs))))

(defthm post-pre-swap-start-p-implies-first-post-cut
  (implies
   (post-pre-swap-start-p
    st m input-1 input-2)
   (not
    (cm-cut-not-taken-p
     m
     (pid input-1))))
  :hints
  (("Goal"
    :in-theory
    (disable
     process-cut-step
     system-step
     cm-cut-not-taken-p
     good-state-p
     good-cut-meta-p
     cut-meta-imp-consistent-p
     legal-input-sequencep
     legal-inputp
     cl-checkpoint-body-inputs-p
     cl-checkpoint-body-input-p
     recovery-free-state-p
     cut-markers-in-transit-p)))
  :rule-classes nil)

(defthm post-pre-swap-start-p-implies-second-pre-cut-at-start
  (implies
   (post-pre-swap-start-p
    st m input-1 input-2)
   (cm-cut-not-taken-p
    m
    (pid input-2)))
  :hints
  (("Goal"
    :in-theory
    (disable
     process-cut-step
     system-step
     cm-cut-not-taken-p
     good-state-p
     good-cut-meta-p
     cut-meta-imp-consistent-p
     legal-input-sequencep
     legal-inputp
     cl-checkpoint-body-inputs-p
     cl-checkpoint-body-input-p
     recovery-free-state-p
     cut-markers-in-transit-p)))
  :rule-classes nil)

(defthm cm-cut-not-taken-p-implies-memberp-state-proc-ids
  (implies
   (and
    (cm-cut-not-taken-p
     m i)
    (good-cut-meta-p
     m)
    (cut-meta-imp-consistent-p
     m st))
   (memberp
    i
    (proc-ids st))))

(defthm good-cut-meta-consistent-implies-initiator-in-state-proc-ids
  (implies
   (and
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p
     m st))
   (memberp
    (car
     (sid m))
    (proc-ids st))))

(defthm input-sid-equality-implies-pid-in-state-proc-ids
  (implies
   (and
    (good-cut-meta-p m)
    (cut-meta-imp-consistent-p
     m st)
    (equal
     (list
      (pid input)
      counter-value)
     (sid m)))
   (memberp
    (pid input)
    (proc-ids st))))

(defthm cm-cut-not-taken-p-of-after-cut-input-sequence-update
  (equal
   (cm-cut-not-taken-p
    (s :after-cut-input-sequence
       value
       m)
    i)
   (cm-cut-not-taken-p
    m
    i)))

(defthm process-cut-step-equal-for-equivalent-states
  (implies
   (and
    (state-equivalent-p
     st-1 st-2)
    (cut-markers-in-transit-p
     m st-1)
    (cut-markers-in-transit-p
     m st-2)
    (cut-meta-imp-consistent-p
     m st-1)
    (cut-meta-imp-consistent-p
     m st-2)
    (good-cut-meta-p m)
    (good-state-p st-1)
    (good-state-p st-2)
    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)
    (legal-inputp st-1 input)
    (legal-inputp st-2 input)
    (cl-checkpoint-body-input-p input))
   (equal
    (process-cut-step
     input st-1 m)
    (process-cut-step
     input st-2 m)))
:hints
(("Goal"
  :in-theory
  (disable
    ;; Keep the large hypotheses opaque.
    cut-markers-in-transit-p
    cut-meta-imp-consistent-p
    good-cut-meta-p
    good-state-p
    recovery-free-state-p
    legal-inputp
    cl-checkpoint-body-input-p
    ;; Keep the component relations available as hypotheses.
    procs-equivalent-p
    cl-checkpoint-control-equivalent-p
    ;; Avoid transition-system expansion.
    system-step
    cm-cut-not-taken-p
    get-msg-from-channel))
 ("Subgoal 1.4"
 :use
 ((:instance
   good-cut-meta-consistent-implies-initiator-in-state-proc-ids
   (m m)
   (st st-1))
  (:instance
   procs-equivalent-p-implies-nbrs-from-equal
   (ids
    (proc-ids st-1))
   (procs-1
    (procs st-1))
   (procs-2
    (procs st-2))
   (i
    (pid input)))))))

(defthm good-cut-meta-p-of-after-cut-input-sequence-update
  (implies
   (and
    (good-cut-meta-p m)
    (true-listp
     value))
   (good-cut-meta-p
    (s :after-cut-input-sequence
       value
       m))))

;; CROSS-STATE PRESERVATION OF CUT-META CONSISTENCY

(defthm cut-meta-imp-consistent-p-preserved-by-equivalent-state-step
  (implies
   (and
    (state-equivalent-p
     st-1 st-2)
    (cut-markers-in-transit-p
     m st-1)
    (cut-markers-in-transit-p
     m st-2)
    (cut-meta-imp-consistent-p
     m st-1)
    (cut-meta-imp-consistent-p
     m st-2)
    (good-cut-meta-p m)
    (good-state-p st-1)
    (good-state-p st-2)
    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)
    (legal-inputp st-1 input)
    (legal-inputp st-2 input)
    (cl-checkpoint-body-input-p input))
   (cut-meta-imp-consistent-p
    ;; Metadata computed from ST-1.
    (process-cut-step
     input st-1 m)
    ;; Implementation state computed from ST-2.
    (system-step
     st-2 input)))
  :hints
  (("Goal"
    :in-theory
    (disable state-equivalent-p
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-inputp
      cl-checkpoint-body-input-p
      process-cut-step
      system-step))))

;; CROSS-STATE PRESERVATION OF CUT MARKERS IN TRANSIT

(defthm cut-markers-in-transit-p-preserved-by-equivalent-state-step
  (implies
   (and
    (state-equivalent-p
     st-1 st-2)
    (cut-markers-in-transit-p
     m st-1)
    (cut-markers-in-transit-p
     m st-2)
    (cut-meta-imp-consistent-p
     m st-1)
    (cut-meta-imp-consistent-p
     m st-2)
    (good-cut-meta-p m)
    (good-state-p st-1)
    (good-state-p st-2)
    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)
    (legal-inputp st-1 input)
    (legal-inputp st-2 input)
    (cl-checkpoint-body-input-p input))
   (cut-markers-in-transit-p
    ;; Metadata computed from ST-1.
    (process-cut-step
     input st-1 m)
    ;; Implementation state computed from ST-2.
    (system-step
     st-2 input)))
  :hints
  (("Goal"
    :in-theory
    (disable state-equivalent-p
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-inputp
      cl-checkpoint-body-input-p
      process-cut-step
      system-step))))

(defthm number-of-before-cut-inputs-of-equal-process-cut-steps
  (implies
   (and
    (equal
     (g :proc-ids st-1)
     (g :proc-ids st-2))
    (equal
     (g :channels st-1)
     (g :channels st-2))
    (procs-equivalent-p
     (g :proc-ids st-1)
     (g :procs st-1)
     (g :procs st-2))
    (cl-checkpoint-control-equivalent-p
     (g :proc-ids st-1)
     (g :procs st-1)
     (g :procs st-2))
    (cut-markers-in-transit-p m st-1)
    (cut-markers-in-transit-p m st-2)
    (cut-meta-imp-consistent-p m st-1)
    (cut-meta-imp-consistent-p m st-2)
    (good-cut-meta-p m)
    (good-state-p st-1)
    (good-state-p st-2)
    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)
    (legal-inputp st-1 input)
    (legal-inputp st-2 input)
    (cl-checkpoint-body-input-p input))
   (equal
    (number-of-before-cut-inputs
     (system-step st-2 input)
     (process-cut-step input st-1 m)
     postfix)
    (number-of-before-cut-inputs
     (system-step st-2 input)
     (process-cut-step input st-2 m)
     postfix)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (process-cut-step-equal-for-equivalent-states)
    :in-theory
    (disable
     number-of-before-cut-inputs
     process-cut-step
     system-step
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     good-cut-meta-p
     good-state-p
     recovery-free-state-p
     legal-inputp
     cl-checkpoint-body-input-p))))

(defthm equal-of-plus-one-and-plus-one
  (implies
   (and
    (natp x)
    (natp y))
   (equal
    (equal
     (+ 1 x)
     (+ 1 y))
    (equal x y))))

(defthm natp-of-number-of-before-cut-inputs
  (natp
   (number-of-before-cut-inputs
    st m inputs)))

(defthm number-of-before-cut-inputs-equal-for-equivalent-states
  (implies
   (and
    (state-equivalent-p
     st-1 st-2)
    (cut-markers-in-transit-p
     m st-1)
    (cut-markers-in-transit-p
     m st-2)
    (cut-meta-imp-consistent-p
     m st-1)
    (cut-meta-imp-consistent-p
     m st-2)
    (good-cut-meta-p m)
    (good-state-p st-1)
    (good-state-p st-2)
    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)
    (true-listp postfix)
    (legal-input-sequencep
     st-1 postfix)
    (legal-input-sequencep
     st-2 postfix)
    (cl-checkpoint-body-inputs-p
     postfix))
   (equal
    (number-of-before-cut-inputs
     st-1 m postfix)
    (number-of-before-cut-inputs
     st-2 m postfix)))
  :hints
  (("Subgoal *1/3"
     :use
 ((:instance
   checkpoint-body-inputs-p-implies-first-is-body-input
   (inputs postfix))
  (:instance
   number-of-before-cut-inputs-of-equal-process-cut-steps
   (input
    (car postfix))
   (postfix
    (cdr postfix))))
    :expand
    ((number-of-before-cut-inputs
      st-2
      m
      postfix)))
   ("Subgoal *1/2"
    :use
((:instance
  number-of-before-cut-inputs-of-equal-process-cut-steps
  (st-1 st-1)
  (st-2 st-2)
  (m m)
  (input
   (car postfix))
  (postfix
   (cdr postfix))))
 :expand
 ((number-of-before-cut-inputs
   st-2
   m
   postfix)))
   ("Goal"
    :in-theory
    (disable cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-inputp
      cl-checkpoint-body-input-p
      procs-equivalent-p
      cl-checkpoint-control-equivalent-p
      system-step
      process-cut-step
      cm-cut-not-taken-p
      CL-CHECKPOINT-BODY-INPUTS-P
      true-listp
      get-msg-from-channel))))

;; Now we start proving commutivity of process-cut-step under swap-start condition.

;; RETIRE COMPLETED STATE-EQUIVALENCE/PREFIX PHASE

(in-theory
 (disable
  checkpoint-control-equivalent-p-implies-snapshot-ids-equal
  checkpoint-control-equivalent-p-implies-counter-equal
  procs-equivalent-p-implies-nbrs-from-equal
  state-equivalent-p-preserved-by-postfix
  post-pre-swap-start-implies-cp-inputs
  post-pre-swap-start-implies-cp-inputs-2
  one-post-pre-swap-with-prefix-and-postfix-final
  legal-input-sequencep-of-append-if
  front-post-pre-swap-preserves-legal-input-sequencep
  swap-first-after-before-preserves-run
  cm-cut-not-taken-p-implies-memberp-state-proc-ids
  good-cut-meta-consistent-implies-initiator-in-state-proc-ids
  input-sid-equality-implies-pid-in-state-proc-ids
  good-cut-meta-p-of-after-cut-input-sequence-update
  equal-of-plus-one-and-plus-one
  natp-of-number-of-before-cut-inputs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;Support Lemmas Start Here;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following metadata-commutation library has one exported result:
(encapsulate
 ()

(local-defthm counter-of-other-process-after-normal-system-step
  (implies
   (and
    (equal
     (g :ttype input)
     :normal)
    (not
     (equal
      proc-id
      (g :pid input))))
   (equal
    (g :counter
       (g proc-id
          (g :procs
             (system-step st input))))
    (g :counter
       (g proc-id
          (g :procs st))))))

(local-defthm marker-head-test-of-send-compute-message
  (equal
   (equal
    (msg-type
     (get-msg-from-channel
      src
      dst
      (send-compute-message
       local-state
       i
       nbrs
       channels)))
    :marker)
   (equal
    (msg-type
     (get-msg-from-channel
      src
      dst
      channels))
    :marker))
  :hints
  (("Goal"
    :induct
    (send-compute-message
     local-state
     i
     nbrs
     channels))))

(local-defthm marker-head-test-unchanged-by-normal-system-step
  (implies
   (equal
    (ttype input-post)
    :normal)
   (equal
    (equal
     (msg-type
      (get-msg-from-channel
       (sender input-pre)
       (pid input-pre)
       (channels
        (system-step st input-post))))
     :marker)
    (equal
     (msg-type
      (get-msg-from-channel
       (sender input-pre)
       (pid input-pre)
       (channels st)))
     :marker)))
  :hints
  (("Goal"
    :in-theory
    (disable send-compute-message
      get-msg-from-channel))))

(local-defthm marker-get-msg-implies-channel-consp
  (implies
   (equal
    (msg-type
     (get-msg-from-channel
      src dst channels))
    :marker)
   (consp
    (channel-state
     src dst channels))))

(local-defthm get-msg-from-channel-unchanged-by-normal-system-step-when-marker
  (implies
   (and
    (equal
     (ttype input-post)
     :normal)
    (equal
     (msg-type
      (get-msg-from-channel
       (sender input-pre)
       (pid input-pre)
       (channels st)))
     :marker))
   (equal
    (get-msg-from-channel
     (sender input-pre)
     (pid input-pre)
     (channels
      (system-step st input-post)))
    (get-msg-from-channel
     (sender input-pre)
     (pid input-pre)
     (channels st))))
  :hints
  (("Goal"
    :in-theory
    (disable send-compute-message
      get-msg-from-channel))))

(local-defthm get-msg-unchanged-by-normal-receive-at-different-dst
  (implies
   (and
    (equal
     (ttype input)
     :receive)
    (equal
     (msg-type
      (current-msg-for-receive
       input st))
     :normal)
    (not
     (equal
      dst
      (pid input))))
   (equal
    (get-msg-from-channel
     src
     dst
     (channels
      (system-step st input)))
    (get-msg-from-channel
     src
     dst
     (channels st))))
  :hints
  (("Goal"
    :in-theory
     (
      disable
      get-msg-from-channel
      remove-message-from-channel
      record-msg-in-snapshots
      two-imp-inputs-swappable-p
      post-pre-swap-start-p
      legal-inputp
      legal-input-sequencep
      no-recovery-step-p
      recovery-free-state-p
      good-state-p
      good-cut-meta-p
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p))))

(local-defthm swappable-receive-receive-preserves-get-messages
  (implies
   (and
    (two-imp-inputs-swappable-p
     st input-1 input-2)
    (equal
     (ttype input-1)
     :receive)
    (equal
     (ttype input-2)
     :receive))
   (and
    ;; INPUT-2 does not change the channel message seen by INPUT-1.
    (equal
     (get-msg-from-channel
      (sender input-1)
      (pid input-1)
      (channels
       (system-step st input-2)))
     (get-msg-from-channel
      (sender input-1)
      (pid input-1)
      (channels st)))
    ;; INPUT-1 does not change the channel message seen by INPUT-2.
    (equal
     (get-msg-from-channel
      (sender input-2)
      (pid input-2)
      (channels
       (system-step st input-1)))
     (get-msg-from-channel
      (sender input-2)
      (pid input-2)
      (channels st)))))
  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel
     remove-message-from-channel
     record-msg-in-snapshots))))

(local-defthm post-pre-receive-receive-preserves-get-msg
  (implies
   (and
    (post-pre-swap-start-p
     st m input-1 input-2)
    (equal
     (ttype input-1)
     :receive)
    (equal
     (ttype input-2)
     :receive))
   (and
    ;; INPUT-2 does not change the channel message seen by INPUT-1.
    (equal
     (get-msg-from-channel
      (sender input-1)
      (pid input-1)
      (channels
       (system-step st input-2)))
     (get-msg-from-channel
      (sender input-1)
      (pid input-1)
      (channels st)))
    ;; INPUT-1 does not change the channel message seen by INPUT-2.
    (equal
     (get-msg-from-channel
      (sender input-2)
      (pid input-2)
      (channels
       (system-step st input-1)))
     (get-msg-from-channel
      (sender input-2)
      (pid input-2)
      (channels st)))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-two-imp-inputs-swappable-p)
     (:instance
       swappable-receive-receive-preserves-get-messages)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Adding an input to either recorded sequence does not modify
;; CUT-NOT-TAKEN.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm cm-cut-not-taken-p-of-cm-add-before-cut-input-sequence
  (equal
   (cm-cut-not-taken-p
    (cm-add-before-cut-input-sequence
     m input)
    pid)
   (cm-cut-not-taken-p
    m pid)))

(local-defthm cm-cut-not-taken-p-of-cm-add-after-cut-input-sequence
  (equal
   (cm-cut-not-taken-p
    (cm-add-after-cut-input-sequence
     m input)
    pid)
   (cm-cut-not-taken-p
    m pid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Updates to BEFORE-CUT-INPUT-SEQUENCE and AFTER-CUT-INPUT-SEQUENCE
;; commute because they modify different fields of M.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm cm-add-before-and-after-cut-input-sequences-commute
  (equal
   (cm-add-before-cut-input-sequence
    (cm-add-after-cut-input-sequence
     m input-post)
    input-pre)
   (cm-add-after-cut-input-sequence
    (cm-add-before-cut-input-sequence
     m input-pre)
    input-post)))

(local-defthm sid-of-cm-add-after-cut-input-sequence
  (equal
   (g :sid
      (cm-add-after-cut-input-sequence
       m input))
   (g :sid m)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Removing a process from CUT-NOT-TAKEN and changing a waiting-marker
;; entry cannot introduce another process into CUT-NOT-TAKEN.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm marker-receive-update-does-not-introduce-cut-not-taken
  (implies
   (not
    (cm-cut-not-taken-p
     m other-pid))
   (not
    (cm-cut-not-taken-p
     (cm-set-waiting-marker-for
      (cm-remove-cut-not-taken
       m
       removed-pid)
      waiting-pid
      waiting-for)
     other-pid))))

;; Adding an AFTER-CUT input commutes with the metadata changes made when a marker is received: removing a PID from CUT-NOT-TAKEN and updating that PID's WAITING-MARKER-FROM entry.

(local-defthm marker-receive-update-commutes-with-add-after-cut-input-sequence
  (equal
   (cm-set-waiting-marker-for
    (cm-remove-cut-not-taken
     (cm-add-after-cut-input-sequence
      m
      input)
     removed-pid)
    waiting-pid
    waiting-for)
   (cm-add-after-cut-input-sequence
    (cm-set-waiting-marker-for
     (cm-remove-cut-not-taken
      m
      removed-pid)
     waiting-pid
     waiting-for)
    input)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Updating WAITING-MARKER-FROM after removing a PID cannot introduce
;; another PID into CUT-NOT-TAKEN.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm waiting-marker-update-after-remove-does-not-introduce-cut-not-taken
  (implies
   (not
    (cm-cut-not-taken-p
     m other-pid))
   (not
    (cm-cut-not-taken-p
     (s :waiting-marker-from
        waiting-marker-map
        (cm-remove-cut-not-taken
         m removed-pid))
     other-pid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The start-checkpoint WAITING-MARKER-FROM update commutes with adding
;; an input to AFTER-CUT-INPUT-SEQUENCE.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm start-checkpoint-waiting-update-commutes-with-add-after-cut-input
  (equal
   ;; Add the after-cut input first; then remove the checkpointing PID
   ;; and install its waiting-marker list.
   (s
    :waiting-marker-from
    (s
     waiting-pid
     waiting-for
     (g
      :waiting-marker-from
      (cm-remove-cut-not-taken
       (cm-add-after-cut-input-sequence
        m input)
       removed-pid)))
    (cm-remove-cut-not-taken
     (cm-add-after-cut-input-sequence
      m input)
     removed-pid))
   ;; Perform the checkpoint metadata update first; then add the
   ;; after-cut input.
   (cm-add-after-cut-input-sequence
    (s
     :waiting-marker-from
     (s
      waiting-pid
      waiting-for
      (g
       :waiting-marker-from
       (cm-remove-cut-not-taken
        m removed-pid)))
     (cm-remove-cut-not-taken
      m removed-pid))
    input)))

(local-defthm add-before-cut-input-commutes-with-after-cut-waiting-update
  (equal
   ;; First record INPUT-POST and update its waiting-marker list;
   ;; then record INPUT-PRE.
   (cm-add-before-cut-input-sequence
    (cm-set-waiting-marker-for
     (cm-add-after-cut-input-sequence
      m input-post)
     pid
     (remove1-equal
      sender
      (cm-waiting-marker-for
       (cm-add-after-cut-input-sequence
        m input-post)
       pid)))
    input-pre)
   ;; First record INPUT-PRE, then record INPUT-POST and perform
   ;; the same waiting-marker update.
   (cm-set-waiting-marker-for
    (cm-add-after-cut-input-sequence
     (cm-add-before-cut-input-sequence
      m input-pre)
     input-post)
    pid
    (remove1-equal
     sender
     (cm-waiting-marker-for
      (cm-add-after-cut-input-sequence
       (cm-add-before-cut-input-sequence
        m input-pre)
       input-post)
      pid)))))

(local-defthm sid-of-cm-add-before-cut-input-sequence
  (equal
   (g :sid
      (cm-add-before-cut-input-sequence
       m input))
   (g :sid m)))

(local-defthm cm-cut-not-taken-p-of-cm-set-waiting-marker-for
  (equal
   (cm-cut-not-taken-p
    (cm-set-waiting-marker-for
     m
     waiting-pid
     waiting-for)
    queried-pid)
   (cm-cut-not-taken-p
    m
    queried-pid)))

(local-defthm cm-remove-cut-not-taken-does-not-introduce-membership
  (implies
   (not
    (cm-cut-not-taken-p
     m queried-pid))
   (not
    (cm-cut-not-taken-p
     (cm-remove-cut-not-taken
      m removed-pid)
     queried-pid))))

(local-defthm post-get-msg-unchanged-in-receive-receive-post-pre-case
  (implies
   (and
    (cut-markers-in-transit-p m st)
    (cut-meta-imp-consistent-p m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)
    (legal-input-sequencep
     st
     (list input-post input-pre))
    (equal (ttype input-post) :receive)
    (equal (ttype input-pre) :receive)
    (not
     (cm-cut-not-taken-p
      m
      (pid input-post)))
    (cm-cut-not-taken-p
     m
     (pid input-pre))
    (not
     (equal
      (msg-type
       (get-msg-from-channel
        (sender input-post)
        (pid input-post)
        (channels st)))
      :marker)))
   (equal
    (get-msg-from-channel
     (sender input-post)
     (pid input-post)
     (channels
      (system-step st input-pre)))
    (get-msg-from-channel
     (sender input-post)
     (pid input-post)
     (channels st))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-receive-receive-preserves-get-msg
      (input-1 input-post)
      (input-2 input-pre)))
    :in-theory
    (disable
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     good-cut-meta-p
     good-state-p
     recovery-free-state-p
     legal-input-sequencep
     get-msg-from-channel
     system-step))))

(local-defthm pre-get-msg-unchanged-in-receive-receive-post-pre-case
  (implies
   (and
    (cut-markers-in-transit-p m st)
    (cut-meta-imp-consistent-p m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)
    (legal-input-sequencep
     st
     (list input-post input-pre))
    (equal (ttype input-post) :receive)
    (equal (ttype input-pre) :receive)
    (not
     (cm-cut-not-taken-p
      m
      (pid input-post)))
    (cm-cut-not-taken-p
     m
     (pid input-pre))
    (not
     (equal
      (msg-type
       (get-msg-from-channel
        (sender input-post)
        (pid input-post)
        (channels st)))
      :marker)))
   (equal
    (get-msg-from-channel
     (sender input-pre)
     (pid input-pre)
     (channels
      (system-step st input-post)))
    (get-msg-from-channel
     (sender input-pre)
     (pid input-pre)
     (channels st))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-receive-receive-preserves-get-msg
      (input-1 input-post)
      (input-2 input-pre)))
    :in-theory
    (disable
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     good-cut-meta-p
     good-state-p
     recovery-free-state-p
     legal-input-sequencep
     get-msg-from-channel
     system-step))))

(local-defthm post-get-msg-unchanged-under-post-pre-swap-start
  (implies
   (and
    (post-pre-swap-start-p
     st m input-post input-pre)
    (equal (ttype input-post) :receive)
    (equal (ttype input-pre) :receive))
   (equal
    (get-msg-from-channel
     (sender input-post)
     (pid input-post)
     (channels
      (system-step st input-pre)))
    (get-msg-from-channel
     (sender input-post)
     (pid input-post)
     (channels st))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-receive-receive-preserves-get-msg
      (input-1 input-post)
      (input-2 input-pre)))
    :in-theory
    (disable
     post-pre-swap-start-p
     post-pre-receive-receive-preserves-get-msg
     get-msg-from-channel
     system-step))))

(local-defthm pre-get-msg-unchanged-under-post-pre-swap-start
  (implies
   (and
    (post-pre-swap-start-p
     st m input-post input-pre)
    (equal (ttype input-post) :receive)
    (equal (ttype input-pre) :receive))
   (equal
    (get-msg-from-channel
     (sender input-pre)
     (pid input-pre)
     (channels
      (system-step st input-post)))
    (get-msg-from-channel
     (sender input-pre)
     (pid input-pre)
     (channels st))))
  :hints
  (("Goal"
    :use
    ((:instance
      post-pre-receive-receive-preserves-get-msg
      (input-1 input-post)
      (input-2 input-pre)))
    :in-theory
    (disable
     post-pre-swap-start-p
     post-pre-receive-receive-preserves-get-msg
     get-msg-from-channel
     system-step))))

(local-defthm post-target-marker-type-preserved-after-pre-receive
  (implies
   (and
    (cut-markers-in-transit-p m st)
    (cut-meta-imp-consistent-p m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)
    (legal-input-sequencep
     st
     (list input-post input-pre))
    (equal
     (ttype input-post)
     :receive)
    (equal
     (ttype input-pre)
     :receive)
    (not
     (cm-cut-not-taken-p
      m
      (pid input-post)))
    (cm-cut-not-taken-p
     m
     (pid input-pre))
    (equal
     (msg-type
      (get-msg-from-channel
       (sender input-post)
       (pid input-post)
       (channels st)))
     :marker)
    (equal
     (sid
      (get-msg-from-channel
       (sender input-post)
       (pid input-post)
       (channels st)))
     (sid m)))
   ;; It must still see a marker after moving INPUT-PRE first.
   (equal
    (msg-type
     (get-msg-from-channel
      (sender input-post)
      (pid input-post)
      (channels
       (system-step st input-pre))))
    :marker))
  :hints
  (("Goal"
    :use
    (post-pre-receive-receive-preserves-get-msg)
    :in-theory
    (disable
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     good-cut-meta-p
     good-state-p
     recovery-free-state-p
     legal-input-sequencep
     get-msg-from-channel
     system-step)))
  :rule-classes
  ((:rewrite
    :match-free :all)))

(local-defthm post-target-marker-sid-preserved-after-pre-receive
  (implies
   (and
    (cut-markers-in-transit-p m st)
    (cut-meta-imp-consistent-p m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)
    (legal-input-sequencep
     st
     (list input-post input-pre))
    (equal
     (ttype input-post)
     :receive)
    (equal
     (ttype input-pre)
     :receive)
    (not
     (cm-cut-not-taken-p
      m
      (pid input-post)))
    (cm-cut-not-taken-p
     m
     (pid input-pre))
    (equal
     (msg-type
      (get-msg-from-channel
       (sender input-post)
       (pid input-post)
       (channels st)))
     :marker)
    (equal
     (sid
      (get-msg-from-channel
       (sender input-post)
       (pid input-post)
       (channels st)))
     (sid m)))
   ;; Its SID must remain the target SID after INPUT-PRE.
   (equal
    (sid
     (get-msg-from-channel
      (sender input-post)
      (pid input-post)
      (channels
       (system-step st input-pre))))
    (sid m)))
  :hints
  (("Goal"
    :use
    (post-pre-receive-receive-preserves-get-msg)
    :in-theory
    (disable
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     good-cut-meta-p
     good-state-p
     recovery-free-state-p
     legal-input-sequencep
     get-msg-from-channel
     system-step)))
  :rule-classes
  ((:rewrite
    :match-free :all)))

(local-defthm pre-get-msg-unchanged-when-post-sees-target-marker
  (implies
   (and
    (cut-markers-in-transit-p m st)
    (cut-meta-imp-consistent-p m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)
    (legal-input-sequencep
     st
     (list input-post input-pre))
    (equal (ttype input-post) :receive)
    (equal (ttype input-pre) :receive)
    (not
     (cm-cut-not-taken-p
      m
      (pid input-post)))
    (cm-cut-not-taken-p
     m
     (pid input-pre))
    (equal
     (msg-type
      (get-msg-from-channel
       (sender input-post)
       (pid input-post)
       (channels st)))
     :marker)
    (equal
     (sid
      (get-msg-from-channel
       (sender input-post)
       (pid input-post)
       (channels st)))
     (sid m)))
   (equal
    (get-msg-from-channel
     (sender input-pre)
     (pid input-pre)
     (channels
      (system-step st input-post)))
    (get-msg-from-channel
     (sender input-pre)
     (pid input-pre)
     (channels st))))
  :hints
  (("Goal"
    :use
    (post-pre-receive-receive-preserves-get-msg)
    :in-theory
    (disable
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     good-cut-meta-p
     good-state-p
     recovery-free-state-p
     legal-input-sequencep
     get-msg-from-channel
     system-step)))
  :rule-classes
  ((:rewrite
    :match-free :all)))

(local-defthm post-pre-cut-status-implies-pids-different
  (implies
   (and
    (not
     (cm-cut-not-taken-p
      m
      (pid input-post)))
    (cm-cut-not-taken-p
     m
     (pid input-pre)))
   (not
    (equal
     (pid input-post)
     (pid input-pre))))
  :rule-classes
  ((:rewrite
    :match-free :all)))

(local-defthm cm-post-pre-target-marker-updates-commute
  (let*
      (;; Metadata after recording both inputs in their global
       ;; before/after sequences.
       (base
        (cm-add-after-cut-input-sequence
         (cm-add-before-cut-input-sequence
          m input-pre)
         input-post))
       ;; Waiting-marker update performed by INPUT-POST.
       (post-waiting
        (remove1-equal
         sender-post
         (cm-waiting-marker-for
          base
          post-pid)))
       ;; Waiting-marker list installed when INPUT-PRE takes the cut.
       (pre-waiting
        (remove1-equal
         sender-pre
         pre-nbrs-from))
       ;; Metadata obtained by processing INPUT-PRE first.
       (after-pre
        (cm-set-waiting-marker-for
         (cm-remove-cut-not-taken
          (cm-add-before-cut-input-sequence
           m input-pre)
          pre-pid)
         pre-pid
         pre-waiting))
       ;; Then record INPUT-POST as an after-cut input.
       (after-pre-post-sequence
        (cm-add-after-cut-input-sequence
         after-pre
         input-post)))
    (implies
     (not
      (equal post-pid pre-pid))
     (equal
      ;; INPUT-POST marker update followed by INPUT-PRE cut update.
      (cm-set-waiting-marker-for
       (cm-remove-cut-not-taken
        (cm-set-waiting-marker-for
         base
         post-pid
         post-waiting)
        pre-pid)
       pre-pid
       pre-waiting)
      ;; INPUT-PRE cut update followed by INPUT-POST marker update.
      (cm-set-waiting-marker-for
       after-pre-post-sequence
       post-pid
       (remove1-equal
        sender-post
        (cm-waiting-marker-for
         after-pre-post-sequence
         post-pid)))))))

(local-defthm sid-of-cm-set-waiting-marker-for
  (equal
   (g :sid
      (cm-set-waiting-marker-for
       m i xs))
   (g :sid m)))

(local-defthm sid-of-cm-remove-cut-not-taken
  (equal
   (g :sid
      (cm-remove-cut-not-taken
       m i))
   (g :sid m)))

;; Corrected hints.

(local-defthm get-msg-from-channel-after-start-checkpoint-when-consp
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
   (equal
    (get-msg-from-channel
     src
     dst
     (channels
      (system-step st input)))
    (get-msg-from-channel
     src
     dst
     (channels st))))
  :hints
  (("Goal"
    :in-theory
    (disable
     send-msg-all-outgoing-channels
     get-msg-from-channel
     start-checkpoint-helper
     create-marker-message))))

;; LEGAL-INPUT-SEQUENCEP may expand to establish legality of INPUT-POST.

(local-defthm post-receive-get-msg-unchanged-by-pre-start-checkpoint
  (implies
   (and
    (legal-input-sequencep
     st
     (list input-post input-pre))
    (equal
     (ttype input-post)
     :receive)
    (equal
     (ttype input-pre)
     :start-checkpoint))
   (equal
    (get-msg-from-channel
     (sender input-post)
     (pid input-post)
     (channels
      (system-step st input-pre)))
    (get-msg-from-channel
     (sender input-post)
     (pid input-post)
     (channels st))))
  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel
     send-msg-all-outgoing-channels))))

;; A RECEIVE step updates only the receiving process, PID(INPUT).

(local-defthm counter-of-other-process-after-receive-system-step
  (implies
   (and
    (equal
     (ttype input)
     :receive)
    (not
     (equal
      proc-id
      (pid input))))
   (equal
    (counter
     (g proc-id
        (procs
         (system-step st input))))
    (counter
     (g proc-id
        (procs st)))))
  :hints
  (("Goal"
    :in-theory
    (disable
     get-msg-from-channel
     remove-message-from-channel
     send-msg-all-outgoing-channels
     record-msg-in-snapshots
     replay-msgs-on-channel
     replay-channel-snapshots))))

;; Reversed orientation needed by COUNTER-OF-OTHER-PROCESS-AFTER-RECEIVE-SYSTEM-STEP.

(local-defthm post-pre-cut-status-implies-reversed-pids-different
  (implies
   (and
    (not
     (cm-cut-not-taken-p
      m
      (pid input-post)))
    (cm-cut-not-taken-p
     m
     (pid input-pre)))
   (not
    (equal
     (pid input-pre)
     (pid input-post))))
  :hints
  (("Goal"
    :cases
    ((equal
      (pid input-post)
      (pid input-pre)))))
  :rule-classes
  ((:rewrite
    :match-free :all)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A post-cut marker receive at POST-PID commutes with the metadata update
;; made when the different process PRE-PID starts/takes the target cut.
;;
;; The lemma deliberately uses the raw S form for the PRE-PID waiting-marker
;; update because PROCESS-CUT-STEP has already expanded that update into S in
;; Subgoal 28.2.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm cm-post-marker-update-commutes-with-pre-start-cut-update
  (let*
      (;; Record INPUT-PRE in the global before-cut sequence and INPUT-POST
       ;; in the global after-cut sequence.
       (base
        (cm-add-after-cut-input-sequence
         (cm-add-before-cut-input-sequence
          m input-pre)
         input-post))
       ;; Waiting-marker list after INPUT-POST receives its marker.
       (post-waiting
        (remove1-equal
         post-sender
         (cm-waiting-marker-for
          base
          post-pid)))
       ;; Metadata after the POST-PID waiting-marker update.
       (after-post-marker
        (cm-set-waiting-marker-for
         base
         post-pid
         post-waiting))
       ;; Then remove PRE-PID from CUT-NOT-TAKEN.
       (left-before-pre-waiting
        (cm-remove-cut-not-taken
         after-post-marker
         pre-pid))
       ;; Metadata obtained by first recording INPUT-PRE and removing
       ;; PRE-PID from CUT-NOT-TAKEN.
       (right-before-pre-waiting
        (cm-remove-cut-not-taken
         (cm-add-before-cut-input-sequence
          m input-pre)
         pre-pid))
       ;; Raw form of installing PRE-PID's initial waiting-marker list.
       (after-pre-start
        (s :waiting-marker-from
           (s pre-pid
              pre-waiting
              (g :waiting-marker-from
                 right-before-pre-waiting))
           right-before-pre-waiting))
       ;; Then record INPUT-POST in the global after-cut sequence.
       (after-pre-start-post-sequence
        (cm-add-after-cut-input-sequence
         after-pre-start
         input-post)))
    (implies
     (not
      (equal post-pid pre-pid))
     (equal
      ;; POST marker update first, followed by PRE start-cut update.
      (s :waiting-marker-from
         (s pre-pid
            pre-waiting
            (g :waiting-marker-from
               left-before-pre-waiting))
         left-before-pre-waiting)
      ;; PRE start-cut update first, followed by POST marker update.
      (cm-set-waiting-marker-for
       after-pre-start-post-sequence
       post-pid
       (remove1-equal
        post-sender
        (cm-waiting-marker-for
         after-pre-start-post-sequence
         post-pid))))))
  ;; Splitting explicitly on the PID equality helps the records library
  ;; normalize the two updates at distinct keys.
  :hints
  (("Goal"
    :cases
    ((equal post-pid pre-pid)))))

;; Adding a before-cut input commutes with the metadata update performed when a process starts its checkpoint: 1.

(local-defthm start-checkpoint-waiting-update-commutes-with-add-before-cut-input
  (equal
   (s
    :waiting-marker-from
    (s
     waiting-pid
     waiting-for
     (g
      :waiting-marker-from
      (cm-remove-cut-not-taken
       (cm-add-before-cut-input-sequence m input)
       removed-pid)))
    (cm-remove-cut-not-taken
     (cm-add-before-cut-input-sequence m input)
     removed-pid))
   (cm-add-before-cut-input-sequence
    (s
     :waiting-marker-from
     (s
      waiting-pid
      waiting-for
      (g
       :waiting-marker-from
       (cm-remove-cut-not-taken
        m
        removed-pid)))
     (cm-remove-cut-not-taken
      m
      removed-pid))
    input)))

(local-defthm remove1-equal-distinct-commute
  (implies
   (not (equal x y))
   (equal
    (remove1-equal
     x
     (remove1-equal y xs))
    (remove1-equal
     y
     (remove1-equal x xs))))
  ;; This induction branches when X is the first element.
  ;; The simplifier handles the corresponding Y case.
  :hints
  (("Goal"
    :induct
    (remove1-equal x xs))))

(local-defthm start-checkpoint-update-commutes-with-before-cut-marker-receive-update
  (let*
      (;; Metadata update performed when INPUT-POST starts its checkpoint.
       (post-update
        (s
         :waiting-marker-from
         (s
          post-pid
          post-waiting
          (g
           :waiting-marker-from
           (cm-remove-cut-not-taken
            m
            post-pid)))
         (cm-remove-cut-not-taken
          m
          post-pid)))
       ;; Original order:
       (pre-after-post
        (cm-set-waiting-marker-for
         (cm-remove-cut-not-taken
          (cm-add-before-cut-input-sequence
           post-update
           input-pre)
          pre-pid)
         pre-pid
         pre-waiting))
       ;; Swapped order:
       ;; PRE is recorded and processes its target marker first.
       (pre-update
        (cm-set-waiting-marker-for
         (cm-remove-cut-not-taken
          (cm-add-before-cut-input-sequence
           m
           input-pre)
          pre-pid)
         pre-pid
         pre-waiting))
       ;; INPUT-POST then starts its checkpoint.
       ;; Keep this in the raw S form occurring in the checkpoint.
       (post-after-pre
        (s
         :waiting-marker-from
         (s
          post-pid
          post-waiting
          (g
           :waiting-marker-from
           (cm-remove-cut-not-taken
            pre-update
            post-pid)))
         (cm-remove-cut-not-taken
          pre-update
          post-pid))))
    (implies
     (and
      (not
       (cm-cut-not-taken-p
        m
        post-pid))
      (cm-cut-not-taken-p
       m
       pre-pid))
     (equal
      pre-after-post
      post-after-pre)))
  ;; The equal-PID case contradicts the two cut-status hypotheses.
  ;; In the different-PID case, the record updates commute.
  :hints
  (("Goal"
    :cases
    ((equal post-pid pre-pid)))))

;; If process I has already taken the target cut, its current (PID, COUNTER) pair cannot equal the target SID.

(local-defthm cut-meta-consistency-cut-taken-implies-current-sid-not-target
  (implies
   (and
    (cut-meta-imp-consistent-p
     m
     st)
    (not
     (cm-cut-not-taken-p
      m
      i)))
   (not
    (equal
     (list
      i
      (counter
       (g i (procs st))))
     (cm-sid m))))
  :hints
  (("Goal"
    :cases
    ((equal
      (list
       i
       (counter
        (g i (procs st))))
      (cm-sid m)))
    :in-theory
    (disable
     cut-meta-imp-procs-consistent-p))))

;; Complete counter behavior of a START-CHECKPOINT step:

(local-defthm counter-after-start-checkpoint-system-step
  (implies
   (equal
    (ttype input)
    :start-checkpoint)
   (equal
    (counter
     (g proc-id
        (procs
         (system-step st input))))
    (if
     (equal
      proc-id
      (pid input))
     (+ 1
        (counter
         (g proc-id
            (procs st))))
     (counter
      (g proc-id
         (procs st))))))
  :hints
  (("Goal"
    :cases
    ((equal
      proc-id
      (pid input))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;Support Lemmas End Here;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; PROCESS-CUT-STEP COMMUTES FOR ONE POST-CUT / BEFORE-CUT SWAP

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; If two processes have different CUT-NOT-TAKEN status,
;; they cannot be the same process.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm
  cl-cut-not-taken-status-different-implies-pids-different

  (implies
   (and
    (cm-cut-not-taken-p m i)
    (not (cm-cut-not-taken-p m j)))

   (not
    (equal i j))))


;; The metadata transition for starting the target checkpoint at I commutes with processing a marker at another process J.

(defthm
  cl-cut-take-update-commutes-with-other-waiting-update

  (implies
   (not (equal i j))

   (equal
    ;; Update J first, then I takes the cut.
    (cm-set-waiting-marker-for
     (cm-remove-cut-not-taken
      (cm-set-waiting-marker-for m j wj)
      i)
     i
     wi)

    ;; I takes the cut first, then update J.
    (cm-set-waiting-marker-for
     (cm-set-waiting-marker-for
      (cm-remove-cut-not-taken m i)
      i
      wi)
     j
     wj))))


(defthm
  cl-waiting-marker-for-after-other-proc-taking-cut

  (implies
   (not
    (equal i j))

   (equal
    (cm-waiting-marker-for

     (cm-add-after-cut-input-sequence

      (cm-set-waiting-marker-for
       (cm-remove-cut-not-taken m i)
       i
       wi)

      input)

     j)

    (cm-waiting-marker-for

     (cm-add-after-cut-input-sequence
      m
      input)

     j))))

(defthm
  cl-waiting-marker-for-unchanged-by-other-proc-taking-cut

  (implies
   (not
    (equal i j))

   (equal
    (cm-waiting-marker-for

     (cm-set-waiting-marker-for
      (cm-remove-cut-not-taken m i)
      i
      wi)

     j)

    (cm-waiting-marker-for
     m
     j))))
  
(defthm post-pre-two-process-cut-steps-commute
    (implies
     (and
      (post-pre-swap-start-p
       st
       m
       input-post
       input-pre)
      (cl-checkpoint-body-input-p input-post)
      (cl-checkpoint-body-input-p input-pre))
   (equal
    ;; Metadata after the original POST/PRE order.
    (process-cut-step
     input-pre
     (system-step
      st
      input-post)
     (process-cut-step
      input-post
      st
      m))
    ;; Metadata after the swapped PRE/POST order.
    (process-cut-step
     input-post
     (system-step
      st
      input-pre)
     (process-cut-step
      input-pre
      st
      m))))
  :hints
  (("Goal"
    :in-theory
    (disable
     system-step
     cm-cut-not-taken
     good-state-p
     good-cut-meta-p
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     recovery-free-state-p
     get-msg-from-channel
     remove-message-from-channel
     legal-input-sequencep
     legal-inputp
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

) ;; end local metadata-commutation library

;; Everything in this block is private support for the exported reordering characterization at its end.
(encapsulate
 ()

(local-defthm number-of-before-cut-inputs-after-post-pre-pair-commutes
  (let* (;; Original order: POST, PRE.
         (st-after-post
          (system-step st input-post))
         (m-after-post
          (process-cut-step
           input-post st m))
         (st-after-post-pre
          (system-step
           st-after-post
           input-pre))
         (m-after-post-pre
          (process-cut-step
           input-pre
           st-after-post
           m-after-post))
         ;; Swapped order: PRE, POST.
         (st-after-pre
          (system-step st input-pre))
         (m-after-pre
          (process-cut-step
           input-pre st m))
         (st-after-pre-post
          (system-step
           st-after-pre
           input-post))
         (m-after-pre-post
          (process-cut-step
           input-post
           st-after-pre
           m-after-pre)))
    (implies
     (and
      (post-pre-swap-start-p
       st m input-post input-pre)
      (true-listp postfix)
      (legal-input-sequencep
       st
       (append
        (list input-post input-pre)
        postfix))
      (cl-checkpoint-body-inputs-p
       (append
        (list input-post input-pre)
        postfix)))
     (equal
      ;; Suffix count after PRE, POST.
      (number-of-before-cut-inputs
       st-after-pre-post
       m-after-pre-post
       postfix)
      ;; Suffix count after POST, PRE.
      (number-of-before-cut-inputs
       st-after-post-pre
       m-after-post-pre
       postfix))))
    :hints
  (("Goal"
    :do-not-induct t
    :use
    (;; ---------------------------------------------------------
     ;; The two pair executions produce equivalent states.
     ;; ---------------------------------------------------------
     (:instance
      front-post-pre-swap-start-implies-state-equivalent
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     ;; ---------------------------------------------------------
     ;; The two pair executions produce exactly equal metadata.
     ;; ---------------------------------------------------------
     (:instance
      post-pre-two-process-cut-steps-commute
      (st st)
      (m m)
      (input-post input-post)
      (input-pre input-pre))
     ;; ---------------------------------------------------------
     ;; Both pair-result states are good and recovery-free.
     ;; ---------------------------------------------------------
     (:instance
      post-pre-swap-start-implies-pair-states-good-and-recovery-free
      (st st)
      (m m)
      (input-1 input-post)
      (input-2 input-pre))
     ;; ---------------------------------------------------------
     ;; The swapped two-input prefix is legal.
     ;; ---------------------------------------------------------
     (:instance
      front-post-pre-swap-start-implies-swapped-pair-legal
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     ;; ---------------------------------------------------------
     ;; POSTFIX is legal after the original pair.
     ;; ---------------------------------------------------------
     (:instance
      legal-input-sequencep-of-append-implies-second
      (st st)
      (inputs-1
       (list input-post input-pre))
      (inputs-2 postfix))
     ;; ---------------------------------------------------------
     ;; POSTFIX is also legal after the swapped pair.
     ;; ---------------------------------------------------------
     (:instance
      front-post-pre-swap-start-implies-swapped-postfix-legal
      (st st)
      (m m)
      (inputs
       (append
        (list input-post input-pre)
        postfix)))
     ;; ---------------------------------------------------------
     ;; Extract the checkpoint-body property of POSTFIX.
     ;; Apply the REST projection twice.
     ;; ---------------------------------------------------------
     (:instance
      checkpoint-body-inputs-p-implies-rest
      (inputs
       (append
        (list input-post input-pre)
        postfix)))
     (:instance
      checkpoint-body-inputs-p-implies-rest
      (inputs
       (rest
        (append
         (list input-post input-pre)
         postfix))))
     ;; ---------------------------------------------------------
     ;; Invariants after the original POST/PRE pair.
     ;; ---------------------------------------------------------
     (:instance
      good-cut-meta-p-over-process-cut-segment
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     (:instance
      cut-meta-imp-consistent-p-over-process-cut-segment
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     (:instance
      cut-markers-in-transit-p-preserved-by-segment
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     ;; ------------------------------------------------------------
     ;; Invariants after the swapped PRE/POST pair.
     ;; ------------------------------------------------------------
     (:instance
      cut-meta-imp-consistent-p-over-process-cut-segment
      (st st)
      (m m)
      (inputs
       (list input-pre input-post)))
     (:instance
      cut-markers-in-transit-p-preserved-by-segment
      (st st)
      (m m)
      (inputs
       (list input-pre input-post)))
     ;; ------------------------------------------------------------
     ;; Apply the previously proved count-equivalence theorem.
     ;; ------------------------------------------------------------
     (:instance
      number-of-before-cut-inputs-equal-for-equivalent-states
      (st-1
       (run-imp
        st
        (list input-post input-pre)))
      (st-2
       (run-imp
        st
        (list input-pre input-post)))
      (m
       (process-cut-segment
        (list input-post input-pre)
        st
        m))
      (postfix postfix)))
    :in-theory
    (disable
      ;; Keep all semantic predicates and recursive counting opaque.
      number-of-before-cut-inputs
      state-equivalent-p
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-input-sequencep
      legal-inputp
      cl-checkpoint-body-inputs-p
      cl-checkpoint-body-input-p
      process-cut-step
      system-step
      cm-cut-not-taken-p
      true-listp
      ;; These are supplied explicitly above.
      number-of-before-cut-inputs-equal-for-equivalent-states
      post-pre-two-process-cut-steps-commute
      front-post-pre-swap-start-implies-state-equivalent
      front-post-pre-swap-start-implies-swapped-pair-legal
      front-post-pre-swap-start-implies-swapped-postfix-legal
      post-pre-swap-start-implies-pair-states-good-and-recovery-free
      legal-input-sequencep-of-append-implies-second
      checkpoint-body-inputs-p-implies-rest
      good-cut-meta-p-over-process-cut-segment
      cut-meta-imp-consistent-p-over-process-cut-segment
      cut-markers-in-transit-p-preserved-by-segment))))

;; Projection from POST-PRE-SWAP-START-P needed when expanding
;; NUMBER-OF-BEFORE-CUT-INPUTS in the original POST/PRE order.
(local-defthm post-pre-swap-start-p-implies-second-pre-cut-after-first
  (implies
   (post-pre-swap-start-p
    st m input-post input-pre)
   (cm-cut-not-taken-p
    (process-cut-step
     input-post st m)
    (pid input-pre)))
  :hints
  (("Goal"
    ;; Open only the swap-start predicate; keep its components opaque.
    :in-theory
    (disable process-cut-step
      cm-cut-not-taken-p
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-input-sequencep
      cl-checkpoint-body-input-p)))
  :rule-classes nil)

(local-defthm number-of-before-cut-inputs-of-swap-first-after-before
  (implies
   (and
    (true-listp inputs)
    (cut-markers-in-transit-p
     m st)
    (cut-meta-imp-consistent-p
     m st)
    (good-cut-meta-p
     m)
    (good-state-p
     st)
    (recovery-free-state-p
     st)
    (legal-input-sequencep
     st inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (equal
    (number-of-before-cut-inputs
     st
     m
     (swap-first-after-before
      st m inputs))
    (number-of-before-cut-inputs
     st m inputs)))
  :hints
  (("Goal"
    :induct
    (swap-first-after-before
     st m inputs)
    :in-theory
    (disable
     post-pre-swap-start-p
     process-cut-step
     system-step
     cm-cut-not-taken-p
     good-state-p
     good-cut-meta-p
     cut-meta-imp-consistent-p
     legal-input-sequencep
     legal-inputp
     cl-checkpoint-body-inputs-p
     cl-checkpoint-body-input-p
     recovery-free-state-p
     cut-markers-in-transit-p))
   ("Subgoal *1/2.2"
    :use
    ((:instance
      post-pre-swap-start-p-implies-second-pre-cut-at-start
      (input-1 (first inputs))
      (input-2 (second inputs)))))
   ("Subgoal *1/2.4'"
    :use
    ((:instance
      post-pre-swap-start-p-implies-first-post-cut
      (input-1
       (first inputs))
      (input-2
       (second inputs)))))
   ("Subgoal *1/2.1"
    :use
    ((:instance
      post-pre-swap-start-p-implies-second-pre-cut-at-start
      (input-1
       (first inputs))
      (input-2
       (second inputs)))))
  ("Subgoal *1/2.3'"
 :use
 ((:instance
   post-pre-swap-start-p-implies-first-post-cut
   (st st)
   (m m)
   (input-1
    (car inputs))
   (input-2
    (cadr inputs)))
  (:instance
   post-pre-swap-start-p-implies-second-pre-cut-after-first
   (st st)
   (m m)
   (input-post
    (car inputs))
   (input-pre
    (cadr inputs)))
  (:instance
   number-of-before-cut-inputs-after-post-pre-pair-commutes
   (st st)
   (m m)
   (input-post
    (car inputs))
   (input-pre
    (cadr inputs))
   (postfix
    (cddr inputs))))
 ;; First expansion handles INPUT-POST.
 ;; Second expansion handles INPUT-PRE.
 :expand
 ((number-of-before-cut-inputs
   st
   m
   inputs)
  (number-of-before-cut-inputs
   (system-step
    st
    (car inputs))
   (process-cut-step
    (car inputs)
    st
    m)
   (cdr inputs))))))

;; ------------------------------------------------------------
;; If the first input is POST and some PRE input remains, then the first POST contributes at least one inversion.
;; ------------------------------------------------------------

(local-defthm first-after-with-positive-before-count-has-positive-inversion-count
  (implies
   (and
    (consp inputs)
    (not
     (cm-cut-not-taken-p
      m
      (pid (first inputs))))
    (< 0
       (number-of-before-cut-inputs
        st m inputs)))
   (< 0
      (inversion-count
       st m inputs)))
  :hints
  (("Goal"
    :do-not-induct t
    ;; The suffix inversion count is nonnegative.
    :use
    ((:instance
      natp-of-inversion-count
      (st
       (system-step st (first inputs)))
      (m
       (process-cut-step
        (first inputs)
        st
        m))
      (inputs
       (rest inputs))))
    ;; Expand exactly one recursion level.
    :expand
    ((inversion-count st m inputs)
     (number-of-before-cut-inputs
      st m inputs))
    :in-theory
    (disable
     ;; Critical: keep the recursive suffix calls closed.
     inversion-count
     number-of-before-cut-inputs
     system-step
     process-cut-step
     cm-cut-not-taken-p))))

(local-defthm zero-inversion-count-and-positive-before-count-implies-first-before
  (implies
   (and
    (consp inputs)
    (equal
     (inversion-count st m inputs)
     0)
    (< 0
       (number-of-before-cut-inputs
        st m inputs)))
   (cm-cut-not-taken-p
    m
    (pid (first inputs))))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance
      first-after-with-positive-before-count-has-positive-inversion-count))
    :in-theory
    (disable
     first-after-with-positive-before-count-has-positive-inversion-count
     inversion-count
     number-of-before-cut-inputs
     system-step
     process-cut-step
     cm-cut-not-taken-p))))

;; ------------------------------------------------------------
;; A dynamically classified adjacent POST/PRE pair is swappable.
;; ------------------------------------------------------------

(local-defthm fixed-post-pre-inversion-is-swappable
  (implies
   (and
    (consp inputs)
    (consp (rest inputs))
    (cut-markers-in-transit-p m st)
    (cut-meta-imp-consistent-p m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)
    (legal-input-sequencep st inputs)
    (cl-checkpoint-body-inputs-p inputs)
    (not
     (cm-cut-not-taken-p
      m
      (pid (first inputs))))
    (cm-cut-not-taken-p
     (process-cut-step
      (first inputs)
      st
      m)
     (pid (second inputs))))
   (post-pre-swap-start-p
    st
    m
    (first inputs)
    (second inputs)))
  :hints
  (("Goal"
    :use
    (;; Legality of the first input.
     (:instance
      legal-input-sequencep-implies-first-legal
      (inputs inputs))
     ;; Legality of the remaining sequence after the first input.
     (:instance
      legal-input-sequencep-implies-rest-legal
      (inputs inputs))
     ;; Legality of the second input in the state after the first.
     (:instance
      legal-input-sequencep-implies-first-legal
      (st
       (system-step st (first inputs)))
      (inputs
       (rest inputs)))
     ;; Body-input property of the first input.
     (:instance
      checkpoint-body-inputs-p-implies-first-is-body-input
      (inputs inputs))
     ;; Body-input property of the remaining sequence.
     (:instance
      checkpoint-body-inputs-p-implies-rest
      (inputs inputs))
     ;; Body-input property of the second input.
     (:instance
      checkpoint-body-inputs-p-implies-first-is-body-input
      (inputs
       (rest inputs))))
    :in-theory
    (disable system-step
      process-cut-step
      cm-cut-not-taken-p
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-inputp
      cl-checkpoint-body-input-p
      cl-checkpoint-body-inputs-p)))
  :rule-classes nil)

;; ONCE POST-CUT, ALWAYS POST-CUT

(local-defthm post-cut-remains-post-after-process-cut-step
  (implies
   (not
    (cm-cut-not-taken-p
     m i))
   (not
    (cm-cut-not-taken-p
     (process-cut-step input st m)
     i)))
  :hints
  (("Goal"
    :use
    (cm-cut-not-taken-p-after-process-cut-step-implies-before)
    ;; This is only propositional contraposition.
    :in-theory
    (theory
     'minimal-theory))))

;; COMPLETE CUT CLASSIFICATION OF A POST/PRE SWAP

(local-defthm post-pre-swap-start-p-implies-complete-cut-classification
  (implies
   (post-pre-swap-start-p
    st
    m
    input-post
    input-pre)
   (and
    ;; INPUT-POST is initially post-cut.
    (not
     (cm-cut-not-taken-p
      m
      (pid input-post)))
    ;; INPUT-PRE is pre-cut immediately before it executes in
    ;; the original POST/PRE order.
    (cm-cut-not-taken-p
     (process-cut-step
      input-post
      st
      m)
     (pid input-pre))
    ;; Since PROCESS-CUT-STEP cannot introduce pre-cut membership,
    ;; INPUT-PRE was already pre-cut in M.
    (cm-cut-not-taken-p
     m
     (pid input-pre))
    ;; Processing INPUT-PRE first cannot make INPUT-POST pre-cut again.
    (not
     (cm-cut-not-taken-p
      (process-cut-step
       input-pre
       st
       m)
      (pid input-post)))))
  :hints
  (("Goal"
    :use
    (;; Obtain the initial post-cut classification.
     (:instance
      post-pre-swap-start-p-implies-first-post-cut
      (input-1 input-post)
      (input-2 input-pre))
     ;; Obtain the initial pre-cut classification of INPUT-PRE.
     (:instance
      post-pre-swap-start-p-implies-second-pre-cut-at-start
      (input-1 input-post)
      (input-2 input-pre))
     ;; INPUT-POST remains post-cut after processing INPUT-PRE.
     (:instance
      post-cut-remains-post-after-process-cut-step
      (input input-pre)
      (i (pid input-post))))
    ;; Opening the swap predicate supplies the second classification:
    ;; INPUT-PRE is pre-cut after processing INPUT-POST.
    :in-theory
    (disable process-cut-step
      system-step
      cm-cut-not-taken-p
      good-state-p
      good-cut-meta-p
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      recovery-free-state-p
      legal-input-sequencep
      legal-inputp
      cl-checkpoint-body-input-p
     ; post-pre-swap-start-p-implies-first-post-cut
     ; post-pre-swap-start-p-implies-second-pre-cut-at-start
      post-cut-remains-post-after-process-cut-step)))
  ;; Use this theorem explicitly only at the common parent branch.
  :rule-classes nil)

;; EQUAL PROCESS-CUT-STEP RESULTS GIVE EQUAL INVERSION COUNTS

(local-defthm inversion-count-of-equal-process-cut-steps
  (implies
   (and
    (state-equivalent-p st-1 st-2)
    (cut-markers-in-transit-p m st-1)
    (cut-markers-in-transit-p m st-2)
    (cut-meta-imp-consistent-p m st-1)
    (cut-meta-imp-consistent-p m st-2)
    (good-cut-meta-p m)
    (good-state-p st-1)
    (good-state-p st-2)
    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)
    (legal-inputp st-1 input)
    (legal-inputp st-2 input)
    (cl-checkpoint-body-input-p input))
   (equal
    (inversion-count
     (system-step st-2 input)
     (process-cut-step input st-1 m)
     postfix)
    (inversion-count
     (system-step st-2 input)
     (process-cut-step input st-2 m)
     postfix)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (process-cut-step-equal-for-equivalent-states)
    :in-theory
    (disable
     inversion-count
     process-cut-step
     system-step
     state-equivalent-p
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     good-cut-meta-p
     good-state-p
     recovery-free-state-p
     legal-inputp
     cl-checkpoint-body-input-p))))

;; INVERSION COUNT IS INVARIANT UNDER CL STATE EQUIVALENCE

(local-defthm inversion-count-equal-for-equivalent-states
  (implies
   (and
    (state-equivalent-p st-1 st-2)
    (cut-markers-in-transit-p m st-1)
    (cut-markers-in-transit-p m st-2)
    (cut-meta-imp-consistent-p m st-1)
    (cut-meta-imp-consistent-p m st-2)
    (good-cut-meta-p m)
    (good-state-p st-1)
    (good-state-p st-2)
    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)
    (true-listp postfix)
    (legal-input-sequencep st-1 postfix)
    (legal-input-sequencep st-2 postfix)
    (cl-checkpoint-body-inputs-p postfix))
   (equal
    (inversion-count st-1 m postfix)
    (inversion-count st-2 m postfix)))
  :hints
  (("Subgoal *1/3"
    :use
    ((:instance
      checkpoint-body-inputs-p-implies-first-is-body-input
      (inputs postfix))
     (:instance
      inversion-count-of-equal-process-cut-steps
      (input (car postfix))
      (postfix (cdr postfix))))
    :expand
    ((inversion-count st-2 m postfix)))
("Subgoal *1/2"
 :use
 (;; The first postfix input is a checkpoint-body input.
  (:instance
   checkpoint-body-inputs-p-implies-first-is-body-input
   (inputs postfix))
  ;; The remaining postfix is also a checkpoint-body sequence.
  (:instance
   checkpoint-body-inputs-p-implies-rest
   (inputs postfix))
  ;; Bridge the two PROCESS-CUT-STEP computations in the recursive
  ;; INVERSION-COUNT term.
  (:instance
   inversion-count-of-equal-process-cut-steps
   (input
    (car postfix))
   (postfix
    (cdr postfix)))
  ;; First equality:
  (:instance
   number-of-before-cut-inputs-equal-for-equivalent-states
   (st-1
    (system-step
     st-1
     (car postfix)))
   (st-2
    (system-step
     st-2
     (car postfix)))
   (m
    (process-cut-step
     (car postfix)
     st-1
     m))
   (postfix
    (cdr postfix)))
  ;; Second equality:
  (:instance
   number-of-before-cut-inputs-of-equal-process-cut-steps
   (input
    (car postfix))
   (postfix
    (cdr postfix))))
 :expand
 ((inversion-count
   st-2
   m
   postfix)))
   ("Goal"
    :in-theory
    (disable cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-inputp
      cl-checkpoint-body-input-p
      procs-equivalent-p
      cl-checkpoint-control-equivalent-p
      system-step
      process-cut-step
      cm-cut-not-taken-p
      cl-checkpoint-body-inputs-p
      true-listp
      get-msg-from-channel))))

;; POSTFIX INVERSION COUNT COMMUTES ACROSS ONE POST/PRE PAIR

(local-defthm inversion-count-after-post-pre-pair-commutes
  (let* (;; ------------------------------------------------------
         ;; Original order: INPUT-POST, INPUT-PRE.
         ;; ------------------------------------------------------
         (st-after-post
          (system-step
           st
           input-post))
         (m-after-post
          (process-cut-step
           input-post
           st
           m))
         (st-after-post-pre
          (system-step
           st-after-post
           input-pre))
         (m-after-post-pre
          (process-cut-step
           input-pre
           st-after-post
           m-after-post))
         ;; ------------------------------------------------------
         ;; Swapped order: INPUT-PRE, INPUT-POST.
         ;; ------------------------------------------------------
         (st-after-pre
          (system-step
           st
           input-pre))
         (m-after-pre
          (process-cut-step
           input-pre
           st
           m))
         (st-after-pre-post
          (system-step
           st-after-pre
           input-post))
         (m-after-pre-post
          (process-cut-step
           input-post
           st-after-pre
           m-after-pre)))
    (implies
     (and
      (post-pre-swap-start-p
       st
       m
       input-post
       input-pre)
      (true-listp postfix)
      (legal-input-sequencep
       st
       (append
        (list input-post input-pre)
        postfix))
      (cl-checkpoint-body-inputs-p
       (append
        (list input-post input-pre)
        postfix)))
     (equal
      ;; POSTFIX inversion count after the swapped PRE/POST pair.
      (inversion-count
       st-after-pre-post
       m-after-pre-post
       postfix)
      ;; POSTFIX inversion count after the original POST/PRE pair.
      (inversion-count
       st-after-post-pre
       m-after-post-pre
       postfix))))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    (;; ---------------------------------------------------------
     ;; The pair-result implementation states are equivalent.
     ;; ---------------------------------------------------------
     (:instance
      front-post-pre-swap-start-implies-state-equivalent
      (inputs
       (list input-post input-pre)))
     ;; ---------------------------------------------------------
     ;; The pair-result cut metadata is exactly equal.
     ;; ---------------------------------------------------------
     (:instance
      post-pre-two-process-cut-steps-commute
      (input-post input-post)
      (input-pre input-pre))
     ;; ---------------------------------------------------------
     ;; Both pair-result states are good and recovery-free.
     ;; ---------------------------------------------------------
     (:instance
      post-pre-swap-start-implies-pair-states-good-and-recovery-free
      (input-1 input-post)
      (input-2 input-pre))
     ;; ---------------------------------------------------------
     ;; The swapped two-input prefix is legal.
     ;; ---------------------------------------------------------
     (:instance
      front-post-pre-swap-start-implies-swapped-pair-legal
      (inputs
       (list input-post input-pre)))
     ;; ---------------------------------------------------------
     ;; POSTFIX is legal after the original pair.
     ;; ---------------------------------------------------------
     (:instance
      legal-input-sequencep-of-append-implies-second
      (inputs-1
       (list input-post input-pre))
      (inputs-2 postfix))
     ;; ---------------------------------------------------------
     ;; POSTFIX is legal after the swapped pair.
     ;; ---------------------------------------------------------
     (:instance
      front-post-pre-swap-start-implies-swapped-postfix-legal
      (inputs
       (append
        (list input-post input-pre)
        postfix)))
     ;; ---------------------------------------------------------
     ;; POSTFIX contains checkpoint-body inputs.
     ;;
     ;; Remove INPUT-POST and INPUT-PRE from the complete sequence.
     ;; ---------------------------------------------------------
     (:instance
      checkpoint-body-inputs-p-implies-rest
      (inputs
       (append
        (list input-post input-pre)
        postfix)))
     (:instance
      checkpoint-body-inputs-p-implies-rest
      (inputs
       (rest
        (append
         (list input-post input-pre)
         postfix))))
     ;; ---------------------------------------------------------
     ;; Invariants after the original POST/PRE pair.
     ;; ---------------------------------------------------------
     (:instance
      good-cut-meta-p-over-process-cut-segment
      (inputs
       (list input-post input-pre)))
     (:instance
      cut-meta-imp-consistent-p-over-process-cut-segment
      (inputs
       (list input-post input-pre)))
     (:instance
      cut-markers-in-transit-p-preserved-by-segment
      (inputs
       (list input-post input-pre)))
     ;; ------------------------------------------------------------
     ;; Invariants after the swapped PRE/POST pair.
     ;; ------------------------------------------------------------
     (:instance
      cut-meta-imp-consistent-p-over-process-cut-segment
      (inputs
       (list input-pre input-post)))
     (:instance
      cut-markers-in-transit-p-preserved-by-segment
      (inputs
       (list input-pre input-post)))
     ;; ------------------------------------------------------------
     ;; Apply the newly proved equivalent-state inversion theorem.
     ;; ------------------------------------------------------------
     (:instance
      inversion-count-equal-for-equivalent-states
      (st-1
       (run-imp
        st
        (list input-post input-pre)))
      (st-2
       (run-imp
        st
        (list input-pre input-post)))
      (m
       (process-cut-segment
        (list input-post input-pre)
        st
        m))
      (postfix postfix)))
    :in-theory
    (disable
      ;; Keep the recursive inversion function opaque.
      inversion-count
      ;; Keep the semantic predicates opaque.
      state-equivalent-p
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-input-sequencep
      legal-inputp
      cl-checkpoint-body-inputs-p
      cl-checkpoint-body-input-p
      process-cut-step
      system-step
      cm-cut-not-taken-p
      true-listp
      ;; These theorems were instantiated explicitly above.
      inversion-count-equal-for-equivalent-states
      post-pre-two-process-cut-steps-commute
      front-post-pre-swap-start-implies-state-equivalent
      front-post-pre-swap-start-implies-swapped-pair-legal
      front-post-pre-swap-start-implies-swapped-postfix-legal
      post-pre-swap-start-implies-pair-states-good-and-recovery-free
      legal-input-sequencep-of-append-implies-second
      checkpoint-body-inputs-p-implies-rest
      good-cut-meta-p-over-process-cut-segment
      cut-meta-imp-consistent-p-over-process-cut-segment
      cut-markers-in-transit-p-preserved-by-segment))))

(local-defthm positive-inversion-count-implies-swap-decreases
  (implies
   (and
    (not
     (zp
      (inversion-count st m inputs)))
    (true-listp inputs)
    (cut-markers-in-transit-p m st)
    (cut-meta-imp-consistent-p m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)
    (legal-input-sequencep
     st inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (<
    (inversion-count
     st m
     (swap-first-after-before
      st m inputs))
    (inversion-count
     st m inputs)))
  :hints
  (("Goal"
    :in-theory (disable
		good-state-p
		good-cut-meta-p
		cut-meta-imp-consistent-p
		legal-input-sequencep
		cl-checkpoint-body-inputs-p
		recovery-free-state-p
		system-step
		cm-cut-not-taken-p
		process-cut-step
		cut-markers-in-transit-p
		post-pre-swap-start-p))
   ("Subgoal *1/2"
 :use
 ((:instance
   post-pre-swap-start-p-implies-complete-cut-classification
   (input-post
    (first inputs))
   (input-pre
    (second inputs)))))
      ("Subgoal *1/3"
    :do-not-induct t
    :use
    ((:instance
      zero-inversion-count-and-positive-before-count-implies-first-before
      (st
       (system-step
        st
        (first inputs)))
      (m
       (process-cut-step
        (first inputs)
        st
        m))
      (inputs
       (rest inputs)))
     (:instance
      fixed-post-pre-inversion-is-swappable)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; EQUAL PROCESS-CUT-STEP RESULTS GIVE EQUAL BEFORE-CUT SUFFIXES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm before-cut-inputs-of-equal-process-cut-steps
  (implies
   (and
    (equal
     (g :proc-ids st-1)
     (g :proc-ids st-2))
    (equal
     (g :channels st-1)
     (g :channels st-2))
    (procs-equivalent-p
     (g :proc-ids st-1)
     (g :procs st-1)
     (g :procs st-2))
    (cl-checkpoint-control-equivalent-p
     (g :proc-ids st-1)
     (g :procs st-1)
     (g :procs st-2))
    (cut-markers-in-transit-p m st-1)
    (cut-markers-in-transit-p m st-2)
    (cut-meta-imp-consistent-p m st-1)
    (cut-meta-imp-consistent-p m st-2)
    (good-cut-meta-p m)
    (good-state-p st-1)
    (good-state-p st-2)
    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)
    (legal-inputp st-1 input)
    (legal-inputp st-2 input)
    (cl-checkpoint-body-input-p input))
   (equal
    (before-cut-inputs
     (system-step st-2 input)
     (process-cut-step input st-1 m)
     postfix)
    (before-cut-inputs
     (system-step st-2 input)
     (process-cut-step input st-2 m)
     postfix)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      process-cut-step-equal-for-equivalent-states
      (st-1 st-1)
      (st-2 st-2)
      (m m)
      (input input)))
    :in-theory
    (disable
     before-cut-inputs
     process-cut-step
     system-step
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     good-cut-meta-p
     good-state-p
     recovery-free-state-p
     legal-inputp
     cl-checkpoint-body-input-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; EQUIVALENT STATES PRODUCE THE SAME BEFORE-CUT SUBSEQUENCE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm before-cut-inputs-equal-for-equivalent-states
  (implies
   (and
    (state-equivalent-p
     st-1 st-2)
    (cut-markers-in-transit-p m st-1)
    (cut-markers-in-transit-p m st-2)
    (cut-meta-imp-consistent-p m st-1)
    (cut-meta-imp-consistent-p m st-2)
    (good-cut-meta-p m)
    (good-state-p st-1)
    (good-state-p st-2)
    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)
    (true-listp postfix)
    (legal-input-sequencep
     st-1 postfix)
    (legal-input-sequencep
     st-2 postfix)
    (cl-checkpoint-body-inputs-p
     postfix))
   (equal
    (before-cut-inputs
     st-1 m postfix)
    (before-cut-inputs
     st-2 m postfix)))
  :hints
  (("Subgoal *1/3"
    :use
    ((:instance
      checkpoint-body-inputs-p-implies-first-is-body-input
      (inputs postfix))
     (:instance
      before-cut-inputs-of-equal-process-cut-steps
      (st-1 st-1)
      (st-2 st-2)
      (m m)
      (input (car postfix))
      (postfix (cdr postfix))))
    :expand
    ((before-cut-inputs
      st-2 m postfix)))
   ("Subgoal *1/2"
    :use
    ((:instance
      before-cut-inputs-of-equal-process-cut-steps
      (st-1 st-1)
      (st-2 st-2)
      (m m)
      (input (car postfix))
      (postfix (cdr postfix))))
    :expand
    ((before-cut-inputs
      st-2 m postfix)))
   ("Goal"
    :in-theory
    (disable cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-inputp
      cl-checkpoint-body-input-p
      procs-equivalent-p
      cl-checkpoint-control-equivalent-p
      system-step
      process-cut-step
      cm-cut-not-taken-p
      get-msg-from-channel))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; EXECUTING A POST/PRE PAIR IN EITHER ORDER GIVES THE SAME
;; BEFORE-CUT SUBSEQUENCE OF THE REMAINING POSTFIX.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm before-cut-inputs-after-post-pre-pair-commutes
  (let*
      (;; Original order: POST, PRE.
       (st-after-post
        (system-step
         st input-post))
       (m-after-post
        (process-cut-step
         input-post st m))
       (st-after-post-pre
        (system-step
         st-after-post
         input-pre))
       (m-after-post-pre
        (process-cut-step
         input-pre
         st-after-post
         m-after-post))
       ;; Swapped order: PRE, POST.
       (st-after-pre
        (system-step
         st input-pre))
       (m-after-pre
        (process-cut-step
         input-pre st m))
       (st-after-pre-post
        (system-step
         st-after-pre
         input-post))
       (m-after-pre-post
        (process-cut-step
         input-post
         st-after-pre
         m-after-pre)))
    (implies
     (and
      (post-pre-swap-start-p
       st m input-post input-pre)
      (true-listp postfix)
      (legal-input-sequencep
       st
       (append
        (list input-post input-pre)
        postfix))
      (cl-checkpoint-body-inputs-p
       (append
        (list input-post input-pre)
        postfix)))
     (equal
      ;; Swapped order.
      (before-cut-inputs
       st-after-pre-post
       m-after-pre-post
       postfix)
      ;; Original order.
      (before-cut-inputs
       st-after-post-pre
       m-after-post-pre
       postfix))))
  :rule-classes nil
  :hints
  (("Goal"
    :do-not-induct t
    :use
    (;; Pair-result implementation states are equivalent.
     (:instance
      front-post-pre-swap-start-implies-state-equivalent
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     ;; Pair-result metadata values are equal.
     (:instance
      post-pre-two-process-cut-steps-commute
      (st st)
      (m m)
      (input-post input-post)
      (input-pre input-pre))
     ;; Both resulting states remain good and recovery-free.
     (:instance
      post-pre-swap-start-implies-pair-states-good-and-recovery-free
      (st st)
      (m m)
      (input-1 input-post)
      (input-2 input-pre))
     ;; The swapped prefix is legal.
     (:instance
      front-post-pre-swap-start-implies-swapped-pair-legal
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     ;; POSTFIX is legal after the original pair.
     (:instance
      legal-input-sequencep-of-append-implies-second
      (st st)
      (inputs-1
       (list input-post input-pre))
      (inputs-2 postfix))
     ;; POSTFIX is legal after the swapped pair.
     (:instance
      front-post-pre-swap-start-implies-swapped-postfix-legal
      (st st)
      (m m)
      (inputs
       (append
        (list input-post input-pre)
        postfix)))
     ;; POSTFIX consists only of checkpoint-body inputs.
     (:instance
      checkpoint-body-inputs-p-implies-rest
      (inputs
       (append
        (list input-post input-pre)
        postfix)))
     (:instance
      checkpoint-body-inputs-p-implies-rest
      (inputs
       (rest
        (append
         (list input-post input-pre)
         postfix))))
     ;; Invariants after the original pair.
     (:instance
      good-cut-meta-p-over-process-cut-segment
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     (:instance
      cut-meta-imp-consistent-p-over-process-cut-segment
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     (:instance
      cut-markers-in-transit-p-preserved-by-segment
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     ;; Invariants after the swapped pair.
     (:instance
      cut-meta-imp-consistent-p-over-process-cut-segment
      (st st)
      (m m)
      (inputs
       (list input-pre input-post)))
     (:instance
      cut-markers-in-transit-p-preserved-by-segment
      (st st)
      (m m)
      (inputs
       (list input-pre input-post)))
     ;; Apply the generalized equivalent-state theorem.
     (:instance
      before-cut-inputs-equal-for-equivalent-states
      (st-1
       (run-imp
        st
        (list input-post input-pre)))
      (st-2
       (run-imp
        st
        (list input-pre input-post)))
      ;; Use original-order metadata as the common metadata.
      (m
       (process-cut-segment
        (list input-post input-pre)
        st
        m))
      (postfix postfix)))
    :in-theory
    (disable before-cut-inputs
      state-equivalent-p
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-input-sequencep
      legal-inputp
      cl-checkpoint-body-inputs-p
      cl-checkpoint-body-input-p
      process-cut-step
      system-step
      cm-cut-not-taken-p
      true-listp
      before-cut-inputs-equal-for-equivalent-states
      post-pre-two-process-cut-steps-commute
      front-post-pre-swap-start-implies-state-equivalent
      front-post-pre-swap-start-implies-swapped-pair-legal
      front-post-pre-swap-start-implies-swapped-postfix-legal
      post-pre-swap-start-implies-pair-states-good-and-recovery-free
      legal-input-sequencep-of-append-implies-second
      checkpoint-body-inputs-p-implies-rest
      good-cut-meta-p-over-process-cut-segment
      cut-meta-imp-consistent-p-over-process-cut-segment
      cut-markers-in-transit-p-preserved-by-segment))))

;; ONE POST/PRE SWAP PRESERVES THE BEFORE-CUT SUBSEQUENCE

(local-defthm before-cut-inputs-of-swap-first-after-before
  (implies
   (and
    (true-listp inputs)
    (cut-markers-in-transit-p m st)
    (cut-meta-imp-consistent-p m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)
    (legal-input-sequencep
     st inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (equal
    (before-cut-inputs
     st
     m
     (swap-first-after-before
      st m inputs))
    (before-cut-inputs
     st m inputs)))
  :hints
  (("Goal"
    :induct
    (swap-first-after-before
     st m inputs)
    ;; SWAP-FIRST-AFTER-BEFORE and BEFORE-CUT-INPUTS remain enabled.
    :in-theory
    (disable
     post-pre-swap-start-p
     process-cut-step
     system-step
     cm-cut-not-taken-p
     good-state-p
     good-cut-meta-p
     cut-meta-imp-consistent-p
     legal-input-sequencep
     legal-inputp
     cl-checkpoint-body-inputs-p
     cl-checkpoint-body-input-p
     recovery-free-state-p
     cut-markers-in-transit-p))
   ;; This is the branch in which the first adjacent POST/PRE pair
   ;; is actually exchanged.
   ("Subgoal *1/2"
    :use
    (;; Supply all four classifications at the common parent branch.
     (:instance
      post-pre-swap-start-p-implies-complete-cut-classification
      (st st)
      (m m)
      (input-post
       (first inputs))
      (input-pre
       (second inputs)))
     ;; The recursive BEFORE-CUT-INPUTS calls on CDDR INPUTS are equal
     ;; after executing the selected pair in either order.
     (:instance
      before-cut-inputs-after-post-pre-pair-commutes
      (st st)
      (m m)
      (input-post
       (first inputs))
      (input-pre
       (second inputs))
      (postfix
       (rest
        (rest inputs)))))
    ;; Expand the original order through both members of the pair.
    ;; The swapped order is exposed by SWAP-FIRST-AFTER-BEFORE.
    :expand
    ((before-cut-inputs
      st
      m
      inputs)
     (before-cut-inputs
      (system-step
       st
       (first inputs))
      (process-cut-step
       (first inputs)
       st
       m)
      (rest inputs)))
    :in-theory
    (disable
   ;  post-pre-swap-start-p-implies-complete-cut-classification
  ;   before-cut-inputs-after-post-pre-pair-commutes
     post-pre-swap-start-p
     process-cut-step
     system-step
     cm-cut-not-taken-p
     good-state-p
     good-cut-meta-p
     cut-meta-imp-consistent-p
     legal-input-sequencep
     legal-inputp
     cl-checkpoint-body-inputs-p
     cl-checkpoint-body-input-p
     recovery-free-state-p
     cut-markers-in-transit-p))))

;; AFTER-CUT-INPUTS: EQUAL PROCESS-CUT-STEP RESULTS

(local-defthm after-cut-inputs-of-equal-process-cut-steps
  (implies
   (and
    (equal
     (g :proc-ids st-1)
     (g :proc-ids st-2))
    (equal
     (g :channels st-1)
     (g :channels st-2))
    (procs-equivalent-p
     (g :proc-ids st-1)
     (g :procs st-1)
     (g :procs st-2))
    (cl-checkpoint-control-equivalent-p
     (g :proc-ids st-1)
     (g :procs st-1)
     (g :procs st-2))
    (cut-markers-in-transit-p m st-1)
    (cut-markers-in-transit-p m st-2)
    (cut-meta-imp-consistent-p m st-1)
    (cut-meta-imp-consistent-p m st-2)
    (good-cut-meta-p m)
    (good-state-p st-1)
    (good-state-p st-2)
    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)
    (legal-inputp st-1 input)
    (legal-inputp st-2 input)
    (cl-checkpoint-body-input-p input))
   (equal
    (after-cut-inputs
     (system-step st-2 input)
     (process-cut-step input st-1 m)
     postfix)
    (after-cut-inputs
     (system-step st-2 input)
     (process-cut-step input st-2 m)
     postfix)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      process-cut-step-equal-for-equivalent-states
      (st-1 st-1)
      (st-2 st-2)
      (m m)
      (input input)))
    :in-theory
    (disable
     after-cut-inputs
     process-cut-step
     system-step
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     good-cut-meta-p
     good-state-p
     recovery-free-state-p
     legal-inputp
     cl-checkpoint-body-input-p))))

;; AFTER-CUT-INPUTS IS EQUAL FOR EQUIVALENT STATES

(local-defthm after-cut-inputs-equal-for-equivalent-states
  (implies
   (and
    (state-equivalent-p
     st-1 st-2)
    (cut-markers-in-transit-p m st-1)
    (cut-markers-in-transit-p m st-2)
    (cut-meta-imp-consistent-p m st-1)
    (cut-meta-imp-consistent-p m st-2)
    (good-cut-meta-p m)
    (good-state-p st-1)
    (good-state-p st-2)
    (recovery-free-state-p st-1)
    (recovery-free-state-p st-2)
    (true-listp postfix)
    (legal-input-sequencep
     st-1 postfix)
    (legal-input-sequencep
     st-2 postfix)
    (cl-checkpoint-body-inputs-p
     postfix))
   (equal
    (after-cut-inputs
     st-1 m postfix)
    (after-cut-inputs
     st-2 m postfix)))
  :hints
  (("Subgoal *1/3"
    :use
    ((:instance
      checkpoint-body-inputs-p-implies-first-is-body-input
      (inputs postfix))
     (:instance
      after-cut-inputs-of-equal-process-cut-steps
      (st-1 st-1)
      (st-2 st-2)
      (m m)
      (input
       (car postfix))
      (postfix
       (cdr postfix))))
    :expand
    ((after-cut-inputs
      st-2 m postfix)))
   ("Subgoal *1/2"
    :use
    ((:instance
      after-cut-inputs-of-equal-process-cut-steps
      (st-1 st-1)
      (st-2 st-2)
      (m m)
      (input
       (car postfix))
      (postfix
       (cdr postfix))))
    :expand
    ((after-cut-inputs
      st-2 m postfix)))
   ("Goal"
    :in-theory
    (disable cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-inputp
      cl-checkpoint-body-input-p
      procs-equivalent-p
      cl-checkpoint-control-equivalent-p
      system-step
      process-cut-step
      cm-cut-not-taken-p
      get-msg-from-channel))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; EXECUTING A POST/PRE PAIR IN EITHER ORDER GIVES THE SAME
;; AFTER-CUT SUBSEQUENCE OF THE UNCHANGED POSTFIX
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm after-cut-inputs-after-post-pre-pair-commutes
  (let*
      (;; Original order: POST, PRE.
       (st-after-post
        (system-step
         st input-post))
       (m-after-post
        (process-cut-step
         input-post st m))
       (st-after-post-pre
        (system-step
         st-after-post
         input-pre))
       (m-after-post-pre
        (process-cut-step
         input-pre
         st-after-post
         m-after-post))
       ;; Swapped order: PRE, POST.
       (st-after-pre
        (system-step
         st input-pre))
       (m-after-pre
        (process-cut-step
         input-pre st m))
       (st-after-pre-post
        (system-step
         st-after-pre
         input-post))
       (m-after-pre-post
        (process-cut-step
         input-post
         st-after-pre
         m-after-pre)))
    (implies
     (and
      (post-pre-swap-start-p
       st m input-post input-pre)
      (true-listp postfix)
      (legal-input-sequencep
       st
       (append
        (list input-post input-pre)
        postfix))
      (cl-checkpoint-body-inputs-p
       (append
        (list input-post input-pre)
        postfix)))
     (equal
      ;; Swapped PRE/POST execution.
      (after-cut-inputs
       st-after-pre-post
       m-after-pre-post
       postfix)
      ;; Original POST/PRE execution.
      (after-cut-inputs
       st-after-post-pre
       m-after-post-pre
       postfix))))
  :rule-classes nil
  :hints
  (("Goal"
    :do-not-induct t
    :use
    (;; The two pair-result implementation states are equivalent.
     (:instance
      front-post-pre-swap-start-implies-state-equivalent
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     ;; The two executions produce exactly equal cut metadata.
     (:instance
      post-pre-two-process-cut-steps-commute
      (st st)
      (m m)
      (input-post input-post)
      (input-pre input-pre))
     ;; Both pair-result states remain good and recovery-free.
     (:instance
      post-pre-swap-start-implies-pair-states-good-and-recovery-free
      (st st)
      (m m)
      (input-1 input-post)
      (input-2 input-pre))
     ;; The swapped two-input prefix is legal.
     (:instance
      front-post-pre-swap-start-implies-swapped-pair-legal
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     ;; POSTFIX is legal after the original pair.
     (:instance
      legal-input-sequencep-of-append-implies-second
      (st st)
      (inputs-1
       (list input-post input-pre))
      (inputs-2 postfix))
     ;; POSTFIX is legal after the swapped pair.
     (:instance
      front-post-pre-swap-start-implies-swapped-postfix-legal
      (st st)
      (m m)
      (inputs
       (append
        (list input-post input-pre)
        postfix)))
     ;; Remove INPUT-POST and INPUT-PRE from the body-input sequence.
     (:instance
      checkpoint-body-inputs-p-implies-rest
      (inputs
       (append
        (list input-post input-pre)
        postfix)))
     (:instance
      checkpoint-body-inputs-p-implies-rest
      (inputs
       (rest
        (append
         (list input-post input-pre)
         postfix))))
     ;; Invariants after the original POST/PRE pair.
     (:instance
      good-cut-meta-p-over-process-cut-segment
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     (:instance
      cut-meta-imp-consistent-p-over-process-cut-segment
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     (:instance
      cut-markers-in-transit-p-preserved-by-segment
      (st st)
      (m m)
      (inputs
       (list input-post input-pre)))
     ;; Invariants after the swapped PRE/POST pair.
     (:instance
      cut-meta-imp-consistent-p-over-process-cut-segment
      (st st)
      (m m)
      (inputs
       (list input-pre input-post)))
     (:instance
      cut-markers-in-transit-p-preserved-by-segment
      (st st)
      (m m)
      (inputs
       (list input-pre input-post)))
     ;; Apply the generalized equivalent-state theorem to POSTFIX.
     (:instance
      after-cut-inputs-equal-for-equivalent-states
      (st-1
       (run-imp
        st
        (list input-post input-pre)))
      (st-2
       (run-imp
        st
        (list input-pre input-post)))
      ;; Exact metadata commutation allows both states to use the
      ;; metadata produced by the original POST/PRE execution.
      (m
       (process-cut-segment
        (list input-post input-pre)
        st
        m))
      (postfix postfix)))
    :in-theory
    (disable after-cut-inputs
      state-equivalent-p
      cut-markers-in-transit-p
      cut-meta-imp-consistent-p
      good-cut-meta-p
      good-state-p
      recovery-free-state-p
      legal-input-sequencep
      legal-inputp
      cl-checkpoint-body-inputs-p
      cl-checkpoint-body-input-p
      process-cut-step
      system-step
      cm-cut-not-taken-p
      true-listp
      after-cut-inputs-equal-for-equivalent-states
      post-pre-two-process-cut-steps-commute
      front-post-pre-swap-start-implies-state-equivalent
      front-post-pre-swap-start-implies-swapped-pair-legal
      front-post-pre-swap-start-implies-swapped-postfix-legal
      post-pre-swap-start-implies-pair-states-good-and-recovery-free
      legal-input-sequencep-of-append-implies-second
      checkpoint-body-inputs-p-implies-rest
      good-cut-meta-p-over-process-cut-segment
      cut-meta-imp-consistent-p-over-process-cut-segment
      cut-markers-in-transit-p-preserved-by-segment))))

;; ONE POST/PRE SWAP PRESERVES THE AFTER-CUT SUBSEQUENCE

(local-defthm after-cut-inputs-of-swap-first-after-before
  (implies
   (and
    (true-listp inputs)
    (cut-markers-in-transit-p m st)
    (cut-meta-imp-consistent-p m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)
    (legal-input-sequencep
     st inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (equal
    (after-cut-inputs
     st
     m
     (swap-first-after-before
      st m inputs))
    (after-cut-inputs
     st m inputs)))
  :hints
  (("Goal"
    :induct
    (swap-first-after-before
     st m inputs)
    ;; Keep SWAP-FIRST-AFTER-BEFORE and AFTER-CUT-INPUTS enabled.
    :in-theory
    (disable
     post-pre-swap-start-p
     process-cut-step
     system-step
     cm-cut-not-taken-p
     good-state-p
     good-cut-meta-p
     cut-meta-imp-consistent-p
     legal-input-sequencep
     legal-inputp
     cl-checkpoint-body-inputs-p
     cl-checkpoint-body-input-p
     recovery-free-state-p
     cut-markers-in-transit-p))
   ;; The first adjacent POST/PRE pair is exchanged here.
   ("Subgoal *1/2"
    :use
    (;; Supply all four classifications at the common parent branch.
     (:instance
      post-pre-swap-start-p-implies-complete-cut-classification
      (st st)
      (m m)
      (input-post
       (first inputs))
      (input-pre
       (second inputs)))
     ;; The recursively computed AFTER-CUT-INPUTS results on the
     ;; unchanged suffix are equal after either execution order.
     (:instance
      after-cut-inputs-after-post-pre-pair-commutes
      (st st)
      (m m)
      (input-post
       (first inputs))
      (input-pre
       (second inputs))
      (postfix
       (rest
        (rest inputs)))))
    ;; Expand the original order through INPUT-POST and INPUT-PRE.
    :expand
    ((after-cut-inputs
      st
      m
      inputs)
     (after-cut-inputs
      (system-step
       st
       (first inputs))
      (process-cut-step
       (first inputs)
       st
       m)
      (rest inputs)))
    :in-theory
    (disable
   ;  post-pre-swap-start-p-implies-complete-cut-classification
   ;  after-cut-inputs-after-post-pre-pair-commutes
     post-pre-swap-start-p
     process-cut-step
     system-step
     cm-cut-not-taken-p
     good-state-p
     good-cut-meta-p
     cut-meta-imp-consistent-p
     legal-input-sequencep
     legal-inputp
     cl-checkpoint-body-inputs-p
     cl-checkpoint-body-input-p
     recovery-free-state-p
     cut-markers-in-transit-p))))

;; ONE SWAP PRESERVES THE COMPLETE BEFORE/AFTER PARTITION

(local-defthm cut-partition-of-swap-first-after-before
  (implies
   (and
    (true-listp inputs)
    (cut-markers-in-transit-p m st)
    (cut-meta-imp-consistent-p m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)
    (legal-input-sequencep
     st inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (equal
    (append
     (before-cut-inputs
      st
      m
      (swap-first-after-before
       st m inputs))
     (after-cut-inputs
      st
      m
      (swap-first-after-before
       st m inputs)))
    (append
     (before-cut-inputs
      st m inputs)
     (after-cut-inputs
      st m inputs))))
  :hints
  (("Goal"
    :use
    ((:instance
      before-cut-inputs-of-swap-first-after-before
      (st st)
      (m m)
      (inputs inputs))
     (:instance
      after-cut-inputs-of-swap-first-after-before
      (st st)
      (m m)
      (inputs inputs)))
    ;; This is only congruence of APPEND after the two list equalities
    ;; have been supplied.
    :in-theory
    (disable
     before-cut-inputs-of-swap-first-after-before
     after-cut-inputs-of-swap-first-after-before
     swap-first-after-before
     before-cut-inputs
     after-cut-inputs
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     good-cut-meta-p
     good-state-p
     recovery-free-state-p
     legal-input-sequencep
     cl-checkpoint-body-inputs-p))))

;; ZERO BEFORE-CUT COUNT MEANS THE FILTERED BEFORE-CUT LIST IS EMPTY

(local-defthm zero-number-of-before-cut-inputs-implies-no-before-cut-inputs
  (implies
   (equal
    (number-of-before-cut-inputs
     st m inputs)
    0)
   (equal
    (before-cut-inputs
     st m inputs)
    nil))
  :hints
  (("Goal"
    :induct
    (number-of-before-cut-inputs
     st m inputs)
    ;; Keep the transition functions and classification predicate opaque.
    :in-theory
    (disable
     system-step
     process-cut-step
     cm-cut-not-taken-p))))

;; ZERO INVERSIONS MEANS THE INPUTS ARE ALREADY PARTITIONED

(local-defthm zero-inversion-count-implies-before-append-after
  (implies
   (and
    (true-listp inputs)
    (equal
     (inversion-count
      st m inputs)
     0))
   (equal
    inputs
    (append
     (before-cut-inputs
      st m inputs)
     (after-cut-inputs
      st m inputs))))
  :rule-classes nil
  :hints
  (("Goal"
    :induct
    (inversion-count
     st m inputs)
    ;; The recursive counting and filtering functions remain enabled.
    :in-theory
    (disable
     system-step
     process-cut-step
     cm-cut-not-taken-p
     number-of-before-cut-inputs
     before-cut-inputs
     after-cut-inputs))
   ;; ------------------------------------------------------------
   ;; First input is after-cut.
   ;; ------------------------------------------------------------
("Subgoal *1/2.1'4'"
 :do-not-induct t
 :expand
 ((before-cut-inputs
   st m inputs)
  (after-cut-inputs
   st m inputs))
 :in-theory
 (disable
  before-cut-inputs
  after-cut-inputs
  inversion-count
  number-of-before-cut-inputs
  system-step
  process-cut-step
  cm-cut-not-taken-p))
;; ------------------------------------------------------------
;; Empty-list base case.
;; ------------------------------------------------------------
("Subgoal *1/1'''"
 :do-not-induct t
 :expand
 ((before-cut-inputs
   st m nil)
  (after-cut-inputs
   st m nil))
 :in-theory
 (disable
  before-cut-inputs
  after-cut-inputs
  inversion-count
  number-of-before-cut-inputs
  system-step
  process-cut-step
  cm-cut-not-taken-p))
   ("Subgoal *1/2.2"
 :do-not-induct t
 ;; The current input is before-cut:
 :expand
 ((before-cut-inputs
   st m inputs)
  (after-cut-inputs
   st m inputs))
 ;; Keep the newly exposed suffix calls opaque.
 :in-theory
 (disable
  before-cut-inputs
  after-cut-inputs
  inversion-count
  number-of-before-cut-inputs
  system-step
  process-cut-step
  cm-cut-not-taken-p))))

(defthm reorder-inputs-returns-before-append-after
  (implies
   (and
    (true-listp inputs)
    (cut-markers-in-transit-p m st)
    (cut-meta-imp-consistent-p m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)
    (legal-input-sequencep
     st inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (equal
    (reorder-inputs
     st m inputs)
    (append
     (before-cut-inputs
      st m inputs)
     (after-cut-inputs
      st m inputs))))
  :hints
  (("Goal"
    :induct
    (reorder-inputs st m inputs)
    :in-theory (disable
		good-state-p
		good-cut-meta-p
		cut-meta-imp-consistent-p
		legal-input-sequencep
		cl-checkpoint-body-inputs-p
		recovery-free-state-p
		cut-markers-in-transit-p
		system-step
		process-cut-step
		cm-cut-not-taken-p))))

) ;; end local dynamic-reordering proof

;; These two exported equalities have large left-hand sides.  Their remaining
;; consumers use them explicitly, so automatic rewriting is unnecessary.
(in-theory
 (disable
  post-pre-two-process-cut-steps-commute
  reorder-inputs-returns-before-append-after))

;; The remaining bridge from the abstract reordering result to a complete checkpoint segment is also scoped.
(encapsulate
 ()

(local-defthm append-append-singleton
  (equal
   (append
    (append xs (list x))
    ys)
   (append
    xs
    (cons x ys))))

(local-defthm append-nil-when-true-listp
  (implies
   (true-listp xs)
   (equal
    (append xs nil)
    xs)))

(local-defthm true-listp-of-append-singleton
  (true-listp
   (append xs (list x))))

(local-defthm true-listp-of-cm-before-cut-input-sequence-of-process-cut-step
  (implies
   (true-listp
    (cm-before-cut-input-sequence m))
   (true-listp
    (cm-before-cut-input-sequence
     (process-cut-step
      input st m)))))

(local-defthm true-listp-of-cm-after-cut-input-sequence-of-process-cut-step
  (implies
   (true-listp
    (cm-after-cut-input-sequence m))
   (true-listp
    (cm-after-cut-input-sequence
     (process-cut-step
      input st m)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ONE PROCESS-CUT-STEP UPDATES THE BEFORE-CUT SEQUENCE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm cm-before-cut-input-sequence-of-process-cut-step
  (equal
   (cm-before-cut-input-sequence
    (process-cut-step input st m))
   (if
    (cm-cut-not-taken-p
     m
     (pid input))
    (append
     (cm-before-cut-input-sequence m)
     (list input))
    (cm-before-cut-input-sequence m)))
  :hints
  (("Goal"
    :in-theory
    (disable current-msg-for-receive
      get-msg-from-channel
      system-step))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ONE PROCESS-CUT-STEP UPDATES THE AFTER-CUT SEQUENCE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm cm-after-cut-input-sequence-of-process-cut-step
  (equal
   (cm-after-cut-input-sequence
    (process-cut-step input st m))
   (if
    (cm-cut-not-taken-p
     m
     (pid input))
    (cm-after-cut-input-sequence m)
    (append
     (cm-after-cut-input-sequence m)
     (list input))))
  :hints
  (("Goal"
    :in-theory
    (disable current-msg-for-receive
      get-msg-from-channel
      system-step))))

(local-defthm cm-before-cut-input-sequence-of-process-cut-segment
  (implies
   ;; Necessary even for the empty-input base case.
   (true-listp
    (cm-before-cut-input-sequence m))
   (equal
    (cm-before-cut-input-sequence
     (process-cut-segment
      inputs st m))
    (append
     (cm-before-cut-input-sequence m)
     (before-cut-inputs
      st m inputs))))
:hints
(("Goal"
  :induct
  (process-cut-segment
   inputs st m)
  :do-not
  '(generalize eliminate-destructors)
  :in-theory
  (union-theories
   (theory
    'minimal-theory)
   '(cm-before-cut-input-sequence-of-process-cut-step
     process-cut-segment
     true-listp-of-cm-before-cut-input-sequence-of-process-cut-step
     append-append-singleton
     true-listp-of-append-singleton
     append-nil-when-true-listp)))
 ;; Recursive case: expand only the current input.
 ("Subgoal *1/2"
  :do-not-induct t
  :expand
  ((process-cut-segment
    inputs st m)
   (before-cut-inputs
    st m inputs))
  :in-theory
  (union-theories
   (theory
    'minimal-theory)
   '(cm-before-cut-input-sequence-of-process-cut-step
     true-listp-of-cm-before-cut-input-sequence-of-process-cut-step
     append-append-singleton
     true-listp-of-append-singleton
     append-nil-when-true-listp)))
 ;; Empty-input base case.
 ("Subgoal *1/1"
  :do-not-induct t
  :expand
  ((process-cut-segment
    inputs st m)
   (before-cut-inputs
    st m inputs))
  :in-theory
  (union-theories
   (theory
    'minimal-theory)
   '(cm-before-cut-input-sequence-of-process-cut-step
     true-listp-of-cm-before-cut-input-sequence-of-process-cut-step
     append-append-singleton
     true-listp-of-append-singleton
     append-nil-when-true-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PROCESS-CUT-SEGMENT RECORDS EXACTLY THE FILTERED AFTER-CUT INPUTS
;;
;; The initial sequence already stored in M remains as a prefix.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm cm-after-cut-input-sequence-of-process-cut-segment
  (implies
   (true-listp
    (cm-after-cut-input-sequence m))
   (equal
    (cm-after-cut-input-sequence
     (process-cut-segment
      inputs st m))
    (append
     (cm-after-cut-input-sequence m)
     (after-cut-inputs
      st m inputs))))
  :rule-classes nil
  :hints
  (("Goal"
    :induct
    (process-cut-segment
     inputs st m)
    :do-not
    '(generalize eliminate-destructors)
    ;; Do not enable PROCESS-CUT-SEGMENT here.
    :in-theory
    (union-theories
     (theory
      'minimal-theory)
     '(cm-after-cut-input-sequence-of-process-cut-step
       process-cut-segment
       true-listp-of-cm-after-cut-input-sequence-of-process-cut-step
       append-append-singleton
       true-listp-of-append-singleton
       append-nil-when-true-listp)))
   ;; Recursive case: open only the current recursion level.
   ("Subgoal *1/2"
    :do-not-induct t
    :expand
    ((process-cut-segment
      inputs st m)
     (after-cut-inputs
      st m inputs))
    :in-theory
    (union-theories
     (theory
      'minimal-theory)
     '(cm-after-cut-input-sequence-of-process-cut-step
       true-listp-of-cm-after-cut-input-sequence-of-process-cut-step
       append-append-singleton
       true-listp-of-append-singleton
       append-nil-when-true-listp)))
   ;; Empty-input base case.
   ("Subgoal *1/1"
    :do-not-induct t
    :expand
    ((process-cut-segment
      inputs st m)
     (after-cut-inputs
      st m inputs))
    :in-theory
    (union-theories
     (theory
      'minimal-theory)
     '(cm-after-cut-input-sequence-of-process-cut-step
       true-listp-of-cm-after-cut-input-sequence-of-process-cut-step
       append-append-singleton
       true-listp-of-append-singleton
       append-nil-when-true-listp)))))

;; REORDER-INPUTS EQUALS THE PARTITION RECORDED BY PROCESS-CUT-SEGMENT

(defthm reorder-inputs-equals-process-cut-segment-partition
  (implies
   (and
    (equal
     (cm-before-cut-input-sequence m)
     nil)
    (equal
     (cm-after-cut-input-sequence m)
     nil)
    (true-listp inputs)
    (cut-markers-in-transit-p m st)
    (cut-meta-imp-consistent-p m st)
    (good-cut-meta-p m)
    (good-state-p st)
    (recovery-free-state-p st)
    (legal-input-sequencep
     st inputs)
    (cl-checkpoint-body-inputs-p
     inputs))
   (equal
    (reorder-inputs
     st m inputs)
    (append
     (cm-before-cut-input-sequence
      (process-cut-segment
       inputs st m))
     (cm-after-cut-input-sequence
      (process-cut-segment
       inputs st m)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (reorder-inputs-returns-before-append-after
     cm-before-cut-input-sequence-of-process-cut-segment
     cm-after-cut-input-sequence-of-process-cut-segment)
    ;; This is only equality transitivity and APPEND simplification.
  :in-theory
  (union-theories
   (theory
    'minimal-theory)
   '(binary-append)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FRESH CUT METADATA STARTS WITH BOTH RECORDED SEQUENCES EMPTY
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm cm-before-cut-input-sequence-of-make-cut-meta
  (equal
   (cm-before-cut-input-sequence
    (make-cut-meta
     sid initiator st))
   nil))

(local-defthm cm-after-cut-input-sequence-of-make-cut-meta
  (equal
   (cm-after-cut-input-sequence
    (make-cut-meta
     sid initiator st))
   nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DIRECT AGREEMENT FOR A CUT SCAN STARTING WITH FRESH METADATA
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm before-cut-inputs-agrees-with-fresh-cut-metadata
  (equal
   (cm-before-cut-input-sequence
    (process-cut-segment
     inputs
     st
     (make-cut-meta
      sid initiator st)))
   (before-cut-inputs
    st
    (make-cut-meta
     sid initiator st)
    inputs))
  :hints
  (("Goal"
    :use
    ((:instance
      cm-before-cut-input-sequence-of-process-cut-segment
      (m
       (make-cut-meta
        sid initiator st))))
    :in-theory
    (disable
     process-cut-segment
     before-cut-inputs
     make-cut-meta
     cm-before-cut-input-sequence))))

(local-defthm after-cut-inputs-agrees-with-fresh-cut-metadata
  (equal
   (cm-after-cut-input-sequence
    (process-cut-segment
     inputs
     st
     (make-cut-meta
      sid initiator st)))
   (after-cut-inputs
    st
    (make-cut-meta
     sid initiator st)
    inputs))
  :hints
  (("Goal"
    :use
    ((:instance
      cm-after-cut-input-sequence-of-process-cut-segment
      (m
       (make-cut-meta
        sid initiator st))))
    :in-theory
    (disable
     process-cut-segment
     after-cut-inputs
     make-cut-meta
     cm-after-cut-input-sequence))))

;; THE UNIFIED SCANNER METADATA EQUALS PROCESS-CUT-SEGMENT.

(local-defthm scan-until-checkpoint-done-equals-process-cut-segment
  (implies
   (checkpoint-completes-at-segment-end-p
    input-seg st m)
   (equal
    (scan-until-checkpoint-done input-seg st m)
    (process-cut-segment input-seg st m)))
  :hints
  (("Goal"
    :induct
    (scan-until-checkpoint-done input-seg st m)
    :in-theory
    (disable
     process-cut-step
     system-step
     checkpoint-collection-complete-p))))


(local-defthm checkpoint-segment-meta-equals-process-cut-segment
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (equal
    (checkpoint-segment-meta st input-seg)
    (process-cut-segment
     input-seg
     st
     (checkpoint-segment-initial-meta st input-seg))))
  :hints
  (("Goal"
    :in-theory
    (disable
     checkpoint-segment-initial-meta
     checkpoint-segment-completep
     checkpoint-completes-at-segment-end-p
     scan-until-checkpoint-done
     process-cut-segment
     process-cut-step
     system-step
     checkpoint-collection-complete-p
     good-state-p
     legal-input-sequencep
     recovery-free-state-p
     cl-checkpoint-body-inputs-p))))


(local-defthm all-initiators-smaller-counters-when-memberp
  (implies
   (and
    (all-initiators-stored-sids-have-smaller-counters-p
     initiators ids procs)
    (memberp initiator initiators))
   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator ids procs))
  :hints
  (("Goal"
    :induct
    (all-initiators-stored-sids-have-smaller-counters-p
     initiators ids procs)
    :in-theory
    (disable
     all-stored-sids-for-initiator-have-smaller-counters-p))))

(local-defthm all-stored-smaller-counters-implies-current-sid-absent
  (implies
   (all-stored-sids-for-initiator-have-smaller-counters-p
    initiator ids procs)
   (target-sid-absent-from-procs-p
    ids
    (list initiator
          (counter (g initiator procs)))
    procs))
  :hints
  (("Goal"
    :induct
    (all-stored-sids-for-initiator-have-smaller-counters-p
     initiator ids procs)
    :in-theory
    (disable
     stored-sids-for-initiator-have-smaller-counters-p))))

(local-defthm good-state-p-implies-current-sid-absent
  (implies
   (and
    (good-state-p st)
    (memberp initiator (proc-ids st)))
   (target-sid-absent-from-procs-p
    (proc-ids st)
    (list initiator
          (counter
           (g initiator (procs st))))
    (procs st)))
  :hints
  (("Goal"
    :expand
    ((good-state-p st))
    :in-theory
    (disable
     good-state-p
     all-initiators-stored-sids-have-smaller-counters-p
     all-stored-sids-for-initiator-have-smaller-counters-p
     target-sid-absent-from-procs-p))))



(local-defthm cm-sid-of-make-cut-meta
  (equal
   (cm-sid
    (make-cut-meta sid initiator st))
   sid))


(local-defthm proc-ids-of-make-cut-meta
  (equal
   (g :proc-ids
      (make-cut-meta sid initiator st))
   (proc-ids st)))

(local-defthm cut-not-taken-of-make-cut-meta
  (equal
   (g :cut-not-taken
      (make-cut-meta sid initiator st))
   (proc-ids st)))

(local-defthm checkpoint-complete-segment-p-implies-initiator-memberp
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (memberp
    (checkpoint-segment-initiator input-seg)
    (proc-ids st))))


(local-defthm checkpoint-complete-segment-p-implies-initial-meta-consistent
  (implies
   (checkpoint-start-end-segment-p st input-seg)
   (cut-meta-imp-consistent-p
    (checkpoint-segment-initial-meta st input-seg)
    st))
    :hints
    (("Goal"
      :use (checkpoint-complete-segment-p-implies-initiator-memberp)
    :in-theory
    (disable
     make-cut-meta
     checkpoint-segment-completep
     checkpoint-completes-at-segment-end-p
     scan-until-checkpoint-done
     process-cut-segment
     process-cut-step
     system-step
     checkpoint-collection-complete-p
     good-state-p
     legal-input-sequencep
     recovery-free-state-p
     cl-checkpoint-body-inputs-p))))




(local-defthm legal-start-checkpoint-sequence-implies-first-pid-memberp
  (implies
   (and
    (consp inputs)
    (legal-input-sequencep st inputs)
    (equal
     (ttype (first inputs))
     :start-checkpoint))

   (memberp
    (pid (first inputs))
    (proc-ids st))))

(local-defthm good-procs-p-and-memberp-implies-counter-natp
  (implies
   (and
    (good-procs-p ids procs all-ids)
    (memberp i ids))
   (natp
    (counter
     (g i procs)))))




(local-defthm g-of-make-empty-waiting-marker-from
  (equal
   (g i
      (make-empty-waiting-marker-from ids))
   nil)

  :rule-classes nil

  :hints
  (("Goal"
    :induct
    (make-empty-waiting-marker-from ids))

   ("Subgoal *1/2''"
    :cases
    ((equal i (car ids)))

    :use
    (:instance
     g-of-s-diff
     (k1 i)
     (k2 (car ids))
     (v nil)
     (r
      (make-empty-waiting-marker-from
       (cdr ids)))))))


(local-defthm good-cut-meta-waiting-for-procs-p-when-table-empty
  (implies
   (equal
    (g :waiting-marker-from m)
    (make-empty-waiting-marker-from all-ids))

   (good-cut-meta-waiting-for-procs-p
    ids m))

  :rule-classes nil

  :hints
  (("Goal"
    :induct
    (good-cut-meta-waiting-for-procs-p
     ids m)

    :in-theory
    (disable
     make-empty-waiting-marker-from
     cm-cut-not-taken-p
     cm-cut-not-taken
     cm-proc-ids))

   ("Subgoal *1/6''"
    :use
    (:instance
     g-of-make-empty-waiting-marker-from
     (i (car ids))
     (ids all-ids)))

   ("Subgoal *1/5''"
    :use
    (:instance
     g-of-make-empty-waiting-marker-from
     (i (car ids))
     (ids all-ids)))

   ("Subgoal *1/4''"
    :use
    (:instance
     g-of-make-empty-waiting-marker-from
     (i (car ids))
     (ids all-ids)))

   ("Subgoal *1/3''"
    :use
    (:instance
     g-of-make-empty-waiting-marker-from
     (i (car ids))
     (ids all-ids)))))



(local-defthm checkpoint-start-end-segment-p-implies-initial-meta-good
  (implies
   (checkpoint-start-end-segment-p st input-seg)

   (good-cut-meta-p
    (checkpoint-segment-initial-meta
     st input-seg)))

  :rule-classes nil

  :hints
  (("Goal"
    :use
    ((:instance
      good-cut-meta-waiting-for-procs-p-when-table-empty
      (ids (proc-ids st))
      (all-ids (proc-ids st))
      (m
       (checkpoint-segment-initial-meta
        st input-seg))))

    :in-theory
    (disable
     good-proc-p
     legal-input-sequencep
     recovery-free-state-p
     cl-checkpoint-body-inputs-p
     scan-until-checkpoint-done
     process-cut-segment
     process-cut-step
     system-step))))



(local-defthm checkpoint-segment-initial-meta-input-sequences-empty
  (and
   (equal
    (cm-before-cut-input-sequence
     (checkpoint-segment-initial-meta st input-seg))
    nil)

   (equal
    (cm-after-cut-input-sequence
     (checkpoint-segment-initial-meta st input-seg))
    nil))

  :rule-classes nil

  :hints
  (("Goal"
    :use
    ((:instance
      cm-before-cut-input-sequence-of-make-cut-meta
      (sid
       (checkpoint-segment-sid st input-seg))
      (initiator
       (checkpoint-segment-initiator input-seg)))

     (:instance
      cm-after-cut-input-sequence-of-make-cut-meta
      (sid
       (checkpoint-segment-sid st input-seg))
      (initiator
       (checkpoint-segment-initiator input-seg))))

    :expand
    ((checkpoint-segment-initial-meta
      st input-seg))

    :in-theory
    (disable
     checkpoint-segment-initial-meta
     checkpoint-segment-sid
     checkpoint-segment-initiator
     make-cut-meta
     cm-before-cut-input-sequence
     cm-after-cut-input-sequence))))


(defthm checkpoint-start-end-segment-reorder-connection
  (implies
   (checkpoint-start-end-segment-p st input-seg)

   (equal
    (reorder-inputs
     st
     (checkpoint-segment-initial-meta st input-seg)
     input-seg)

    (append
     (checkpoint-segment-before-cut-inputs st input-seg)
     (checkpoint-segment-after-cut-inputs st input-seg))))

  :rule-classes nil

  :hints
  (("Goal"
    :do-not-induct t

    :use
    (checkpoint-complete-segment-p-implies-initial-meta-consistent
     checkpoint-start-end-segment-p-implies-initial-meta-good
     checkpoint-segment-meta-equals-process-cut-segment
     checkpoint-segment-initial-meta-input-sequences-empty

     (:instance
      cut-markers-in-transit-p-of-make-cut-meta
      (target-sid
       (checkpoint-segment-sid st input-seg))
      (initiator
       (checkpoint-segment-initiator input-seg)))

     (:instance
      reorder-inputs-equals-process-cut-segment-partition
      (inputs input-seg)
      (m
       (checkpoint-segment-initial-meta
        st input-seg))))

    :expand
    ((checkpoint-segment-initial-meta
      st input-seg)

     (checkpoint-segment-before-cut-inputs
      st input-seg)

     (checkpoint-segment-after-cut-inputs
      st input-seg))

    :in-theory
    (disable
     true-listp
     good-state-p
     recovery-free-state-p
     legal-input-sequencep
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     good-cut-meta-p

     checkpoint-segment-initial-meta
     checkpoint-segment-meta
     checkpoint-segment-before-cut-inputs
     checkpoint-segment-after-cut-inputs
     checkpoint-segment-completep
     checkpoint-completes-at-segment-end-p
     checkpoint-segment-sid
     checkpoint-segment-initiator

     cm-before-cut-input-sequence
     cm-after-cut-input-sequence
     scan-until-checkpoint-done
     process-cut-segment
     process-cut-step
     system-step
     reorder-inputs
     make-cut-meta
     binary-append))))






(defthm checkpoint-complete-segment-reordered-run-state-equivalent
  (implies
   (checkpoint-start-end-segment-p st input-seg)

   (state-equivalent-p
    (run-imp st input-seg)

    (run-imp
     st
     (append
      (checkpoint-segment-before-cut-inputs st input-seg)
      (checkpoint-segment-after-cut-inputs st input-seg)))))

  :rule-classes nil

  :hints
  (("Goal"
    :do-not-induct t

    :use
    (checkpoint-start-end-segment-reorder-connection
     checkpoint-complete-segment-p-implies-initial-meta-consistent
     checkpoint-start-end-segment-p-implies-initial-meta-good

     (:instance
      cut-markers-in-transit-p-of-make-cut-meta
      (target-sid
       (checkpoint-segment-sid st input-seg))
      (initiator
       (checkpoint-segment-initiator input-seg)))

     (:instance
      reorder-inputs-preserves-run
      (inputs input-seg)
      (m
       (checkpoint-segment-initial-meta
        st input-seg))))

    :expand
    ((checkpoint-segment-initial-meta
      st input-seg))

    :in-theory
    (disable
     checkpoint-segment-initial-meta
     checkpoint-segment-sid
     checkpoint-segment-initiator
     checkpoint-segment-completep
     checkpoint-completes-at-segment-end-p
     checkpoint-segment-before-cut-inputs
     checkpoint-segment-after-cut-inputs

     scan-until-checkpoint-done
     process-cut-segment
     process-cut-step
     system-step
     make-cut-meta

     reorder-inputs
     reorder-inputs-returns-before-append-after

     before-cut-inputs
     after-cut-inputs

     run-imp
     run-imp-of-append
     run-imp-when-consp

     state-equivalent-p
     binary-append

     true-listp
     cut-markers-in-transit-p
     cut-meta-imp-consistent-p
     good-cut-meta-p
     good-state-p
     recovery-free-state-p
     legal-input-sequencep

     reorder-inputs-preserves-run))))

) ;; end local segment-connection proof
