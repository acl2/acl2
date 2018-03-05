; Copyright (C) 2017, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(local (include-book "arithmetic/top-with-meta" :dir :system))

(defun snap (x y)
  (intern (string-append (symbol-name x) (symbol-name y)) "ACL2"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; variable naming rules from here on...
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

1. ((fair-run(A,IP)  & valid-system(A,IP))    => valid-run(A,IP))
2. ((valid-run(A,IP) & match-systems(A,B,IP)) => fair-run(B,IP))

We will assume:

fair-run(A,IP) & 
valid-system(A,IP) &
match-systems(A,B,IP)

and prove:

valid-run(A,IP) & 
fair-run(B,IP)

This allows us to say that for any key predicate IP and systems A,B, if we prove:

  valid-system(A,IP) & match-systems(A,B,IP)

then any fair infinite run of A can be mapped to a fair infinite run of B and
further if we prove valid-system(B,IP), then any fair infinite run of A can be
mapped to a valid infinite run of B (which is the more likely specification for
A). This can be even further extended to any chain of systems: A1,..,Ak where
for each system Ai, we have proven valid-system(Ai) and match-system(Ai,Ai+1),
then every fair infinite run of A1 corresponds to a valid infinite run of Ak.

inf-run(A) needs:
   (A-step x y k)  -> bool
   (A-iinv x)      -> bool

async-system(B) needs:
   (B-step x y k)  -> bool
   (B-iinv x)      -> bool

valid-system(A) needs:
   (A-noblk k x)   -> bool
   (A-nstrv k x)   -> ord

match-system(A,B) needs:
   (A-map x)       -> B-state
   (A-rank k x)    -> ord

|#

(defmacro def-inf-run (name)
  (declare (xargs :guard (symbolp name)))
  (let ((next (snap name '-next))
        (init (snap name '-init))
        (blok (snap name '-blok))
        (pick (snap name '-pick))
        (step (snap name '-step))
        (run  (snap name '-run)))
    (let ((run-open-step (snap name '-run-open-step))
          (run-init-thm (snap name '-run-init))
          (run-step-thm (snap name '-run-step)))
      `(progn
         (local (defun ,step (x y k)
                  (if (or (null k)      ;; finite stutter
                          (,blok x k))  ;; or k is blocked in x
                      (equal x y)
                    (,next x y k))))
         (defthm ,run-open-step
           (equal (,step x y k)
                  (if (or (null k)      ;; finite stutter
                          (,blok x k))  ;; or k is blocked in x
                      (equal x y)
                    (,next x y k))))
         (defthm ,run-init-thm  ;; nil or empty record is only initial state..
           (implies (zp i)
                    (,init (,run i))))
         (defthm ,run-step-thm
           (implies (posp i)
                    (,step (,run (1- i))
                           (,run i)
                           (,pick i))))))))

(defmacro def-mapped-run (impl spec)
  (let ((i-map (snap impl '-map))
        (i-run (snap impl '-run))
        (s-run (snap spec '-run)))
    `(progn
       (defun ,s-run (i) (,i-map (,i-run i))))))

(defmacro def-fair-pick (name id-p)
  (declare (xargs :guard (and (symbolp name) (symbolp id-p))))
  (let ((pick (snap name '-pick))
        (fair (snap name '-fair)))
    (let ((pick-key-thm   (snap name '-pick-is-key))
          (fair-nat-thm   (snap name '-fair-is-nat))
          (pick-fair-thm  (snap name '-pick-is-fair)))
      `(progn
         (defthm ,pick-key-thm
           (implies (,pick i)
                    (,id-p (,pick i))))
         (defthm ,fair-nat-thm
           (natp (,fair k i))
           :rule-classes (:type-prescription :rewrite))
         (defthm ,pick-fair-thm
           (implies (and (posp i)
                         (,id-p k)
                         (not (equal (,pick i) k)))
                    (< (,fair k i) (,fair k (1- i))))
           :rule-classes (:linear :rewrite))))))

;; the progress theorem.. for each KEY k, if a transaction exists for k, then
;; it will make "progress" to completion (i.e. some change in state) or the
;; measure function applied to k will decrease:
(defmacro def-valid-run (name id-p)
  (declare (xargs :guard (and (symbolp name) (symbolp id-p))))
  (let ((run  (snap name '-run))
        (pick (snap name '-pick))
        (prog (snap name '-prog)))
    (let ((prog-is-nat  (snap name '-prog-is-nat))
          (run-prog-thm (snap name '-run-prog-thm)))
      `(progn
         (defthm ,prog-is-nat
           (natp (,prog k i))
           :rule-classes (:type-prescription :rewrite))
         (defthm ,run-prog-thm
           (implies (and (posp i)
                         (,id-p k)
                         (not (and (equal (,pick i) k)
                                   (not (equal (,run i) (,run (1- i)))))))
                    (< (,prog k i) (,prog k (1- i))))
           :rule-classes (:linear :rewrite))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro def-system-props (name id-p)
  (declare (xargs :guard (and (symbolp name) (symbolp id-p))))
  (let ((next (snap name '-next))
        (init (snap name '-init))
        (blok (snap name '-blok))
        (iinv (snap name '-iinv)))
    (let ((nil-is-not-id    (snap name '-nil-is-not-id))
          (next-must-change (snap name '-next-must-change))
          (iinv-init-thm    (snap name '-iinv-init))
          (iinv-next-thm    (snap name '-iinv-next)))
      `(progn
         (defthm ,nil-is-not-id
           (not (,id-p nil)))
         (defthm ,next-must-change
           (equal (,next x x k) nil))
         (defthm ,iinv-init-thm 
           (implies (,init x) (,iinv x)))
         (defthm ,iinv-next-thm
           (implies (and (,iinv x)
                         (,id-p k)
                         (not (,blok x k))
                         (,next x y k))
                    (,iinv y)))))))
  
(defmacro def-valid-system (name id-p)
  (declare (xargs :guard (and (symbolp name) (symbolp id-p))))
  (let ((next    (snap name '-next))
        (blok    (snap name '-blok))
        (iinv    (snap name '-iinv))
        (noblk   (snap name '-noblk))
        (nstrv   (snap name '-nstrv))
        (starver (snap name '-starver)))
    (let ((nstrv-is-ord   (snap name '-nstrv-is-ord))
          (noblk-blk-thm  (snap name '-noblk-blk-thm))
          (noblk-inv-thm  (snap name '-noblk-inv-thm))
          (no-strv-thm    (snap name '-no-strv-thm))
          (no-starver-thm (snap name '-no-starver-thm))
          (starver-thm    (snap name '-starver-thm))
          (starver-is-id  (snap name '-starver-is-id))
          (starver-persists (snap name '-starver-persists)))
      `(progn
         (defthm ,noblk-blk-thm
           (implies (and (,iinv x)
                         (,id-p k)
                         (,noblk k x))
                    (not (,blok x k))))
         (defthm ,noblk-inv-thm
           (implies (and (,iinv x)
                         (,id-p k) 
                         (,id-p l)
                         (not (equal k l))
                         (,noblk k x)
                         (,next x y l)
                         (not (,blok x l)))
                    (,noblk k y)))
         (defthm ,nstrv-is-ord
           (o-p (,nstrv k x)))
         (defthm ,starver-is-id
           (implies (,id-p k)
                    (,id-p (,starver k x))))
         (defthm ,starver-thm
           (implies (and (,id-p k)
                         (,iinv x)
                         (not (,noblk k x)))
                    (not (,blok x (,starver k x)))))
         (defthm ,no-starver-thm
           (implies (and (,iinv x)
                         (,id-p k)
                         (not (equal (,starver k x) k))
                         (,next x y (,starver k x))
                         (not (,noblk k x)))
                    (o< (,nstrv k y) (,nstrv k x))))
         (defthm ,no-strv-thm
           (implies (and (,iinv x)
                         (,id-p k)
                         (,id-p l)
                         (not (equal k l))
                         (,next x y l)
                         (not (,blok x l))
                         (not (,noblk k x)))
                    (o<= (,nstrv k y) (,nstrv k x))))
         (defthm ,starver-persists
           (implies (and (,iinv x)
                         (,id-p k)
                         (,id-p l)
                         (,next x y l)
                         (not (,blok x l))
                         (not (equal l k))
                         (not (,noblk k x))
                         (not (equal l (,starver k x)))
                         (equal (,nstrv k y) (,nstrv k x)))
                    (equal (,starver k y) (,starver k x))))))))

(defmacro def-match-systems (impl spec id-p)
  (declare (xargs :guard (and (symbolp impl) (symbolp spec) (symbolp id-p))))
  (let ((i-next (snap impl '-next))
        (i-blok (snap impl '-blok))
        (i-iinv (snap impl '-iinv))
        (i-init (snap impl '-init))
        (i-map  (snap impl '-map))
        (i-rank (snap impl '-rank))
        (s-init (snap spec '-init))
        (s-next (snap spec '-next))
        (s-blok (snap spec '-blok)))
    (let ((map-init-to-init   (snap impl '-map-init-to-init))
          (rank-is-ord        (snap impl '-rank-is-ord))
          (map-match-next     (snap impl '-map-match-next))
          (map-finite-stutter (snap impl '-map-finite-stutter))
          (map-rank-stable    (snap impl '-map-rank-stable)))
      `(progn
         (defthm ,map-init-to-init
           (implies (,i-init x) (,s-init (,i-map x))))
         (defthm ,rank-is-ord
           (o-p (,i-rank k x)))
         (defthm ,map-match-next
           (implies (and (,i-iinv x)
                         (,id-p k)
                         (,i-next x y k)
                         (not (,i-blok x k))
                         (not (equal (,i-map x) (,i-map y))))
                    (and (,s-next (,i-map x) (,i-map y) k)
                         (not (,s-blok (,i-map x) k)))))
         (defthm ,map-finite-stutter
           (implies (and (,i-iinv x)
                         (,id-p k)
                         (,i-next x y k)
                         (not (,i-blok x k))
                         (equal (,i-map x) (,i-map y)))
                    (o< (,i-rank k y) (,i-rank k x))))
         (defthm ,map-rank-stable
           (implies (and (,i-iinv x)
                         (,id-p k)
                         (,id-p l)
                         (not (equal k l))
                         (,i-next x y l)
                         (not (,i-blok x l)))
                    (o<= (,i-rank k y) (,i-rank k x))))))))

#| IMPL to SPEC:

In order to prove the relationship from IMPL to SPEC, we define a mapping from
states in IMPL to states in SPEC which is per transaction.

Given an infinite run of IMPL, we need to prove that the infinite sequence
defined by mapping the IMPL states in the IMPL run into SPEC states defines a
SPEC run (allowing for finite stuttering).

Assuming that we have function (impl-run i) defining an infinite IMPL run and a
mapping (impl-map x) which takes an IMPL state and returns a SPEC state, then
we define the spec run simply as the function:

  (defun spec-run (i) (impl-map (impl-run i)))

and then need to prove the following facts about spec-run to show that it is
a run of SPEC:

  (defthm spec-run-init-thm
    (implies (zp i) (init-spec (spec-run i))))

  (defthm spec-run-next-thm
    (implies (posp i)
             (spec-next (spec-run (1- i))
                        (spec-run i)
                        (spec-pick i)
                        (spec-stutter i))))

  (defthm spec-run-prog-thm
    (implies (and (posp i) (spec-stutter i))
             (o< (spec-rank i) (spec-rank (1- i))))))

|#
(encapsulate
 (;; IMPL/SPEC shared definition:
  (id-p (x)             t) ;; identifier predicate for common set of selectors
  ;; IMPL definition -- 
  (impl-init  (x)       t)
  (impl-next  (x y k)   t) ;; state x transitions to state y on selector k
  (impl-blok  (x k)     t) ;; state x blocked for transitions for selector k
  ;; SPEC definition -- 
  (spec-init  (x)       t)
  (spec-next  (x y k)   t) ;; state x transitions to state y on selector k
  (spec-blok  (x k)     t) ;; state x blocked for transitions for selector k
  ;; IMPL to SPEC refinement -- 
  (impl-map   (x)       t) ;; maps impl states to corresponding spec states
  ;; IMPL run definitions -- 
  (impl-pick  (i)       t) ;; returns selection for natural time i during run
  (impl-fair  (k i)     t) ;; returns natural countdown at time i until k selected
  (impl-step  (x y k)   t) ;; step relation used to define run which merges blok,pick,next
  (impl-run   (i)       t) ;; infinite run sequence mapping naturals to impl states
  ;; IMPL state properties --
  (impl-iinv    (x)     t) ;; inductive invariant for impl on states
  (impl-noblk   (k x)   t) ;; is selector k invariantly unblocked in state x
  (impl-nstrv   (k x)   t) ;; ordinal decreases until k is in a noblk state
  (impl-starver (k x)   t) ;; starver of k in x who is not blocked in x
  (impl-rank    (k x)   t) ;; ordinal decreases until spec matches transition for k
  )  
 
 ;; Local witness functions for the exported signatures:
 ;; IMPL/SPEC shared definition:
 (local (defun id-p         (x)      (equal x t)))
 ;; IMPL definition -- 
 (local (defun impl-init    (x)      (not x)))
 (local (defun impl-next    (x y k)  (declare (ignore k)) (equal (not x) y)))
 (local (defun impl-blok    (x k)    (declare (ignore x k)) nil))
 ;; SPEC definition -- 
 (local (defun spec-init    (x)      (not x)))
 (local (defun spec-next    (x y k)  (declare (ignore k)) (equal (not x) y)))
 (local (defun spec-blok    (x k)    (declare (ignore x k)) nil))
 ;; IMPL to SPEC refinement -- 
 (local (defun impl-map     (x)       x))
 ;; IMPL run assumptions -- 
 (local (defun impl-pick    (i)      (declare (ignore i)) t))
 (local (defun impl-fair    (k i)    (declare (ignore k i)) 0))
 (local (defun impl-run     (i)      (if (zp i) nil (not (impl-run (1- i))))))
 ;; IMPL state properties --
 (local (defun impl-iinv    (x)      (booleanp x)))
 (local (defun impl-noblk   (k x)    (declare (ignore k x)) t))
 (local (defun impl-nstrv   (k x)    (declare (ignore k x)) 0))
 (local (defun impl-starver (k x)    (declare (ignore k x)) t))
 (local (defun impl-rank    (k x)    (declare (ignore k x)) 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; P0::: IMPORTANT NOTE:
;;  As we mentioned before, exported properties from this encapsulation are the following macros which
;;  expand as we presented before and represent the assumptions we make moving forward:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 (def-system-props  impl id-p)
 (def-valid-system  impl id-p)
 (def-match-systems impl spec id-p)
 (def-inf-run       impl)
 (def-fair-pick     impl id-p)
)

(defthm impl-starver-is-not-nil
  (implies (id-p k)
           (iff (impl-starver k x) t))
  :hints (("Goal"
           :use ((:instance impl-starver-is-id))
           :in-theory (disable impl-starver-is-id)
           :cases ((impl-starver k x)))))

;; outside

;impl-prog  ;; 
;spec-run
;spec-pick
;spec-fair

;; we need to change the shape of some theorems.. they were defined for clarity but
;; are not the best for rewriting, so we address that here..

(in-theory (disable impl-run-open-step impl-run-step impl-iinv-next impl-noblk-inv-thm))

(defthm impl-step-thm-1
  (implies (and (posp i) (null (impl-pick i)))
           (equal (impl-run i) (impl-run (1- i))))
    :hints (("Goal" :use ((:instance impl-run-open-step
                                   (x (impl-run (1- i)))
                                   (y (impl-run i))
                                   (k (impl-pick i)))
                        (:instance impl-run-step)))))

(defthm impl-step-thm-2
  (implies (and (posp i) (impl-pick i) (impl-blok (impl-run (1- i)) (impl-pick i)))
           (equal (impl-run i) (impl-run (1- i))))
  :hints (("Goal" :use ((:instance impl-run-open-step
                                   (x (impl-run (1- i)))
                                   (y (impl-run i))
                                   (k (impl-pick i)))
                        (:instance impl-run-step)))))

(defthm impl-step-thm-3
  (implies (and (posp i) (impl-pick i) (not (impl-blok (impl-run (1- i)) (impl-pick i))))
           (impl-next (impl-run (1- i)) (impl-run i) (impl-pick i)))
  :hints (("Goal" :use ((:instance impl-run-open-step
                                   (x (impl-run (1- i)))
                                   (y (impl-run i))
                                   (k (impl-pick i)))
                        (:instance impl-run-step)))))

(defun nat-ind (i) (if (zp i) nil (not (nat-ind (1- i)))))

(defthm impl-run-inv-prop
  (implies (and (posp i)
                (impl-pick i)
                (not (impl-blok (impl-run (1- i)) (impl-pick i)))
                (impl-iinv (impl-run (1- i))))
           (impl-iinv (impl-run i)))
    :hints (("Goal" :use ((:instance impl-run-open-step
                                   (x (impl-run (1- i)))
                                   (y (impl-run i))
                                   (k (impl-pick i)))
                          (:instance impl-iinv-next
                                     (x (impl-run (1- i)))
                                     (y (impl-run i))
                                     (k (impl-pick i)))
                          (:instance impl-run-step)))))

(defthm impl-iinv-impl-run
  (impl-iinv (impl-run i))
  :hints (("Goal" :induct (nat-ind i))
          ("Subgoal *1/2" :cases ((not (impl-pick i))
                                  (and (impl-pick i)
                                       (impl-blok (impl-run (1- i)) (impl-pick i)))))))

(defun ord-nat-pair (o n)
  ;; simple function which returns cartesian product of an o-p ordinal o and natural n:
  (make-ord (if (atom o) (1+ o) o) 1 n))

(local
(defthm atom-ord-implies-natp-add1
  (implies (and (o-p x)
                (not (consp x)))
           (natp (1+ x)))))
(local
(defthm atom-ord-implies-linear-add1
  (implies (and (o-p x)
                (not (consp x)))
           (> (1+ x) 0))))

(defthm impl-fair-<-junk1
  (implies (and (natp i)
                (id-p k)
                (not (equal (impl-pick (1+ i)) k)))
           (< (impl-fair k (1+ i))
              (impl-fair k i)))
  :hints (("Goal" :use ((:instance impl-pick-is-fair
                                   (i (1+ i))))))
  :rule-classes (:linear :rewrite))

(in-theory (enable o< o-p ord-nat-pair))

(defthm ord-nat-pair-o-p
  (implies (and (o-p o) (natp n))
           (o-p (ord-nat-pair o n))))

(defthm ord-nat-pair-equal
  (implies (and (o-p o1) (o-p o2))
           (equal (equal (ord-nat-pair o1 n1)
                         (ord-nat-pair o2 n2))
                  (and (equal o1 o2) (equal n1 n2)))))

(defthm ord-nat-pair-o<
  (implies (and (o-p o1) (natp n1)
                (o-p o2) (natp n2))
           (equal (o< (ord-nat-pair o1 n1)
                      (ord-nat-pair o2 n2))
                  (or (o< o1 o2)
                      (and (equal o1 o2)
                           (< n1 n2))))))

(defthm o-p-natp-redux
  (implies (natp x) (o-p x)))

(defthm o<-natp-redux
  (implies (and (natp x) (natp y))
           (equal (o< x y) (< x y))))

(defthm o<=-is-really-o<=
  (implies (and (o-p x) 
                (o-p y) 
                (o<= x y)
                (not (equal x y)))
           (o< x y)))

(defthm o<=-is-total-o-p
  (implies (and (o-p x)
                (o-p y)
                (o<= x y)
                (o<= y x))
           (equal (equal x y) t)))

(in-theory (disable o< o-p ord-nat-pair))

(local (defthm prog-junk1
  (implies (and (natp i) (id-p k)
                (impl-noblk k (impl-run i))
                (equal (impl-run (1+ i)) (impl-run i)))
           (< (impl-fair k (1+ i)) (impl-fair k i)))
  :hints (("Goal" :use ((:instance impl-run-open-step
                                   (x (impl-run i))
                                   (y (impl-run (1+ i)))
                                   (k (impl-pick (1+ i))))
                        (:instance impl-run-step
                                   (i (1+ i)))
                        (:instance impl-pick-is-fair
                                   (i (1+ i))))))))

(local (defthm prog-junk2
  (implies (and (natp i)
                (id-p k)
                (not (equal (impl-pick (1+ i)) k))
                (not (impl-noblk k (impl-run i)))
                (not (equal (impl-nstrv k (impl-run (1+ i)))
                            (impl-nstrv k (impl-run i)))))
           (o< (impl-nstrv k (impl-run (1+ i)))
               (impl-nstrv k (impl-run i))))
  :hints (("Goal" :use ((:instance impl-run-open-step
                                   (x (impl-run i))
                                   (y (impl-run (1+ i)))
                                   (k (impl-pick (1+ i))))
                        (:instance impl-run-step
                                   (i (1+ i)))
                        (:instance impl-no-strv-thm
                                   (x (impl-run i))
                                   (y (impl-run (1+ i)))
                                   (l (impl-pick (1+ i)))))))))

(local (defthm prog-junk3
  (implies (and (natp i)
                (id-p k)
                (not (equal (impl-pick (1+ i)) k))
                (not (impl-noblk k (impl-run i)))
                (not (o< (impl-nstrv k (impl-run (1+ i)))
                         (impl-nstrv k (impl-run i)))))
           (< (impl-fair (impl-starver k (impl-run (1+ i))) (1+ i))
              (impl-fair (impl-starver k (impl-run i)) i)))
  :hints (("Goal" 
           :use ((:instance impl-run-open-step
                            (x (impl-run i))
                            (y (impl-run (1+ i)))
                            (k (impl-pick (1+ i))))
                 (:instance impl-run-step
                            (i (1+ i)))
                 (:instance impl-no-starver-thm
                            (x (impl-run i))
                            (y (impl-run (1+ i))))
                 (:instance impl-no-strv-thm
                            (x (impl-run i))
                            (y (impl-run (1+ i)))
                            (l (impl-pick (1+ i))))
                 (:instance impl-starver-persists
                            (x (impl-run i))
                            (y (impl-run (1+ i)))
                            (l (impl-pick (1+ i))))
                 (:instance impl-pick-is-fair
                            (k (impl-starver k (impl-run i)))
                            (i (1+ i))))
           :cases ((equal (impl-starver k (impl-run i))
                          (impl-pick (1+ i))))))))

(local (defthm prog-junk4
  (implies (and (natp i)
                (id-p k)
                (equal (impl-run (1+ i)) (impl-run i))
                (not (impl-noblk k (impl-run i)))
                (not (o< (impl-nstrv k (impl-run (1+ i)))
                         (impl-nstrv k (impl-run i)))))
           (< (impl-fair (impl-starver k (impl-run i)) (1+ i))
              (impl-fair (impl-starver k (impl-run i)) i)))
  :hints (("Goal" 
           :use ((:instance impl-run-open-step
                            (x (impl-run i))
                            (y (impl-run (1+ i)))
                            (k (impl-pick (1+ i))))
                 (:instance impl-run-step
                            (i (1+ i)))
                 (:instance impl-no-starver-thm
                            (x (impl-run i))
                            (y (impl-run (1+ i))))
                 (:instance impl-no-strv-thm
                            (x (impl-run i))
                            (y (impl-run (1+ i)))
                            (l (impl-pick (1+ i))))
                 (:instance impl-pick-is-fair
                            (k (impl-starver k (impl-run i)))
                            (i (1+ i))))
           :cases ((equal (impl-starver k (impl-run i))
                          (impl-pick (1+ i))))))))

(local (defthm prog-junk5
         (IMPLIES (AND (NATP I)
                       (ID-P K)
                       (NOT (EQUAL (IMPL-PICK (+ 1 I)) K))
                       (NOT (IMPL-NOBLK K (IMPL-RUN (+ 1 I))))
                       (IMPL-NOBLK K (IMPL-RUN I)))
                  (O< (ORD-NAT-PAIR (IMPL-NSTRV K (IMPL-RUN (+ 1 I)))
                                    (IMPL-FAIR (IMPL-STARVER K (IMPL-RUN (+ 1 I)))
                                               (+ 1 I)))
                      (IMPL-FAIR K I)))
         :hints (("Goal" :in-theory (disable impl-noblk-inv-thm)
                  :use ((:instance impl-run-step
                                   (i (1+ i)))
                        (:instance impl-run-open-step
                                   (x (impl-run i))
                                   (y (impl-run (1+ i)))
                                   (k (impl-pick (1+ i))))
                        (:instance impl-noblk-inv-thm
                                   (x (impl-run i))
                                   (y (impl-run (1+ i)))
                                   (k k)
                                   (l (impl-pick (1+ i)))))))))

(local (defthm prog-junk6
         (IMPLIES (AND (NATP I)
                       (ID-P K)
                       (NOT (EQUAL (IMPL-PICK (+ 1 I)) K))
                       (IMPL-NOBLK K (IMPL-RUN (+ 1 I)))
                       (NOT (IMPL-NOBLK K (IMPL-RUN I))))
                  (O< (IMPL-FAIR K (+ 1 I))
                      (ORD-NAT-PAIR (IMPL-NSTRV K (IMPL-RUN I))
                                    (IMPL-FAIR (IMPL-STARVER K (IMPL-RUN I))
                                               I))))
         :hints (("Goal" :in-theory (enable o<)))))

(defun impl-prog (k i)
  (declare 
   (xargs :measure
          (if (impl-noblk k (impl-run i))
              (impl-fair k i)              
            (ord-nat-pair (impl-nstrv k (impl-run i))
                          (impl-fair (impl-starver k (impl-run i)) i)))))
  (cond
   ((not (and (natp i) (id-p k)))  ;; ill-formed case
    0)
   ((and (equal (impl-pick (1+ i)) k)   ;; ready to go..
         (not (equal (impl-run (1+ i)) (impl-run i))))
    0)
   (t (1+ (impl-prog k (1+ i))))))

(defthm impl-prog-is-nat*
  (natp (impl-prog k i))
  :rule-classes (:type-prescription :rewrite))

(defthm impl-run-step-noblk-inv
  (implies (and (posp i)
                (id-p (impl-pick i))
                (equal (impl-run (1- i)) (impl-run i)))
           (not (impl-noblk (impl-pick i) (impl-run i))))
    :hints (("Goal" :use ((:instance impl-run-open-step
                                   (x (impl-run (1- i)))
                                   (y (impl-run i))
                                   (k (impl-pick i)))
                          (:instance impl-run-step)))))
(defthm run-prog-junk1
  (implies (and (posp i)
                (id-p k)
                (not (equal (impl-pick i) k))
                (impl-noblk k (impl-run (1- i))))
           (impl-noblk k (impl-run i)))
  :hints (("Goal" :use ((:instance impl-run-open-step
                                   (x (impl-run (1- i)))
                                   (y (impl-run i))
                                   (k (impl-pick i)))
                        (:instance impl-run-step)
                        (:instance impl-noblk-inv-thm
                                   (x (impl-run (1- i)))
                                   (y (impl-run i))
                                   (l (impl-pick i)))))))

(defthm impl-run-prog-thm*
  (implies (and (posp i)
                (id-p k)
                (not (and (equal (impl-pick i) k)
                          (not (equal (impl-run i) (impl-run (1- i)))))))
           (< (impl-prog k i) (impl-prog k (1- i))))
  :rule-classes (:linear :rewrite))

;; go ahead and prove our first goal here (we will "repeat" all of the goals at the
;; end of this book later..)
(def-valid-run impl id-p)

;; now go ahead and define our run of spec from the mapped impl states of our impl
;; run.. we will then start working on showing that this is a infinite run of spec.
;; with fair picks:
(def-mapped-run impl spec)

;; in order to show that the mapped run is an infinite run, we need to show that
;; we can define a pick function for the spec run which ensures the spec-run-step
;; theorem:
(defun spec-pick (i)
  (and (posp i)
       (impl-pick i)
       (not (equal (impl-map (impl-run (1- i)))
                   (impl-map (impl-run i))))
       (impl-pick i)))

(defun spec-step (x y k)
  (if (or (null k) (spec-blok x k))
      (equal x y)
    (spec-next x y k)))

(defthm spec-run-step*
  (implies (posp i)
           (spec-step (spec-run (1- i))
                      (spec-run i)
                      (spec-pick i)))
  :hints (("Goal" :use ((:instance impl-run-open-step
                                   (x (impl-run (1- i)))
                                   (y (impl-run i))
                                   (k (impl-pick i)))
                        (:instance impl-run-step)
                        (:instance impl-map-match-next
                                   (x (impl-run (1- i)))
                                   (y (impl-run i))
                                   (k (impl-pick i)))))))

(defthm spec-run-open-step
  (equal (spec-step x y k)
         (if (or (null k) (spec-blok x k))
             (equal x y)
           (spec-next x y k))))

(defthm spec-run-init
  (implies (zp i) (spec-init (spec-run i))))

(in-theory (disable spec-step spec-run-open-step spec-run spec-pick))

;; go ahead and prove our next goal that the mapped run from the impl to the spec
;; is indeed an infinite run of the spec.. (we will "repeat" this as well at the
;; end of the book):
(def-inf-run spec)

;; now we need to show that the pick we defined for the spec run (the function
;; spec-pick above) is indeed a fair picker leading to a fair run of spec:
(in-theory (enable spec-pick))

(defun spec-fair (k i)
  (declare
   (xargs
    :measure
    (ord-nat-pair (impl-rank k (impl-run i))
                  (impl-prog k i))
    :hints
    (("Goal"
      :use ((:instance impl-run-open-step
                       (x (impl-run i))
                       (y (impl-run (1+ i)))
                       (k (impl-pick (1+ i))))
            (:instance impl-run-step
                       (i (1+ i)))
            (:instance impl-map-finite-stutter
                       (x (impl-run i))
                       (y (impl-run (1+ i)))
                       (k (impl-pick (1+ i))))
            (:instance impl-map-rank-stable
                       (x (impl-run i))
                       (y (impl-run (1+ i)))
                       (l (impl-pick (1+ i)))))))))
  (cond
   ((not (and (natp i) (id-p k)))      ;; ill-formed case
    0)
   ((equal (spec-pick (1+ i)) k)  ;; spec-pick matches k
    0)
   (t (1+ (spec-fair k (1+ i))))))

(def-fair-pick spec id-p)

;; BUT.. we can do even better.. because of how we had to guarantee
;; that we could generate a fair matching selection for each k,i (i.e.
;; by ensuring that we actually caused a transition in the spec)..
;; we can actually prove that the "mapped" spec-run actually must
;; make progress for each k and is thus valid..:

(defun spec-prog (k i)
  (declare
   (xargs
    :measure
    (ord-nat-pair (impl-rank k (impl-run i))
                  (impl-prog k i))
    :hints
    (("Goal"
      :in-theory (enable spec-run)
      :use ((:instance impl-run-open-step
                       (x (impl-run i))
                       (y (impl-run (1+ i)))
                       (k (impl-pick (1+ i))))
            (:instance impl-run-step
                       (i (1+ i)))
            (:instance impl-map-finite-stutter
                       (x (impl-run i))
                       (y (impl-run (1+ i)))
                       (k (impl-pick (1+ i))))
            (:instance impl-map-rank-stable
                       (x (impl-run i))
                       (y (impl-run (1+ i)))
                       (l (impl-pick (1+ i)))))))))
  (cond
   ((not (and (natp i) (id-p k)))      ;; ill-formed case
    0)
   ((and (equal (spec-pick (1+ i)) k)  ;; spec-pick matches k
         (not (equal (spec-run (1+ i)) (spec-run i))))
    0)
   (t (1+ (spec-prog k (1+ i))))))

(def-valid-run spec id-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; P1::: IMPORTANT NOTE:
;;  As we mentioned before, the only non-local properties from this encapsulation are the following macros which
;;  expand as we presented before and represent the assumptions we make moving forward:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-valid-run  impl id-p)
(def-mapped-run impl spec)
(def-inf-run    spec)
(def-fair-pick  spec id-p)
(def-valid-run  spec id-p)
