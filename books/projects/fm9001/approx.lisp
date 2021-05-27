;; Copyright (C) 2016, Regents of the University of Texas
;; Written by Cuong Chau (derived from earlier work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; See the README for historical information.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; February 2021

(in-package "FM9001")

(include-book "de")
(include-book "monotonicity-macros")

(local (include-book "list-rewrites"))

;; ======================================================================

;;; Table of Contents:
;;;
;;; 1. INITIALIZATION
;;; 2. APPROXIMATION NOTIONS
;;; 3. notion of MONOTONICITY-PROPERTY for a module
;;; 4. MONOTONICITY LEMMAS FOR BOOLEAN FUNCTIONS
;;; 5. MONOTONICITY LEMMAS FOR PRIMITIVE HARDWARE COMPONENTS
;;;    except the RAM
;;; 6. MONOTONICITY LEMMA for the RAM
;;; 7. MONOTONICITY FOR ALL PRIMITIVES
;;; 8. MONOTONICITY OF DE
;;; 9. MONOTONICITY FOR SIMULATION

;; ======================================================================

;;;;;                  INITIALIZATION                  ;;;;;

;; Note: This file requires macros defined in "monotonicity-macros.lisp".

;; ======================================================================

;;;;;               APPROXIMATION NOTIONS              ;;;;;

;; Here we define (b-approx a1 a2), which holds when a1 and a2 are
;; equal unless a1 is *X* (or anything other than T, NIL, or *Z*,
;; actually).  Then we extend this "bit approximation" notion to
;; bit vectors (V-APPROX V1 V2) and states [including RAM states]
;; (S-APPROX S1 S2).

(defund b-knownp (x)
  (declare (xargs :guard t))
  (or (equal x t)
      (equal x nil)
      (equal x *z*)))

(defun b-approx (a1 a2)
  (declare (xargs :guard t))
  (if (b-knownp a1)
      (equal a1 a2)
    t))

(defun v-approx (v1 v2)
  (declare (xargs :guard t))
  ;; implies that v1 and v2 have the same length
  (if (consp v1)
      (and (consp v2)
           (b-approx (car v1) (car v2))
           (v-approx (cdr v1) (cdr v2)))
    ;; need the following so that approximation by a known
    ;; value implies equality
    (equal v1 v2)))

(defthm v-approx-x-x
  (v-approx x x))

(defun v-knownp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (b-knownp (car x))
           (v-knownp (cdr x)))
    t))

(defthm v-knownp-implies-v-approx-is-equal
  ;; stated in the contrapositive for rewrite rule purposes
  (implies (and (not (equal x y))
                (v-knownp x))
           (not (v-approx x y))))

;; We now consider approximation for states.  We demand that they have
;; the same type, in order that PAIRLIS$ acts the same "kind of way"
;; on each.  This appears to be important, or so I thought at one
;; time, in proving monotonicity in bizarre cases where we call
;; PAIRLIS$ on non-lists.

;; I want to be able to prove (s-approx x x), so that I can instantiate
;; lemmas roughly of the form
;; (implies (s-approx x y) (equal (foo x y) (bar x y)))
;; to obtain, say,
;; (equal (foo x x) (bar x x)).

(defun mem-width ()
  (declare (xargs :guard t))
  32)

(defun s-approx (s1 s2)
  (declare (xargs :guard t))
  (cond
   ;; the empty list (aes 31-Mar-92)
   ;; ((or (equal s1 nil) (equal s2 nil))
   ;;  (equal s1 s2))
   ((or (ramp s1) (ramp s2))
    (if (ramp s1)
        (if (ramp s2)
            (v-approx (ram-guts s1) (ram-guts s2))
          nil)
      nil))
   ((or (romp s1) (romp s2))
    (if (romp s1)
        (if (romp s2)
            (v-approx (rom-guts s1) (rom-guts s2))
          nil)
      nil))
   ((or (stubp s1) (stubp s2))
    (if (stubp s1)
        (if (stubp s2)
            (v-approx (stub-guts s1) (stub-guts s2))
          nil)
      nil))
   ((or (consp s1) (consp s2))
    (if (consp s1)
        (if (consp s2)
            (and (s-approx (car s1) (car s2))
                 (s-approx (cdr s1) (cdr s2)))
          nil)
      nil))
   ;; In the final case, we view s1 and s2 as values in four-valued logic,
   ;; where any "wrong" value is simply viewed as X
   (t (b-approx s1 s2))))

(defthm s-approx-x-x
  (s-approx x x))

(defthmd s-approx-car
  (implies (s-approx s1 s2)
           (s-approx (car s1) (car s2)))
  :hints (("Goal" :in-theory (enable mem-theory))))

(encapsulate
  ()

  (local
   (defthmd s-approx-cdr-aux-1
     (implies (and (4v-listp v1)
                   (4v-listp v2)
                   (v-approx v1 v2))
              (s-approx (list v1) (list v2)))
     :hints (("Goal"
              :in-theory (e/d (4vp mem-theory)
                              (bvp-is-true-listp
                               (:type-prescription bvp)
                               v-knownp
                               default-car
                               default-cdr))))))

  (local
   (defthm s-approx-cdr-aux-2
     (implies (and (memp mem1)
                   (memp mem2)
                   (v-approx (cadr mem1) (cadr mem2)))
              (s-approx (cdr mem1) (cdr mem2)))
     :hints (("Goal"
              :use (:instance s-approx-cdr-aux-1
                              (v1 (cadr mem1))
                              (v2 (cadr mem2)))
              :in-theory (e/d (list-rewrite-1
                               mem-theory)
                              (s-approx))))))

  (defthmd s-approx-cdr
    (implies (s-approx s1 s2)
             (s-approx (cdr s1) (cdr s2)))
    :hints (("Goal" :in-theory (enable rom-guts-of-romp
                                       ram-guts-of-ramp
                                       stub-guts-of-stubp)))))

(defun good-s (s)
  (declare (xargs :guard t))
  (cond
   ((ramp s)
    (equal (len (ram-guts s)) (mem-width)))
   ((romp s)
    (equal (len (rom-guts s)) (mem-width)))
   ((stubp s)
    (equal (len (stub-guts s)) (mem-width)))
   ((consp s)
    (and (good-s (car s))
         (good-s (cdr s))))
   (t t)))

(defthmd good-s-car
  (implies (good-s s)
           (good-s (car s)))
  :hints (("Goal" :in-theory (enable mem-theory))))

(encapsulate
  ()

  (local
   (defthmd good-s-cdr-aux-1
     (implies (4v-listp v)
              (good-s (list v)))
     :hints (("Goal"
              :in-theory (e/d (4vp mem-theory)
                              (bvp-is-true-listp
                               default-car
                               default-cdr))))))

  (local
   (defthm good-s-cdr-aux-2
     (implies (memp mem)
              (good-s (cdr mem)))
     :hints (("Goal"
              :use (:instance good-s-cdr-aux-1
                              (v (cadr mem)))
              :in-theory (e/d (list-rewrite-1
                               mem-theory)
                              (good-s))))))

  (defthmd good-s-cdr
    (implies (good-s s)
             (good-s (cdr s)))))

(defun s-knownp (s)
  (declare (xargs :guard t))
  (cond
   ;; the empty list (aes 31-Mar-92)
   ;; ((equal s nil)
   ;;  T)
   ((ramp s)
    (v-knownp (ram-guts s)))
   ((romp s)
    (v-knownp (rom-guts s)))
   ((stubp s)
    (v-knownp (stub-guts s)))
   ((consp s)
    (and (s-knownp (car s))
         (s-knownp (cdr s))))
   ;; In the final case, we view s as a value in four-valued logic,
   ;; where any "wrong" value is simply viewed as X.
   (t (b-knownp s))))

(defthm s-knownp-implies-s-approx-is-equal
  (implies (and (s-knownp x)
                (not (equal x y)))
           (not (s-approx x y)))
  :hints (("Goal"
           :in-theory (enable b-knownp mem-theory))))

(defun v-approx-alist (alist1 alist2)
  (declare (xargs :guard (and (alistp alist1)
                              (alistp alist2))))
  ;; Checks that both alists have the same "strip-cars", and that
  ;; v-approx holds of the strip-cdrs (if that were defined).
  (if (consp alist1)
      (and (consp alist2)
           (equal (caar alist1) (caar alist2))
           (b-approx (cdar alist1) (cdar alist2))
           (v-approx-alist (cdr alist1) (cdr alist2)))
    (atom alist2)))

(defun s-approx-alist (alist1 alist2)
  (declare (xargs :guard (and (alistp alist1)
                              (alistp alist2))))
  ;; Checks that both alists have the same "strip-cars", and that s-approx
  ;; holds of the strip-cdrs (if that were defined).  This is different from
  ;; v-approx-alist, in that the strip-cdrs is a list of states rather than a
  ;; single vector (i.e. rather than a list of bits).
  (if (consp alist1)
      (and (consp alist2)
           (equal (caar alist1) (caar alist2))
           (s-approx (cdar alist1) (cdar alist2))
           (s-approx-alist (cdr alist1) (cdr alist2)))
    (atom alist2)))

;; ======================================================================

;;;;;   notion of MONOTONICITY-PROPERTY for a module   ;;;;;

(defun monotonicity-property (flag fn netlist a1 a2 s1 s2)
  (case flag
    (0 (implies (and (v-approx a1 a2)
                     (s-approx s1 s2))
                (v-approx (se fn a1 s1 netlist)
                          (se fn a2 s2 netlist))))
    (1 (implies (and (v-approx-alist a1 a2)
                     (s-approx-alist s1 s2))
                (v-approx-alist (se-occ fn a1 s1 netlist)
                                (se-occ fn a2 s2 netlist))))
    (2 (implies (and (v-approx a1 a2)
                     (s-approx s1 s2))
                (s-approx (de fn a1 s1 netlist)
                          (de fn a2 s2 netlist))))
    (3 (implies (and (v-approx-alist a1 a2)
                     (s-approx-alist s1 s2))
                (s-approx-alist (de-occ fn a1 s1 netlist)
                                (de-occ fn a2 s2 netlist))))
    (otherwise t)))

;; Now we prove a bunch of trivial lemmas in order to help
;; us to control the proof later.

(defthm monotonicity-property-consequence-0
  (implies (and (monotonicity-property 0 fn netlist a1 a2 s1 s2)
                (v-approx a1 a2)
                (s-approx s1 s2))
           (v-approx (se fn a1 s1 netlist)
                     (se fn a2 s2 netlist))))

(defthm monotonicity-property-consequence-1
  (implies (and (monotonicity-property 1 fn netlist a1 a2 s1 s2)
                (v-approx-alist a1 a2)
                (s-approx-alist s1 s2))
           (v-approx-alist (se-occ fn a1 s1 netlist)
                           (se-occ fn a2 s2 netlist))))

(defthm monotonicity-property-consequence-2
  (implies (and (monotonicity-property 2 fn netlist a1 a2 s1 s2)
                (v-approx a1 a2)
                (s-approx s1 s2))
           (s-approx (de fn a1 s1 netlist)
                     (de fn a2 s2 netlist))))

(defthm monotonicity-property-consequence-3
  (implies (and (monotonicity-property 3 fn netlist a1 a2 s1 s2)
                (v-approx-alist a1 a2)
                (s-approx-alist s1 s2))
           (s-approx-alist (de-occ fn a1 s1 netlist)
                           (de-occ fn a2 s2 netlist))))

(defthmd monotonicity-property-opener-0
  ;; need iff below rather than equal in order for the proof to go through
  (iff (monotonicity-property 0 fn netlist a1 a2 s1 s2)
       (implies (and (v-approx a1 a2)
                     (s-approx s1 s2))
                (v-approx (se fn a1 s1 netlist)
                          (se fn a2 s2 netlist)))))

(defthmd monotonicity-property-opener-1
  ;; need iff below rather than equal in order for the proof to go through
  (iff (monotonicity-property 1 fn netlist a1 a2 s1 s2)
       (implies (and (v-approx-alist a1 a2)
                     (s-approx-alist s1 s2))
                (v-approx-alist (se-occ fn a1 s1 netlist)
                                (se-occ fn a2 s2 netlist)))))

(defthmd monotonicity-property-opener-2
  ;; need iff below rather than equal in order for the proof to go through
  (iff (monotonicity-property 2 fn netlist a1 a2 s1 s2)
       (implies (and (v-approx a1 a2)
                     (s-approx s1 s2))
                (s-approx (de fn a1 s1 netlist)
                          (de fn a2 s2 netlist)))))

(defthmd monotonicity-property-opener-3
  ;; need iff below rather than equal in order for the proof to go through
  (iff (monotonicity-property 3 fn netlist a1 a2 s1 s2)
       (implies (and (v-approx-alist a1 a2)
                     (s-approx-alist s1 s2))
                (s-approx-alist (de-occ fn a1 s1 netlist)
                                (de-occ fn a2 s2 netlist)))))

(in-theory (disable monotonicity-property))

;; ======================================================================

;;;;;    MONOTONICITY LEMMAS FOR BOOLEAN FUNCTIONS     ;;;;;

;; See the file monotonicity-macros.lisp for the definition
;; and a sample expansion of the macro MONOTONICITY-LEMMAS.
;; The idea is to show that basic boolean functions are monotone
;; with respect to the partial order defined by B-APPROX, i.e.
;; (roughly stated) that changing an input from (X) can only
;; change the output if it was formerly (X).

(in-theory (enable f-gates 3vp b-knownp))

(monotonicity-lemmas
 (f-buf f-and) (1 2))

(monotonicity-lemmas
 (f-and3 f-and4) (3 4)
 (("Goal" :in-theory (disable f-and b-approx))))

(monotonicity-lemmas (f-not) (1))

(monotonicity-lemmas
 (f-nand f-nand3 f-nand4 f-nand5 f-nand6 f-nand8)
 (2 3 4 5 6 8)
 (("Goal" :in-theory (disable f-and f-not b-approx))))

(monotonicity-lemmas (f-or) (2))

(monotonicity-lemmas
 (f-or3 f-or4 f-nor f-nor3 f-nor4 f-nor5 f-nor6 f-nor8)
 (3 4 2 3 4 5 6 8)
 (("Goal" :in-theory (disable f-or f-not b-approx))))

(monotonicity-lemmas (f-xor f-equv) (2 2))

(monotonicity-lemmas
 (f-xor3 f-equv3) (3 3)
 (("Goal" :in-theory (disable f-xor f-equv b-approx))))

(monotonicity-lemmas (f-if ft-buf ft-wire f-pullup) (3 2 2 1))

(in-theory (disable f-gates 3vp b-knownp))

;; Do not remove the following -- although MONOTONICITY-LEMMAS does
;; not occur explicitly below, it does get used by the macro
;; PROVE-PRIMITIVE-MONOTONICITY.
(deftheory monotonicity-lemmas-theory
  '(f-buf-monotone f-and-monotone f-and3-monotone f-and4-monotone
                   f-not-monotone
                   f-nand-monotone f-nand3-monotone
                   f-nand4-monotone f-nand5-monotone f-nand6-monotone
                   f-nand8-monotone f-or-monotone f-or3-monotone f-or4-monotone
                   f-nor-monotone f-nor3-monotone f-nor4-monotone
                   f-nor5-monotone f-nor6-monotone f-nor8-monotone
                   f-xor-monotone f-xor3-monotone f-equv-monotone f-equv3-monotone
                   f-if-monotone ft-buf-monotone ft-wire-monotone f-pullup-monotone))

(in-theory (disable b-approx))

;; ======================================================================

;;;;;             MONOTONICITY LEMMAS FOR              ;;;;;
;;;;;          PRIMITIVE HARDWARE COMPONENTS           ;;;;;
;;;;;                except the RAM                    ;;;;;

;; Next, let's prove that some primitive hardware components are
;; monotone, in the sense that when an input or "leaf" of the state is
;; changed from (X), they change their values or states only by
;; "filling in" for (X)s.

;; First, a couple of lemmas.

(defthm s-approx-implies-b-approx
  ;; geez, total functions are something
  (implies (s-approx x y)
           (b-approx x y))
  :hints (("Goal" :in-theory (enable b-approx b-knownp))))

(defthm 3vp-f-buf
  (3vp (f-buf x))
  :hints (("Goal" :in-theory (enable f-buf))))

(defthm 4vp-f-buf
  (4vp (f-buf x))
  :hints (("Goal" :in-theory (enable f-buf 3vp))))

(defthm 4vp-f-if
  (4vp (f-if x y z))
  :hints (("Goal" :in-theory (enable f-if 3vp))))

(defthm 4vp-implies-s-approx-is-b-approx
  (implies (and (4vp x)
                (4vp y)
                (b-approx x y))
           (equal (s-approx x y)
                  t))
  :hints (("Goal" :in-theory (enable 4vp))))

;;;   >(mapcar 'car common-lisp-primp-database)
;;;   (AO2 AO4 AO6 AO7 B-AND B-AND3 B-AND4 B-EQUV B-EQUV3 B-IF B-NAND
;;;                ; B1I deleted from primp-database (aes)
;;;        B-NAND3 B-NAND4 B-NAND5 B-NAND6 B-NAND8 B-NBUF B-NOR B-NOR3 B-NOR4
;;;        B-NOR5 B-NOR6 B-NOR8 B-NOT B-NOT-B4IP B-NOT-IVAP B-OR B-OR3 B-OR4
;;;        B-XOR B-XOR3 DEL2 DEL4 DEL10 PROCMON DP-RAM-16X32 FD1 FD1S FD1SP
;;;        FD1SLP ID LS-NAND3 LS-BUF10 MEM-32X32 T-BUF T-WIRE PULLUP
;;;        TTL-BIDIRECT TTL-CLK-INPUT TTL-INPUT TTL-OUTPUT
;;;        TTL-OUTPUT-PARAMETRIC TTL-OUTPUT-FAST TTL-TRI-OUTPUT
;;;        TTL-TRI-OUTPUT-FAST VDD VDD-PARAMETRIC VSS)
;;;
;;;   >

(local
 (defthm v-approx=>b-approx
   (implies (v-approx x y)
            (b-approx (car x) (car y)))))

(in-theory (enable s-approx-car))

;; B1I was deleted from the following because it is no longer in the
;; primp-database. (aes)
(prove-primitive-monotonicity
 (AO2 AO6 B-AND B-AND3 B-AND4 B-BUF B-EQUV B-EQUV3 B-IF B-NAND
      B-NAND3 B-NAND4 B-NAND5 B-NAND6 B-NAND8 B-NBUF B-NOR B-NOR3 B-NOR4
      B-NOR5 B-NOR6 B-NOR8 B-NOT B-NOT-B4IP B-OR B-OR3 B-OR4
      B-XOR DEL4 PROCMON

      FD1 FD1S
      FD1SLP ID
      ;; @@## LS-NAND3 LS-BUF10

      RAM-ENABLE-CIRCUIT T-BUF T-WIRE PULLUP
      TTL-BIDIRECT TTL-CLK-INPUT TTL-INPUT TTL-OUTPUT
      TTL-OUTPUT-PARAMETRIC TTL-OUTPUT-FAST TTL-TRI-OUTPUT
      TTL-TRI-OUTPUT-FAST VDD VDD-PARAMETRIC VSS))

; Notice that we do NOT have above:
; (prove-primitive-monotonicity (DP-RAM-16X32))
; (prove-primitive-monotonicity mem-32x32)

(in-theory (disable s-approx-car))


;; B1I-monotone was deleted from the following because B1I is no longer
;; in the primp-database. (aes)
(deftheory primitives-monotone
  '(AO2-monotone
    AO6-monotone B-AND-monotone
    B-AND3-monotone B-AND4-monotone B-BUF-monotone
    B-EQUV-monotone B-EQUV3-monotone
    B-IF-monotone B-NAND-monotone
    B-NAND3-monotone B-NAND4-monotone B-NAND5-monotone
    B-NAND6-monotone B-NAND8-monotone B-NBUF-monotone B-NOR-monotone
    B-NOR3-monotone B-NOR4-monotone
    B-NOR5-monotone B-NOR6-monotone B-NOR8-monotone B-NOT-monotone
    B-NOT-B4IP-monotone B-OR-monotone
    B-OR3-monotone B-OR4-monotone
    B-XOR-monotone
    DEL4-monotone PROCMON-monotone
    FD1-monotone FD1S-monotone
    FD1SLP-monotone ID-monotone
;;; @@##  LS-NAND3-monotone LS-BUF10-monotone
    RAM-ENABLE-CIRCUIT-monotone
    T-BUF-monotone T-WIRE-monotone PULLUP-monotone
    TTL-BIDIRECT-monotone TTL-CLK-INPUT-monotone
    TTL-INPUT-monotone TTL-OUTPUT-monotone
    TTL-OUTPUT-PARAMETRIC-monotone TTL-OUTPUT-FAST-monotone
    TTL-TRI-OUTPUT-monotone
    TTL-TRI-OUTPUT-FAST-monotone VDD-monotone
    VDD-PARAMETRIC-monotone VSS-monotone))

;; ======================================================================

;;;;;         MONOTONICITY LEMMA for the RAM           ;;;;;

;; This part of the proof seemed to take close to a couple of weeks!
;; All the rest put together was only about 3 days.  The goal is
;; to prove the equivalent of (prove-primitive-monotonicity (DP-RAM-16X32)).

(defthm v-approx-bvp
  (implies (bvp x)
           (equal (v-approx x y)
                  (equal x y)))
  :hints (("Goal" :in-theory (enable bvp b-knownp b-approx))))

(defun read-mem1-monotone-induction (v-addr mem1 mem2)
  (cond
   ((or (stubp mem1) (stubp mem2) (atom v-addr)
        (atom mem1) (atom mem2))
    t)
   ((car v-addr)
    (read-mem1-monotone-induction (cdr v-addr) (cdr mem1) (cdr mem2)))
   (t (read-mem1-monotone-induction (cdr v-addr) (car mem1) (car mem2)))))

(local
 (defthm read-mem1-of-car-memp
   (implies (memp mem)
            (not (read-mem1 v-addr (car mem))))
   :hints (("Goal" :in-theory (enable read-mem1 mem-theory)))))

(defthm read-mem1-monotone
  (implies (and (bvp v-addr)
                (s-approx mem1 mem2))
           (v-approx (read-mem1 v-addr mem1)
                     (read-mem1 v-addr mem2)))
  :hints (("Goal"
           :induct (read-mem1-monotone-induction v-addr mem1 mem2)
           :in-theory (enable bvp read-mem1 s-approx-car s-approx-cdr))))

(defthm bvp-implies-v-knownp
  (implies (bvp x)
           (v-knownp x))
  :hints (("Goal"
           :in-theory (enable bvp b-knownp))))

(defthm v-approx-implies-b-approx-nth
  (implies (and (equal (nth n x) c)
                (not (equal (nth n y) c))
                (b-knownp c))
           (not (v-approx x y)))
  :hints (("Goal"
           :in-theory (enable b-approx b-knownp))))

(defthm v-approx-implies-take-equal
  (implies (and (v-approx x y)
                (bvp (take n x)))
           (equal (take n x)
                  (take n y)))
  :hints (("Goal"
           :in-theory (enable bvp b-approx b-knownp))))

(defthm v-approx-nthcdr
  (implies (v-approx x y)
           (v-approx (nthcdr n x)
                     (nthcdr n y)))
  :hints (("Goal"
           :in-theory (enable b-approx b-knownp))))

(defthm v-approx-implies-subseq-list-equal
  (implies (and (v-approx x y)
                (bvp (subseq-list x i j)))
           (equal (subseq-list x i j)
                  (subseq-list y i j)))
  :hints (("Goal"
           :use (:instance v-approx-implies-take-equal
                           (n (- j i))
                           (x (nthcdr i x))
                           (y (nthcdr i y))))))

(defthm v-approx-bvp-subseq-list
  (implies (and (v-approx x y)
                (bvp (subseq-list x i j)))
           (bvp (subseq-list y i j)))
  :hints (("Goal"
           :use v-approx-implies-subseq-list-equal
           :in-theory (disable v-approx subseq-list
                               v-approx-implies-subseq-list-equal)))
  :rule-classes (:rewrite :type-prescription))

(defthm v-approx-make-list-x
  (implies (and (equal (len y) bits)
                (true-listp y))
           (v-approx (make-list bits :initial-element *x*)
                     y))
  :hints (("Goal" :in-theory (enable b-approx b-knownp))))

(defthm read-mem-monotone
  (implies (and (bvp v-addr)
                (s-approx mem1 mem2))
           (v-approx (read-mem v-addr mem1)
                     (read-mem v-addr mem2)))
  :hints (("Goal" :in-theory (enable read-mem))))

(defthm len-of-v-approx
  (implies (v-approx v1 v2)
           (equal (len v1) (len v2))))

(defthm equal-len-read-mem1
  (implies (s-approx s1 s2)
           (equal (equal (len (read-mem1 a s2))
                         (len (read-mem1 a s1)))
                  t))
  :hints (("Goal" :in-theory (enable read-mem1 s-approx-cdr))))

(defthm equal-len-read-mem
  (implies (s-approx s1 s2)
           (equal (equal (len (read-mem a s2))
                         (len (read-mem a s1)))
                  t))
  :hints (("Goal" :in-theory (enable read-mem))))

(defthm true-listp-of-v-approx
  (implies (v-approx v1 v2)
           (iff (true-listp v1)
                (true-listp v2))))

(defthm s-approx-implies-true-listp-read-mem1
  (implies (and (s-approx s1 s2)
                (true-listp (read-mem1 a s1)))
           (true-listp (read-mem1 a s2)))
  :hints (("Goal" :in-theory (enable read-mem1 s-approx-cdr)))
  :rule-classes :type-prescription)

(defthm s-approx-implies-true-listp-read-mem
  (implies (and (s-approx s1 s2)
                (true-listp (read-mem a s1)))
           (true-listp (read-mem a s2)))
  :hints (("Goal" :in-theory (enable read-mem)))
  :rule-classes :type-prescription)

(defthm dual-port-ram-value-monotone
  (implies (and (s-approx s1 s2)
                (v-approx a1 a2))
           (v-approx (dual-port-ram-value bits address-lines a1 s1)
                     (dual-port-ram-value bits address-lines a2 s2)))
  :hints (("Goal" :in-theory (disable subseq-list
                                      make-list-ac-removal))))

(defun dual-port-ram-value-body (bits a-address b-address wen st)
  (declare (xargs :guard (natp bits)))
  (if (or (not (bvp a-address))
          (and (not (equal wen t))
               (or (not (bvp b-address))
                   (equal a-address b-address))))
      (make-list bits :initial-element *x*)
    (let ((val (read-mem a-address st)))
      (if (and (true-listp val)
               (equal (len val) bits))
          val
        (make-list bits :initial-element *x*)))))

(defthm dual-port-ram-value-is-dual-port-ram-value-body
  (let ((a-address (subseq-list args 0 address-lines))
        (b-address (subseq-list args address-lines (* 2 address-lines)))
        (wen (nth (* 2 address-lines) args)))
    (equal (dual-port-ram-value bits address-lines args st)
           (dual-port-ram-value-body bits a-address b-address wen st))))

(defthm se-primp-apply-dp-ram-16x32
  (equal (se-primp-apply 'dp-ram-16x32 a s)
         (dual-port-ram-value 32 4 a (car s)))
  :hints (("Goal"
           :in-theory (e/d (se-rules
                            open-nth open-take
                            car-nthcdr cdr-nthcdr)
                           (dual-port-ram-value
                            true-listp
                            nth nthcdr
                            nthcdr-of-len-l
                            bvp-is-true-listp)))))

(defthm dp-ram-16x32-monotone-value
  (monotonicity-property 0 'dp-ram-16x32 netlist a1 a2 s1 s2)
  :hints (("Goal"
           :in-theory (e/d (se-rules
                            monotonicity-property-opener-0
                            s-approx-car)
                           (dual-port-ram-value
                            dual-port-ram-value-is-dual-port-ram-value-body)))))

;; This concludes the ``value'' half of the RAM's monotonicity lemma.
;; We move on to the ``state'' half.

(in-theory (disable v-knownp v-approx
                    s-knownp
                    s-knownp-implies-s-approx-is-equal
                    4vp-implies-s-approx-is-b-approx))

(defthm s-approx-opener
  (and ;; add case for empty list (aes 31-Mar-92)
       ;; (implies (or (equal s1 nil) (equal s2 nil))
       ;;          (equal (s-approx s1 s2)
       ;;                 (equal s1 s2)))
       (implies (or (ramp s1) (ramp s2))
                (equal (s-approx s1 s2)
                       (if (ramp s1)
                           (if (ramp s2)
                               (v-approx (ram-guts s1) (ram-guts s2))
                             nil)
                         nil)))
       (implies (or (romp s1) (romp s2))
                (equal (s-approx s1 s2)
                       (if (romp s1)
                           (if (romp s2)
                               (v-approx (rom-guts s1) (rom-guts s2))
                             nil)
                         nil)))
       (implies (or (stubp s1) (stubp s2))
                (equal (s-approx s1 s2)
                       (if (stubp s1)
                           (if (stubp s2)
                               (v-approx (stub-guts s1) (stub-guts s2))
                             nil)
                         nil)))
       (implies (and (or (consp s1) (consp s2))
                     (not (or (ramp s1) (ramp s2)
                              (romp s1) (romp s2)
                              (stubp s1) (stubp s2))))
                (equal (s-approx s1 s2)
                       (if (consp s1)
                           (if (consp s2)
                               (and (s-approx (car s1) (car s2))
                                    (s-approx (cdr s1) (cdr s2)))
                             nil)
                         nil)))
       (implies (not (or ;; add case for empty list (aes 31-Mar-92)
                         ;; (equal s1 nil) (equal s2 nil)
                         (ramp s1) (ramp s2)
                         (romp s1) (romp s2)
                         (stubp s1) (stubp s2)
                         (consp s1) (consp s2)))
                ;; In the final case, we view s1 and s2 as values in
                ;; four-valued logic, where any "wrong" value is simply viewed
                ;; as (X).
                (equal (s-approx s1 s2)
                       (b-approx s1 s2)))))

(in-theory (disable s-approx mem-width (mem-width)))

(defthm v-approx-implies-nth-does-not-go-from-nil-to-t
  (implies (and (not (nth n a1))
                (nth n a2))
           (not (v-approx a1 a2)))
  :hints (("Goal" :in-theory (enable v-approx b-approx))))

(defthm write-mem1-opener
  (and (implies (stubp mem)
                (equal (write-mem1 v-addr mem value) mem))
       (implies (atom v-addr)
                (equal (write-mem1 v-addr mem value)
                       (if (ramp mem) (ram value) mem)))
       (implies (and (consp v-addr) (atom mem))
                (equal (write-mem1 v-addr mem value)
                       mem))
       (implies (and (not (stubp mem)) (consp mem)
                     (consp v-addr) (car v-addr))
                (equal (write-mem1 v-addr mem value)
                       (cons (car mem)
                             (write-mem1 (cdr v-addr)
                                         (cdr mem)
                                         value))))
       (implies (and (not (stubp mem)) (consp mem)
                     (consp v-addr) (not (car v-addr)))
                (equal (write-mem1 v-addr mem value)
                       (cons (write-mem1 (cdr v-addr)
                                         (car mem)
                                         value)
                             (cdr mem)))))
  :hints (("Goal" :in-theory (enable write-mem1))))

(encapsulate
  ()

  (local
   (defthmd write-mem1-list-4v-listp
     (implies (4v-listp v)
              (equal (write-mem1 v-addr (list v) value)
                     (list v)))
     :hints (("Goal"
              :induct (write-mem1 v-addr (list v) value)
              :in-theory (enable write-mem1 4vp mem-theory)))))

  (defthm write-mem1-cdr-of-memp
    (implies (memp mem)
             (equal (write-mem1 v-addr (cdr mem) value)
                    (cdr mem)))
    :hints (("Goal"
             :use (:instance write-mem1-list-4v-listp
                             (v (cadr mem)))
             :in-theory (enable list-rewrite-1 mem-theory)))))

(defthm v-approx-of-v-fourfix
  (implies (v-approx v1 v2)
           (v-approx (v-fourfix v1) (v-fourfix v2)))
  :hints (("Goal" :in-theory (enable v-approx b-approx v-fourfix))))

(defthm s-approx-of-ram-v-approx
  (implies (v-approx data1 data2)
           (s-approx (ram data1) (ram data2)))
  :hints (("Goal" :in-theory (enable mem-theory))))

(defthm write-mem1-monotone
  (implies (and (s-approx mem1 mem2)
                (v-approx data1 data2))
           (s-approx (write-mem1 v-addr mem1 data1)
                     (write-mem1 v-addr mem2 data2)))
  :hints (("Goal"
           :in-theory (enable write-mem1 s-approx
                              rom-guts-of-romp
                              ram-guts-of-ramp
                              stub-guts-of-stubp))))

(defthm write-mem-monotone
  (implies (and (s-approx mem1 mem2)
                (v-approx data1 data2))
           (s-approx (write-mem v-addr mem1 data1)
                     (write-mem v-addr mem2 data2)))
  :hints (("Goal" :in-theory (enable write-mem))))

(defthm v-approx-len
  (implies (v-approx v1 v2)
           (not (< (len v1) (len v2))))
  :hints (("Goal" :in-theory (enable v-approx))))

(local
 (defthm cadr-ram
   (equal (cadr (ram x))
          (v-fourfix x))
   :hints (("Goal" :in-theory (enable ram)))))

(local
 (defthm true-listp-cadr-of-ramp
   (implies (ramp x)
            (true-listp (cadr x)))
   :hints (("Goal"
            :in-theory (enable ram-guts-of-ramp)
            :use true-listp-ram-guts-of-ramp))
   :rule-classes :type-prescription))

(defthm s-approx-write-mem1-id
  (implies (and (s-approx s1 s2)
                ;;(good-s s1)
                (good-s s2)
                )
           (s-approx (write-mem1 v-addr
                                 s1
                                 (make-list (mem-width)
                                            :initial-element *x*))
                     s2))
  :hints (("Goal"
           :in-theory (e/d (write-mem1 s-approx
                                       rom-guts-of-romp
                                       ram-guts-of-ramp
                                       stub-guts-of-stubp)
                           (make-list-ac-removal)))))

(defthm s-approx-write-mem-id
  (implies (and (good-s s2)
                (s-approx s1 s2))
           (s-approx (write-mem v-addr
                                s1
                                (make-list (mem-width)
                                           :initial-element *x*))
                     s2))
  :hints (("Goal"
           :in-theory (e/d (write-mem)
                           (make-list-ac-removal)))))

(local
 (defthm romp-constant-ram-instance
   (implies (consp mem)
            (equal (romp (cons (constant-ram (car mem) value)
                               (constant-ram (cdr mem) value)))
                   (romp mem)))
   :hints (("Goal"
            :in-theory (e/d (constant-ram mem-theory)
                            (romp-constant-ram))
            :use romp-constant-ram))))

(local
 (defthm ramp-constant-ram-instance
   (implies (consp mem)
            (equal (ramp (cons (constant-ram (car mem) value)
                               (constant-ram (cdr mem) value)))
                   (ramp mem)))
   :hints (("Goal"
            :in-theory (e/d (constant-ram mem-theory)
                            (ramp-constant-ram))
            :use ramp-constant-ram))))

(local
 (defthm stubp-constant-ram-instance
   (implies (consp mem)
            (equal (stubp (cons (constant-ram (car mem) value)
                                (constant-ram (cdr mem) value)))
                   (stubp mem)))
   :hints (("Goal"
            :in-theory (e/d (constant-ram mem-theory)
                            (stubp-constant-ram))
            :use stubp-constant-ram))))

(local
 (defthm constant-ram-of-4v-listp
   (implies (4v-listp mem)
            (equal (constant-ram mem value)
                   mem))
   :hints (("Goal" :in-theory (enable constant-ram 4vp mem-theory)))))

(local
 (defthm s-approx-constant-ram-x-id-aux
   (implies (or (romp mem) (stubp mem))
            (equal (constant-ram mem value)
                   mem))
   :hints (("Goal" :in-theory (enable constant-ram mem-theory)))))

(defthm s-approx-constant-ram-x-id
  (implies (and (good-s s2)
                (s-approx s1 s2))
           (s-approx (constant-ram s1
                                   (make-list (mem-width)
                                              :initial-element *x*))
                     s2))
  :hints (("Goal"
           :induct (s-approx s1 s2)
           :in-theory (e/d (constant-ram s-approx)
                           (make-list-ac-removal)))))

(defthm s-approx-constant-ram-x-constant-ram-x
  (implies (s-approx s1 s2)
           (s-approx (constant-ram s1
                                   (make-list (mem-width)
                                              :initial-element *x*))
                     (constant-ram s2
                                   (make-list (mem-width)
                                              :initial-element *x*))))
  :hints (("Goal"
           :induct (s-approx s1 s2)
           :in-theory (e/d (constant-ram s-approx)
                           (make-list-ac-removal)))))

(defthm v-approx-preserves-len
  (implies (v-approx a1 a2)
           (equal (len a1) (len a2)))
  :hints (("Goal" :in-theory (enable v-approx))))

(defthm v-approx-take
  (implies (v-approx x y)
           (v-approx (take n x)
                     (take n y)))
  :hints (("Goal" :in-theory (enable v-approx))))

(defthm v-approx-subseq-list
  (implies (v-approx a1 a2)
           (v-approx (subseq-list a1 i j)
                     (subseq-list a2 i j))))

(defthm mem-width-non-zero
  (not (equal (mem-width) 0)))

(defthm s-approx-constant-ram-x-write-mem1
  (implies (and (s-approx s1 s2)
                (true-listp v)
                (equal (len v) (mem-width))
                (good-s s2))
           (s-approx (constant-ram s1
                                   (make-list (mem-width)
                                              :initial-element *x*))
                     (write-mem1 v-addr s2 v)))
  :hints (("Goal"
           :in-theory (e/d (constant-ram write-mem1 s-approx
                                         rom-guts-of-romp
                                         ram-guts-of-ramp
                                         stub-guts-of-stubp)
                           (make-list-ac-removal)))))

(defthm s-approx-constant-ram-x-write-mem
  (implies (and (s-approx s1 s2)
                (true-listp v)
                (equal (len v) (mem-width))
                (good-s s2))
           (s-approx (constant-ram s1
                                   (make-list (mem-width)
                                              :initial-element *x*))
                     (write-mem v-addr s2 v)))
  :hints (("Goal"
           :in-theory (e/d (write-mem)
                           (make-list-ac-removal)))))

(defthm v-approx-preserves-true-listp
  (implies (not (iff (true-listp v1) (true-listp v2)))
           (not (v-approx v1 v2)))
  :hints (("Goal" :in-theory (enable v-approx))))

;; Here's something silly, needed because mem-width is disabled below.
(defthm mem-width-linear-facts
  (and (< 31 (mem-width))
       (< (mem-width) 33))
  :hints (("Goal" :in-theory (enable mem-width)))
  :rule-classes :linear)

;; A main goal!

(defthm dual-port-ram-state-monotone
  (implies
   (and (s-approx s1 s2)
        (good-s s2)
        (v-approx a1 a2))
   (s-approx (dual-port-ram-state (mem-width) 4 a1 s1)
             (dual-port-ram-state (mem-width) 4 a2 s2)))
  :hints (("Goal"
           :in-theory (disable subseq-list make-list-ac-removal))))

(defthm dual-port-ram-state-monotone-rewrite
  (implies
   (and (s-approx s1 s2)
        (good-s s2)
        (v-approx a1 a2))
   (s-approx (dual-port-ram-state 32 4 a1 s1)
             (dual-port-ram-state 32 4 a2 s2)))
  :hints (("Goal"
           :use dual-port-ram-state-monotone
           :in-theory (enable mem-width))))

(defun dual-port-ram-state-body (bits b-address wen data st)
  (declare (xargs :guard (natp bits)))
  (if (equal wen t)
      st
    ;;  There is a potential write.  If the address is unknown, wipe out the
    ;;  state.
    (if (not (bvp b-address))
        ;; omitting the things about the length and properness of args here
        (constant-ram st (make-list bits :initial-element *x*))
      ;;  If WEN is solidly low, update the state with data, otherwise X out
      ;;  the addressed entry.
      (if (equal wen nil)
          (write-mem b-address st data)
        (write-mem b-address st (make-list bits :initial-element *x*))))))

(defthm dual-port-ram-state-is-dual-port-ram-state-body
  (let ((b-address (subseq-list args address-lines (* 2 address-lines)))
        (wen (nth (* 2 address-lines) args))
        (data (subseq-list args
                           (1+ (* 2 address-lines))
                           (+ 1 (* 2 address-lines) bits))))
    (equal (dual-port-ram-state bits address-lines args st)
           (dual-port-ram-state-body bits b-address wen data st))))

(defthm de-primp-apply-dp-ram-16x32
  (equal (de-primp-apply 'dp-ram-16x32 a s)
         (list (dual-port-ram-state 32 4 a (car s))))
  :hints (("Goal"
           :in-theory (e/d (de-rules
                            open-take
                            car-nthcdr cdr-nthcdr)
                           (dual-port-ram-state
                            true-listp
                            nth nthcdr
                            nthcdr-of-len-l
                            take-of-too-many
                            bvp-is-true-listp)))))

(defthmd s-approx-of-list
  (implies (s-approx s1 s2)
           (s-approx (list s1) (list s2)))
  :hints (("Goal" :in-theory (enable s-approx mem-theory))))

;;; Here's the state half of the RAM's monotonicity
(defthm dp-ram-16x32-monotone-state
  (implies (good-s s2)
           (monotonicity-property 2 'dp-ram-16x32 netlist a1 a2 s1 s2))
  :hints (("Goal"
           :in-theory
           (e/d (de-rules
                 monotonicity-property-opener-2
                 good-s-car
                 s-approx-car
                 s-approx-of-list)
                (dual-port-ram-state
                 dual-port-ram-state-is-dual-port-ram-state-body)))))

(defthm dp-ram-16x32-monotone
  (and
   (monotonicity-property 0 'dp-ram-16x32 netlist a1 a2 s1 s2)
   (implies (good-s s2)
            (monotonicity-property 2 'dp-ram-16x32 netlist a1 a2 s1 s2))))

;; ======================================================================

;;;;;         MONOTONICITY FOR ALL PRIMITIVES          ;;;;;

;; Here we recognize circuits that do not contain mem-32x32 (or
;; whatever EXCEPTIONS may be -- i.e. we'll apply it to '(mem-32x32)),
;; with the recognizer OK-NETLISTP.  Then we prove monotonicity for
;; all primitives except mem-32x32, which will be important in the
;; base step of our proof of monotonicty for all cases satisfying
;; OK-NETLISTP in the next section "MONOTONICITY OF DE".

(defun ok-netlistp (flag fn netlist exceptions)
  (declare (xargs :measure (se-measure fn netlist)))
  ;; Here exceptions is a list of "bad" primitive names
  ;; that we are not allowed to use.  The flag is like
  ;; in dual-eval: if 0 or 2, then fn is a single module name, else
  ;; fn is a list of module occurrences.  Actually 0 and 2 behave the
  ;; same, as do 1 and 3 (see OK-NETLISTP-REDUCTION-REWRITE somewhat
  ;; below), but it seemed that the proofs were more likely to go
  ;; through easily if I used the same recursion structure here as is
  ;; used for dual-eval.
  (case flag
        (0 (if (primp fn)
               (not (member fn exceptions))
             (let ((module (assoc fn netlist)))
               (if (consp module)
                   (ok-netlistp 1
                                (md-occs module)
                                (delete-to-eq fn netlist)
                                exceptions)
                 nil))))
        (1 (let ((body fn))
             (if (consp body)
                 (let ((occurrence (car body)))
                   (let ((fn (occ-fn occurrence)))
                     (and (ok-netlistp 0 fn netlist exceptions)
                          (ok-netlistp 1 (cdr body) netlist exceptions))))
               t)))
        (2 (if (primp fn)
               (not (member fn exceptions))
             (let ((module (assoc fn netlist)))
               (if (consp module)
                   (ok-netlistp 3
                                (md-occs module)
                                (delete-to-eq fn netlist)
                                exceptions)
                 nil))))
        (3 (let ((body fn))
             (if (consp body)
                 (let ((occurrence (car body)))
                   (let ((fn (occ-fn occurrence)))
                     (and (ok-netlistp 2 fn netlist exceptions)
                          (ok-netlistp 3 (cdr body) netlist exceptions))))
               t)))
        (otherwise nil)))

(defthm primp-monotone
  (implies
   (and (primp fn)
        (or (equal flag 0)
            (and (equal flag 2)
                 (implies (equal fn 'dp-ram-16x32)
                          (good-s s2))))
        (not (equal fn 'mem-32x32)))
   (monotonicity-property flag fn netlist a1 a2 s1 s2))
  :hints (("Goal" :in-theory (enable primp))))

;; ======================================================================

;;;;;            MONOTONICITY OF DE             ;;;;;

(defun de-monotone-induction (flag fn netlist a1 a2 s1 s2)
  (declare (xargs :measure (se-measure fn netlist)))
  (case flag
    (0 (if (primp fn)
           t
         (let ((module (assoc fn netlist)))
           (if (consp module)
               (let ((inputs  (md-ins module))
                     ;;(outputs (md-outs module))
                     (occurrences (md-occs module))
                     (statenames (md-sts module)))
                 (de-monotone-induction
                  1
                  occurrences
                  (delete-to-eq fn netlist)
                  (pairlis$ inputs a1)
                  (pairlis$ inputs a2)
                  (pairlis$ statenames s1)
                  (pairlis$ statenames s2)))
             t))))
    (1 (let ((body fn)
             (occurrence (car fn)))
         (if (consp body)
             (let ((occ-name (occ-name occurrence))
                   (outputs (occ-outs occurrence))
                   (fn (occ-fn occurrence))
                   (inputs (occ-ins occurrence)))
               (and
                (de-monotone-induction 0
                                       fn
                                       netlist
                                       (assoc-eq-values inputs a1)
                                       (assoc-eq-values inputs a2)
                                       (assoc-eq-value occ-name s1)
                                       (assoc-eq-value occ-name s2))
                (de-monotone-induction
                 1
                 (cdr body)
                 netlist
                 (append
                  (pairlis$ outputs
                            (se
                             fn
                             (assoc-eq-values inputs a1)
                             (assoc-eq-value occ-name s1)
                             netlist))
                  a1)
                 (append
                  (pairlis$ outputs
                            (se
                             fn
                             (assoc-eq-values inputs a2)
                             (assoc-eq-value occ-name s2)
                             netlist))
                  a2)
                 s1 s2)))
           (list a1 a2))))
    (2 (if (primp fn)
           t
         (let ((module (assoc fn netlist)))
           (if (consp module)
               (let ((inputs  (md-ins module))
                     ;;(outputs (md-outs module))
                     (occurrences (md-occs module))
                     (statenames (md-sts module)))
                 (and ;; (de-monotone-induction
                      ;;  1
                      ;;  occurrences
                      ;;  (delete-to-eq fn netlist)
                      ;;  (pairlis$ inputs a1)
                      ;;  (pairlis$ inputs a2)
                      ;;  (pairlis$ statenames s1)
                      ;;  (pairlis$ statenames s2))
                      (de-monotone-induction
                       3
                       occurrences
                       (delete-to-eq fn netlist)
                       (se-occ
                        occurrences
                        (pairlis$ inputs a1)
                        (pairlis$ statenames s1)
                        (delete-to-eq fn netlist))
                       (se-occ
                        occurrences
                        (pairlis$ inputs a2)
                        (pairlis$ statenames s2)
                        (delete-to-eq fn netlist))
                       (pairlis$ statenames s1)
                       (pairlis$ statenames s2))))
             t))))
    (3 (let ((body fn))
         (if (consp body)
             (let ((occurrence (car body)))
               (let ((occ-name (occ-name occurrence))
                     ;;(outputs (occ-outs occurrence))
                     (fn (occ-fn occurrence))
                     (inputs (occ-ins occurrence)))
                 (and (de-monotone-induction
                       2
                       fn
                       netlist
                       (assoc-eq-values inputs a1)
                       (assoc-eq-values inputs a2)
                       (assoc-eq-value occ-name s1)
                       (assoc-eq-value occ-name s2))
                      (de-monotone-induction
                       3
                       (cdr body)
                       netlist
                       a1 a2
                       (update-alist occ-name
                                     (de fn
                                         (assoc-eq-values inputs a1)
                                         (assoc-eq-value occ-name s1)
                                         netlist)
                                     s1)
                       (update-alist occ-name
                                     (de fn
                                         (assoc-eq-values inputs a2)
                                         (assoc-eq-value occ-name s2)
                                         netlist)
                                     s2)))))
           (list s1 s2))))
    (otherwise t)))

(defthm v-approx-alist-implies-b-approx-assoc-eq-value
  (implies (v-approx-alist alist1 alist2)
           (b-approx (assoc-eq-value x alist1)
                     (assoc-eq-value x alist2)))
  :hints (("Goal" :in-theory (enable assoc-eq-value))))

(defthm v-approx-alist-implies-v-approx-assoc-eq-values
  (implies (v-approx-alist alist1 alist2)
           (v-approx (assoc-eq-values x alist1)
                     (assoc-eq-values x alist2)))
  :hints (("Goal" :in-theory (enable assoc-eq-values v-approx))))

(defun s-approx-list (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (s-approx (car x) (car y))
           (s-approx-list (cdr x) (cdr y)))
    (atom y)))

(defthm s-approx-list-implies-s-approx-alist
  (implies (s-approx-list s1 s2)
           (s-approx-alist (pairlis$ x s1)
                           (pairlis$ x s2))))

(defthm v-approx-implies-v-approx-alist
  (implies (v-approx v1 v2)
           (v-approx-alist (pairlis$ x v1)
                           (pairlis$ x v2)))
  :hints (("Goal" :in-theory (enable v-approx))))

(defthm s-approx-alist-implies-s-approx-assoc-eq-value
  (implies (s-approx-alist s1 s2)
           (s-approx (assoc-eq-value w s1)
                     (assoc-eq-value w s2)))
  :hints (("Goal" :in-theory (enable assoc-eq-value))))

(defthm v-approx-alist-append
  (implies (and (v-approx-alist a c)
                (v-approx-alist b d))
           (v-approx-alist (append a b) (append c d))))

(defthm s-approx-alist-implies-s-approx-list-assoc-eq-values
  (implies (s-approx-alist x y)
           (s-approx-list (assoc-eq-values a x) (assoc-eq-values a y)))
  :hints (("Goal" :in-theory (enable assoc-eq-values))))

(local
 (defthm s-approx-implies-s-approx-alist-aux
   (implies (or (and (romp s1) (romp s2))
                (and (ramp s1) (ramp s2))
                (and (stubp s1) (stubp s2)))
            (s-approx (car s1) (car s2)))
   :hints (("Goal" :in-theory (enable mem-theory)))))

(defthm s-approx-implies-s-approx-alist
  (implies (s-approx s1 s2)
           (s-approx-alist (pairlis$ x s1)
                           (pairlis$ x s2)))
  :hints (("Goal"
           :induct (s-approx-alist (pairlis$ x s1)
                                   (pairlis$ x s2))
           :in-theory (enable s-approx s-approx-cdr))))

;; The lemma above and the one below may either supersede,
;; subsume, or be subsumed by, corresponding lemmas about
;; s-approx-list -- or so I thought at some point.

(defthm true-listp=>not-memp-cons
  (implies (true-listp x)
           (not (memp (cons x y))))
  :hints (("Goal" :in-theory (enable mem-theory))))

(encapsulate
  ()

  (local
   (defthm s-approx-alist-implies-s-approx-assoc-eq-values-aux
     (implies (and (true-list-listp (assoc-eq-values a x))
                   (true-list-listp (assoc-eq-values a y))
                   (s-approx-alist x y))
              (s-approx (assoc-eq-values a x) (assoc-eq-values a y)))
     :hints (("Goal"
              :in-theory (e/d (s-approx assoc-eq-values)
                              (assoc-eq-values-cdr))))))

  (local
   (defthm true-listp-of-s-approx
     (implies (and (s-approx s1 s2)
                   (true-listp s1))
              (true-listp s2))
     :hints (("Goal" :in-theory (enable s-approx b-approx mem-theory)))))

  (local
   (defthm true-list-listp-of-s-approx-alist
     (implies (and (true-list-listp (assoc-eq-values a x))
                   (s-approx-alist x y))
              (true-list-listp (assoc-eq-values a y)))
     :hints (("Goal"
              :in-theory (e/d (s-approx assoc-eq-values)
                              (assoc-eq-values-cdr)))
             ("Subgoal *1/3"
              :use (:instance true-listp-of-s-approx
                              (s1 (assoc-eq-value (car a) x))
                              (s2 (assoc-eq-value (car a) y)))))))

  (defthm s-approx-alist-implies-s-approx-assoc-eq-values
    (implies (and (true-list-listp (assoc-eq-values a x))
                  (s-approx-alist x y))
             (s-approx (assoc-eq-values a x) (assoc-eq-values a y))))
  )

(defthm s-approx-alist-update-alist
  (implies (and (s-approx-alist x y)
                (s-approx s1 s2))
           (s-approx-alist (update-alist e s1 x)
                           (update-alist e s2 y)))
  :hints (("Goal" :in-theory (enable update-alist))))

(defthm ok-netlistp-reduction
  ;; The next lemma OK-NETLISTP-REDUCTION-REWRITE is the one
  ;; we actually want, but it's stated this way first for
  ;; the purpose of convenient proof by induction.
  (implies (or (equal flag 2) (equal flag 3))
           (equal (ok-netlistp flag fn netlist exceptions)
                  (if (equal flag 2)
                      (ok-netlistp 0 fn netlist exceptions)
                    (ok-netlistp 1 fn netlist exceptions)))))

(defthm ok-netlistp-reduction-rewrite
  (and (equal (ok-netlistp 2 fn netlist exceptions)
              (ok-netlistp 0 fn netlist exceptions))
       (equal (ok-netlistp 3 fn netlist exceptions)
              (ok-netlistp 1 fn netlist exceptions))))

(defthm de-monotone-no-ram-0+1
  (implies (and (or (equal flag 0) (equal flag 1))
                (ok-netlistp flag fn netlist '(mem-32x32 dp-ram-16x32)))
           (monotonicity-property flag fn netlist a1 a2 s1 s2))
  :hints (("Goal"
           :induct (de-monotone-induction flag fn netlist a1 a2 s1 s2)
           :in-theory (enable se monotonicity-property))
          ("Subgoal *1/2"
           :use net-syntax-okp->module-syntax-okp)))

(encapsulate
  ()

  (local
   (defthm sts-occs-okp=>true-list-listp-assoc-eq-values-aux-1
     (implies (sts-occs-okp occs sts-alist netlist)
              (true-list-listp
               (assoc-eq-values (strip-cars occs) sts-alist)))
     :hints (("Goal"
              :in-theory (e/d (assoc-eq-values occ-name)
                              (assoc-eq-values-cdr))))))

  (local
   (defthm sts-occs-okp=>true-list-listp-assoc-eq-values-aux-2
     (implies (and (true-list-listp y)
                   (true-listp x)
                   (subsetp x y))
              (true-list-listp x))))

  (local
   (defthm sts-occs-okp=>true-list-listp-assoc-eq-values-aux-3
     (implies (member e x)
              (member (assoc-eq-value e alist)
                      (assoc-eq-values x alist)))
     :hints (("Goal" :in-theory (enable assoc-eq-values)))))

  (local
   (defthm sts-occs-okp=>true-list-listp-assoc-eq-values-aux-4
     (implies (subsetp x y)
              (subsetp (assoc-eq-values x alist)
                       (assoc-eq-values y alist)))
     :hints (("Goal" :in-theory (enable assoc-eq-values)))))

  (defthm sts-occs-okp=>true-list-listp-assoc-eq-values
    (implies (and (sts-occs-okp occs sts-alist netlist)
                  (subsetp w (strip-cars occs)))
             (true-list-listp (assoc-eq-values w sts-alist)))
    :hints (("Goal"
             :use (:instance sts-occs-okp=>true-list-listp-assoc-eq-values-aux-2
                             (x (assoc-eq-values w sts-alist))
                             (y (assoc-eq-values (strip-cars occs) sts-alist)))
             :in-theory (e/d (assoc-eq-values occ-name)
                             (assoc-eq-values-cdr)))))
  )

(defthm de-monotone-no-ram-2+3
  (implies (and (or (equal flag 2) (equal flag 3))
                (ok-netlistp flag fn netlist '(mem-32x32 dp-ram-16x32)))
           (if (equal flag 2)
               (implies
                (well-formed-sts fn s1 netlist)
                (monotonicity-property flag fn netlist a1 a2 s1 s2))
             (implies
              (well-formed-sts-occs fn s1 netlist)
              (monotonicity-property flag fn netlist a1 a2 s1 s2))))
  :hints
  (("Goal"
    :induct (de-monotone-induction flag fn netlist a1 a2 s1 s2)
    :in-theory (e/d (de occ-name
                        well-formed-sts
                        well-formed-sts-occs
                        monotonicity-property)
                    (well-formed-sts-occs-de-occ)))
   ("Subgoal *1/2"
    :use (net-syntax-okp->module-syntax-okp
          (:instance
           well-formed-sts-occs-de-occ
           (occs (md-occs (assoc-equal fn netlist)))
           (wire-alist (se-occ (md-occs (assoc-equal fn netlist))
                               (pairlis$ (md-ins (assoc-equal fn netlist))
                                         a1)
                               (pairlis$ (md-sts (assoc-equal fn netlist))
                                         s1)
                               (delete-to-eq fn netlist)))
           (sts-alist (pairlis$ (md-sts (assoc-equal fn netlist))
                                s1))
           (netlist (delete-to-eq fn netlist)))
          (:instance
           well-formed-sts-occs-de-occ
           (occs (md-occs (assoc-equal fn netlist)))
           (wire-alist (se-occ (md-occs (assoc-equal fn netlist))
                               (pairlis$ (md-ins (assoc-equal fn netlist))
                                         a2)
                               (pairlis$ (md-sts (assoc-equal fn netlist))
                                         s2)
                               (delete-to-eq fn netlist)))
           (sts-alist (pairlis$ (md-sts (assoc-equal fn netlist))
                                s2))
           (netlist (delete-to-eq fn netlist))))))
  :rule-classes nil)

(defthm de-monotone-no-ram-2
  (implies (and (equal flag 2)
                (ok-netlistp flag fn netlist '(mem-32x32 dp-ram-16x32))
                (well-formed-sts fn s1 netlist))
           (monotonicity-property flag fn netlist a1 a2 s1 s2))
  :hints (("Goal" :use de-monotone-no-ram-2+3)))

(defthm de-monotone-no-ram-3
  (implies (and (equal flag 3)
                (ok-netlistp flag fn netlist '(mem-32x32 dp-ram-16x32))
                (well-formed-sts-occs fn s1 netlist))
           (monotonicity-property flag fn netlist a1 a2 s1 s2))
  :hints (("Goal" :use de-monotone-no-ram-2+3)))

(defun good-s-alist (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (good-s (cdar x))
           (good-s-alist (cdr x)))
    (null x)))

(defthm good-s-alist-pairlis$
  (implies (good-s s)
           (good-s-alist (pairlis$ x s)))
  :hints (("Goal"
           :induct (good-s-alist (pairlis$ x s))
           :in-theory (enable good-s-cdr mem-theory))))

(defthm good-s-assoc-eq-value
  (implies (good-s-alist x)
           (good-s (assoc-eq-value w x)))
  :hints (("Goal" :in-theory (enable assoc-eq-value))))

(defthm good-s-assoc-eq-values
  (implies (and (true-list-listp (assoc-eq-values w x))
                (good-s-alist x))
           (good-s (assoc-eq-values w x)))
  :hints (("Goal" :in-theory (enable assoc-eq-values))))

(defthm good-s-alist-update-alist
  (implies (and (good-s s)
                (good-s-alist s-alist))
           (good-s-alist (update-alist key s s-alist)))
  :hints (("Goal" :in-theory (enable update-alist))))

(defthm de-monotone-0+1
  (implies (and (or (equal flag 0) (equal flag 1))
                (ok-netlistp flag fn netlist '(mem-32x32)))
           (monotonicity-property flag fn netlist a1 a2 s1 s2))
  :hints (("Goal"
           :induct (de-monotone-induction flag fn netlist a1 a2 s1 s2)
           :in-theory (enable se monotonicity-property))))

(local
 (defthm not-memp-of-list-good-s
   (implies (good-s s)
            (and (not (romp (list s)))
                 (not (ramp (list s)))
                 (not (stubp (list s)))))
   :hints (("Goal" :in-theory (enable mem-theory)))))

(defthm f-buf-preserves-good-s
  (good-s (f-buf x))
  :hints (("Goal" :in-theory (enable f-gates 3vp))))

(defthm f-if-preserves-good-s
  (good-s (f-if x y z))
  :hints (("Goal" :in-theory (enable f-gates 3vp))))

(defthm good-s-constant-ram
  (implies (good-s s)
           (good-s (constant-ram s (make-list 32 :initial-element *x*))))
  :hints (("Goal" :in-theory (enable constant-ram))))

(defthm good-s-write-mem1
  (implies (and (good-s s)
                (equal (len value) 32))
           (good-s (write-mem1 v-addr s value)))
  :hints (("Goal" :in-theory (enable write-mem1
                                     rom-guts-of-romp
                                     ram-guts-of-ramp
                                     stub-guts-of-stubp))))

(defthm good-s-write-mem
  (implies (and (good-s s)
                (equal (len value) 32))
           (good-s (write-mem v-addr s value)))
  :hints (("Goal" :in-theory (enable write-mem))))

(defthm primp-preserves-good-s
  (implies (and (not (equal fn 'mem-32x32))
                (good-s sts))
           (good-s (de-primp-apply fn ins sts)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (de-primp-apply good-s-car)
                           (make-list-ac-removal
                            (make-list-ac))))))

(defthm good-s-de<->good-s-alist-de-occ
  (if (equal flag 'term)
      (implies (and (ok-netlistp 2 fn netlist '(mem-32x32))
                    (good-s sts)
                    (well-formed-sts fn sts netlist))
               (good-s (de fn ins sts netlist)))
    (implies (and (ok-netlistp 3 occs netlist '(mem-32x32))
                  (good-s-alist sts-alist)
                  (well-formed-sts-occs occs sts-alist netlist))
             (good-s-alist (de-occ occs wire-alist sts-alist netlist))))
  :hints
  (("Goal"
    :in-theory (e/d (de occ-name
                        well-formed-sts
                        well-formed-sts-occs)
                    (well-formed-sts-occs-de-occ))
    :induct (flag-de flag
                     fn ins sts
                     occs wire-alist sts-alist
                     netlist))
   ("Subgoal *1/2"
    :use (net-syntax-okp->module-syntax-okp
          (:instance
           well-formed-sts-occs-de-occ
           (occs (md-occs (assoc-equal fn netlist)))
           (wire-alist (se-occ (md-occs (assoc-equal fn netlist))
                               (pairlis$ (md-ins (assoc-equal fn netlist))
                                         ins)
                               (pairlis$ (md-sts (assoc-equal fn netlist))
                                         sts)
                               (delete-to-eq fn netlist)))
           (sts-alist (pairlis$ (md-sts (assoc-equal fn netlist))
                                sts))
           (netlist (delete-to-eq fn netlist))))))
  :rule-classes nil)

(defthm good-s-de
  (implies (and (ok-netlistp 2 fn netlist '(mem-32x32))
                (good-s sts)
                (well-formed-sts fn sts netlist))
           (good-s (de fn ins sts netlist)))
  :hints (("Goal" :use (:instance good-s-de<->good-s-alist-de-occ
                                  (flag 'term)))))

(defthm good-s-alist-de-occ
  (implies (and (ok-netlistp 3 occs netlist '(mem-32x32))
                (good-s-alist sts-alist)
                (well-formed-sts-occs occs sts-alist netlist))
           (good-s-alist (de-occ occs wire-alist sts-alist netlist)))
  :hints (("Goal" :use (:instance good-s-de<->good-s-alist-de-occ
                                  (flag 'list)))))

(defthm de-monotone-2+3
  (implies (and (or (equal flag 2) (equal flag 3))
                (ok-netlistp flag fn netlist '(mem-32x32)))
           (if (equal flag 2)
               (implies
                (and (good-s s2)
                     (well-formed-sts fn s1 netlist)
                     (well-formed-sts fn s2 netlist))
                (monotonicity-property flag fn netlist a1 a2 s1 s2))
             (implies
              (and (good-s-alist s2)
                   (well-formed-sts-occs fn s1 netlist)
                   (well-formed-sts-occs fn s2 netlist))
              (monotonicity-property flag fn netlist a1 a2 s1 s2))))
  :hints
  (("Goal"
    :induct (de-monotone-induction flag fn netlist a1 a2 s1 s2)
    :in-theory (e/d (de occ-name
                        well-formed-sts
                        well-formed-sts-occs
                        monotonicity-property)
                    (well-formed-sts-occs-de-occ)))
   ("Subgoal *1/2"
    :use (net-syntax-okp->module-syntax-okp
          (:instance
           well-formed-sts-occs-de-occ
           (occs (md-occs (assoc-equal fn netlist)))
           (wire-alist (se-occ (md-occs (assoc-equal fn netlist))
                               (pairlis$ (md-ins (assoc-equal fn netlist))
                                         a1)
                               (pairlis$ (md-sts (assoc-equal fn netlist))
                                         s1)
                               (delete-to-eq fn netlist)))
           (sts-alist (pairlis$ (md-sts (assoc-equal fn netlist))
                                s1))
           (netlist (delete-to-eq fn netlist)))
          (:instance
           well-formed-sts-occs-de-occ
           (occs (md-occs (assoc-equal fn netlist)))
           (wire-alist (se-occ (md-occs (assoc-equal fn netlist))
                               (pairlis$ (md-ins (assoc-equal fn netlist))
                                         a2)
                               (pairlis$ (md-sts (assoc-equal fn netlist))
                                         s2)
                               (delete-to-eq fn netlist)))
           (sts-alist (pairlis$ (md-sts (assoc-equal fn netlist))
                                s2))
           (netlist (delete-to-eq fn netlist))))))
  :rule-classes nil)

(defthm de-monotone-2
  (implies (and (equal flag 2)
                (ok-netlistp flag fn netlist '(mem-32x32))
                (good-s s2)
                (well-formed-sts fn s1 netlist)
                (well-formed-sts fn s2 netlist))
           (monotonicity-property flag fn netlist a1 a2 s1 s2))
  :hints (("Goal" :use de-monotone-2+3)))

(defthm de-monotone-3
  (implies (and (equal flag 3)
                (ok-netlistp flag fn netlist '(mem-32x32))
                (good-s-alist s2)
                (well-formed-sts-occs fn s1 netlist)
                (well-formed-sts-occs fn s2 netlist))
           (monotonicity-property flag fn netlist a1 a2 s1 s2))
  :hints (("Goal" :use de-monotone-2+3)))

;; ======================================================================

;;;;;           MONOTONICITY FOR SIMULATION            ;;;;;

(defun v-approx-list (x y)
  (declare (xargs :guard t))
  ;; This is only to be used for the simulation lemma, so I imagine
  ;; that I don't care about the final cdrs.
  (if (consp x)
      (and (consp y)
           (v-approx (car x) (car y))
           (v-approx-list (cdr x) (cdr y)))
    (atom y)))

(defun v-s-approx-list (x y)
  (declare (xargs :guard (and (true-list-listp x)
                              (true-list-listp y))))
  ;; assumes x and y are lists of doublets
  (if (consp x)
      (and (consp y)
           (v-approx (caar x) (caar y))
           (s-approx (cadar x) (cadar y))
           (v-s-approx-list (cdr x) (cdr y)))
    t))

(defthm v-approx-car-nth
  (implies (and (v-s-approx-list final-1 final-2)
                (consp final-1)
                (< n (len final-1)))
           (v-approx (car (nth n final-1))
                     (car (nth n final-2)))))

(defthm s-approx-cadr-nth
  (implies (and (v-s-approx-list final-1 final-2)
                (consp final-1)
                (< n (len final-1)))
           (s-approx (cadr (nth n final-1))
                     (cadr (nth n final-2)))))

;; In the following lemma, I'd probably be happy if inputs-1
;; actually equals inputs-2.

(defthm simulate-monotone
  (implies (and (v-approx-list inputs-1 inputs-2)
                (s-approx st-1 st-2)
                (good-s st-2)
                (well-formed-sts fn st-1 netlist)
                (well-formed-sts fn st-2 netlist)
                (ok-netlistp 0 fn netlist '(mem-32x32))
                (ok-netlistp 2 fn netlist '(mem-32x32)))
           (v-s-approx-list
            (simulate fn inputs-1 st-1 netlist)
            (simulate fn inputs-2 st-2 netlist))))

(defthm v-approx-list-x-x
  (v-approx-list x x))

(defun doublet-p (x)
  (declare (xargs :guard (true-listp x)))
  (equal x (list (car x) (cadr x))))

(defun doublet-n-simulate-induction (fn inputs st netlist n)
  (if (zp n)
      st
    (let ((new-st (de fn (car inputs) st netlist)))
      (doublet-n-simulate-induction
       fn (cdr inputs) new-st netlist (1- n)))))

(defthm doublet-n-simulate
  (implies (and (consp inputs)
                (< n (len inputs)))
           (doublet-p (nth n (simulate fn inputs st netlist))))
  :hints (("Goal"
           :induct (doublet-n-simulate-induction fn inputs st netlist n)
           :expand (simulate fn inputs st netlist))))

(defthm doublet-p-equal-approx
  (implies (and (doublet-p x)
                (doublet-p y)
                (v-knownp (car x))
                (s-knownp (cadr x))
                (v-approx (car x) (car y))
                (s-approx (cadr x) (cadr y)))
           (equal x y))
  :hints (("Goal" :in-theory (enable s-knownp-implies-s-approx-is-equal)))
  :rule-classes nil)

(in-theory (disable doublet-p))

(defthm len-simulate
  (equal (len (simulate fn inputs st netlist))
         (len inputs)))

(local
 (defthm consp-simulate
   (implies (consp inputs)
            (consp (simulate fn inputs st netlist)))
   :rule-classes :type-prescription))

(defthm xs-suffice-for-reset-lemma-verbose
  (let ((final-1 (nth n (simulate fn inputs st-1 netlist)))
        (final-2 (nth n (simulate fn inputs st-2 netlist))))
    (implies (and (< n (len inputs))
                  (s-approx st-1 st-2)
                  (v-knownp (car final-1))
                  (s-knownp (cadr final-1))
                  (good-s st-2)
                  (well-formed-sts fn st-1 netlist)
                  (well-formed-sts fn st-2 netlist)
                  (ok-netlistp 0 fn netlist '(mem-32x32))
                  (ok-netlistp 2 fn netlist '(mem-32x32)))
             (equal final-1 final-2)))
  :hints (("Goal"
           :cases ((atom inputs) (consp inputs))
           :use (:instance doublet-p-equal-approx
                           (x (nth n (simulate fn inputs st-1 netlist)))
                           (y (nth n (simulate fn inputs st-2 netlist)))))))

(defthm xs-suffice-for-reset-lemma
  (let ((final-1 (nth n (simulate fn inputs st-1 netlist)))
        (final-2 (nth n (simulate fn inputs st-2 netlist))))
    (implies (and (< n (len inputs))
                  (s-approx st-1 st-2)
                  (v-knownp (car final-1))
                  (s-knownp (cadr final-1))
                  (good-s st-2)
                  (well-formed-sts fn st-1 netlist)
                  (well-formed-sts fn st-2 netlist)
                  (ok-netlistp 0 fn netlist '(mem-32x32)))
             (equal final-1 final-2))))
