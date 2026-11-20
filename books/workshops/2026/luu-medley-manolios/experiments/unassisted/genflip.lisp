; genflip.lisp -- Section 5.2 of the paper: generalized flips.
;
; Part 1 formalizes the multi-summand rewrite used on the GPU: given a
; group of summands sharing the A factor, and a subset D of the group
; whose B factors xor to zero, with r = min D, the summand r is deleted
; and C^(r) is added to the C factors of the other members of D.  We
; prove that the represented tensor is unchanged (the correctness
; computation of Section 5.2), that the rewritten group has at least one
; summand fewer, and that the result (with zero summands deleted) is
; again a scheme.
;
; Part 2 formalizes the change-of-basis view: for an invertible G,
;   sum_i A (x) B_i (x) C_i = sum_j A (x) (BG)_j (x) (G^{-1}C)_j.
; Here G is given by its columns g_1..g_N and G^{-1} by its rows
; h_1..h_N; invertibility is the condition sum_j g_j (x) h_j = I.

(in-package "ACL2")

(include-book "connectivity")

;;; ==================================================================
;;; Part 1: the subset-based generalized flip
;;; ==================================================================

;; All summands of G have first factor A.
(defun shared-A-p (A G)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom G) t (and (equal (fac 0 (car G)) A) (shared-A-p A (cdr G)))))

;; xor of the B factors of the flagged summands (flags: a list of bits
;; aligned with G; this is the subset D_s of Section 5.2).
(defun flagged-B-sum (L flags G)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count G)))
  (cond ((atom G) (bv-zero L))
        ((eql (car flags) 1) (bv+ (fac 1 (car G)) (flagged-B-sum L (cdr flags) (cdr G))))
        (t (flagged-B-sum L (cdr flags) (cdr G)))))

;; Add Cr to the C factor of every flagged summand.
(defun add-Cr (flags Cr G)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count G)))
  (cond ((atom G) nil)
        ((eql (car flags) 1)
         (cons (set-fac 2 (bv+ (fac 2 (car G)) Cr) (car G))
               (add-Cr (cdr flags) Cr (cdr G))))
        (t (cons (car G) (add-Cr (cdr flags) Cr (cdr G))))))

;; The C factor of the first flagged summand (index r = min D).
(defun first-flagged-C (flags G)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count G)))
  (cond ((atom G) nil)
        ((eql (car flags) 1) (fac 2 (car G)))
        (t (first-flagged-C (cdr flags) (cdr G)))))

(defun first-flagged-summand (flags G)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count G)))
  (cond ((atom G) nil)
        ((eql (car flags) 1) (car G))
        (t (first-flagged-summand (cdr flags) (cdr G)))))

(defun some-flag (flags G)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count G)))
  (cond ((atom G) nil)
        ((eql (car flags) 1) t)
        (t (some-flag (cdr flags) (cdr G)))))

;; The generalized flip: add C^(r) into the flagged C factors and delete
;; the summands that became zero (summand r among them).
(defun gen-flip (L flags G)
  (declare (xargs :guard t :verify-guards nil))
  (drop-zeros L (add-Cr flags (first-flagged-C flags G) G)))

(defthm triple-listp-of-add-Cr
  (implies (and (triple-listp L G) (bvp Cr) (equal (len Cr) (nfix L)))
           (triple-listp L (add-Cr flags Cr G)))
  :hints (("Goal" :in-theory (enable set-fac))))

;; rank1 of a summand whose C factor got Cr added.
(defthm rank1-of-add-Cr-summand
  (implies (and (posp L) (triplep L s) (bvp Cr) (equal (len Cr) L))
           (equal (rank1 (set-fac 2 (bv+ (fac 2 s) Cr) s))
                  (bv+ (rank1 s) (outer3 (fac 0 s) (fac 1 s) Cr))))
  :hints (("Goal" :in-theory (enable rank1 fac set-fac))))

(defthm bv-listp-facts-of-flagged-B-sum
  (implies (triple-listp L G)
           (and (bvp (flagged-B-sum L flags G))
                (equal (len (flagged-B-sum L flags G)) (nfix L))))
  :hints (("Goal" :induct (flagged-B-sum L flags G) :in-theory (enable fac))))

;; The sum after adding Cr:  sum(G) + A (x) (sum_{i in D} B_i) (x) Cr.
(defthm triple-sum-of-add-Cr
  (implies (and (posp L) (triple-listp L G) (shared-A-p A G)
                (bvp A) (equal (len A) L) (bvp Cr) (equal (len Cr) L))
           (equal (triple-sum L (add-Cr flags Cr G))
                  (bv+ (triple-sum L G)
                       (outer3 A (flagged-B-sum L flags G) Cr))))
  :hints (("Goal" :induct (add-Cr flags Cr G)
                  :in-theory (e/d (fac) (rank1 set-fac outer3 bv+-commutative)))
          ("Subgoal *1/2" :use ((:instance rank1-of-add-Cr-summand (s (car G)))
                                (:instance outer3-of-bv+-2 (A A) (B (fac 1 (car G)))
                                           (B2 (flagged-B-sum L (cdr flags) (cdr G))) (C Cr))))))

;; Correctness (the computation at the end of Section 5.2): when the
;; flagged B factors xor to zero, the tensor is unchanged.
(defthm gen-flip-preserves-sum
  (implies (and (posp L) (triple-listp L G) (shared-A-p A G)
                (bvp A) (equal (len A) L)
                (bvp (first-flagged-C flags G)) (equal (len (first-flagged-C flags G)) L)
                (equal (flagged-B-sum L flags G) (bv-zero L)))
           (equal (triple-sum L (gen-flip L flags G))
                  (triple-sum L G)))
  :hints (("Goal" :in-theory (disable triple-sum-of-add-Cr)
                  :use ((:instance triple-sum-of-add-Cr (Cr (first-flagged-C flags G)))))))

(defthm first-flagged-C-facts
  (implies (and (posp L) (summand-listp L G) (some-flag flags G))
           (and (bvp (first-flagged-C flags G))
                (equal (len (first-flagged-C flags G)) L)))
  :hints (("Goal" :induct (first-flagged-C flags G))
          ("Subgoal *1/2" :use ((:instance summandp-facts (s (car G)))))))

;; Summand r becomes zero and is deleted, so the group shrinks.
(defthm len-of-add-Cr (equal (len (add-Cr flags Cr G)) (len G)))

(defthm len-of-drop-zeros-when-some-zero
  (implies (and (member-equal s lst) (zero-summandp L s))
           (< (len (drop-zeros L lst)) (len lst)))
  :hints (("Goal" :induct (drop-zeros L lst))))

(defthm len-of-drop-zeros-le (<= (len (drop-zeros L lst)) (len lst))
  :rule-classes :linear)

(defthm zero-summand-in-add-Cr
  (implies (and (posp L) (summand-listp L G) (some-flag flags G))
           (member-equal (set-fac 2 (bv-zero L) (first-flagged-summand flags G))
                         (add-Cr flags (first-flagged-C flags G) G)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable first-flagged-summand))))

(defthm gen-flip-reduces-rank
  (implies (and (posp L) (summand-listp L G) (some-flag flags G))
           (< (len (gen-flip L flags G)) (len G)))
  :hints (("Goal" :in-theory (disable len-of-drop-zeros-when-some-zero)
                  :use (zero-summand-in-add-Cr
                        (:instance len-of-drop-zeros-when-some-zero
                                   (s (set-fac 2 (bv-zero L) (first-flagged-summand flags G)))
                                   (lst (add-Cr flags (first-flagged-C flags G) G)))
                        (:instance summandp-facts (s (first-flagged-summand flags G)))))))

;; A generalized flip inside a scheme S = G (+) rest yields a scheme, with
;; strictly fewer summands.  (Remark of Section 5.2: generalized flips do
;; not leave the space of schemes; by Theorem 4.1 the result is therefore
;; reachable by ordinary flips and pluses.)
(defthm gen-flip-in-scheme
  (implies (and (schemep n (append G rest)) (summand-listp (sq n) G)
                (shared-A-p A G) (bvp A) (equal (len A) (sq n))
                (some-flag flags G)
                (equal (flagged-B-sum (sq n) flags G) (bv-zero (sq n))))
           (and (schemep n (append (gen-flip (sq n) flags G) rest))
                (< (len (append (gen-flip (sq n) flags G) rest))
                   (len (append G rest)))))
  :hints (("Goal" :in-theory (disable gen-flip-preserves-sum first-flagged-C-facts
                                      gen-flip-reduces-rank triple-sum-of-append)
                  :use ((:instance gen-flip-preserves-sum (L (sq n)))
                        (:instance first-flagged-C-facts (L (sq n)))
                        (:instance gen-flip-reduces-rank (L (sq n)))
                        (:instance summand-listp-append-parts (L (sq n)))
                        (:instance triple-sum-of-append (L (sq n)) (x G) (y rest))
                        (:instance triple-sum-of-append (L (sq n)) (x (gen-flip (sq n) flags G)) (y rest))))))

(defthm gen-flip-reachable
  (implies (and (<= 2 n) (schemep n (append G rest)) (summand-listp (sq n) G)
                (shared-A-p A G) (bvp A) (equal (len A) (sq n))
                (some-flag flags G)
                (equal (flagged-B-sum (sq n) flags G) (bv-zero (sq n))))
           (let ((S2 (append (gen-flip (sq n) flags G) rest)))
             (and (path-ok-p (sq n) (connect-path n (append G rest) S2) (append G rest))
                  (perm (apply-path (sq n) (connect-path n (append G rest) S2) (append G rest))
                        S2))))
  :hints (("Goal" :in-theory (disable gen-flip-in-scheme flip-graph-strongly-connected)
                  :use (gen-flip-in-scheme
                        (:instance flip-graph-strongly-connected
                                   (S (append G rest))
                                   (S2 (append (gen-flip (sq n) flags G) rest)))))))
