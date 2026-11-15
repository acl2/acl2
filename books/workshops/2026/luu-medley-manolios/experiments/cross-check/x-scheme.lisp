; x-scheme.lisp -- MECHANICAL RENAMING (prefix x-) of ../unassisted/scheme.lisp
; produced by rename.py in this directory; do not edit by hand.
; scheme.lisp -- Schemes and the matrix multiplication flip graph.
;
; Definition 2.2 (schemes / vertices): a scheme for M^(n) is a list of
; summands (A B C), each a triple of nonzero n x n matrices over F_2,
; whose rank-one tensors sum to M^(n).  Lists are read as multisets:
; two lists that are permutations of each other denote the same vertex.
;
; Definition 2.3 (flip and plus transformations): edges of the graph.
; We represent a move as (:flip p s t) or (:plus p s t), where p in
; {0,1,2} is the position (A, B or C) and s, t are summands of the
; current scheme (t is taken from the scheme with one copy of s removed,
; so that two equal summands can be used together).  Zero summands
; produced by a move are deleted.
;
; The main results here: every move maps schemes to schemes (the remark
; after Definition 2.3), the same for paths, and perm-congruence of all
; notions (so the multiset view is sound).

(in-package "ACL2")

(include-book "x-mmt")

;;; ------------------------------------------------------------------
;;; Summands
;;; ------------------------------------------------------------------

(defun x-fac (p s)
  (declare (xargs :guard (and (natp p) (true-listp s))))
  (case p (0 (car s)) (1 (cadr s)) (t (caddr s))))

(defun x-set-fac (p v s)
  (declare (xargs :guard (and (natp p) (true-listp s))))
  (case p
    (0 (list v (cadr s) (caddr s)))
    (1 (list (car s) v (caddr s)))
    (t (list (car s) (cadr s) v))))

(defun x-posp3 (p)
  (declare (xargs :guard t))
  (or (eql p 0) (eql p 1) (eql p 2)))

;; The two positions other than p, in increasing order.
(defun x-other-lo (p)
  (declare (xargs :guard t))
  (if (eql p 0) 1 0))
(defun x-other-hi (p)
  (declare (xargs :guard t))
  (if (eql p 2) 1 2))

(defun x-zero-summandp (L s)
  (declare (xargs :guard (and (natp L) (true-listp s))))
  (or (equal (car s) (x-bv-zero L))
      (equal (cadr s) (x-bv-zero L))
      (equal (caddr s) (x-bv-zero L))))

(defun x-summandp (L s)
  (declare (xargs :guard (natp L)))
  (and (x-triplep L s) (not (x-zero-summandp L s))))

(defun x-summand-listp (L lst)
  (declare (xargs :guard (natp L)))
  (if (atom lst) (null lst)
    (and (x-summandp L (car lst)) (x-summand-listp L (cdr lst)))))

(defthm x-summand-listp-forward-to-triple-listp
  (implies (x-summand-listp L lst) (x-triple-listp L lst))
  :rule-classes (:forward-chaining :rewrite))

(defthm x-summand-listp-of-append
  (implies (true-listp x)
           (equal (x-summand-listp L (append x y))
                  (and (x-summand-listp L x) (x-summand-listp L y))))
  :hints (("Goal" :induct (x-summand-listp L x))))

(defthm x-summand-listp-of-cons
  (equal (x-summand-listp L (cons s x))
         (and (x-summandp L s) (x-summand-listp L x))))

(defthm x-summand-listp-of-remove1
  (implies (x-summand-listp L x) (x-summand-listp L (remove1-equal s x)))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal s x))))

(defthm x-summand-listp-member
  (implies (and (member-equal s x) (x-summand-listp L x))
           (x-summandp L s))
  :hints (("Goal" :induct (x-summand-listp L x))))

(defthm x-summand-listp-of-remove1-converse
  (implies (and (member-equal s y) (x-summandp L s) (true-listp y)
                (x-summand-listp L (remove1-equal s y)))
           (x-summand-listp L y))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal s y))))

(defthm x-summand-listp-when-perm
  (implies (and (perm x y) (x-summand-listp L x) (true-listp y))
           (x-summand-listp L y))
  :hints (("Goal" :in-theory (enable perm) :induct (perm x y))))

(defthm x-summand-listp-forward-to-true-listp
  (implies (x-summand-listp L x) (true-listp x))
  :rule-classes :forward-chaining)

;; Deleting the zero summands of a list.
(defun x-drop-zeros (L lst)
  (declare (xargs :guard (and (natp L) (x-triple-listp L lst))))
  (cond ((atom lst) nil)
        ((x-zero-summandp L (car lst)) (x-drop-zeros L (cdr lst)))
        (t (cons (car lst) (x-drop-zeros L (cdr lst))))))

(defthm x-summand-listp-of-drop-zeros
  (implies (x-triple-listp L lst) (x-summand-listp L (x-drop-zeros L lst))))

(defthm x-rank1-of-zero-summand
  (implies (and (x-triplep L s) (x-zero-summandp L s))
           (equal (x-rank1 s) (x-bv-zero (x-tlen L))))
  :hints (("Goal" :in-theory (enable x-rank1))))

(defthm x-triple-sum-of-drop-zeros
  (implies (and (natp L) (x-triple-listp L lst))
           (equal (x-triple-sum L (x-drop-zeros L lst)) (x-triple-sum L lst)))
  :hints (("Goal" :induct (x-drop-zeros L lst))
          ("Subgoal *1/2" :use ((:instance x-rank1-of-zero-summand (s (car lst)))))))

;; Rank-one tensors of summands are nonzero (Definition 2.2).
(defthm x-rank1-nonzero
  (implies (x-summandp L s)
           (not (equal (x-rank1 s) (x-bv-zero (x-tlen L)))))
  :hints (("Goal" :in-theory (e/d (x-rank1) (x-outer3-nonzero))
                  :use ((:instance x-outer3-nonzero (A (car s)) (B (cadr s)) (C (caddr s)))))))

;;; ------------------------------------------------------------------
;;; Schemes (Definition 2.2)
;;; ------------------------------------------------------------------

(defun x-schemep (n S)
  (declare (xargs :guard t))
  (and (posp n)
       (x-summand-listp (x-sq n) S)
       (equal (x-triple-sum (x-sq n) S) (x-mmt n))))

(defthm x-summand-listp-of-naive-k
  (implies (and (posp n) (natp i) (natp j) (< i n) (< j n))
           (x-summand-listp (x-sq n) (x-naive-k n i j k))))
(defthm x-summand-listp-of-naive-j
  (implies (and (posp n) (natp i) (< i n))
           (x-summand-listp (x-sq n) (x-naive-j n i j))))
(defthm x-summand-listp-of-naive-i
  (implies (posp n)
           (x-summand-listp (x-sq n) (x-naive-i n i))))

(defthm x-schemep-of-naive-scheme
  (implies (posp n) (x-schemep n (x-naive-scheme n)))
  :hints (("Goal" :in-theory (enable x-mmt x-naive-scheme))))

;;; ------------------------------------------------------------------
;;; Flip and plus transformations (Definition 2.3)
;;; ------------------------------------------------------------------

;; Flip on position p of summands s and t with equal p-factors:
;;   s gets its hi-factor replaced by (s_hi + t_hi),
;;   t gets its lo-factor replaced by (t_lo + s_lo),
;; where lo < hi are the two other positions.  For p = 0 (the A position):
;;   A(x)B(x)C, A(x)B'(x)C'  -->  A(x)B(x)(C+C'), A(x)(B'+B)(x)C'.
(defun x-flip-results (p s u)
  (declare (xargs :guard (and (natp p) (true-listp s) (true-listp u))
                  :verify-guards nil))
  (list (x-set-fac (x-other-hi p) (x-bv+ (x-fac (x-other-hi p) s) (x-fac (x-other-hi p) u)) s)
        (x-set-fac (x-other-lo p) (x-bv+ (x-fac (x-other-lo p) u) (x-fac (x-other-lo p) s)) u)))

;; Plus on position p with pivot piv, replacing target tgt by two summands:
;;   tgt with p-factor (tgt_p + piv_p), and tgt with p-factor piv_p.
(defun x-plus-results (p piv tgt)
  (declare (xargs :guard (and (natp p) (true-listp piv) (true-listp tgt))
                  :verify-guards nil))
  (list (x-set-fac p (x-bv+ (x-fac p tgt) (x-fac p piv)) tgt)
        (x-set-fac p (x-fac p piv) tgt)))

(defun x-move-kind (m) (declare (xargs :guard (true-listp m))) (car m))
(defun x-move-pos (m) (declare (xargs :guard (true-listp m))) (cadr m))
(defun x-move-s (m) (declare (xargs :guard (true-listp m))) (caddr m))
(defun x-move-t (m) (declare (xargs :guard (true-listp m))) (cadddr m))

(defun x-flip-move (p s u) (declare (xargs :guard t)) (list :flip p s u))
(defun x-plus-move (p piv tgt) (declare (xargs :guard t)) (list :plus p piv tgt))

;; When is a move applicable to the list S?
(defun x-move-ok-p (m S)
  (declare (xargs :guard (and (true-listp m) (true-listp S))
                  :verify-guards nil))
  (let ((p (x-move-pos m)) (s1 (x-move-s m)) (u (x-move-t m)))
    (and (x-posp3 p)
         (true-listp s1) (true-listp u)
         (member-equal s1 S)
         (member-equal u (remove1-equal s1 S))
         (case (x-move-kind m)
           (:flip (equal (x-fac p s1) (x-fac p u)))
           (:plus t)
           (t nil)))))

(defun x-apply-move (L m S)
  (declare (xargs :guard (and (natp L) (true-listp m) (x-triple-listp L S)
                              (x-move-ok-p m S))
                  :verify-guards nil))
  (let ((p (x-move-pos m)) (s1 (x-move-s m)) (u (x-move-t m)))
    (case (x-move-kind m)
      (:flip (append (remove1-equal u (remove1-equal s1 S))
                     (x-drop-zeros L (x-flip-results p s1 u))))
      (t (append (remove1-equal u S)
                 (x-drop-zeros L (x-plus-results p s1 u)))))))

;;; ------------------------------------------------------------------
;;; Moves preserve the represented tensor
;;; ------------------------------------------------------------------

(defthm x-triplep-of-set-fac
  (implies (and (x-triplep L s) (x-bvp v) (equal (len v) (nfix L)))
           (x-triplep L (x-set-fac p v s))))

(defthm x-bvp-of-fac
  (implies (and (x-bvp (car s)) (x-bvp (cadr s)) (x-bvp (caddr s)))
           (x-bvp (x-fac p s))))
(defthm x-len-of-fac
  (equal (len (x-fac p s))
         (case p (0 (len (car s))) (1 (len (cadr s))) (t (len (caddr s))))))

(defthm x-triple-listp-of-flip-results
  (implies (and (x-triplep L s) (x-triplep L u))
           (x-triple-listp L (x-flip-results p s u))))

(defthm x-triple-listp-of-plus-results
  (implies (and (x-triplep L piv) (x-triplep L tgt))
           (x-triple-listp L (x-plus-results p piv tgt))))

;; The algebra behind a flip:
;;   A(x)B(x)C + A(x)B'(x)C' = A(x)B(x)(C+C') + A(x)(B'+B)(x)C'.
(defthm x-flip-preserves-sum
  (implies (and (x-posp3 p) (x-triplep L s) (x-triplep L u)
                (equal (x-fac p s) (x-fac p u)))
           (equal (x-triple-sum L (x-flip-results p s u))
                  (x-bv+ (x-rank1 s) (x-rank1 u))))
  :hints (("Goal" :in-theory (enable x-rank1)
                  :cases ((equal p 0) (equal p 1) (equal p 2)))))

;; The algebra behind a plus:  A'(x)B'(x)C' = (A'+A)(x)B'(x)C' + A(x)B'(x)C'.
(defthm x-plus-preserves-sum
  (implies (and (x-posp3 p) (x-triplep L piv) (x-triplep L tgt))
           (equal (x-triple-sum L (x-plus-results p piv tgt))
                  (x-rank1 tgt)))
  :hints (("Goal" :in-theory (enable x-rank1)
                  :cases ((equal p 0) (equal p 1) (equal p 2)))))

(defthm x-member-of-remove1-implies-member
  (implies (member-equal u (remove1-equal s1 S))
           (member-equal u S))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm x-bv+-cancel-pair
  (implies (and (x-bvp x) (x-bvp y) (x-bvp z)
                (equal (len x) (len y)) (equal (len x) (len z)))
           (equal (x-bv+ (x-bv+ x y) (x-bv+ y (x-bv+ x z))) z))
  :hints (("Goal" :in-theory (disable x-bv+-associative x-bv+-commutative x-bv+-commutative-2)
                  :use ((:instance x-bv+-associative (x x) (y y) (z (x-bv+ y (x-bv+ x z))))
                        (:instance x-bv+-self-in-middle (x y) (y (x-bv+ x z)))
                        (:instance x-bv+-self-in-middle (x x) (y z))))))

(defthm x-apply-move-preserves-sum
  (implies (and (posp L) (x-triple-listp L S) (x-move-ok-p m S))
           (equal (x-triple-sum L (x-apply-move L m S))
                  (x-triple-sum L S)))
  :hints (("Goal" :in-theory (disable x-flip-results x-plus-results x-posp3 x-fac x-set-fac))))

(defthm x-triple-listp-of-drop-zeros
  (implies (x-triple-listp L lst) (x-triple-listp L (x-drop-zeros L lst))))

(defthm x-apply-move-preserves-triple-listp
  (implies (and (posp L) (x-triple-listp L S) (x-move-ok-p m S))
           (x-triple-listp L (x-apply-move L m S)))
  :hints (("Goal" :in-theory (disable x-flip-results x-plus-results x-posp3 x-fac x-set-fac))))

(defthm x-apply-move-preserves-summand-listp
  (implies (and (posp L) (x-summand-listp L S) (x-move-ok-p m S))
           (x-summand-listp L (x-apply-move L m S)))
  :hints (("Goal" :in-theory (disable x-flip-results x-plus-results x-posp3 x-fac x-set-fac))))

;; Remark after Definition 2.3: every vertex reached by a flip or plus
;; transformation is again a decomposition of M^(n).
(defthm x-apply-move-preserves-schemep
  (implies (and (x-schemep n S) (x-move-ok-p m S))
           (x-schemep n (x-apply-move (x-sq n) m S)))
  :hints (("Goal" :in-theory (disable x-apply-move x-move-ok-p))))

;;; ------------------------------------------------------------------
;;; Paths
;;; ------------------------------------------------------------------

(defun x-path-ok-p (L path S)
  (declare (xargs :guard (and (natp L) (true-listp path) (x-triple-listp L S))
                  :verify-guards nil))
  (if (atom path)
      t
    (and (true-listp (car path))
         (x-move-ok-p (car path) S)
         (x-path-ok-p L (cdr path) (x-apply-move L (car path) S)))))

(defun x-apply-path (L path S)
  (declare (xargs :guard (and (natp L) (true-listp path) (x-triple-listp L S))
                  :verify-guards nil))
  (if (atom path)
      S
    (x-apply-path L (cdr path) (x-apply-move L (car path) S))))

(defthm x-path-ok-p-of-append
  (equal (x-path-ok-p L (append p1 p2) S)
         (and (x-path-ok-p L p1 S)
              (x-path-ok-p L p2 (x-apply-path L p1 S))))
  :hints (("Goal" :induct (x-apply-path L p1 S))))

(defthm x-apply-path-of-append
  (equal (x-apply-path L (append p1 p2) S)
         (x-apply-path L p2 (x-apply-path L p1 S)))
  :hints (("Goal" :induct (x-apply-path L p1 S))))

(defthm x-apply-path-preserves-schemep
  (implies (and (x-schemep n S) (x-path-ok-p (x-sq n) path S))
           (x-schemep n (x-apply-path (x-sq n) path S)))
  :hints (("Goal" :induct (x-apply-path (x-sq n) path S)
                  :in-theory (disable x-schemep x-apply-move x-move-ok-p))))

(defthm x-apply-path-preserves-summand-listp
  (implies (and (posp L) (x-summand-listp L S) (x-path-ok-p L path S))
           (x-summand-listp L (x-apply-path L path S)))
  :hints (("Goal" :induct (x-apply-path L path S)
                  :in-theory (disable x-apply-move x-move-ok-p))))

(defthm x-apply-path-preserves-sum
  (implies (and (posp L) (x-triple-listp L S) (x-path-ok-p L path S))
           (equal (x-triple-sum L (x-apply-path L path S)) (x-triple-sum L S)))
  :hints (("Goal" :induct (x-apply-path L path S)
                  :in-theory (disable x-apply-move x-move-ok-p))))

;;; ------------------------------------------------------------------
;;; Multiset (perm) congruences: the graph lives on multisets
;;; ------------------------------------------------------------------

(defcong perm equal (x-move-ok-p m S) 2
  :hints (("Goal" :in-theory (disable x-posp3 x-fac))))

(defcong perm perm (x-apply-move L m S) 3
  :hints (("Goal" :in-theory (disable x-flip-results x-plus-results x-drop-zeros))))

(defun x-ind-path2 (L path S1 S2)
  (if (atom path)
      (list L S1 S2)
    (x-ind-path2 L (cdr path) (x-apply-move L (car path) S1) (x-apply-move L (car path) S2))))

(defcong perm equal (x-path-ok-p L path S) 3
  :hints (("Goal" :induct (x-ind-path2 L path S S-equiv)
                  :in-theory (disable x-apply-move x-move-ok-p))))

(defcong perm perm (x-apply-path L path S) 3
  :hints (("Goal" :induct (x-ind-path2 L path S S-equiv)
                  :in-theory (disable x-apply-move x-move-ok-p))))

(defthm x-schemep-when-perm
  (implies (and (perm S1 S2) (x-schemep n S1) (true-listp S2))
           (x-schemep n S2))
  :hints (("Goal" :use ((:instance x-triple-sum-when-perm (x S1) (y S2) (L (x-sq n)))))))

(defthm x-true-listp-of-apply-move
  (true-listp (x-apply-move L m S)))
(defthm x-true-listp-of-apply-path
  (implies (true-listp S) (true-listp (x-apply-path L path S))))

(in-theory (disable x-fac x-set-fac x-other-lo x-other-hi x-posp3 x-flip-results x-plus-results
                    x-move-ok-p x-apply-move))

;;; ------------------------------------------------------------------
;;; Observation 4.1: two identical summands can be deleted with a flip
;;; ------------------------------------------------------------------

(defun x-delete-pair-move (s)
  (declare (xargs :guard t))
  (x-flip-move 0 s s))

(defthm x-delete-pair-move-ok
  (implies (and (true-listp s1) (member-equal s1 S) (member-equal s1 (remove1-equal s1 S)))
           (x-move-ok-p (x-delete-pair-move s1) S))
  :hints (("Goal" :in-theory (enable x-move-ok-p x-posp3))))

(defthm x-apply-delete-pair-move
  (implies (and (natp L) (x-triplep L s1) (true-listp S))
           (equal (x-apply-move L (x-delete-pair-move s1) S)
                  (remove1-equal s1 (remove1-equal s1 S))))
  :hints (("Goal" :in-theory (enable x-apply-move x-flip-results x-fac x-set-fac x-other-lo x-other-hi))))
