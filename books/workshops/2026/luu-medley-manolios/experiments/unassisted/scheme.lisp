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

(include-book "mmt")

;;; ------------------------------------------------------------------
;;; Summands
;;; ------------------------------------------------------------------

(defun fac (p s)
  (declare (xargs :guard (and (natp p) (true-listp s))))
  (case p (0 (car s)) (1 (cadr s)) (t (caddr s))))

(defun set-fac (p v s)
  (declare (xargs :guard (and (natp p) (true-listp s))))
  (case p
    (0 (list v (cadr s) (caddr s)))
    (1 (list (car s) v (caddr s)))
    (t (list (car s) (cadr s) v))))

(defun posp3 (p)
  (declare (xargs :guard t))
  (or (eql p 0) (eql p 1) (eql p 2)))

;; The two positions other than p, in increasing order.
(defun other-lo (p)
  (declare (xargs :guard t))
  (if (eql p 0) 1 0))
(defun other-hi (p)
  (declare (xargs :guard t))
  (if (eql p 2) 1 2))

(defun zero-summandp (L s)
  (declare (xargs :guard (and (natp L) (true-listp s))))
  (or (equal (car s) (bv-zero L))
      (equal (cadr s) (bv-zero L))
      (equal (caddr s) (bv-zero L))))

(defun summandp (L s)
  (declare (xargs :guard (natp L)))
  (and (triplep L s) (not (zero-summandp L s))))

(defun summand-listp (L lst)
  (declare (xargs :guard (natp L)))
  (if (atom lst) (null lst)
    (and (summandp L (car lst)) (summand-listp L (cdr lst)))))

(defthm summand-listp-forward-to-triple-listp
  (implies (summand-listp L lst) (triple-listp L lst))
  :rule-classes (:forward-chaining :rewrite))

(defthm summand-listp-of-append
  (implies (true-listp x)
           (equal (summand-listp L (append x y))
                  (and (summand-listp L x) (summand-listp L y))))
  :hints (("Goal" :induct (summand-listp L x))))

(defthm summand-listp-of-cons
  (equal (summand-listp L (cons s x))
         (and (summandp L s) (summand-listp L x))))

(defthm summand-listp-of-remove1
  (implies (summand-listp L x) (summand-listp L (remove1-equal s x)))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal s x))))

(defthm summand-listp-member
  (implies (and (member-equal s x) (summand-listp L x))
           (summandp L s))
  :hints (("Goal" :induct (summand-listp L x))))

(defthm summand-listp-of-remove1-converse
  (implies (and (member-equal s y) (summandp L s) (true-listp y)
                (summand-listp L (remove1-equal s y)))
           (summand-listp L y))
  :hints (("Goal" :in-theory (enable remove1-equal) :induct (remove1-equal s y))))

(defthm summand-listp-when-perm
  (implies (and (perm x y) (summand-listp L x) (true-listp y))
           (summand-listp L y))
  :hints (("Goal" :in-theory (enable perm) :induct (perm x y))))

(defthm summand-listp-forward-to-true-listp
  (implies (summand-listp L x) (true-listp x))
  :rule-classes :forward-chaining)

;; Deleting the zero summands of a list.
(defun drop-zeros (L lst)
  (declare (xargs :guard (and (natp L) (triple-listp L lst))))
  (cond ((atom lst) nil)
        ((zero-summandp L (car lst)) (drop-zeros L (cdr lst)))
        (t (cons (car lst) (drop-zeros L (cdr lst))))))

(defthm summand-listp-of-drop-zeros
  (implies (triple-listp L lst) (summand-listp L (drop-zeros L lst))))

(defthm rank1-of-zero-summand
  (implies (and (triplep L s) (zero-summandp L s))
           (equal (rank1 s) (bv-zero (tlen L))))
  :hints (("Goal" :in-theory (enable rank1))))

(defthm triple-sum-of-drop-zeros
  (implies (and (natp L) (triple-listp L lst))
           (equal (triple-sum L (drop-zeros L lst)) (triple-sum L lst)))
  :hints (("Goal" :induct (drop-zeros L lst))
          ("Subgoal *1/2" :use ((:instance rank1-of-zero-summand (s (car lst)))))))

;; Rank-one tensors of summands are nonzero (Definition 2.2).
(defthm rank1-nonzero
  (implies (summandp L s)
           (not (equal (rank1 s) (bv-zero (tlen L)))))
  :hints (("Goal" :in-theory (e/d (rank1) (outer3-nonzero))
                  :use ((:instance outer3-nonzero (A (car s)) (B (cadr s)) (C (caddr s)))))))

;;; ------------------------------------------------------------------
;;; Schemes (Definition 2.2)
;;; ------------------------------------------------------------------

(defun schemep (n S)
  (declare (xargs :guard t))
  (and (posp n)
       (summand-listp (sq n) S)
       (equal (triple-sum (sq n) S) (mmt n))))

(defthm summand-listp-of-naive-k
  (implies (and (posp n) (natp i) (natp j) (< i n) (< j n))
           (summand-listp (sq n) (naive-k n i j k))))
(defthm summand-listp-of-naive-j
  (implies (and (posp n) (natp i) (< i n))
           (summand-listp (sq n) (naive-j n i j))))
(defthm summand-listp-of-naive-i
  (implies (posp n)
           (summand-listp (sq n) (naive-i n i))))

(defthm schemep-of-naive-scheme
  (implies (posp n) (schemep n (naive-scheme n)))
  :hints (("Goal" :in-theory (enable mmt naive-scheme))))

;;; ------------------------------------------------------------------
;;; Flip and plus transformations (Definition 2.3)
;;; ------------------------------------------------------------------

;; Flip on position p of summands s and t with equal p-factors:
;;   s gets its hi-factor replaced by (s_hi + t_hi),
;;   t gets its lo-factor replaced by (t_lo + s_lo),
;; where lo < hi are the two other positions.  For p = 0 (the A position):
;;   A(x)B(x)C, A(x)B'(x)C'  -->  A(x)B(x)(C+C'), A(x)(B'+B)(x)C'.
(defun flip-results (p s u)
  (declare (xargs :guard (and (natp p) (true-listp s) (true-listp u))
                  :verify-guards nil))
  (list (set-fac (other-hi p) (bv+ (fac (other-hi p) s) (fac (other-hi p) u)) s)
        (set-fac (other-lo p) (bv+ (fac (other-lo p) u) (fac (other-lo p) s)) u)))

;; Plus on position p with pivot piv, replacing target tgt by two summands:
;;   tgt with p-factor (tgt_p + piv_p), and tgt with p-factor piv_p.
(defun plus-results (p piv tgt)
  (declare (xargs :guard (and (natp p) (true-listp piv) (true-listp tgt))
                  :verify-guards nil))
  (list (set-fac p (bv+ (fac p tgt) (fac p piv)) tgt)
        (set-fac p (fac p piv) tgt)))

(defun move-kind (m) (declare (xargs :guard (true-listp m))) (car m))
(defun move-pos (m) (declare (xargs :guard (true-listp m))) (cadr m))
(defun move-s (m) (declare (xargs :guard (true-listp m))) (caddr m))
(defun move-t (m) (declare (xargs :guard (true-listp m))) (cadddr m))

(defun flip-move (p s u) (declare (xargs :guard t)) (list :flip p s u))
(defun plus-move (p piv tgt) (declare (xargs :guard t)) (list :plus p piv tgt))

;; When is a move applicable to the list S?
(defun move-ok-p (m S)
  (declare (xargs :guard (and (true-listp m) (true-listp S))
                  :verify-guards nil))
  (let ((p (move-pos m)) (s1 (move-s m)) (u (move-t m)))
    (and (posp3 p)
         (true-listp s1) (true-listp u)
         (member-equal s1 S)
         (member-equal u (remove1-equal s1 S))
         (case (move-kind m)
           (:flip (equal (fac p s1) (fac p u)))
           (:plus t)
           (t nil)))))

(defun apply-move (L m S)
  (declare (xargs :guard (and (natp L) (true-listp m) (triple-listp L S)
                              (move-ok-p m S))
                  :verify-guards nil))
  (let ((p (move-pos m)) (s1 (move-s m)) (u (move-t m)))
    (case (move-kind m)
      (:flip (append (remove1-equal u (remove1-equal s1 S))
                     (drop-zeros L (flip-results p s1 u))))
      (t (append (remove1-equal u S)
                 (drop-zeros L (plus-results p s1 u)))))))

;;; ------------------------------------------------------------------
;;; Moves preserve the represented tensor
;;; ------------------------------------------------------------------

(defthm triplep-of-set-fac
  (implies (and (triplep L s) (bvp v) (equal (len v) (nfix L)))
           (triplep L (set-fac p v s))))

(defthm bvp-of-fac
  (implies (and (bvp (car s)) (bvp (cadr s)) (bvp (caddr s)))
           (bvp (fac p s))))
(defthm len-of-fac
  (equal (len (fac p s))
         (case p (0 (len (car s))) (1 (len (cadr s))) (t (len (caddr s))))))

(defthm triple-listp-of-flip-results
  (implies (and (triplep L s) (triplep L u))
           (triple-listp L (flip-results p s u))))

(defthm triple-listp-of-plus-results
  (implies (and (triplep L piv) (triplep L tgt))
           (triple-listp L (plus-results p piv tgt))))

;; The algebra behind a flip:
;;   A(x)B(x)C + A(x)B'(x)C' = A(x)B(x)(C+C') + A(x)(B'+B)(x)C'.
(defthm flip-preserves-sum
  (implies (and (posp3 p) (triplep L s) (triplep L u)
                (equal (fac p s) (fac p u)))
           (equal (triple-sum L (flip-results p s u))
                  (bv+ (rank1 s) (rank1 u))))
  :hints (("Goal" :in-theory (enable rank1)
                  :cases ((equal p 0) (equal p 1) (equal p 2)))))

;; The algebra behind a plus:  A'(x)B'(x)C' = (A'+A)(x)B'(x)C' + A(x)B'(x)C'.
(defthm plus-preserves-sum
  (implies (and (posp3 p) (triplep L piv) (triplep L tgt))
           (equal (triple-sum L (plus-results p piv tgt))
                  (rank1 tgt)))
  :hints (("Goal" :in-theory (enable rank1)
                  :cases ((equal p 0) (equal p 1) (equal p 2)))))

(defthm member-of-remove1-implies-member
  (implies (member-equal u (remove1-equal s1 S))
           (member-equal u S))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable remove1-equal))))

(defthm bv+-cancel-pair
  (implies (and (bvp x) (bvp y) (bvp z)
                (equal (len x) (len y)) (equal (len x) (len z)))
           (equal (bv+ (bv+ x y) (bv+ y (bv+ x z))) z))
  :hints (("Goal" :in-theory (disable bv+-associative bv+-commutative bv+-commutative-2)
                  :use ((:instance bv+-associative (x x) (y y) (z (bv+ y (bv+ x z))))
                        (:instance bv+-self-in-middle (x y) (y (bv+ x z)))
                        (:instance bv+-self-in-middle (x x) (y z))))))

(defthm apply-move-preserves-sum
  (implies (and (posp L) (triple-listp L S) (move-ok-p m S))
           (equal (triple-sum L (apply-move L m S))
                  (triple-sum L S)))
  :hints (("Goal" :in-theory (disable flip-results plus-results posp3 fac set-fac))))

(defthm triple-listp-of-drop-zeros
  (implies (triple-listp L lst) (triple-listp L (drop-zeros L lst))))

(defthm apply-move-preserves-triple-listp
  (implies (and (posp L) (triple-listp L S) (move-ok-p m S))
           (triple-listp L (apply-move L m S)))
  :hints (("Goal" :in-theory (disable flip-results plus-results posp3 fac set-fac))))

(defthm apply-move-preserves-summand-listp
  (implies (and (posp L) (summand-listp L S) (move-ok-p m S))
           (summand-listp L (apply-move L m S)))
  :hints (("Goal" :in-theory (disable flip-results plus-results posp3 fac set-fac))))

;; Remark after Definition 2.3: every vertex reached by a flip or plus
;; transformation is again a decomposition of M^(n).
(defthm apply-move-preserves-schemep
  (implies (and (schemep n S) (move-ok-p m S))
           (schemep n (apply-move (sq n) m S)))
  :hints (("Goal" :in-theory (disable apply-move move-ok-p))))

;;; ------------------------------------------------------------------
;;; Paths
;;; ------------------------------------------------------------------

(defun path-ok-p (L path S)
  (declare (xargs :guard (and (natp L) (true-listp path) (triple-listp L S))
                  :verify-guards nil))
  (if (atom path)
      t
    (and (true-listp (car path))
         (move-ok-p (car path) S)
         (path-ok-p L (cdr path) (apply-move L (car path) S)))))

(defun apply-path (L path S)
  (declare (xargs :guard (and (natp L) (true-listp path) (triple-listp L S))
                  :verify-guards nil))
  (if (atom path)
      S
    (apply-path L (cdr path) (apply-move L (car path) S))))

(defthm path-ok-p-of-append
  (equal (path-ok-p L (append p1 p2) S)
         (and (path-ok-p L p1 S)
              (path-ok-p L p2 (apply-path L p1 S))))
  :hints (("Goal" :induct (apply-path L p1 S))))

(defthm apply-path-of-append
  (equal (apply-path L (append p1 p2) S)
         (apply-path L p2 (apply-path L p1 S)))
  :hints (("Goal" :induct (apply-path L p1 S))))

(defthm apply-path-preserves-schemep
  (implies (and (schemep n S) (path-ok-p (sq n) path S))
           (schemep n (apply-path (sq n) path S)))
  :hints (("Goal" :induct (apply-path (sq n) path S)
                  :in-theory (disable schemep apply-move move-ok-p))))

(defthm apply-path-preserves-summand-listp
  (implies (and (posp L) (summand-listp L S) (path-ok-p L path S))
           (summand-listp L (apply-path L path S)))
  :hints (("Goal" :induct (apply-path L path S)
                  :in-theory (disable apply-move move-ok-p))))

(defthm apply-path-preserves-sum
  (implies (and (posp L) (triple-listp L S) (path-ok-p L path S))
           (equal (triple-sum L (apply-path L path S)) (triple-sum L S)))
  :hints (("Goal" :induct (apply-path L path S)
                  :in-theory (disable apply-move move-ok-p))))

;;; ------------------------------------------------------------------
;;; Multiset (perm) congruences: the graph lives on multisets
;;; ------------------------------------------------------------------

(defcong perm equal (move-ok-p m S) 2
  :hints (("Goal" :in-theory (disable posp3 fac))))

(defcong perm perm (apply-move L m S) 3
  :hints (("Goal" :in-theory (disable flip-results plus-results drop-zeros))))

(defun ind-path2 (L path S1 S2)
  (if (atom path)
      (list L S1 S2)
    (ind-path2 L (cdr path) (apply-move L (car path) S1) (apply-move L (car path) S2))))

(defcong perm equal (path-ok-p L path S) 3
  :hints (("Goal" :induct (ind-path2 L path S S-equiv)
                  :in-theory (disable apply-move move-ok-p))))

(defcong perm perm (apply-path L path S) 3
  :hints (("Goal" :induct (ind-path2 L path S S-equiv)
                  :in-theory (disable apply-move move-ok-p))))

(defthm schemep-when-perm
  (implies (and (perm S1 S2) (schemep n S1) (true-listp S2))
           (schemep n S2))
  :hints (("Goal" :use ((:instance triple-sum-when-perm (x S1) (y S2) (L (sq n)))))))

(defthm true-listp-of-apply-move
  (true-listp (apply-move L m S)))
(defthm true-listp-of-apply-path
  (implies (true-listp S) (true-listp (apply-path L path S))))

(in-theory (disable fac set-fac other-lo other-hi posp3 flip-results plus-results
                    move-ok-p apply-move))

;;; ------------------------------------------------------------------
;;; Observation 4.1: two identical summands can be deleted with a flip
;;; ------------------------------------------------------------------

(defun delete-pair-move (s)
  (declare (xargs :guard t))
  (flip-move 0 s s))

(defthm delete-pair-move-ok
  (implies (and (true-listp s1) (member-equal s1 S) (member-equal s1 (remove1-equal s1 S)))
           (move-ok-p (delete-pair-move s1) S))
  :hints (("Goal" :in-theory (enable move-ok-p posp3))))

(defthm apply-delete-pair-move
  (implies (and (natp L) (triplep L s1) (true-listp S))
           (equal (apply-move L (delete-pair-move s1) S)
                  (remove1-equal s1 (remove1-equal s1 S))))
  :hints (("Goal" :in-theory (enable apply-move flip-results fac set-fac other-lo other-hi))))
