; overview-prelims.lisp -- the objects, and the statement of the main theorem.
;
; First of three tours of this development: the connectivity of the flip
; graph of matrix multiplication schemes over F2, formalized in ACL2.
; This file sets up everything needed to READ the main theorem and states
; it.  How the theorem is proved is laid out in overview-proof.lisp; what
; schemes have to do with algorithms for multiplying matrices, in
; overview-algo.lisp.
;
; The two files are the long form of the ACL2 Workshop 2026 paper
; "Formalizing the Connectivity Theorem for the Matrix Multiplication Flip
; Graph in ACL2" (draft1.tex), whose page limit forced most definitions
; and theorems out.  Here every definition and theorem the paper shows or
; names appears in full, in the paper's order, with the paper's commentary
; and more.  The theorem itself is Theorem 4.1 of Medley, Gokul, Luu and
; Manolios, "GPU-Accelerated Search for Fast Matrix Multiplication over
; F2" (ALENEX 2027), which we call the companion paper below.
;
; Every definition and theorem in these files is the real one,
; restated verbatim from the books this file includes, with two omissions:
; proof hints, and the routine typing theorems in the /// sections of the
; defines.  ACL2 accepts a restated event only if it is identical to the
; original (hints aside), so certifying the files checks that the tour
; has not drifted from the development.  Certification checks the code,
; not the commentary.
;
; Notation in the commentary.  A summand is written (A,B,C) or, when the
; tensor is meant, A (x) B (x) C.  Addition of matrices is entrywise xor
; and is written +; over F2 subtraction is the same operation.  Schemes
; are multisets: "S plus two copies of s" and "S with R removed" are
; multiset operations, and the ACL2 forms are (obag::insert s (obag::insert
; s S)) and (delete-list R S).  E_ij is the unit matrix with a single 1 at
; row i, column j, indexed from 0 in the code and from 1 in the papers.
;
; Reading order.  Bit lists and matrices; summands and schemes; the flip
; and plus moves; moves, paths, and the zero-deletion convention; what a
; scheme computes; the matrix multiplication tensor and correct schemes;
; the main theorem; the standard scheme, a correct scheme for every n; the
; rank-245 scheme of the companion paper.

(in-package "ACL2")

(include-book "main")
(include-book "standard")
(include-book "rank245")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Bit lists and bit matrices
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Throughout the development we use define and defrule from the std
; library in place of defun and defthm.  This is a matter of convenience
; only.
;
; Over F2 a matrix entry is a bit, addition is bitxor, and every element
; is its own negative.  A vector is a true list of bits, and a matrix is
; a list of its rows.  Each of the two has two recognizers.  bit-list-p
; and bit-list-listp are structural and say nothing about size; bit-listnp
; and bit-matp fix the dimensions.

(define bit-list-p (x)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (bitp (car x))
         (bit-list-p (cdr x)))))

(define bit-list-listp (a)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom a)
      (null a)
    (and (bit-list-p (car a))
         (bit-list-listp (cdr a)))))

(define bit-listnp (x (n natp))
  :returns (yes/no booleanp)
  (if (zp n)
      (null x)
    (and (consp x)
         (bitp (car x))
         (bit-listnp (cdr x) (1- n)))))

(define bit-matp (a (m natp) (n natp))
  :returns (yes/no booleanp)
  :measure (nfix m)
  (if (zp m)
      (null a)
    (and (consp a)
         (bit-listnp (car a) n)
         (bit-matp (cdr a) (1- m) n))))

; The structural recognizers are the guards.  bit-list-add below calls
; bitxor, whose guard requires integers, and bit-list-p on the arguments
; is what supplies that.  The dimensioned recognizers are what the
; theorems are stated with: the facts the proofs use are about objects of
; the same size -- two lists of length n, three n x n factors, a tensor of
; n^6 bits.  Both are needed because most operations take no dimension
; argument, so their guards and :returns cannot mention an n, while a fact
; such as "the result is a bit list" is too weak for any proof to use.
; The two are related by (bit-listnp x (len x)) if and only if
; (bit-list-p x).
;
; This gives every operation the same shape: the guard and the :returns
; use the structural recognizers, and a separate theorem states that
; inputs of the right size give an output of the right size.  bit-list-add
; and its size theorem are the pattern; the size theorems of the other
; operations are the routine ones left out of this file.

(define bit-list-add ((x bit-list-p) (y bit-list-p))
  :returns (z bit-list-p)
  (if (and (consp x) (consp y))
      (cons (bitxor (car x) (car y))
            (bit-list-add (cdr x) (cdr y)))
    nil))

(defrule bit-listnp-of-bit-list-add
    (implies (and (bit-listnp x n)
                  (bit-listnp y n))
             (bit-listnp (bit-list-add x y) n)))

; bit-list-add truncates to the shorter argument, so its commutativity and
; associativity hold without hypotheses.  bit-mat-add applies it row by
; row, (bit-listn0 n) and (bit-mat0 m n) are the zero vector and the zero
; matrix, and bit-list-scale multiplies a list by a bit.

(define bit-listn0 ((n natp))
  :returns (r bit-list-p)
  (repeat n 0))

(define bit-mat0 ((m natp) (n natp))
  :returns (a bit-list-listp)
  (repeat m (bit-listn0 n)))

(define bit-mat-add ((a bit-list-listp) (b bit-list-listp))
  :returns (c bit-list-listp)
  (if (and (consp a) (consp b))
      (cons (bit-list-add (car a) (car b))
            (bit-mat-add (cdr a) (cdr b)))
    nil))

(define bit-list-scale ((b bitp) (x bit-list-p))
  :returns (z bit-list-p)
  (if (atom x)
      nil
    (cons (bitand b (car x))
          (bit-list-scale b (cdr x)))))

; Two further operations are what the tensor of a scheme is built from:
; the outer product of two bit lists, and the row-major flattening of a
; matrix.

(define bit-list-outer ((u bit-list-p) (v bit-list-p))
  :returns (z bit-list-p)
  (if (atom u)
      nil
    (append (bit-list-scale (car u) v)
            (bit-list-outer (cdr u) v))))

(define mat-flat ((a bit-list-listp))
  :returns (l bit-list-p :hyp (bit-list-listp a))
  (if (atom a)
      nil
    (append (car a) (mat-flat (cdr a)))))

; One algebraic fact about addition does the cancelling everywhere in the
; connectivity argument.  Its consequence for two lists of the same
; length, that their sum is zero if and only if they are equal, is what
; decides whether a summand vanishes.

(defrule bit-list-add-same
    (implies (bit-listnp x n)
             (equal (bit-list-add x x)
                    (bit-listn0 n))))

; Unit matrices.  (bit-unit-list j n) is the length-n vector with a single
; 1 at index j, and (bit-mat-unit i j m n) is the m x n matrix E_ij.  The
; matrix multiplication tensor below is a sum of tensors of unit matrices,
; and the deletion argument in overview-proof.lisp breaks every summand
; down to unit matrices.

(define bit-unit-list ((j natp) (n natp))
  :returns (l bit-list-p)
  (if (zp n)
      nil
    (if (zp j)
        (cons 1 (bit-listn0 (1- n)))
      (cons 0 (bit-unit-list (1- j) (1- n))))))

(define bit-mat-unit ((i natp) (j natp) (m natp) (n natp))
  :returns (a bit-list-listp)
  (if (zp m)
      nil
    (if (zp i)
        (cons (bit-unit-list j n) (bit-mat0 (1- m) n))
      (cons (bit-listn0 n) (bit-mat-unit (1- i) j (1- m) n)))))

; Lists of matrices get the same two-tier treatment.  They appear in the
; span layer of the proof, where the A-components of a list of summands
; are collected into a list of matrices.

(define bit-mat-list-p (x)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (bit-list-listp (car x))
         (bit-mat-list-p (cdr x)))))

(define bit-mat-listnp (x (m natp) (n natp))
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (bit-matp (car x) m n)
         (bit-mat-listnp (cdr x) m n))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Summands and schemes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A summand is a triple (A,B,C) of matrices, representing the rank-one
; tensor A (x) B (x) C, and a scheme is a multiset of summands.  This is
; the companion paper's definition of the vertices of the flip graph,
; except that the paper also requires the summands to sum to the matrix
; multiplication tensor; that condition is deferred to correct-schemep
; below, and schemep recognizes the multiset structure alone.
;
; mat-triplep is the structural recognizer, a list of three matrices with
; no condition on size.  The accessors summand-A, summand-B and summand-C
; are car, cadr and caddr, and both spellings occur in the development.
; summandp recognizes a summand of an n-scheme: three n x n factors, none
; of which is zero.

(define mat-triplep (s)
  :enabled t
  :returns (yes/no booleanp)
  (and (true-listp s)
       (equal (len s) 3)
       (bit-list-listp (car s))
       (bit-list-listp (cadr s))
       (bit-list-listp (caddr s))))

(define mat-triple-listp (l)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (mat-triplep (car l))
         (mat-triple-listp (cdr l)))))

(define summand ((a bit-list-listp) (b bit-list-listp) (c bit-list-listp))
  :enabled t
  :returns (s mat-triplep :hyp :guard)
  (list a b c))

(define summand-A ((s mat-triplep))
  :enabled t
  :returns (a bit-list-listp :hyp :guard)
  (car s))

(define summand-B ((s mat-triplep))
  :enabled t
  :returns (b bit-list-listp :hyp :guard)
  (cadr s))

(define summand-C ((s mat-triplep))
  :enabled t
  :returns (c bit-list-listp :hyp :guard)
  (caddr s))

(define summand0p ((s mat-triplep) (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (or (equal (summand-A s) (bit-mat0 n n))
      (equal (summand-B s) (bit-mat0 n n))
      (equal (summand-C s) (bit-mat0 n n))))

(define summandp (s (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (and (mat-triplep s)
       (bit-matp (car s) n n)
       (bit-matp (cadr s) n n)
       (bit-matp (caddr s) n n)
       (not (summand0p s n))))

(define summand-listp (x (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (summandp (car x) n)
         (summand-listp (cdr x) n))))

; We represent a scheme as an obag from the std/obags library, that is, a
; list sorted by the total order << in which elements may repeat.
; Multiplicity is preserved, and two schemes are equal if and only if they
; are equal as lists.  The rank of a scheme is its number of summands.

(define schemep (x (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (and (obag::bagp x)
       (summand-listp x n)))

(define scheme-rank (x)
  :enabled t
  :returns (r natp)
  (len x))

; summand-dimp is summandp without the nonzero condition, and
; summand-dim-listp is its list form.  They are the guards of the span
; layer of the proof, which manipulates lists of summands whose factors
; may be zero.

(define summand-dimp (s (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (and (mat-triplep s)
       (bit-matp (car s) n n)
       (bit-matp (cadr s) n n)
       (bit-matp (caddr s) n n)))

(define summand-dim-listp (l (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (summand-dimp (car l) n)
         (summand-dim-listp (cdr l) n))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Flip and plus
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We write s[p] for the factor of a summand s at position p in {0,1,2},
; where 0, 1, 2 stand for A, B, C, and s[p -> M] for s with that factor
; replaced by M.  These are the functions summand-get-pos and
; summand-set-pos.  The functions pos-next and pos-prev step through the
; three positions cyclically.

(define pos-next ((p natp))
  :enabled t
  (case p (0 1) (1 2) (t 0)))

(define pos-prev ((p natp))
  :enabled t
  (case p (0 2) (1 0) (t 1)))

(define summand-get-pos ((s mat-triplep) p)
  :enabled t
  :returns (m bit-list-listp :hyp :guard)
  (case p
    (0 (car s))
    (1 (cadr s))
    (t (caddr s))))

(define summand-set-pos ((s mat-triplep) p (m bit-list-listp))
  :enabled t
  :returns (s1 mat-triplep :hyp :guard)
  (case p
    (0 (summand m (cadr s) (caddr s)))
    (1 (summand (car s) m (caddr s)))
    (t (summand (car s) (cadr s) m))))

; Both moves take two summands that agree at position p and give back two
; summands.  A flip consumes both inputs; a plus consumes only its target
; and reads its pivot.

(define flip ((s1 mat-triplep) (s2 mat-triplep) (p natp))
  :enabled t
  :returns (l mat-triple-listp :hyp :guard)
  (let ((q (pos-next p))
        (r (pos-prev p)))
    (list (summand-set-pos s1 r (bit-mat-add (summand-get-pos s1 r)
                                             (summand-get-pos s2 r)))
          (summand-set-pos s2 q (bit-mat-add (summand-get-pos s2 q)
                                             (summand-get-pos s1 q))))))

(define plus ((target mat-triplep) (pivot mat-triplep) (p natp))
  :enabled t
  :returns (l mat-triple-listp :hyp :guard)
  (list (summand-set-pos target p (bit-mat-add (summand-get-pos target p)
                                               (summand-get-pos pivot p)))
        (summand-set-pos target p (summand-get-pos pivot p))))

; These are the two transformations of the companion paper's definition
; of the edges.  Take p = 0.  Applied to (A,B,C) and (A,B',C'), flip
; returns (A,B,C+C') and (A,B'+B,C'), while the paper gives
; A (x) B (x) (C+C') and A' (x) (B'-B) (x) C'; over F2 subtraction is
; addition.  Applied to a target (A',B',C') and a pivot (A,B,C), plus
; returns (A'+A,B',C') and (A,B',C'), while the paper replaces the second
; summand by (A'-A) (x) B' (x) C' and A (x) B' (x) C'.  The other
; positions are obtained by cyclic rotation.  A flip is sum-preserving
; because the cross terms cancel in characteristic two; a plus is
; sum-preserving because (A' + A) + A = A'.
;
; The paper's definition ends both cases with the words "any zero summands
; deleted".  In our development every insertion into a scheme goes through
; insert-all-nonzero, which drops any summand that has a zero factor.

(define insert-all-nonzero ((l mat-triple-listp) (s obag::bagp) (n natp))
  :enabled t
  :returns (s1 obag::bagp :hyp (obag::bagp s))
  (if (atom l)
      s
    (if (summand0p (car l) n)
        (insert-all-nonzero (cdr l) s n)
      (obag::insert (car l) (insert-all-nonzero (cdr l) s n)))))

; Zero summands are thus excluded twice, since summandp does not admit
; them and insert-all-nonzero does not insert them.  As a consequence the
; lemmas of the proof need no hypotheses to rule out degenerate cases.
; When the output of a construction would be zero it is simply dropped,
; and the identity we prove still holds.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Moves and paths
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A move is a list (:flip p s1 s2) or (:plus p s1 s2), giving the kind of
; transformation, the position, and the two summands involved.  For a
; plus, s1 is the target and s2 the pivot.

(define move-kind ((move true-listp)) :enabled t (car move))

(define move-pos ((move true-listp)) :enabled t (cadr move))

(define move-s1 ((move true-listp)) :enabled t (caddr move))

(define move-s2 ((move true-listp)) :enabled t (cadddr move))

(define move-p (move)
  :enabled t
  :returns (yes/no booleanp)
  (and (true-listp move)
       (equal (len move) 4)
       (or (eq (move-kind move) :flip)
           (eq (move-kind move) :plus))
       (natp (move-pos move))
       (< (move-pos move) 3)
       (mat-triplep (move-s1 move))
       (mat-triplep (move-s2 move))))

(define move-list-p (moves)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom moves)
      (null moves)
    (and (move-p (car moves))
         (move-list-p (cdr moves)))))

; A move is valid on a scheme if the two summands are present in it and,
; for a flip, agree at position p.  When the two summands are the same,
; presence means multiplicity at least two.  A bag does not distinguish
; occurrences of an element, so membership alone would allow a move to
; consume the same summand twice.

(define move-validp ((move move-p) (sch obag::bagp))
  :enabled t
  :returns (yes/no booleanp)
  (case (move-kind move)
    (:flip (and (natp (move-pos move))
                (< (move-pos move) 3)
                (if (equal (move-s1 move) (move-s2 move))
                    (<= 2 (obag::occs (move-s1 move) sch))
                  (and (obag::in (move-s1 move) sch)
                       (obag::in (move-s2 move) sch)
                       (equal (summand-get-pos (move-s1 move) (move-pos move))
                              (summand-get-pos (move-s2 move) (move-pos move)))))))
    (:plus (and (natp (move-pos move))
                (< (move-pos move) 3)
                (if (equal (move-s1 move) (move-s2 move))
                    (<= 2 (obag::occs (move-s1 move) sch))
                  (and (obag::in (move-s1 move) sch)
                       (obag::in (move-s2 move) sch)))))
    (t nil)))

; Applying a move deletes the summands it consumes, namely the target of a
; plus or both summands of a flip, and inserts the outputs.  A path is a
; list of moves.  It is valid if each move is valid on the scheme produced
; by the moves before it.

(define apply-move ((move move-p) (sch obag::bagp) (n natp))
  :returns (sch1 obag::bagp :hyp (obag::bagp sch))
  (case (move-kind move)
    (:plus (insert-all-nonzero (plus (move-s1 move) (move-s2 move) (move-pos move))
                               (obag::delete (move-s1 move) sch)
                               n))
    (:flip (insert-all-nonzero (flip (move-s1 move) (move-s2 move) (move-pos move))
                               (obag::delete (move-s1 move)
                                             (obag::delete (move-s2 move) sch))
                               n))
    (t sch)))

(define apply-moves ((moves move-list-p) (sch obag::bagp) (n natp))
  :returns (sch1 obag::bagp :hyp (obag::bagp sch))
  (if (atom moves)
      sch
    (apply-moves (cdr moves) (apply-move (car moves) sch n) n)))

(define path-validp ((moves move-list-p) (sch obag::bagp) (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (if (atom moves)
      t
    (and (move-validp (car moves) sch)
         (path-validp (cdr moves) (apply-move (car moves) sch n) n))))

; A valid path takes an n-scheme to an n-scheme.

(defrule schemep-of-apply-moves
    (implies (and (schemep sch n)
                  (path-validp moves sch n))
             (schemep (apply-moves moves sch n) n)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; What a scheme computes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We represent an order-three tensor over n x n matrices as a flat bit
; list of length n^6.  The tensor of a summand is the outer product of the
; row-major flattenings of its three factors, and the tensor of a scheme,
; scheme-sum, is the sum of the tensors of its summands.

(define tensor ((a bit-list-listp) (b bit-list-listp) (c bit-list-listp))
  :returns (tt bit-list-p :hyp :guard)
  (bit-list-outer (mat-flat a)
                  (bit-list-outer (mat-flat b) (mat-flat c))))

(define summand-tensor ((s mat-triplep))
  :enabled t
  (tensor (car s) (cadr s) (caddr s)))

(define scheme-sum ((l mat-triple-listp) (n natp))
  :returns (tt bit-list-p)
  (if (atom l)
      (bit-listn0 (* n n n n n n))
    (bit-list-add (summand-tensor (car l))
                  (scheme-sum (cdr l) n))))

; The matrix multiplication tensor is the sum over all i,j,k < n of
; E_ij (x) E_jk (x) E_ik.  We define it with three nested recursions, one
; for each of the three indices.  mm-tensor-3 sums over k for fixed i and
; j; mm-tensor-2 sums the result over j for fixed i; mm-tensor-1 sums that
; over i; and mm-tensor starts all three indices at n.  Each level
; recurses downward on its own index, and each has its own length theorem
; so that the length n^6 of the result is known at every level.
;
; This is the sum given as Lemma lemma:mmt in the paper, not the paper's
; definition of the tensor by its action on a pair of matrices.  That the
; two agree is not formalized; see the discussion of adequacy in the
; paper's future work.

(define mm-tensor-3 ((i natp) (j natp) (k natp) (n natp))
  :returns (tt bit-list-p)
  :verify-guards :after-returns
  (if (zp k)
      (bit-listn0 (* n n n n n n))
    (bit-list-add
     (tensor (bit-mat-unit i j n n)
             (bit-mat-unit j (1- k) n n)
             (bit-mat-unit i (1- k) n n))
     (mm-tensor-3 i j (1- k) n))))

(define mm-tensor-2 ((i natp) (j natp) (n natp))
  :returns (tt bit-list-p)
  :verify-guards :after-returns
  (if (zp j)
      (bit-listn0 (* n n n n n n))
    (bit-list-add (mm-tensor-3 i (1- j) n n)
                  (mm-tensor-2 i (1- j) n))))

(define mm-tensor-1 ((i natp) (n natp))
  :returns (tt bit-list-p)
  :verify-guards :after-returns
  (if (zp i)
      (bit-listn0 (* n n n n n n))
    (bit-list-add (mm-tensor-2 (1- i) n n)
                  (mm-tensor-1 (1- i) n))))

(define mm-tensor ((n natp))
  :returns (tt bit-list-p)
  (mm-tensor-1 n n))

; A scheme is correct if it is well formed and its tensor is mm-tensor.
; This is the companion paper's notion of scheme, and correct schemes are
; exactly the bilinear algorithms for n x n matrix multiplication over F2,
; a scheme of rank r using r multiplications.

(define correct-schemep (sch (n natp))
  :returns (yes/no booleanp)
  (and (schemep sch n)
       (equal (scheme-sum sch n) (mm-tensor n))))

; A valid path preserves the tensor of a scheme and therefore preserves
; correctness.  The proof uses the fact that over F2 deleting a summand
; changes the tensor of a scheme in the same way as inserting it, so that
; the effect of a single move follows from the bilinearity of tensor in
; each factor.  The case of a path follows by induction.  This is the
; invariant every lemma of the proof relies on to keep its hypotheses
; alive from one step to the next.

(defruled scheme-sum-of-apply-moves
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (path-validp moves sch n)
                (natp n))
           (equal (scheme-sum (apply-moves moves sch n) n)
                  (scheme-sum sch n))))

(defrule correct-schemep-of-apply-moves
  (implies (and (correct-schemep sch n)
                (path-validp moves sch n)
                (natp n))
           (correct-schemep (apply-moves moves sch n) n)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The main theorem (thm:main)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; For any two correct schemes of the same size n >= 2, the path main-path,
; defined at the end of overview-proof.lisp, is valid from the first, and
; applying it yields the second.
;
; The theorem contains no existential quantifier.  The path is a function
; of the two schemes, and the theorem states what applying it produces.
; The formal versions of the four lemmas of the informal proof have the
; same form: each names a function that computes a path, and states that
; the path is valid and that applying it lands on an explicitly named
; scheme.  Naming the destination is what lets each lemma hand its result
; to the next.

(defrule flip-plus-connectivity
  (implies (and (correct-schemep sch n)
                (correct-schemep sch2 n)
                (natp n) (<= 2 n))
           (b* ((path (main-path sch sch2 n))
                (res (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal res sch2)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Existence: the standard algorithm is a correct scheme
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The main theorem is about correct schemes, and this shows there is one
; for every n.  The standard algorithm is defined by the same three
; nested recursions as mm-tensor, inserting the summand (E_ij, E_jk, E_ik)
; into a bag at each step, so that scheme-sum-of-insert and
; scheme-sum-of-insert-list match the three levels of the tensor one by
; one.  Its rank is n^3, and at n = 2 it is exactly *arb-std2* below.

(define standard-scheme-3 ((i natp) (j natp) (k natp) (n natp))
  :returns (sch obag::bagp)
  :verify-guards :after-returns
  (if (zp k)
      nil
    (obag::insert (summand (bit-mat-unit i j n n)
                           (bit-mat-unit j (1- k) n n)
                           (bit-mat-unit i (1- k) n n))
                  (standard-scheme-3 i j (1- k) n))))

(define standard-scheme-2 ((i natp) (j natp) (n natp))
  :returns (sch obag::bagp)
  :verify-guards :after-returns
  (if (zp j)
      nil
    (insert-list (standard-scheme-3 i (1- j) n n)
                 (standard-scheme-2 i (1- j) n))))

(define standard-scheme-1 ((i natp) (n natp))
  :returns (sch obag::bagp)
  :verify-guards :after-returns
  (if (zp i)
      nil
    (insert-list (standard-scheme-2 (1- i) n n)
                 (standard-scheme-1 (1- i) n))))

(define standard-scheme ((n natp))
  :returns (sch obag::bagp)
  (standard-scheme-1 n n))

(defrule scheme-sum-of-standard-scheme
  (implies (natp n)
           (equal (scheme-sum (standard-scheme n) n)
                  (mm-tensor n))))

(defrule correct-schemep-of-standard-scheme
  (implies (natp n)
           (correct-schemep (standard-scheme n) n)))

(defrule scheme-rank-of-standard-scheme
  (implies (natp n)
           (equal (scheme-rank (standard-scheme n))
                  (* n n n))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The rank-245 scheme of the companion paper
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Appendix A of the companion paper gives a rank-245 scheme for 7 x 7
; matrix multiplication over F2 as a compressed block of 245 triples of
; 49-bit masks, bit 7*i+j of a mask being entry [i,j].  rank245-data.lisp
; holds the decoded masks; mask-mat turns a mask into a 7 x 7 matrix and
; masks-scheme builds the bag.  That the result is a correct scheme is
; checked by evaluation (about eight seconds), and by the main theorem it
; is reachable from the standard rank-343 scheme.  The last theorem is a
; pure instantiation of flip-plus-connectivity; its hint keeps the theory
; minimal so that ACL2 does not try to run main-path on the concrete
; schemes.

(define mask-row ((m natp) (i natp) (j natp) (n natp))
  :guard (<= j n)
  :returns (r bit-list-p)
  (if (zp j)
      nil
    (cons (if (logbitp (+ (* n i) (- n j)) m) 1 0)
          (mask-row m i (1- j) n))))

(define mask-rows ((m natp) (i natp) (n natp))
  :guard (<= i n)
  :returns (a bit-list-listp)
  (if (zp i)
      nil
    (cons (mask-row m (- n i) n n)
          (mask-rows m (1- i) n))))

(define mask-mat ((m natp) (n natp))
  :returns (a bit-list-listp)
  (mask-rows m n n))

(define masks-scheme ((l mask-triple-listp) (n natp))
  :returns (sch obag::bagp)
  :verify-guards :after-returns
  (if (atom l)
      nil
    (obag::insert (summand (mask-mat (first (car l)) n)
                           (mask-mat (second (car l)) n)
                           (mask-mat (third (car l)) n))
                  (masks-scheme (cdr l) n))))

(defconst *rank245-scheme* (masks-scheme *rank245-masks* 7))

(defrule rank245-has-rank-245
  (equal (scheme-rank *rank245-scheme*) 245))

(defrule rank245-is-correct
  (correct-schemep *rank245-scheme* 7))

(defrule rank245-reachable-from-standard
  (b* ((path (main-path (standard-scheme 7) *rank245-scheme* 7))
       (res (apply-moves path (standard-scheme 7) 7)))
    (and (path-validp path (standard-scheme 7) 7)
         (equal res *rank245-scheme*))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Open items (not part of the tour)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; bound on the size of path

;; run main-path on some examples

;; main-path2 shorter length

;; upper bound highest rank found -> saturate flip graph
