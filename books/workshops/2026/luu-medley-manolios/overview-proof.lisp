; overview-proof.lisp -- how the main theorem is proved.
;
; Second of the three tours; read overview-prelims.lisp first for the
; objects, the notation used in the commentary, and the statement being
; proved (overview-algo.lisp, on schemes and algorithms, is independent of
; this file).  The parts below follow the paper: the proof informally; the
; span lemma and the chain construction; adding summands; deleting
; summands; assembling the connectivity path.  The last part runs the
; construction at n = 2.
;
; As in the prelims, every definition and theorem is the real one,
; restated verbatim with proof hints and routine typing theorems left
; out.  Every path in the development is computed by a function, and
; every lemma about one says two things: the path is valid, and applying
; it lands on an explicitly named scheme.

(in-package "ACL2")

(include-book "overview-prelims")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The proof, informally
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorem and the lemmas it rests on, as stated in the companion
; paper.  The labels in brackets are the ones used in the paper and in
; the commentary below.
;
; THEOREM [thm:main] (Flip-plus connectivity).  Over F2, for every
; n >= 2, the directed matrix multiplication flip graph whose edges are
; ordinary flip and plus transformations is strongly connected.
; Equivalently, for any two schemes S and S' for the matrix
; multiplication tensor, there is a directed path from S to S' using only
; flip and plus transformations.
;
; LEMMA [lemma:mmt] (Matrix multiplication tensor).  The matrix
; multiplication tensor for multiplying two n x n matrices is the sum,
; over all i, j, k from 1 to n, of E_ij (x) E_jk (x) E_ik, where E_ij is
; the n x n matrix with a 1 at position (i,j) and zeros everywhere else.
;
; LEMMA [lemma:span] (Spanning).  Let S be a scheme for the matrix
; multiplication tensor.  Then the A-components of the summands of S span
; the full space of n x n matrices, and likewise for the B- and
; C-components.
;
; LEMMA [lemma:add-duplicate-sum] (Adding a duplicate sum).  Let S be a
; scheme over F2, and suppose A (x) B (x) C and A' (x) B' (x) C' are
; summands of S.  Let X = A + A'.  Then there is a path from S to S plus
; two copies of X (x) B (x) C.  Analogous statements hold for the B and C
; positions.
;
; LEMMA [lem:add-arbitrary] (Adding an arbitrary summand).  Let S be a
; scheme over F2 with n >= 2, and let X, Y, Z be nonzero n x n matrices.
; Then there is a path from S to S plus two copies of X (x) Y (x) Z.
;
; LEMMA [lemma:zero-subset] (Removing a zero-summing submultiset).  Let S
; be a scheme over F2 with n >= 2 and let R be a submultiset of S whose
; summands sum to zero.  Then there is a path from S to S with R removed.
;
; The proof depends on one property of F2: two identical summands cancel,
; so a flip of a summand with itself removes both copies.  The task is
; therefore to produce identical pairs.  lemma:add-duplicate-sum adds two
; copies of a combined summand.  It is the only lemma that adds summands;
; the remaining lemmas are built from it.  Since the A-component of the
; combined summand is the sum of two A-components already in the scheme,
; iterating the lemma reaches any matrix in their span, and by lemma:span
; that span is the whole space.  Repeating the argument in the B and C
; positions gives lem:add-arbitrary.  lemma:mmt gives the explicit form
; of the tensor from which the proof of the spanning lemma reads off
; entries.  lemma:zero-subset removes a zero-summing submultiset by
; decomposing its summands into tensors of unit matrices, which must then
; occur with even multiplicity and can be deleted in identical pairs.
; thm:main follows.  Given schemes S and S', we add two copies of every
; summand of S' to S by lem:add-arbitrary, obtaining S plus S' plus S'.
; The submultiset S plus S' sums to zero, so lemma:zero-subset removes it
; and S' remains.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lemma:mmt -- the entry law of the matrix multiplication tensor
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We formalize lemma:mmt as an entry law.  The entry of the flat n^6-bit
; vector at the index of ((ia,ja),(ib,jb),(ic,jc)) is 1 if ja = ib,
; ia = ic and jb = jc, and 0 otherwise.  Every fact about matrix
; multiplication used in the development is derived from this theorem.
; We proved it by induction over the three levels of mm-tensor, using
; lemmas that give the nth entry of each operation on bit lists; together
; these give the entry of a tensor in terms of the entries of its factors.

(define mat-entry ((i natp) (j natp) (a bit-list-listp))
  :enabled t
  (nth j (nth i a)))

(defrule nth-of-mm-tensor
  (implies (and (natp n)
                (natp ia) (natp ja) (natp ib) (natp jb) (natp ic) (natp jc)
                (< ia n) (< ja n) (< ib n) (< jb n) (< ic n) (< jc n))
           (equal (nth (+ jc (* ic n) (* jb n n) (* ib n n n)
                          (* ja n n n n) (* ia n n n n n))
                       (mm-tensor n))
                  (if (and (equal ia ic) (equal ja ib) (equal jb jc))
                      1 0))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lemma:span -- a correct scheme spans the whole matrix space
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We state the spanning lemma with the linear combination made explicit.
; For fixed i and j and any k, the function a-witness-sum adds the
; A-factors of those summands whose coefficient B[j,k] * C[i,k] is 1.  On
; a correct scheme the result is the unit matrix E_ij.

(define a-witness-sum ((l mat-triple-listp) (i natp) (j natp) (k natp)
                       (n natp))
  :guard (and (summand-dim-listp l n) (< i n) (< j n) (< k n))
  :returns (w bit-list-listp :hyp (mat-triple-listp l))
  :verify-guards :after-returns
  (if (atom l)
      (bit-mat0 n n)
    (if (equal (bitand (mat-entry j k (cadr (car l)))
                       (mat-entry i k (caddr (car l))))
               1)
        (bit-mat-add (car (car l))
                     (a-witness-sum (cdr l) i j k n))
      (a-witness-sum (cdr l) i j k n))))

(defrule span-lemma
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (natp j) (natp k)
                (< i n) (< j n) (< k n))
           (equal (a-witness-sum sch i j k n)
                  (bit-mat-unit i j n n))))

; The proof compares entries.  Entry (a,b) of the witness sum equals the
; entry of the tensor of the scheme at the index of ((a,b),(j,k),(i,k)).
; Since the scheme is correct, this is an entry of mm-tensor, and by the
; entry law it is 1 exactly when a = i and b = j, which is entry (a,b) of
; E_ij.  To conclude that the two matrices are equal without a
; quantifier, mat-diff-pos computes the first position at which two
; matrices differ, and mat-diff-pos-correct says that two unequal
; well-formed matrices differ at a valid position.

(define first-diff-index (x y)
  :returns (i natp)
  (cond ((or (atom x) (atom y)) 0)
        ((equal (car x) (car y))
         (+ 1 (first-diff-index (cdr x) (cdr y))))
        (t 0)))

(define mat-diff-pos ((x true-listp) (y true-listp))
  :returns (pos consp)
  (let ((i (first-diff-index x y)))
    (cons i (first-diff-index (nth i x) (nth i y)))))

(defruled mat-diff-pos-correct
  (implies (and (bit-matp x m n)
                (bit-matp y m n)
                (natp m) (natp n)
                (not (equal x y)))
           (let* ((pos (mat-diff-pos x y))
                  (i (car pos))
                  (j (cdr pos)))
             (and (< i m)
                  (< j n)
                  (not (equal (mat-entry i j x)
                              (mat-entry i j y)))))))

; b-span-lemma and c-span-lemma treat the other two components in the
; same way, with b-witness-sum and c-witness-sum the mirror images of
; a-witness-sum.  Only the A versions are used by the rest of the
; development, since the B and C legs of the construction reuse the
; A-position functions through the symmetry described under "Adding an
; arbitrary summand" below.

(defrule b-span-lemma
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (natp j) (natp k)
                (< i n) (< j n) (< k n))
           (equal (b-witness-sum sch i j k n)
                  (bit-mat-unit j k n n))))

(defrule c-span-lemma
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (natp j) (natp k)
                (< i n) (< j n) (< k n))
           (equal (c-witness-sum sch i j k n)
                  (bit-mat-unit i k n n))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; From spanning to a chain
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lem:add-arbitrary requires more than the spanning lemma provides.  For
; an arbitrary nonzero X it needs a list of summands u1, ..., uk of the
; scheme whose A-components, added to the A-component A0 of a chosen seed
; summand, sum to X, and it needs each partial sum A0, A0 + A(u1),
; A0 + A(u1) + A(u2), ... to be nonzero, because the construction under
; "Adding summands" carries a summand with that A-component and a zero
; component would make it vanish on insertion.  The spanning lemma says
; such a chain EXISTS; a path cannot be built from an existence
; statement, so this part computes one.  The construction has four
; stages:
;
;   scheme S, target matrix X
;        |  find-summand-a-neq: the first summand whose A-component
;        |  differs from X
;        v
;   seed s0 = (A0, B0, C0)
;        |  basis-new: keep a summand iff its A-component is not in the
;        |  span of the A-components already kept
;        v
;   pool of summands, seed last                   (arb-basis)
;        |  span-witness on the target X + A0 over the pool's
;        |  A-components
;        v
;   one bit per pool element                      (arb-coeffs)
;        |  select-summands: the pool summands whose bit is 1
;        v
;   chain u1, ..., uk                             (arb-us)
;
; The chain is consumed by grow-chain under "Adding summands".
;
; The construction is built on one predicate, which decides whether a
; matrix is the sum of some sublist of a list of matrices.  Over F2 the
; only coefficients are 0 and 1, so this can be decided by considering,
; for each element of the list, whether to skip it or to use it and
; subtract it from the target.

(define in-spanp ((x bit-list-listp) (mats bit-mat-list-p) (m natp) (n natp))
  :returns (yes/no booleanp)
  (if (atom mats)
      (equal x (bit-mat0 m n))
    (or (in-spanp x (cdr mats) m n)
        (in-spanp (bit-mat-add x (car mats)) (cdr mats) m n))))

; in-spanp takes time exponential in the length of its list.  We did not
; attempt to improve on this.  Our interest is in proving the theorem,
; not in running the construction, and none of these functions is
; intended to be executed on schemes of realistic size.  The definition
; has the advantage that its two branches, skipping an element or using
; it, are exactly the choices a witness must record, so the witness
; function below follows the same recursion and its correctness proof
; follows the same induction.  We considered two alternatives.  An
; existential quantifier introduced with defun-sk cannot be executed and
; is awkward to use in rewriting, and Gaussian elimination over F2 would
; require more definitions and more proof for an efficiency we do not
; need.
;
; in-spanp is asked one question twice over, about two different lists.
; In basis-new below it is asked of each candidate summand against the
; pile of summands kept so far, which grows: is this one already makeable
; from what I have?  In span-witness it is asked of the target against
; the pool elements not yet visited, which shrinks: can I still reach the
; target without this element?
;
; In terms of in-spanp, the spanning lemma states that every matrix is in
; the span of the A-components of a correct scheme.  The proof combines
; span-lemma with the fact that the unit matrices span the whole space.

(define a-components ((l mat-triple-listp))
  :returns (mats bit-mat-list-p :hyp :guard)
  (if (atom l)
      nil
    (cons (car (car l)) (a-components (cdr l)))))

(defruled a-components-span-everything
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (bit-matp y n n))
           (in-spanp y (a-components sch) n n)))

; The witness.  span-witness traverses the list and applies in-spanp to
; the target at each element.  If the target is still in the span of the
; remaining elements, the current element is not needed and its bit is 0.
; Otherwise it is needed, its bit is 1, and it is subtracted from the
; target.  lincomb adds the elements whose bit is 1.  If the target is in
; the span, the bits reproduce it.

(define span-witness ((x bit-list-listp) (mats bit-mat-list-p) (m natp) (n natp))
  :returns (coeffs bit-list-p)
  (if (atom mats)
      nil
    (if (in-spanp x (cdr mats) m n)
        (cons 0 (span-witness x (cdr mats) m n))
      (cons 1 (span-witness (bit-mat-add x (car mats)) (cdr mats) m n)))))

(define lincomb ((coeffs bit-list-p) (mats bit-mat-list-p) (m natp) (n natp))
  :measure (acl2-count mats)
  :returns (x bit-list-listp :hyp (bit-mat-list-p mats))
  (if (atom mats)
      (bit-mat0 m n)
    (if (equal (car coeffs) 1)
        (bit-mat-add (car mats)
                     (lincomb (cdr coeffs) (cdr mats) m n))
      (lincomb (cdr coeffs) (cdr mats) m n))))

(defrule lincomb-of-span-witness
  (implies (and (in-spanp x mats m n)
                (bit-matp x m n)
                (bit-mat-listnp mats m n))
           (equal (lincomb (span-witness x mats m n) mats m n)
                  x)))

; The seed and the pool.  The seed is the first summand of the scheme
; whose A-component differs from X.  Such a summand exists when n >= 2,
; since if every A-component were equal to X they would span only {0, X},
; contradicting a-components-span-everything.  Its A-component A0 is the
; starting point of the chain, and its B- and C-components are carried
; unchanged through the construction under "Adding summands".
; find-summand-a-neq returns nil when there is no such summand, which is
; why arb-basis checks its result with mat-triplep before using it.

(define find-summand-a-neq ((l mat-triple-listp) (x bit-list-listp))
  :returns (s (or (null s) (mat-triplep s))
              :hyp :guard)
  (if (atom l)
      nil
    (if (equal (car (car l)) x)
        (find-summand-a-neq (cdr l) x)
      (car l))))

; basis-new traverses the summands of the scheme, starting with the seed
; already accumulated, and keeps a summand only if its A-component is not
; in the span of the A-components already kept.  The pool, arb-basis,
; consists of the summands it keeps, with the seed appended at the end.

(define basis-new ((l mat-triple-listp) (acc mat-triple-listp) (n natp))
  :returns (ws mat-triple-listp :hyp :guard)
  (if (atom l)
      nil
    (if (in-spanp (car (car l)) (a-components acc) n n)
        (basis-new (cdr l) acc n)
      (append (basis-new (cdr l) (cons (car l) acc) n)
              (list (car l))))))

(define arb-basis ((sch mat-triple-listp) (x bit-list-listp) (n natp))
  :returns (bs mat-triple-listp :hyp :guard)
  (b* ((s0 (find-summand-a-neq sch x))
       ((unless (mat-triplep s0)) nil))
    (append (basis-new sch (list s0) n)
            (list s0))))

; Two theorems establish that the pool is a basis.  Nothing is lost by
; discarding: every matrix in the span of the A-components of the scheme
; is in the span of those of the pool, so the pool spans the whole space
; just as the whole scheme did (arb-basis-spans).  What the discarding
; buys is independence, in the sense that no element of the pool is in
; the span of the elements after it (independentp-of-basis-new).

(define independentp ((mats bit-mat-list-p) (m natp) (n natp))
  :returns (yes/no booleanp)
  (if (atom mats)
      t
    (and (not (in-spanp (car mats) (cdr mats) m n))
         (independentp (cdr mats) m n))))

(defruled arb-basis-spans
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n)
                (bit-matp y n n))
           (in-spanp y (a-components (arb-basis sch x n)) n n)))

(defruled independentp-of-basis-new
  (implies (and (independentp (a-components acc) n n)
                (summand-dim-listp l n)
                (summand-dim-listp acc n)
                (natp n))
           (independentp (a-components (append (basis-new l acc n) acc)) n n)))

; The chain.  It starts at A0 and must end at X, so the target passed to
; span-witness is X + A0.  arb-coeffs computes the resulting bit for each
; pool element, and arb-us selects the pool summands whose bit is 1.
; Their A-components sum to X + A0 (lincomb-of-arb-coeffs).

(define arb-coeffs ((sch mat-triple-listp) (x bit-list-listp) (n natp))
  :returns (coeffs bit-list-p)
  (span-witness (bit-mat-add x (car (find-summand-a-neq sch x)))
                (a-components (arb-basis sch x n))
                n n))

(define select-summands ((coeffs bit-list-p) (l mat-triple-listp))
  :measure (acl2-count l)
  :returns (us mat-triple-listp :hyp (mat-triple-listp l))
  (if (atom l)
      nil
    (if (equal (car coeffs) 1)
        (cons (car l) (select-summands (cdr coeffs) (cdr l)))
      (select-summands (cdr coeffs) (cdr l)))))

(define arb-us ((sch mat-triple-listp) (x bit-list-listp) (n natp))
  :returns (us mat-triple-listp :hyp :guard)
  (select-summands (arb-coeffs sch x n) (arb-basis sch x n)))

(defruled lincomb-of-arb-coeffs
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n))
           (equal (lincomb (arb-coeffs sch x n)
                           (a-components (arb-basis sch x n)) n n)
                  (bit-mat-add x (car (find-summand-a-neq sch x))))))

; Independence is what guarantees that the partial sums are nonzero.  The
; predicate select-chain-okp expresses the condition in terms of the
; bits: starting from p, every running total along the selected elements
; is nonzero, and so is the final total.  It holds whenever p together
; with the A-components of the pool is independent.

(define select-chain-okp ((p bit-list-listp) (coeffs bit-list-p)
                          (l mat-triple-listp) (n natp))
  :measure (acl2-count l)
  :returns (yes/no booleanp)
  (if (atom l)
      (not (equal p (bit-mat0 n n)))
    (if (equal (car coeffs) 1)
        (and (not (equal p (bit-mat0 n n)))
             (select-chain-okp (bit-mat-add p (car (car l)))
                               (cdr coeffs) (cdr l) n))
      (select-chain-okp p (cdr coeffs) (cdr l) n))))

(defruled select-chain-okp-when-independent
  (implies (and (independentp (cons p (a-components l)) n n)
                (bit-matp p n n)
                (summand-dim-listp l n)
                (natp n))
           (select-chain-okp p c l n)))

; This is the reason the seed is placed last in the pool.  The
; combination that reaches X + A0 may or may not use the A-component of
; the seed itself.  If it does, then because the seed is last it is used
; at the final step, where the running total is X, which is nonzero by
; hypothesis.  Every earlier total contains A0 and is a nontrivial
; combination of independent matrices, hence nonzero.  The case
; distinction on the coefficient of the seed that appears in the informal
; proof therefore does not arise in the construction or in the proofs; it
; is handled by the order of the list.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lemma:add-duplicate-sum -- adding a duplicate sum
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The informal proof of lemma:add-duplicate-sum exhibits a sequence of
; moves.  We define a function that returns that sequence and prove the
; lemma by executing it symbolically.

(define add-duplicate-path ((a1 bit-list-listp) (b1 bit-list-listp) (c1 bit-list-listp)
                       (a2 bit-list-listp) (b2 bit-list-listp) (c2 bit-list-listp)
                       (n natp))
  :enabled t
  :returns (moves move-list-p :hyp :guard)
  (let* ((x (bit-mat-add a1 a2))
         (s1 (summand a1 b1 c1))
         (s2 (summand a2 b2 c2)))
    (cond ((equal x (bit-mat0 n n)) nil)
          ((equal b1 b2)
           (list (list :plus 0 s1 s2)
                 (list :plus 0 (summand a2 b1 c1) (summand x b1 c1))))
          (t
           (list (list :plus 0 s1 s2)
                 (list :plus 1 (summand x b1 c1) s2)
                 (list :plus 0 (summand a2 b1 c1) (summand x (bit-mat-add b1 b2) c1))
                 (list :flip 0
                       (summand x (bit-mat-add b1 b2) c1)
                       (summand x b2 c1)))))))

; Let s1 = (A1,B1,C1), s2 = (A2,B2,C2) and X = A1 + A2.  In the general
; case B1 /= B2 the four moves act as follows.  The first plus, with
; target s1 and pivot s2, replaces s1 by (X,B1,C1) and (A2,B1,C1).  The
; second plus, at position 1 with target (X,B1,C1) and pivot s2, replaces
; it by (X,B1+B2,C1) and (X,B2,C1).  The third plus, with target
; (A2,B1,C1) and pivot (X,B1+B2,C1), replaces it by (A2+X,B1,C1), which
; is s1 again since A2 + X = A1, and by (X,B1,C1).  The final flip acts
; on (X,B1+B2,C1) and (X,B2,C1), which agree at position 0.  One of its
; outputs has third factor C1 + C1 = 0 and is dropped; the other has
; second factor B2 + (B1 + B2) = B1, giving the second copy of (X,B1,C1).
; The scheme now contains s1, s2 and two copies of (X,B1,C1), and nothing
; else has changed.
;
; When B1 = B2 the flip is not needed and two pluses suffice.  When X = 0
; the path is empty.  The lemma holds in this case as well, because the
; two summands it claims to add are zero and insert-all-nonzero drops
; them, so both sides of the equation are the original scheme.  The
; formal statement therefore has no hypothesis on X.

(defrule add-duplicate
  (implies (and (schemep sch n)
                (obag::in (summand a1 b1 c1) sch)
                (obag::in (summand a2 b2 c2) sch))
           (let ((path (add-duplicate-path a1 b1 c1 a2 b2 c2 n))
                 (x (bit-mat-add a1 a2)))
             (and (path-validp path sch n)
                  (equal (apply-moves path sch n)
                         (insert-all-nonzero (list (summand x b1 c1) (summand x b1 c1))
                                             sch
                                             n))))))

; The proof is a single symbolic execution of the four moves, with no
; induction, split into a validity half (bag membership) and a result
; half (insert and delete rewriting), which need disjoint lemma sets.
; Combined with correct-schemep-of-apply-moves this gives the form used
; in the rest of the development.

(defrule add-duplicate-correctness
  (implies (and (correct-schemep sch n)
                (obag::in (summand a1 b1 c1) sch)
                (obag::in (summand a2 b2 c2) sch)
                (natp n))
           (let* ((path (add-duplicate-path a1 b1 c1 a2 b2 c2 n))
                  (sch2 (apply-moves path sch n))
                  (x (bit-mat-add a1 a2)))
             (and (path-validp path sch n)
                  (equal sch2
                         (insert-all-nonzero (list (summand x b1 c1)
                                                   (summand x b1 c1))
                                             sch n))
                  (correct-schemep sch2 n)))))

; Note the asymmetry that the rest of the proof lives on: the B- and
; C-components of the new summand come from s1 alone, and s2 contributes
; only its A-component.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lem:add-arbitrary -- walking a chain
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lemma:add-duplicate-sum can only build summands out of material already
; present.  lem:add-arbitrary lifts that to arbitrary nonzero X, Y, Z.
; To carry the A-component from A0 to X we apply the duplicate-sum step
; once for each summand of the chain from the previous part.  Each
; application adds a pair of copies of the next partial sum, and the pair
; from the previous step must then be removed.  A flip of a summand with
; itself does this, since both of its outputs have a factor added to
; itself and are therefore zero.

(defrule delete-pair-result
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (<= 2 (obag::occs s sch))
                (natp n)
                (natp p)
                (< p 3))
           (equal (apply-move (list :flip p s s) sch n)
                  (obag::delete s (obag::delete s sch)))))

; grow-chain performs one round for each summand u of the chain: the
; add-duplicate-path step with first summand (p, B0, C0) and second
; summand u, followed by the flip that deletes the pair of (p, B0, C0).
; The carried pair thus walks A0 -> A0 + A(u1) -> ... -> X while the
; scheme picks up no debris.  chain-sum computes the final partial sum,
; partial-sums-okp checks that every partial sum is nonzero, and
; us-in-schemep checks that every summand of the chain is in the scheme.

(define grow-chain ((p bit-list-listp) (b0 bit-list-listp) (c0 bit-list-listp)
                    (us mat-triple-listp) (n natp))
  :returns (moves move-list-p :hyp :guard)
  (if (atom us)
      nil
    (let ((u (car us))
          (s (summand p b0 c0)))
      (append (append (add-duplicate-path p b0 c0 (car u) (cadr u) (caddr u) n)
                      (list (list :flip 0 s s)))
              (grow-chain (bit-mat-add p (car u)) b0 c0 (cdr us) n)))))

(define chain-sum ((p bit-list-listp) (us mat-triple-listp))
  :returns (q bit-list-listp :hyp :guard)
  (if (atom us)
      p
    (chain-sum (bit-mat-add p (car (car us))) (cdr us))))

(define partial-sums-okp ((p bit-list-listp) (us mat-triple-listp) (n natp))
  :returns (yes/no booleanp)
  :measure (acl2-count us)
  (and (not (equal p (bit-mat0 n n)))
       (if (atom us)
           t
         (partial-sums-okp (bit-mat-add p (car (car us))) (cdr us) n))))

(define us-in-schemep ((us mat-triple-listp) (sch obag::bagp))
  :returns (yes/no booleanp)
  (if (atom us)
      t
    (and (obag::in (car us) sch)
         (us-in-schemep (cdr us) sch))))

; One round: starting from a scheme with two copies of (p, B0, C0), and u
; in the scheme with p + A(u) nonzero, the duplicate-sum step followed by
; the self-flip is valid and replaces the pair by two copies of
; (p + A(u), B0, C0).

(defruled one-step
  (implies (and (schemep sch n)
                (natp n)
                (summandp (summand p b0 c0) n)
                (obag::in u sch)
                (not (equal (bit-mat-add p (car u)) (bit-mat0 n n))))
           (let* ((s (summand p b0 c0))
                  (cur (obag::insert s (obag::insert s sch)))
                  (x (bit-mat-add p (car u)))
                  (path (append (add-duplicate-path p b0 c0
                                               (car u) (cadr u) (caddr u) n)
                                (list (list :flip 0 s s)))))
             (and (path-validp path cur n)
                  (equal (apply-moves path cur n)
                         (obag::insert (summand x b0 c0)
                                       (obag::insert (summand x b0 c0) sch)))))))

; The whole chain, by induction on it using one-step: starting from a
; scheme containing two copies of (p, B0, C0), with every summand of the
; chain in the scheme and every partial sum nonzero, the path is valid
; and the result is the scheme with two copies of (chain-sum, B0, C0) in
; place of the original pair.

(defrule grow-chain-invariant
  (implies (and (schemep sch n)
                (natp n)
                (summandp (summand p b0 c0) n)
                (us-in-schemep us sch)
                (summand-listp us n)
                (partial-sums-okp p us n))
           (let ((cur (obag::insert (summand p b0 c0)
                                    (obag::insert (summand p b0 c0) sch)))
                 (x (chain-sum p us)))
             (and (path-validp (grow-chain p b0 c0 us n) cur n)
                  (equal (apply-moves (grow-chain p b0 c0 us n) cur n)
                         (obag::insert (summand x b0 c0)
                                       (obag::insert (summand x b0 c0) sch)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lem:add-arbitrary -- adding an arbitrary summand
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; For the A position, add-arbitrary-a-path finds the seed and the chain,
; applies add-duplicate-path once to the seed and the first element of
; the chain to obtain the first pair, and hands the rest of the chain to
; grow-chain.

(define add-arbitrary-a-path ((sch mat-triple-listp) (x bit-list-listp) (n natp))
  :returns (moves move-list-p :hyp :guard)
  (let* ((s0 (find-summand-a-neq sch x))
         (a0 (car s0))
         (b0 (cadr s0))
         (c0 (caddr s0))
         (us (arb-us sch x n))
         (u1 (car us)))
    (append (add-duplicate-path a0 b0 c0 (car u1) (cadr u1) (caddr u1) n)
            (grow-chain (bit-mat-add a0 (car u1)) b0 c0 (cdr us) n))))

; The hypotheses of grow-chain-invariant are discharged by the following
; theorem about the chain, which is the result of the span layer: every
; partial sum along arb-us is nonzero, and the chain ends at X.

(defruled arb-us-okp
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n)
                (not (equal x (bit-mat0 n n))))
           (and (partial-sums-okp (car (find-summand-a-neq sch x))
                                  (arb-us sch x n) n)
                (equal (chain-sum (car (find-summand-a-neq sch x))
                                  (arb-us sch x n))
                       x))))

; The A leg therefore takes a correct scheme to the same scheme plus two
; copies of (X, B0, C0), where B0 and C0 are inherited from the seed.

(defrule add-arbitrary-a
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n)
                (not (equal x (bit-mat0 n n))))
           (let* ((s0 (find-summand-a-neq sch x))
                  (b0 (cadr s0))
                  (c0 (caddr s0))
                  (path (add-arbitrary-a-path sch x n))
                  (sch2 (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal sch2
                         (obag::insert (summand x b0 c0)
                                       (obag::insert (summand x b0 c0) sch)))
                  (correct-schemep sch2 n)))))

; The B and C legs apply the same construction to the carried pair.  No
; new seed is chosen: the pair (X, B0, C0) is the seed of the B leg, and
; the pair (X, Y, C0) it produces is the seed of the C leg.  Each leg is
; empty when its component already has the required value, and each ends
; by deleting the stale pair with a self-flip.
;
; The B leg is built from mirror images of the A-position functions,
; with the roles of the positions rotated: add-duplicate-b-path is
; add-duplicate-path with the moves at positions 1 and 2 instead of 0
; and 1, so that the new summand takes its B-component from the sum and
; its A- and C-components from the first summand; grow-chain-b,
; b-components, basis-new-b, arb-basis-b, arb-coeffs-b and arb-us-b are
; the corresponding mirrors of grow-chain, a-components, basis-new,
; arb-basis, arb-coeffs and arb-us, with one-step-b the mirror of
; one-step; and add-arbitrary-b-path is the mirror of
; add-arbitrary-a-path, taking the seed s0 as an argument instead of
; searching for it.  The C leg is the same with position 2.  Only
; add-duplicate-b-path and the two leg functions are shown; the rest
; differ from the A versions by the position only.

(define add-duplicate-b-path ((a1 bit-list-listp) (b1 bit-list-listp) (c1 bit-list-listp)
                         (a2 bit-list-listp) (b2 bit-list-listp) (c2 bit-list-listp)
                         (n natp))
  :enabled t
  :returns (moves move-list-p :hyp :guard)
  (let* ((y (bit-mat-add b1 b2))
         (s1 (summand a1 b1 c1))
         (s2 (summand a2 b2 c2)))
    (cond ((equal y (bit-mat0 n n)) nil)
          ((equal c1 c2)
           (list (list :plus 1 s1 s2)
                 (list :plus 1 (summand a1 b2 c1) (summand a1 y c1))))
          (t
           (list (list :plus 1 s1 s2)
                 (list :plus 2 (summand a1 y c1) s2)
                 (list :plus 1 (summand a1 b2 c1) (summand a1 y (bit-mat-add c1 c2)))
                 (list :flip 1
                       (summand a1 y (bit-mat-add c1 c2))
                       (summand a1 y c2)))))))

(define add-arbitrary-b-path ((sch mat-triple-listp) (s0 mat-triplep)
                              (y bit-list-listp) (n natp))
  :returns (moves move-list-p :hyp :guard)
  (let* ((a0 (car s0))
         (b0 (cadr s0))
         (c0 (caddr s0))
         (us (arb-us-b sch s0 y n))
         (u1 (car us)))
    (append (add-duplicate-b-path a0 b0 c0 (car u1) (cadr u1) (caddr u1) n)
            (grow-chain-b a0 (bit-mat-add b0 (cadr u1)) c0 (cdr us) n))))

(define add-arbitrary-c-path ((sch mat-triple-listp) (s0 mat-triplep)
                              (z bit-list-listp) (n natp))
  :returns (moves move-list-p :hyp :guard)
  (let* ((a0 (car s0))
         (b0 (cadr s0))
         (c0 (caddr s0))
         (us (arb-us-c sch s0 z n))
         (u1 (car us)))
    (append (add-duplicate-c-path a0 b0 c0 (car u1) (cadr u1) (caddr u1) n)
            (grow-chain-c a0 b0 (bit-mat-add c0 (caddr u1)) (cdr us) n))))

; arb-path-b runs the B leg on the scheme as it stands after the A leg,
; namely sch plus two copies of s1 = (X, B0, C0), and deletes the pair of
; s1 at the end; arb-path-c does the same for the C leg starting from the
; pair of (X, Y, C0).  add-arbitrary-path is the concatenation of the
; three legs.

(define arb-path-b ((sch mat-triple-listp) (x bit-list-listp) (y bit-list-listp)
                    (n natp))
  :guard (obag::bagp sch)
  :returns (moves move-list-p :hyp :guard)
  (let* ((s0 (find-summand-a-neq sch x))
         (b0 (cadr s0))
         (c0 (caddr s0))
         (s1 (summand x b0 c0))
         (sch1 (obag::insert s1 (obag::insert s1 sch))))
    (if (equal b0 y)
        nil
      (append (add-arbitrary-b-path sch1 s1 y n)
              (list (list :flip 0 s1 s1))))))

(define arb-path-c ((sch mat-triple-listp) (x bit-list-listp) (y bit-list-listp)
                    (z bit-list-listp) (n natp))
  :guard (obag::bagp sch)
  :returns (moves move-list-p :hyp :guard)
  (let* ((s0 (find-summand-a-neq sch x))
         (c0 (caddr s0))
         (s2 (summand x y c0))
         (sch2 (obag::insert s2 (obag::insert s2 sch))))
    (if (equal c0 z)
        nil
      (append (add-arbitrary-c-path sch2 s2 z n)
              (list (list :flip 0 s2 s2))))))

(define add-arbitrary-path ((sch mat-triple-listp)
                            (x bit-list-listp) (y bit-list-listp) (z bit-list-listp)
                            (n natp))
  :guard (obag::bagp sch)
  :returns (moves move-list-p :hyp :guard)
  (append (add-arbitrary-a-path sch x n)
          (append (arb-path-b sch x y n)
                  (arb-path-c sch x y z n))))

; The result is lem:add-arbitrary.  Its hypotheses are those of the
; informal lemma.  Two copies is not a choice; it is what the
; duplicate-sum step produces, and it is exactly right, since identical
; tensors cancel over F2 and the scheme stays correct throughout.

(defrule add-arbitrary
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n)
                (not (equal x (bit-mat0 n n)))
                (bit-matp y n n)
                (not (equal y (bit-mat0 n n)))
                (bit-matp z n n)
                (not (equal z (bit-mat0 n n))))
           (let* ((path (add-arbitrary-path sch x y z n))
                  (s (summand x y z))
                  (sch3 (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal sch3
                         (obag::insert s (obag::insert s sch)))
                  (correct-schemep sch3 n)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lemma:zero-subset -- the plan
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; lemma:zero-subset states that a submultiset r of a correct scheme whose
; summands sum to zero can be removed by a valid path.  The only move
; that removes summands is a flip of a summand with itself, which deletes
; both copies of an identical pair.  A zero-summing submultiset need not
; contain such a pair; for example, (A,B,C), (A',B,C) and (A+A',B,C) sum
; to zero and are pairwise distinct.  We therefore first replace every
; summand of r by summands whose three factors are unit matrices.  Among
; such summands a zero sum forces every summand to occur an even number
; of times, and they can then be removed in pairs.  The path has four
; stages: one decomposition sweep for each of the three positions, and a
; pass that deletes pairs.  The three sweeps take nothing out -- the
; scheme grows while its sum stays put -- and the last pass is the only
; one that removes anything.
;
; The statements below use three functions on lists of summands.
; insert-list inserts each element of a list into a bag, delete-list
; deletes one copy of each, and list-in-bagp holds when a list is a
; submultiset of a bag, counting multiplicity.

(define insert-list ((l mat-triple-listp) (b obag::bagp))
  :returns (b1 obag::bagp :hyp (obag::bagp b))
  (if (atom l)
      b
    (obag::insert (car l) (insert-list (cdr l) b))))

(define delete-list ((l mat-triple-listp) (b obag::bagp))
  :returns (b1 obag::bagp :hyp (obag::bagp b))
  (if (atom l)
      b
    (delete-list (cdr l) (obag::delete (car l) b))))

(define list-in-bagp ((l mat-triple-listp) (b obag::bagp))
  :returns (yes/no booleanp)
  (if (atom l)
      t
    (and (obag::in (car l) b)
         (list-in-bagp (cdr l) (obag::delete (car l) b)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lemma:zero-subset -- splitting one component
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Let s be a summand of the scheme, p a position, M the factor of s at p,
; and u a nonzero matrix other than M.  We add two copies of s[p -> u] by
; add-arbitrary-path, then flip s[p -> u] against s at position
; (pos-prev p), where the two agree.  One output is s with M replaced by
; M + u.  The other has a factor added to itself, so it is zero and is
; dropped.  The result is the scheme with s replaced by s[p -> u] and
; s[p -> M + u].  Nothing in this step requires u to be a unit matrix;
; that choice is made in the next step.

(defruled replace-step
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (natp n)
                (obag::in s sch)
                (natp p) (< p 3)
                (bit-matp u n n)
                (not (equal u (bit-mat0 n n)))
                (not (equal u (summand-get-pos s p))))
           (b* ((sp (summand-set-pos s p u))
                (spp (summand-set-pos s p (bit-mat-add (summand-get-pos s p) u)))
                (sch1 (obag::insert sp (obag::insert sp sch)))
                (move (list :flip (pos-prev p) sp s)))
             (and (move-validp move sch1)
                  (equal (apply-move move sch1 n)
                         (obag::insert spp
                                       (obag::insert sp (obag::delete s sch))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lemma:zero-subset -- decomposing a summand
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The unit matrix chosen at each step is the one at the first 1 of M.
; count-ones-list and count-ones-mat count the ones in a vector and in a
; matrix; first-one-row is the index of the first row containing a 1, and
; first-one-col-mat the column of the first 1 in that row.  bit-mat-unit2
; is a second definition of the unit matrix E_ij, with the same body as
; bit-mat-unit; it belongs to the span layer, which was developed
; separately, and bit-mat-unit2-is-bit-mat-unit identifies the two.

(define count-ones-list ((r bit-list-p))
  :returns (k natp)
  (if (atom r)
      0
    (+ (if (equal (car r) 1) 1 0)
       (count-ones-list (cdr r)))))

(define count-ones-mat ((x bit-list-listp))
  :returns (k natp)
  (if (atom x)
      0
    (+ (count-ones-list (car x))
       (count-ones-mat (cdr x)))))

(define first-one-col ((r bit-list-p))
  :returns (j natp)
  (if (atom r)
      0
    (if (equal (car r) 1)
        0
      (1+ (first-one-col (cdr r))))))

(define first-one-row ((x bit-list-listp))
  :returns (i natp)
  (if (atom x)
      0
    (if (< 0 (count-ones-list (car x)))
        0
      (1+ (first-one-row (cdr x))))))

(define first-one-col-mat ((x bit-list-listp))
  :returns (j natp)
  (if (atom x)
      0
    (if (< 0 (count-ones-list (car x)))
        (first-one-col (car x))
      (first-one-col-mat (cdr x)))))

(define bit-mat-unit2 ((i natp) (j natp) (m natp) (n natp))
  :returns (a bit-list-listp)
  (if (zp m)
      nil
    (if (zp i)
        (cons (bit-unit-list j n) (bit-mat0 (1- m) n))
      (cons (bit-listn0 n) (bit-mat-unit2 (1- i) j (1- m) n)))))

(defruled bit-mat-unit2-is-bit-mat-unit
  (equal (bit-mat-unit2 i j m n)
         (bit-mat-unit i j m n)))

; units-of returns the list of unit matrices whose sum is a given matrix,
; one for each 1 in it, by repeatedly clearing the first 1.  set-pos-all
; returns the copies of a summand with its factor at position p replaced
; by each matrix of a list in turn.

(define units-of ((x bit-list-listp) (m natp) (n natp))
  :returns (l bit-mat-list-p)
  :measure (count-ones-mat x)
  (if (or (not (bit-matp x m n))
          (equal x (bit-mat0 m n)))
      nil
    (cons (bit-mat-unit2 (first-one-row x) (first-one-col-mat x) m n)
          (units-of (bit-mat-add x (bit-mat-unit2 (first-one-row x)
                                                  (first-one-col-mat x)
                                                  m n))
                    m n))))

(define set-pos-all ((s mat-triplep) (p natp) (us bit-mat-list-p))
  :returns (l mat-triple-listp :hyp :guard)
  (if (atom us)
      nil
    (cons (summand-set-pos s p (car us))
          (set-pos-all s p (cdr us)))))

; decompose-pos-path takes a scheme, one summand s of it, and a position
; p.  It repeats the step of the previous part with u the unit matrix at
; the first 1 of M, so that M loses a 1 each time, until M is itself a
; unit matrix.  The measure is the number of ones in M.

(define decompose-pos-path ((sch obag::bagp) (s mat-triplep) (p natp) (n natp))
  :guard (mat-triple-listp sch)
  :measure (count-ones-mat (summand-get-pos s p))
  :returns (moves move-list-p :hyp :guard)
  (b* ((xp (summand-get-pos s p))
       ((unless (and (bit-matp xp n n)
                     (natp n)
                     (<= 2 (count-ones-mat xp))))
        nil)
       (u (bit-mat-unit2 (first-one-row xp) (first-one-col-mat xp) n n))
       (sp (summand-set-pos s p u))
       (xpp (bit-mat-add xp u))
       (spp (summand-set-pos s p xpp))
       (sch2 (obag::insert spp
                           (obag::insert sp (obag::delete s sch)))))
    (append (append (add-arbitrary-path sch (car sp) (cadr sp) (caddr sp) n)
                    (list (list :flip (pos-prev p) sp s)))
            (decompose-pos-path sch2 spp p n))))

; Applying the path replaces s by one summand for each unit matrix of M,
; with the other two factors unchanged, and preserves correctness.

(defrule decompose-pos-invariant
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (obag::in s sch)
                (natp p) (< p 3))
           (b* ((path (decompose-pos-path sch s p n))
                (res (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal res
                         (insert-list
                          (set-pos-all s p (units-of (summand-get-pos s p) n n))
                          (obag::delete s sch)))
                  (correct-schemep res n)))))

; decompose-list-pos-path applies this to every summand of a list.
; expand-pos-list is the bookkeeping side of the same thing: a list of
; summands and a position in, a longer list out, no moves involved.  It
; is the destination, the path is the route, and the invariant theorem
; is what says the route arrives.  expand-pos-list is needed because the
; path for the second sweep is constructed before the first sweep is
; applied, so the scheme the second sweep starts from must be computed
; rather than observed.

(define expand-pos-list ((l mat-triple-listp) (p natp) (n natp))
  :returns (e mat-triple-listp :hyp :guard)
  (if (atom l)
      nil
    (append (set-pos-all (car l) p
                         (units-of (summand-get-pos (car l) p) n n))
            (expand-pos-list (cdr l) p n))))

(define decompose-list-pos-path ((sch obag::bagp) (l mat-triple-listp)
                                 (p natp) (n natp))
  :guard (mat-triple-listp sch)
  :returns (moves move-list-p :hyp :guard)
  (if (atom l)
      nil
    (append (decompose-pos-path sch (car l) p n)
            (decompose-list-pos-path
             (insert-list (set-pos-all (car l) p
                                       (units-of (summand-get-pos (car l) p)
                                                 n n))
                          (obag::delete (car l) sch))
             (cdr l) p n))))

(defrule decompose-list-pos-invariant
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (list-in-bagp l sch)
                (natp p) (< p 3))
           (b* ((path (decompose-list-pos-path sch l p n))
                (res (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal res
                         (insert-list (expand-pos-list l p n)
                                      (delete-list l sch)))
                  (correct-schemep res n)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lemma:zero-subset -- parity
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A unit matrix is one equal to E_ij for some valid i and j;
; unit-index-of finds that (i,j), or nil.  A unit summand is a summand
; whose three factors are unit matrices.

(define unit-index-of (a (m natp) (n natp))
  :returns (pos (or (null pos)
                    (and (consp pos) (natp (car pos)) (natp (cdr pos)))))
  (b* ((pos (mat-first-one a))
       ((unless pos) nil)
       (i (car pos))
       (j (cdr pos))
       ((unless (and (< i (nfix m)) (< j (nfix n)))) nil))
    pos))

(define unit-matp (a (m natp) (n natp))
  :returns (yes/no booleanp)
  (b* ((pos (unit-index-of a m n)))
    (and (bit-matp a m n)
         (consp pos)
         (equal a (bit-mat-unit (car pos) (cdr pos) m n)))))

(define unit-summandp (s (n natp))
  :returns (yes/no booleanp)
  (and (summand-dimp s n)
       (unit-matp (car s) n n)
       (unit-matp (cadr s) n n)
       (unit-matp (caddr s) n n)))

(define unit-summand-listp (l (n natp))
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (unit-summandp (car l) n)
         (unit-summand-listp (cdr l) n))))

; The tensor of a unit summand has a single 1, at an index determined by
; the positions of the ones in its three factors, and distinct unit
; summands have distinct indices.  Reading the tensor of a list of unit
; summands at the index of a summand s therefore gives the number of
; occurrences of s in the list modulo two.  If the tensor is zero, that
; number is even.

(defrule even-occs-when-zero-scheme-sum
  (implies (and (obag::bagp l)
                (unit-summand-listp l n) (natp n)
                (equal (scheme-sum l n) (bit-listn0 (* n n n n n n)))
                (obag::in s l))
           (evenp (obag::occs s l))))

; In particular, the first element of a nonempty zero-summing list of
; unit summands occurs again later in the list, and at least twice in any
; scheme that contains the list.

(defruled head-pair-facts
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (natp n)
                (unit-summand-listp l n)
                (list-in-bagp l sch)
                (equal (scheme-sum l n) (bit-listn0 (* n n n n n n)))
                (consp l))
           (and (member-equal (car l) (cdr l))
                (<= 2 (obag::occs (car l) sch)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lemma:zero-subset -- deleting in pairs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; delete-pairs-path flips the first element of the list with itself,
; which deletes two copies of it from the scheme, removes one further
; occurrence of it from the list, and continues with the rest.  Both
; outputs of the flip add a matrix to itself, so both are zero and both
; are dropped.

(define delete-pairs-path ((sch obag::bagp) (l mat-triple-listp) (n natp))
  :irrelevant-formals-ok t
  :measure (len l)
  :returns (moves move-list-p :hyp :guard)
  (declare (irrelevant sch n))
  (if (atom l)
      nil
    (cons (list :flip 0 (car l) (car l))
          (delete-pairs-path (obag::delete (car l)
                                           (obag::delete (car l) sch))
                             (remove1-equal (car l) (cdr l))
                             n))))

; Applied to a zero-summing list of unit summands contained in the
; scheme, it removes the whole list.  The proof is by induction on the
; list, with head-pair-facts supplying the twin at each step.

(defrule delete-pairs-invariant
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (natp n)
                (unit-summand-listp l n)
                (list-in-bagp l sch)
                (equal (scheme-sum l n) (bit-listn0 (* n n n n n n))))
           (b* ((path (delete-pairs-path sch l n))
                (res (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal res (delete-list l sch))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lemma:zero-subset -- the lemma
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; zero-subset-path performs the three sweeps at positions 0, 1 and 2 and
; then deletes pairs.  It calls expand-pos-list to work out the list
; after each sweep, because the path is built before any move is applied
; and each sweep has to be told which scheme and which list it works on.
; base, the part of the scheme outside r, is never touched.

(define zero-subset-path ((sch obag::bagp) (r mat-triple-listp) (n natp))
  :guard (mat-triple-listp sch)
  :returns (moves move-list-p :hyp :guard)
  (b* ((base (delete-list r sch))
       (l1 (expand-pos-list r 0 n))
       (sch1 (insert-list l1 base))
       (l2 (expand-pos-list l1 1 n))
       (sch2 (insert-list l2 base))
       (l3 (expand-pos-list l2 2 n))
       (sch3 (insert-list l3 base)))
    (append (decompose-list-pos-path sch r 0 n)
            (append (decompose-list-pos-path sch1 l1 1 n)
                    (append (decompose-list-pos-path sch2 l2 2 n)
                            (delete-pairs-path sch3 l3 n))))))

; After the three sweeps every summand of the list is a unit summand, and
; no sweep changes the sum of the list, since the unit matrices of a
; matrix add up to that matrix.

(defruled unit-summand-listp-of-triple-expand
  (implies (and (summand-listp r n)
                (natp n))
           (unit-summand-listp
            (expand-pos-list (expand-pos-list (expand-pos-list r 0 n) 1 n) 2 n)
            n)))

(defruled scheme-sum-of-expand-pos-list
  (implies (and (summand-listp l n)
                (natp n) (natp p) (< p 3))
           (equal (scheme-sum (expand-pos-list l p n) n)
                  (scheme-sum l n))))

; lemma:zero-subset follows.  The result is the scheme with r removed,
; and it is correct.

(defrule zero-subset
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (true-listp r)
                (list-in-bagp r sch)
                (equal (scheme-sum r n) (bit-listn0 (* n n n n n n))))
           (b* ((path (zero-subset-path sch r n))
                (res (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal res (delete-list r sch))
                  (correct-schemep (delete-list r sch) n)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; thm:main -- assembling the connectivity path
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The path of thm:main has two parts.  graft-path applies
; add-arbitrary-path once for each summand of the target scheme, adding
; two copies of each.  The scheme remains correct throughout, since two
; copies of a summand contribute nothing to the tensor over F2.

(define graft-path ((sch obag::bagp) (l mat-triple-listp) (n natp))
  :guard (mat-triple-listp sch)
  :returns (moves move-list-p :hyp :guard)
  (if (atom l)
      nil
    (append (add-arbitrary-path sch (car (car l)) (cadr (car l))
                                (caddr (car l)) n)
            (graft-path (obag::insert (car l) (obag::insert (car l) sch))
                        (cdr l) n))))

(defrule graft-invariant
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (summand-listp l n))
           (b* ((path (graft-path sch l n))
                (res (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal res (insert-list l (insert-list l sch)))
                  (correct-schemep res n)))))

; Starting from S and adding every summand of S' gives S plus S' plus
; S'.  The submultiset S plus S' sums to mm-tensor + mm-tensor = 0, so
; zero-subset-path removes it and one copy of S' remains.  main-path is
; the concatenation of the two paths.

(define main-path ((sch obag::bagp) (sch2 obag::bagp) (n natp))
  :guard (and (mat-triple-listp sch) (mat-triple-listp sch2))
  :returns (moves move-list-p :hyp :guard)
  (append (graft-path sch sch2 n)
          (zero-subset-path (insert-list sch2 (insert-list sch2 sch))
                            (append sch sch2)
                            n)))

; The main theorem, stated in overview-prelims.lisp, follows by
; instantiating graft-invariant with l the target scheme and zero-subset
; with the scheme after the graft and r = S plus S'.  No induction is
; needed.  Each of the two theorems states the scheme its path produces,
; and the two schemes agree.

(defrule flip-plus-connectivity
  (implies (and (correct-schemep sch n)
                (correct-schemep sch2 n)
                (natp n) (<= 2 n))
           (b* ((path (main-path sch sch2 n))
                (res (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal res sch2)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Seeing it run
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Every function above is executable, and every construction was checked
; by running it at n = 2 before being proved.  *arb-std2* is the standard
; algorithm at n = 2, the 8 summands E_ij (x) E_jk (x) E_ik.

(defconst *arb-std2*
  (obag::insert
   (summand (bit-mat-unit 0 0 2 2) (bit-mat-unit 0 0 2 2) (bit-mat-unit 0 0 2 2))
   (obag::insert
    (summand (bit-mat-unit 0 0 2 2) (bit-mat-unit 0 1 2 2) (bit-mat-unit 0 1 2 2))
    (obag::insert
     (summand (bit-mat-unit 0 1 2 2) (bit-mat-unit 1 0 2 2) (bit-mat-unit 0 0 2 2))
     (obag::insert
      (summand (bit-mat-unit 0 1 2 2) (bit-mat-unit 1 1 2 2) (bit-mat-unit 0 1 2 2))
      (obag::insert
       (summand (bit-mat-unit 1 0 2 2) (bit-mat-unit 0 0 2 2) (bit-mat-unit 1 0 2 2))
       (obag::insert
        (summand (bit-mat-unit 1 0 2 2) (bit-mat-unit 0 1 2 2) (bit-mat-unit 1 1 2 2))
        (obag::insert
         (summand (bit-mat-unit 1 1 2 2) (bit-mat-unit 1 0 2 2) (bit-mat-unit 1 0 2 2))
         (obag::insert
          (summand (bit-mat-unit 1 1 2 2) (bit-mat-unit 1 1 2 2) (bit-mat-unit 1 1 2 2))
          nil)))))))))

; Add an arbitrary summand to it to get a correct scheme of rank 10, then
; let main-path walk back from that scheme to the standard one.

(assert-event
 (let* ((x '((1 1) (0 1))) (y '((0 1) (1 1))) (z '((1 0) (1 1)))
        (path0 (add-arbitrary-path *arb-std2* x y z 2))
        (schb (apply-moves path0 *arb-std2* 2))
        (path (main-path schb *arb-std2* 2)))
   (and (correct-schemep *arb-std2* 2)
        (equal (scheme-rank *arb-std2*) 8)
        (correct-schemep schb 2)
        (equal (scheme-rank schb) 10)
        (path-validp path schb 2)
        (equal (apply-moves path schb 2) *arb-std2*))))

; And the two cases of the chain construction: the seed's A-component is
; E11 and the pool is (E00, E01, E10, E11) with the seed last.  For
; X = E00 + E01 + E11 the seed's own A-component is unused; for X = E00
; it is used, and lands as the last link of the chain.

(assert-event
 (let ((x1 '((1 1) (0 1)))
       (x2 '((1 0) (0 0))))
   (and (equal (car (find-summand-a-neq *arb-std2* x1)) '((0 0) (0 1)))
        (equal (a-components (arb-basis *arb-std2* x1 2))
               '(((1 0) (0 0)) ((0 1) (0 0)) ((0 0) (1 0)) ((0 0) (0 1))))
        (equal (arb-coeffs *arb-std2* x1 2) '(1 1 0 0))
        (equal (a-components (arb-us *arb-std2* x1 2))
               '(((1 0) (0 0)) ((0 1) (0 0))))
        (equal (arb-coeffs *arb-std2* x2 2) '(1 0 0 1))
        (equal (a-components (arb-us *arb-std2* x2 2))
               '(((1 0) (0 0)) ((0 0) (0 1)))))))
