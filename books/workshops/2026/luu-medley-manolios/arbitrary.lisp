; Support for the add-arbitrary lemma of the companion paper: from any
; correct scheme sch for n x n matrix multiplication over F2 (n >= 2) and
; any nonzero n x n matrices X, Y, Z, there is a valid path from sch to sch
; plus two copies of X (x) Y (x) Z (theorem add-arbitrary, in add-arbitrary.lisp,
; which assembles the legs developed here).
;
; The book first develops the A-position version (add-arbitrary-a): a path
; to sch plus two copies of (summand X B0 C0), where (summand A0 B0 C0) is
; a summand of sch chosen with A0 /= X.  Stage 5 then mirrors the whole
; development in the B and C positions and composes the three legs.
;
; The proof follows the companion paper:
;
;  - Stage 1: by the span lemma, the A-components of the summands of sch
;    span F2^{nxn} (a-components-span-everything).
;  - Stage 2: a greedy pass over the summands of sch, seeded with the
;    chosen summand s0, extracts summands whose A-components are
;    independent and still span everything (basis-new).
;  - Stage 3: writing X + A0 in that basis (span-witness) selects the
;    summand chain u1, ..., ut; because s0 sits at the END of the basis
;    list, the selected chain automatically realizes the paper's ordering
;    trick (when the coefficient of A0 is 1, the extra copy of A0 comes
;    last), and independence makes every partial sum
;    A0, A0 + A(u1), ... nonzero (select-chain-okp-when-independent);
;    the chain lands exactly on X (chain-sum-of-arb-us).
;  - Stage 4: add-arbitrary-relative (iterate.lisp) walks the pair along
;    the chain: add-arbitrary-a.
;
; All constructions are executable and were validated end to end at n = 2
; on the standard rank-8 scheme, for all 15 nonzero 2x2 matrices X
; (path-validp and the exact resulting bag); see the assert-event forms.

(in-package "ACL2")

(include-book "span")
(include-book "gf2span")
(include-book "iterate")

(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The A-components of a summand list.

(define a-components ((l mat-triple-listp))
  :returns (mats bit-mat-list-p :hyp :guard)
  (if (atom l)
      nil
    (cons (car (car l)) (a-components (cdr l))))
  ///
  (defrule bit-mat-listnp-of-a-components
    (implies (summand-dim-listp l n)
             (bit-mat-listnp (a-components l) n n))
    :induct (a-components l)
    :enable bit-mat-listnp)
  (defrule len-of-a-components
    (equal (len (a-components l)) (len l)))
  (defruled a-components-of-append
    (equal (a-components (append l1 l2))
           (append (a-components l1) (a-components l2)))
    :induct (cdr-induct l1)))

;;; The first summand whose A-component differs from x (nil if none).

(define find-summand-a-neq ((l mat-triple-listp) (x bit-list-listp))
  :returns (s (or (null s) (mat-triplep s))
              :hyp :guard
              :hints (("Goal"
                       :induct (find-summand-a-neq l x)
                       :in-theory (enable mat-triple-listp))))
  (if (atom l)
      nil
    (if (equal (car (car l)) x)
        (find-summand-a-neq (cdr l) x)
      (car l))))

;;; What the seed is, structurally.  find-summand-a-neq returns either a
;;; member of l or nil, and nil's car/cadr/caddr are nil, which IS a
;;; bit-list-listp -- so the component facts hold unconditionally, while
;;; mat-triplep needs the non-nil case.

(defruled mat-triplep-of-find-summand-a-neq
  (implies (and (mat-triple-listp l)
                (find-summand-a-neq l x))
           (mat-triplep (find-summand-a-neq l x)))
  :induct (find-summand-a-neq l x)
  :enable find-summand-a-neq)

(defruled true-listp-of-find-summand-a-neq
  (implies (mat-triple-listp l)
           (true-listp (find-summand-a-neq l x)))
  :induct (find-summand-a-neq l x)
  :enable find-summand-a-neq
  :rule-classes (:rewrite :type-prescription))

(defruled true-listp-of-cdr-of-find-summand-a-neq
  (implies (mat-triple-listp l)
           (true-listp (cdr (find-summand-a-neq l x))))
  :induct (find-summand-a-neq l x)
  :enable find-summand-a-neq
  :rule-classes (:rewrite :type-prescription))

(defruled true-listp-of-cddr-of-find-summand-a-neq
  (implies (mat-triple-listp l)
           (true-listp (cddr (find-summand-a-neq l x))))
  :induct (find-summand-a-neq l x)
  :enable find-summand-a-neq
  :rule-classes (:rewrite :type-prescription))

(defruled bit-list-listp-of-car-of-find-summand-a-neq
  (implies (mat-triple-listp l)
           (bit-list-listp (car (find-summand-a-neq l x))))
  :induct (find-summand-a-neq l x)
  :enable find-summand-a-neq)

(defruled bit-list-listp-of-cadr-of-find-summand-a-neq
  (implies (mat-triple-listp l)
           (bit-list-listp (cadr (find-summand-a-neq l x))))
  :induct (find-summand-a-neq l x)
  :enable find-summand-a-neq)

(defruled bit-list-listp-of-caddr-of-find-summand-a-neq
  (implies (mat-triple-listp l)
           (bit-list-listp (caddr (find-summand-a-neq l x))))
  :induct (find-summand-a-neq l x)
  :enable find-summand-a-neq)

(deftheory find-summand-a-neq-shape
  '(mat-triplep-of-find-summand-a-neq
    true-listp-of-find-summand-a-neq
    true-listp-of-cdr-of-find-summand-a-neq
    true-listp-of-cddr-of-find-summand-a-neq
    bit-list-listp-of-car-of-find-summand-a-neq
    bit-list-listp-of-cadr-of-find-summand-a-neq
    bit-list-listp-of-caddr-of-find-summand-a-neq))

;;; Everything the guard proofs of this book need about the shape of a seed
;;; summand and of the head of a chain.  Kept out of the global theory: as
;;; enabled rules these fire on every car/cdr goal and cost a tenfold
;;; slowdown across the development.

(deftheory arb-guard-lemmas
  (union-theories (theory 'find-summand-a-neq-shape)
                  (theory 'mat-triple-head-lemmas)))

;;; The summands selected by a coefficient vector, in order.

(define select-summands ((coeffs bit-list-p) (l mat-triple-listp))
  :measure (acl2-count l)
  :returns (us mat-triple-listp :hyp (mat-triple-listp l))
  (if (atom l)
      nil
    (if (equal (car coeffs) 1)
        (cons (car l) (select-summands (cdr coeffs) (cdr l)))
      (select-summands (cdr coeffs) (cdr l)))))

;;; All partial sums along the coefficient-selected summands are nonzero.
;;; This is the computable form in which the independence argument is made;
;;; it coincides with partial-sums-okp of the selected chain
;;; (select-chain-okp-as-partial-sums-okp below).

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

;;; summand-listp / summand-dim-listp closure under append.

(defruled mat-triple-listp-of-append
  (implies (and (mat-triple-listp l1)
                (mat-triple-listp l2))
           (mat-triple-listp (append l1 l2)))
  :induct (cdr-induct l1))

(defruled summand-listp-of-append
  (implies (and (summand-listp l1 n)
                (summand-listp l2 n))
           (summand-listp (append l1 l2) n))
  :induct (cdr-induct l1))

(defruled summand-dim-listp-of-append
  (implies (and (summand-dim-listp l1 n)
                (summand-dim-listp l2 n))
           (summand-dim-listp (append l1 l2) n))
  :induct (cdr-induct l1))

;;; Greedy basis extension: the summands of l (in back-to-front order of
;;; adoption) whose A-components are independent over acc's A-components.
;;; The basis itself is (append (basis-new l acc n) acc): the accumulator
;;; -- in our use, the single seed summand s0 -- stays at the END, which
;;; is what makes the selected chain of Stage 3 realize the paper's
;;; ordering trick with no case analysis in the construction.

(define basis-new ((l mat-triple-listp) (acc mat-triple-listp) (n natp))
  :returns (ws mat-triple-listp :hyp :guard
               :hints (("Goal" :in-theory (enable mat-triple-listp-of-append))))
  (if (atom l)
      nil
    (if (in-spanp (car (car l)) (a-components acc) n n)
        (basis-new (cdr l) acc n)
      (append (basis-new (cdr l) (cons (car l) acc) n)
              (list (car l)))))
  ///
  (defrule summand-listp-of-basis-new
    (implies (and (summand-listp l n)
                  (summand-listp acc n))
             (summand-listp (basis-new l acc n) n))
    :induct (basis-new l acc n)
    :enable (summand-listp-of-append)))

;;; The chosen basis, coefficients, and chain for a given scheme and target.

;;; The (unless (mat-triplep s0)) test is a totality guard, not part of the
;;; construction: find-summand-a-neq signals "no such summand" with nil, and
;;; nil is not a mat-triplep, so (list s0) would not be a legal argument to
;;; basis-new.  Under the hypotheses of every theorem about arb-basis the
;;; seed exists (arb-s0-facts), so the test is always true there and no
;;; statement changes; without it the guard obligation is simply false and
;;; the alternative is to carry (mat-triplep (find-summand-a-neq sch x)) as a
;;; guard conjunct all the way up through graft-path, where it stops being
;;; discharegable without correct-schemep.

(define arb-basis ((sch mat-triple-listp) (x bit-list-listp) (n natp))
  :returns (bs mat-triple-listp :hyp :guard
               :hints (("Goal" :in-theory (enable mat-triple-listp-of-append))))
  (b* ((s0 (find-summand-a-neq sch x))
       ((unless (mat-triplep s0)) nil))
    (append (basis-new sch (list s0) n)
            (list s0))))

(define arb-coeffs ((sch mat-triple-listp) (x bit-list-listp) (n natp))
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (union-theories (theory 'arb-guard-lemmas)
                                            (current-theory :here))))
  :returns (coeffs bit-list-p)
  (span-witness (bit-mat-add x (car (find-summand-a-neq sch x)))
                (a-components (arb-basis sch x n))
                n n))

(define arb-us ((sch mat-triple-listp) (x bit-list-listp) (n natp))
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (union-theories (theory 'arb-guard-lemmas)
                                            (current-theory :here))))
  :returns (us mat-triple-listp :hyp :guard)
  (select-summands (arb-coeffs sch x n) (arb-basis sch x n)))

;;; The path: the add-duplicate step for (A0,B0,C0) and u1 manufactures the
;;; first pair, and grow-chain walks it along the rest of the chain.

(define add-arbitrary-a-path ((sch mat-triple-listp) (x bit-list-listp) (n natp))
  :returns (moves move-list-p :hyp :guard
                  :hints (("Goal"
                           :do-not-induct t
                           :in-theory (union-theories (theory 'arb-guard-lemmas)
                                                      (disable arb-us mat-triple-listp
                                                               add-duplicate-path
                                                               grow-chain
                                                               find-summand-a-neq))
                           :use (mat-triple-listp-of-arb-us
                                 (:instance mat-triple-head-facts
                                            (l (arb-us sch x n)))))))
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (union-theories (theory 'arb-guard-lemmas)
                                            (disable arb-us mat-triple-listp))
                 :use (mat-triple-listp-of-arb-us
                       (:instance mat-triple-head-facts
                                  (l (arb-us sch x n))))))
  (let* ((s0 (find-summand-a-neq sch x))
         (a0 (car s0))
         (b0 (cadr s0))
         (c0 (caddr s0))
         (us (arb-us sch x n))
         (u1 (car us)))
    (append (add-duplicate-path a0 b0 c0 (car u1) (cadr u1) (caddr u1) n)
            (grow-chain (bit-mat-add a0 (car u1)) b0 c0 (cdr us) n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Executable validation at n = 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The standard rank-8 scheme (e_ij (x) e_jk (x) e_ik for i,j,k < 2).

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

(assert-event (correct-schemep *arb-std2* 2))

;;; One coefficient-0 case and one coefficient-1 case for the seed,
;;; checked end to end: the path is valid and lands exactly on the scheme
;;; plus two copies of (summand x b0 c0).  (All 15 nonzero 2x2 matrices
;;; were checked during development.)

(defconst *arb-x1* '((0 1) (1 0)))
(defconst *arb-x2* '((1 1) (1 1)))

(assert-event
 (and (let* ((x *arb-x1*)
             (s0 (find-summand-a-neq *arb-std2* x))
             (a0 (car s0))
             (us (arb-us *arb-std2* x 2))
             (path (add-arbitrary-a-path *arb-std2* x 2)))
        (and (not (equal a0 x))
             (independentp (a-components (arb-basis *arb-std2* x 2)) 2 2)
             (partial-sums-okp a0 us 2)
             (equal (chain-sum a0 us) x)
             (path-validp path *arb-std2* 2)
             (equal (apply-moves path *arb-std2* 2)
                    (obag::insert (summand x (cadr s0) (caddr s0))
                                  (obag::insert (summand x (cadr s0) (caddr s0))
                                                *arb-std2*)))))
      (let* ((x *arb-x2*)
             (s0 (find-summand-a-neq *arb-std2* x))
             (a0 (car s0))
             (us (arb-us *arb-std2* x 2))
             (path (add-arbitrary-a-path *arb-std2* x 2)))
        (and (not (equal a0 x))
             (independentp (a-components (arb-basis *arb-std2* x 2)) 2 2)
             (partial-sums-okp a0 us 2)
             (equal (chain-sum a0 us) x)
             (path-validp path *arb-std2* 2)
             (equal (apply-moves path *arb-std2* 2)
                    (obag::insert (summand x (cadr s0) (caddr s0))
                                  (obag::insert (summand x (cadr s0) (caddr s0))
                                                *arb-std2*)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Bridge lemmas
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The two unit-matrix definitions (top.lisp vs gf2span.lisp) coincide.

(defruled bit-mat-unit2-is-bit-mat-unit
  (equal (bit-mat-unit2 i j m n)
         (bit-mat-unit i j m n))
  :induct (bit-mat-unit2 i j m n)
  :enable (bit-mat-unit2 bit-mat-unit))

;;; Membership in the list sense gives obag membership on bags.

(defruled in-when-member-equal
  (implies (and (obag::bagp sch)
                (member-equal s sch))
           (obag::in s sch))
  :induct (member-equal s sch)
  :enable (obag::in obag::head obag::tail obag::emptyp obag::bfix obag::bagp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 1: the A-components of a correct scheme span everything
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The witness sum lies in the span of the A-components.

(defruled in-spanp-of-a-witness-sum
  (implies (and (summand-dim-listp l n)
                (natp n))
           (in-spanp (a-witness-sum l i j k n) (a-components l) n n))
  :induct (a-witness-sum l i j k n)
  :enable (a-witness-sum a-components in-spanp in-spanp-step))

;;; Every unit matrix is in the span of the A-components of a correct
;;; scheme (the span lemma, transported to the span predicate).

(defruled unit-in-a-span
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (natp j) (< i n) (< j n))
           (in-spanp (bit-mat-unit i j n n) (a-components sch) n n))
  :do-not-induct t
  :enable (correct-schemep)
  :disable (a-witness-sum bit-mat-unit)
  :use ((:instance span-lemma (k 0))
        (:instance in-spanp-of-a-witness-sum (l sch) (k 0))))

;;; all-in-spanp distributes over append.

(defruled all-in-spanp-of-append
  (equal (all-in-spanp (append l1 l2) mats m n)
         (and (all-in-spanp l1 mats m n)
              (all-in-spanp l2 mats m n)))
  :induct (cdr-induct l1)
  :enable (all-in-spanp))

;;; Rows and the full grid of units are in the span.

(defruled all-in-spanp-of-unit-row
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (< i n) (natp j))
           (all-in-spanp (unit-row i j n n) (a-components sch) n n))
  :induct (unit-row i j n n)
  :enable (unit-row all-in-spanp unit-in-a-span
           bit-mat-unit2-is-bit-mat-unit))

(defruled all-in-spanp-of-all-units
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (natp j))
           (all-in-spanp (all-units i j n n) (a-components sch) n n))
  :induct (all-units i j n n)
  :enable (all-units all-in-spanp all-in-spanp-of-append
           all-in-spanp-of-unit-row))

(defruled spans-unitsp-of-a-components
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n))
           (spans-unitsp (a-components sch) n n))
  :enable (spans-unitsp)
  :use ((:instance all-in-spanp-of-all-units (i 0) (j 0))))

;;; Stage 1 capstone.

(defruled a-components-span-everything
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (bit-matp y n n))
           (in-spanp y (a-components sch) n n))
  :do-not-induct t
  :enable (correct-schemep)
  :use (spans-unitsp-of-a-components
        (:instance in-spanp-when-spans-unitsp
                   (mats (a-components sch)) (x y) (m n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 2: span algebra and the extracted basis
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Extending the list on the right preserves span membership.

(defruled in-spanp-of-append-weaken
  (implies (and (in-spanp x l1 m n)
                (bit-mat-listnp l2 m n))
           (in-spanp x (append l1 l2) m n))
  :induct (in-spanp x l1 m n)
  :enable (in-spanp))

;;; If x + a and a are in a span, so is x.

(defruled span-step-lemma
  (implies (and (in-spanp (bit-mat-add x a) mats2 m n)
                (in-spanp a mats2 m n)
                (bit-matp x m n)
                (bit-matp a m n)
                (bit-mat-listnp mats2 m n))
           (in-spanp x mats2 m n))
  :do-not-induct t
  :use ((:instance in-spanp-closed-under-add
                   (x (bit-mat-add x a)) (y a) (mats mats2))))

;;; Transitivity: if x is in span(mats) and every element of mats is in
;;; span(mats2), then x is in span(mats2).

(defruled span-subset-transitive
  (implies (and (in-spanp x mats m n)
                (all-in-spanp mats mats2 m n)
                (bit-matp x m n)
                (bit-mat-listnp mats m n)
                (bit-mat-listnp mats2 m n)
                (natp m) (natp n))
           (in-spanp x mats2 m n))
  :induct (in-spanp x mats m n)
  :enable (in-spanp all-in-spanp bit-mat-listnp span-step-lemma))

;;; us-in-schemep distributes over append; basis-new preserves it.

(defruled us-in-schemep-of-append
  (equal (us-in-schemep (append l1 l2) sch)
         (and (us-in-schemep l1 sch)
              (us-in-schemep l2 sch)))
  :induct (cdr-induct l1)
  :enable (us-in-schemep))

(defruled us-in-schemep-of-basis-new
  (implies (and (us-in-schemep l sch)
                (us-in-schemep acc sch))
           (us-in-schemep (basis-new l acc n) sch))
  :induct (basis-new l acc n)
  :enable (basis-new us-in-schemep us-in-schemep-of-append))

;;; Independence of the extracted basis (with the accumulator appended).

(defruled independentp-of-basis-new
  (implies (and (independentp (a-components acc) n n)
                (summand-dim-listp l n)
                (summand-dim-listp acc n)
                (natp n))
           (independentp (a-components (append (basis-new l acc n) acc)) n n))
  :induct (basis-new l acc n)
  :enable (basis-new independentp a-components a-components-of-append))

(defruled summand-dim-listp-of-basis-new
  (implies (and (summand-dim-listp l n)
                (summand-dim-listp acc n))
           (summand-dim-listp (basis-new l acc n) n))
  :induct (basis-new l acc n)
  :enable (basis-new summand-dim-listp-of-append))

;;; Every list is all-in-spanp of itself.

(local
 (defrule subsetp-equal-of-cons-right
   (implies (subsetp-equal l mats)
            (subsetp-equal l (cons a mats)))
   :induct (cdr-induct l)))

(local
 (defrule subsetp-equal-reflexive
   (subsetp-equal l l)
   :induct (cdr-induct l)))

(defruled all-in-spanp-reflexive
  (implies (bit-mat-listnp mats m n)
           (all-in-spanp mats mats m n))
  :use ((:instance all-in-spanp-when-subsetp (l mats))))

;;; Span preservation: everything in l or acc has its A-component in the
;;; span of the A-components of (basis-new l acc n) ++ acc.

(defruled basis-new-spans
  (implies (and (summand-dim-listp l n)
                (summand-dim-listp acc n)
                (natp n))
           (and (all-in-spanp (a-components l)
                              (a-components (append (basis-new l acc n) acc))
                              n n)
                (all-in-spanp (a-components acc)
                              (a-components (append (basis-new l acc n) acc))
                              n n)))
  :induct (basis-new l acc n)
  :enable (basis-new all-in-spanp a-components a-components-of-append
           span-subset-transitive all-in-spanp-reflexive
           summand-dim-listp-of-append summand-dim-listp-of-basis-new
           member-in-spanp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 3: choosing s0 and the chain
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The arithmetic book is included here, after the events above, so that
;;; the proof environment of the first half of this book is unchanged.
(local (include-book "arithmetic/top-with-meta" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 3a: a summand with A-component different from x exists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; all elements of a matrix list equal x

(define all-eqp ((mats bit-mat-list-p) (x bit-list-listp))
  :returns (yes/no booleanp)
  (if (atom mats)
      t
    (and (equal (car mats) x)
         (all-eqp (cdr mats) x))))

;;; The span of a constant list is {0, x}.

(defrule in-spanp-collapse-when-all-eqp
  (implies (and (all-eqp mats x)
                (in-spanp y mats m n)
                (bit-matp y m n)
                (bit-matp x m n)
                (bit-mat-listnp mats m n)
                (natp m) (natp n))
           (or (equal y (bit-mat0 m n))
               (equal y x)))
  :rule-classes nil
  :induct (in-spanp y mats m n)
  :enable (in-spanp all-eqp bit-mat-listnp
           bit-mat-add-equal-arg2))

(defruled all-eqp-when-find-fails
  (implies (and (summand-listp l n)
                (not (find-summand-a-neq l x)))
           (all-eqp (a-components l) x))
  :induct (find-summand-a-neq l x)
  :enable (find-summand-a-neq all-eqp a-components))

(defruled find-summand-a-neq-props
  (implies (find-summand-a-neq l x)
           (and (member-equal (find-summand-a-neq l x) l)
                (not (equal (car (find-summand-a-neq l x)) x))))
  :induct (find-summand-a-neq l x)
  :enable (find-summand-a-neq))

;;; If every A-component equaled x, the span would be contained in {0, x};
;;; but for n >= 2 the units E00 and E01 are distinct, nonzero, and both in
;;; the span -- contradiction.  So the search succeeds.

(defruled find-summand-a-neq-succeeds
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n))
           (find-summand-a-neq sch x))
  :do-not-induct t
  :enable (correct-schemep)
  :disable (bit-mat-unit mat-entry)
  :use ((:instance unit-in-a-span (i 0) (j 0))
        (:instance unit-in-a-span (i 0) (j 1))
        (:instance all-eqp-when-find-fails (l sch) (n n))
        (:instance in-spanp-collapse-when-all-eqp
                   (mats (a-components sch)) (y (bit-mat-unit 0 0 n n)) (m n))
        (:instance in-spanp-collapse-when-all-eqp
                   (mats (a-components sch)) (y (bit-mat-unit 0 1 n n)) (m n))
        (:instance mat-entry-of-bit-mat-unit (a 0) (b 0) (i 0) (j 0) (m n))
        (:instance mat-entry-of-bit-mat-unit (a 0) (b 1) (i 0) (j 0) (m n))
        (:instance mat-entry-of-bit-mat-unit (a 0) (b 0) (i 0) (j 1) (m n))
        (:instance mat-entry-of-bit-mat-unit (a 0) (b 1) (i 0) (j 1) (m n))
        (:instance mat-entry-of-bit-mat0 (i 0) (j 0) (m n))
        (:instance mat-entry-of-bit-mat0 (i 0) (j 1) (m n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 3b: splitting off the seed at the end of the basis
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Splitting a linear combination over an appended matrix list.

(defruled lincomb-of-append-split
  (implies (and (bit-mat-listnp m1 m n)
                (bit-mat-listnp m2 m n)
                (natp m) (natp n))
           (equal (lincomb c (append m1 m2) m n)
                  (bit-mat-add (lincomb c m1 m n)
                               (lincomb (nthcdr (len m1) c) m2 m n))))
  :induct (lincomb c m1 m n)
  :enable (lincomb bit-mat-listnp nthcdr
           bit-mat-add-associative))

;;; Extra coefficients beyond the list length are ignored.

(defruled lincomb-of-append-coeffs
  (implies (equal (len d) (len mats))
           (equal (lincomb (append d z) mats m n)
                  (lincomb d mats m n)))
  :induct (lincomb d mats m n)
  :enable (lincomb))

(defruled nthcdr-of-len-of-append
  (implies (equal (len d) k)
           (equal (nthcdr k (append d z)) z))
  :induct (cdr-dec-induct d k)
  :enable (nthcdr))

(defruled nth-of-len-of-append
  (implies (equal (len d) k)
           (equal (nth k (append d z)) (car z)))
  :induct (cdr-dec-induct d k)
  :enable (nth))

;;; A vector ending in 1 is not the zero vector.

(defruled append-list-1-not-bit-listn0
  (not (equal (append d (list 1)) (bit-listn0 k)))
  :induct (cdr-dec-induct d k)
  :enable (bit-listn0 repeat))

;;; A prefix of an independent list is independent.

(defruled independentp-of-append-prefix
  (implies (and (independentp (append ws z) n n)
                (bit-mat-listnp ws n n)
                (bit-mat-listnp z n n))
           (independentp ws n n))
  :induct (cdr-induct ws)
  :enable (independentp bit-mat-listnp in-spanp-of-append-weaken))

;;; The last element of an independent list is not in the span of the
;;; rest: a vanishing combination whose coefficient vector ends in 1
;;; would contradict lincomb-nonzero-when-independentp.

(defruled not-in-spanp-last-when-independentp
  (implies (and (independentp (append ws (list a)) n n)
                (bit-mat-listnp ws n n)
                (bit-matp a n n)
                (natp n))
           (not (in-spanp a ws n n)))
  :do-not-induct t
  :enable (lincomb bit-mat-listnp bit-mat-add-same
           lincomb-of-append-coeffs
           nthcdr-of-len-of-append nth-of-len-of-append)
  :use ((:instance lincomb-of-span-witness (x a) (mats ws) (m n))
        (:instance lincomb-nonzero-when-independentp
                   (coeffs (append (span-witness a ws n n) (list 1)))
                   (mats (append ws (list a))) (m n))
        (:instance lincomb-of-append-split
                   (c (append (span-witness a ws n n) (list 1)))
                   (m1 ws) (m2 (list a)) (m n))
        (:instance append-list-1-not-bit-listn0
                   (d (span-witness a ws n n))
                   (k (len (append ws (list a)))))
        (:instance bit-listnp-of-append
                   (x (span-witness a ws n n)) (y (list 1))
                   (m (len ws)) (n 1) (l (+ 1 (len ws))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 3c: chain sums and partial sums of a selected chain
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Pulling an addend out of the chain accumulator.

(defruled chain-sum-of-add
  (equal (chain-sum (bit-mat-add p q) us)
         (bit-mat-add p (chain-sum q us)))
  :induct (chain-sum q us)
  :enable (chain-sum bit-mat-add-associative))

(defruled chain-sum-select-step
  (equal (chain-sum (bit-mat-add p a) us)
         (bit-mat-add a (chain-sum p us)))
  :do-not-induct t
  :use ((:instance chain-sum-of-add (p a) (q p)))
  :enable (bit-mat-add-commutative))

;;; The chain over a selected sublist is the linear combination.

(defruled chain-sum-of-select-summands
  (implies (and (summand-dim-listp l n)
                (bit-matp p n n)
                (natp n))
           (equal (chain-sum p (select-summands c l))
                  (bit-mat-add p (lincomb c (a-components l) n n))))
  :induct (select-summands c l)
  :enable (chain-sum select-summands lincomb a-components
           chain-sum-select-step
           bit-mat-add-commutative bit-mat-add-commutative-2
           bit-mat-add-associative))

;;; chain-sum and partial-sums-okp over append.

(defruled chain-sum-of-append
  (equal (chain-sum p (append u1 u2))
         (chain-sum (chain-sum p u1) u2))
  :induct (chain-sum p u1)
  :enable (chain-sum))

(defruled partial-sums-okp-of-append
  (equal (partial-sums-okp p (append u1 u2) n)
         (and (partial-sums-okp p u1 n)
              (partial-sums-okp (chain-sum p u1) u2 n)))
  :induct (chain-sum p u1)
  :enable (chain-sum partial-sums-okp))

(defruled chain-sum-nonzero-when-partial-sums-okp
  (implies (partial-sums-okp p us n)
           (not (equal (chain-sum p us) (bit-mat0 n n))))
  :induct (chain-sum p us)
  :enable (chain-sum partial-sums-okp))

;;; The computable partial-sum check equals partial-sums-okp of the chain.

(defruled select-chain-okp-as-partial-sums-okp
  (equal (select-chain-okp p c l n)
         (partial-sums-okp p (select-summands c l) n))
  :induct (select-chain-okp p c l n)
  :enable (select-chain-okp select-summands partial-sums-okp))

;;; The heart of Stage 3: when p together with the A-components of l is
;;; independent, every partial sum along ANY selected chain is nonzero.
;;; (The induction carries the invariant that the running sum stays
;;; independent from the remaining A-components.)

(defruled select-chain-okp-when-independent
  (implies (and (independentp (cons p (a-components l)) n n)
                (bit-matp p n n)
                (summand-dim-listp l n)
                (natp n))
           (select-chain-okp p c l n))
  :induct (select-chain-okp p c l n)
  :enable (select-chain-okp independentp in-spanp a-components))

;;; select-summands: membership, typing, append.

(defruled us-in-schemep-of-select-summands
  (implies (us-in-schemep l sch)
           (us-in-schemep (select-summands c l) sch))
  :induct (select-summands c l)
  :enable (select-summands us-in-schemep))

(defruled summand-listp-of-select-summands
  (implies (summand-listp l n)
           (summand-listp (select-summands c l) n))
  :induct (select-summands c l)
  :enable (select-summands))

(defruled select-summands-of-append
  (equal (select-summands c (append l1 l2))
         (append (select-summands c l1)
                 (select-summands (nthcdr (len l1) c) l2)))
  :induct (select-summands c l1)
  :enable (select-summands nthcdr))

;;; A scheme is us-in-schemep of itself.

(defruled us-in-schemep-when-subsetp
  (implies (and (obag::bagp sch)
                (subsetp-equal l sch))
           (us-in-schemep l sch))
  :induct (cdr-induct l)
  :enable (us-in-schemep in-when-member-equal))

(defruled us-in-schemep-of-self
  (implies (obag::bagp sch)
           (us-in-schemep sch sch))
  :use ((:instance us-in-schemep-when-subsetp (l sch))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 3d: the chosen objects and their properties
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Facts about the chosen summand s0.

(defruled arb-s0-facts
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n))
           (and (summandp (find-summand-a-neq sch x) n)
                (obag::in (find-summand-a-neq sch x) sch)
                (not (equal (car (find-summand-a-neq sch x)) x))))
  :do-not-induct t
  :enable (correct-schemep)
  :use (find-summand-a-neq-succeeds
        (:instance find-summand-a-neq-props (l sch))
        (:instance in-when-member-equal (s (find-summand-a-neq sch x)))
        (:instance summandp-when-in-summand-listp
                   (s (find-summand-a-neq sch x)))))

;;; Facts about the extracted basis.

(defruled arb-basis-facts
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n))
           (and (summand-listp (arb-basis sch x n) n)
                (us-in-schemep (arb-basis sch x n) sch)
                (independentp (a-components (arb-basis sch x n)) n n)))
  :do-not-induct t
  :enable (arb-basis correct-schemep a-components independentp in-spanp
           us-in-schemep summand-listp-of-append us-in-schemep-of-append
           us-in-schemep-of-basis-new)
  :use (arb-s0-facts
        us-in-schemep-of-self
        (:instance independentp-of-basis-new
                   (l sch) (acc (list (find-summand-a-neq sch x))))
        (:instance us-in-schemep-of-basis-new
                   (l sch) (acc (list (find-summand-a-neq sch x))))))

;;; The basis spans everything.

(defruled arb-basis-spans
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n)
                (bit-matp y n n))
           (in-spanp y (a-components (arb-basis sch x n)) n n))
  :do-not-induct t
  :enable (arb-basis correct-schemep)
  :use (arb-s0-facts
        arb-basis-facts
        (:instance a-components-span-everything)
        (:instance basis-new-spans
                   (l sch) (acc (list (find-summand-a-neq sch x))))
        (:instance span-subset-transitive
                   (x y) (mats (a-components sch))
                   (mats2 (a-components (arb-basis sch x n)))
                   (m n))))

;;; The witness coefficients reconstruct x + a0.

(defruled lincomb-of-arb-coeffs
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n))
           (equal (lincomb (arb-coeffs sch x n)
                           (a-components (arb-basis sch x n)) n n)
                  (bit-mat-add x (car (find-summand-a-neq sch x)))))
  :do-not-induct t
  :enable (arb-coeffs correct-schemep)
  :use (arb-s0-facts
        arb-basis-facts
        (:instance arb-basis-spans
                   (y (bit-mat-add x (car (find-summand-a-neq sch x)))))
        (:instance lincomb-of-span-witness
                   (x (bit-mat-add x (car (find-summand-a-neq sch x))))
                   (mats (a-components (arb-basis sch x n)))
                   (m n))))

;;; The Stage 3 capstone: the selected chain has all partial sums nonzero
;;; and lands exactly on x.  The two coefficient cases of the paper (the
;;; coefficient of A0 in the basis expansion being 0 or 1) show up here as
;;; the case split on the last coefficient; because the seed sits at the
;;; end of the basis list, the coefficient-1 case automatically appends
;;; the extra copy of A0 at the END of the chain, exactly the paper's
;;; ordering trick.

(defruled arb-us-okp
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n)
                (not (equal x (bit-mat0 n n))))
           (and (partial-sums-okp (car (find-summand-a-neq sch x))
                                  (arb-us sch x n) n)
                (equal (chain-sum (car (find-summand-a-neq sch x))
                                  (arb-us sch x n))
                       x)))
  :do-not-induct t
  :enable (arb-us arb-basis correct-schemep
           a-components a-components-of-append
           select-summands lincomb partial-sums-okp chain-sum
           chain-sum-of-append partial-sums-okp-of-append
           select-chain-okp-as-partial-sums-okp
           independentp bit-mat-listnp
           bit-mat-add-commutative bit-mat-add-commutative-2
           bit-mat-add-associative bit-mat-add-same)
  :use (arb-s0-facts
        arb-basis-facts
        lincomb-of-arb-coeffs
        (:instance select-summands-of-append
                   (c (arb-coeffs sch x n))
                   (l1 (basis-new sch (list (find-summand-a-neq sch x)) n))
                   (l2 (list (find-summand-a-neq sch x))))
        (:instance lincomb-of-append-split
                   (c (arb-coeffs sch x n))
                   (m1 (a-components
                        (basis-new sch (list (find-summand-a-neq sch x)) n)))
                   (m2 (list (car (find-summand-a-neq sch x))))
                   (m n))
        (:instance independentp-of-append-prefix
                   (ws (a-components
                        (basis-new sch (list (find-summand-a-neq sch x)) n)))
                   (z (list (car (find-summand-a-neq sch x)))))
        (:instance not-in-spanp-last-when-independentp
                   (ws (a-components
                        (basis-new sch (list (find-summand-a-neq sch x)) n)))
                   (a (car (find-summand-a-neq sch x))))
        (:instance select-chain-okp-when-independent
                   (p (car (find-summand-a-neq sch x)))
                   (c (arb-coeffs sch x n))
                   (l (basis-new sch (list (find-summand-a-neq sch x)) n)))
        (:instance chain-sum-of-select-summands
                   (p (car (find-summand-a-neq sch x)))
                   (c (arb-coeffs sch x n))
                   (l (basis-new sch (list (find-summand-a-neq sch x)) n)))
        (:instance chain-sum-nonzero-when-partial-sums-okp
                   (p (car (find-summand-a-neq sch x)))
                   (us (select-summands
                        (arb-coeffs sch x n)
                        (basis-new sch (list (find-summand-a-neq sch x)) n))))))

;;; Membership and typing of the chain; nonemptiness.

(defruled arb-us-more-facts
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n))
           (and (us-in-schemep (arb-us sch x n) sch)
                (summand-listp (arb-us sch x n) n)))
  :do-not-induct t
  :enable (arb-us us-in-schemep-of-select-summands
           summand-listp-of-select-summands)
  :use (arb-basis-facts))

;;; If the chain were empty its sum would be a0, but the sum is x /= a0.

(defruled consp-of-arb-us
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n)
                (not (equal x (bit-mat0 n n))))
           (consp (arb-us sch x n)))
  :do-not-induct t
  :enable (chain-sum)
  :use (arb-us-okp arb-s0-facts))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 4: the add-arbitrary lemma, A position
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; From any correct scheme sch (n >= 2) and any nonzero n x n matrix x,
;;; the constructed path is valid, lands exactly on sch plus two copies of
;;; (summand x B0 C0) -- where (A0, B0, C0) is the chosen summand of sch,
;;; A0 /= x -- and the result is again a correct scheme.

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
                  (correct-schemep sch2 n))))
  :do-not-induct t
  :enable (add-arbitrary-a-path correct-schemep)
  :disable (add-duplicate-path grow-chain add-arbitrary-relative)
  :use (arb-s0-facts
        arb-us-okp
        arb-us-more-facts
        consp-of-arb-us
        (:instance add-arbitrary-relative
                   (a0 (car (find-summand-a-neq sch x)))
                   (b0 (cadr (find-summand-a-neq sch x)))
                   (c0 (caddr (find-summand-a-neq sch x)))
                   (us (arb-us sch x n)))
        (:instance correct-schemep-of-apply-moves
                   (moves (add-arbitrary-a-path sch x n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stage 5: the B and C positions, and the full add-arbitrary lemma
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; The A-position development above is mirrored in the B and C positions:
;;;
;;;  - add-duplicate-b / add-duplicate-c: the pair-manufacturing path of Lemma 4.5,
;;;    with the moves cyclically shifted one and two positions
;;;    (plus@1 [plus@2, plus@1, flip@1] with special case c1 = c2, and
;;;     plus@2 [plus@0, plus@2, flip@2] with special case a1 = a2).
;;;    Both were validated by execution at n = 2 on all 64 ordered summand
;;;    pairs of the standard scheme before proving.
;;;  - grow-chain-b / grow-chain-c and add-arbitrary-relative-b / -c: the
;;;    iteration cores, mirroring iterate.lisp.
;;;  - b-components / c-components span everything (b-span-lemma /
;;;    c-span-lemma), the seeded greedy bases, and the chain constructions.
;;;    Unlike the A position, the seed summand s0 here is a PARAMETER (in
;;;    the full lemma it is one of the two copies just added), so no search
;;;    and no n >= 2 side condition are needed in these stages.
;;;  - add-arbitrary-b / add-arbitrary-c: from a correct scheme containing
;;;    s0 and a nonzero target different from s0's component, a valid path
;;;    adds the pair with that component replaced.
;;;  - add-arbitrary-b-replace / -c-replace: the same, starting from
;;;    sch + pair(s0) and DELETING the old pair afterwards (self-flip,
;;;    rem:delete-identical-pair), landing on sch + the new pair.
;;;  - add-arbitrary: the full lemma.  For nonzero X, Y, Z the composed
;;;    path walks sch to sch + two copies of X (x) Y (x) Z: the A leg
;;;    manufactures pair(X, B0, C0); the B leg replaces B0 by Y (empty if
;;;    B0 = Y); the C leg replaces C0 by Z (empty if C0 = Z).
;;;    Validated end to end at n = 2 (see the assert-event forms below).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 5a: Lemma 4.5 in the B and C positions; iteration cores
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; add-duplicate-b (validated in probe 6)

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

(local
 (defruled bit-list-add-cancel-first
   (implies (and (bit-list-p y)
                 (<= (len y) (len x)))
            (equal (bit-list-add x (bit-list-add x y))
                   y))
   :induct (cdr-cdr-induct x y)
   :enable (bit-list-add)))

(defruled add-duplicate-b-validp-core
  (implies (and (obag::bagp sch)
                (summandp (summand a1 b1 c1) n)
                (summandp (summand a2 b2 c2) n)
                (obag::in (summand a1 b1 c1) sch)
                (obag::in (summand a2 b2 c2) sch))
           (path-validp (add-duplicate-b-path a1 b1 c1 a2 b2 c2 n) sch n))
  :use ((:instance bit-mat-add-equal-arg2 (a c1) (b c2) (m n) (n n))
        (:instance bit-mat-add-equal-arg1 (a b1) (b b2) (m n) (n n))
        (:instance bit-mat-add-equal-arg2 (a b1) (b b2) (m n) (n n))
        (:instance bit-mat-add-equal-arg1 (a c1) (b c2) (m n) (n n)))
  :in-theory (enable apply-move in-of-insert in-of-delete))

(defruled add-duplicate-b-result-core
  (implies (and (obag::bagp sch)
                (summandp (summand a1 b1 c1) n)
                (summandp (summand a2 b2 c2) n)
                (obag::in (summand a1 b1 c1) sch)
                (obag::in (summand a2 b2 c2) sch))
           (equal (apply-moves (add-duplicate-b-path a1 b1 c1 a2 b2 c2 n) sch n)
                  (insert-all-nonzero
                   (list (summand a1 (bit-mat-add b1 b2) c1)
                         (summand a1 (bit-mat-add b1 b2) c1))
                   sch n)))
  :use ((:instance bit-mat-add-equal-arg2 (a c1) (b c2) (m n) (n n))
        (:instance bit-mat-add-equal-arg1 (a b1) (b b2) (m n) (n n))
        (:instance bit-mat-add-equal-arg2 (a b1) (b b2) (m n) (n n))
        (:instance bit-mat-add-equal-arg1 (a c1) (b c2) (m n) (n n)))
  :in-theory (enable apply-moves apply-move in-of-insert in-of-delete))

(defrule add-duplicate-b
  (implies (and (schemep sch n)
                (obag::in (summand a1 b1 c1) sch)
                (obag::in (summand a2 b2 c2) sch))
           (let ((path (add-duplicate-b-path a1 b1 c1 a2 b2 c2 n))
                 (y (bit-mat-add b1 b2)))
             (and (path-validp path sch n)
                  (equal (apply-moves path sch n)
                         (insert-all-nonzero (list (summand a1 y c1)
                                                   (summand a1 y c1))
                                             sch
                                             n)))))
  :use ((:instance summandp-when-in-summand-listp (s (summand a1 b1 c1)))
        (:instance summandp-when-in-summand-listp (s (summand a2 b2 c2)))
        add-duplicate-b-validp-core
        add-duplicate-b-result-core))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; add-duplicate-c

(define add-duplicate-c-path ((a1 bit-list-listp) (b1 bit-list-listp) (c1 bit-list-listp)
                         (a2 bit-list-listp) (b2 bit-list-listp) (c2 bit-list-listp)
                         (n natp))
  :enabled t
  :returns (moves move-list-p :hyp :guard)
  (let* ((z (bit-mat-add c1 c2))
         (s1 (summand a1 b1 c1))
         (s2 (summand a2 b2 c2)))
    (cond ((equal z (bit-mat0 n n)) nil)
          ((equal a1 a2)
           (list (list :plus 2 s1 s2)
                 (list :plus 2 (summand a1 b1 c2) (summand a1 b1 z))))
          (t
           (list (list :plus 2 s1 s2)
                 (list :plus 0 (summand a1 b1 z) s2)
                 (list :plus 2 (summand a1 b1 c2) (summand (bit-mat-add a1 a2) b1 z))
                 (list :flip 2
                       (summand (bit-mat-add a1 a2) b1 z)
                       (summand a2 b1 z)))))))

(defruled add-duplicate-c-validp-core
  (implies (and (obag::bagp sch)
                (summandp (summand a1 b1 c1) n)
                (summandp (summand a2 b2 c2) n)
                (obag::in (summand a1 b1 c1) sch)
                (obag::in (summand a2 b2 c2) sch))
           (path-validp (add-duplicate-c-path a1 b1 c1 a2 b2 c2 n) sch n))
  :use ((:instance bit-mat-add-equal-arg2 (a a1) (b a2) (m n) (n n))
        (:instance bit-mat-add-equal-arg1 (a c1) (b c2) (m n) (n n))
        (:instance bit-mat-add-equal-arg2 (a c1) (b c2) (m n) (n n))
        (:instance bit-mat-add-equal-arg1 (a a1) (b a2) (m n) (n n)))
  :in-theory (enable apply-move in-of-insert in-of-delete))

(defruled add-duplicate-c-result-core
  (implies (and (obag::bagp sch)
                (summandp (summand a1 b1 c1) n)
                (summandp (summand a2 b2 c2) n)
                (obag::in (summand a1 b1 c1) sch)
                (obag::in (summand a2 b2 c2) sch))
           (equal (apply-moves (add-duplicate-c-path a1 b1 c1 a2 b2 c2 n) sch n)
                  (insert-all-nonzero
                   (list (summand a1 b1 (bit-mat-add c1 c2))
                         (summand a1 b1 (bit-mat-add c1 c2)))
                   sch n)))
  :use ((:instance bit-mat-add-equal-arg2 (a a1) (b a2) (m n) (n n))
        (:instance bit-mat-add-equal-arg1 (a c1) (b c2) (m n) (n n))
        (:instance bit-mat-add-equal-arg2 (a c1) (b c2) (m n) (n n))
        (:instance bit-mat-add-equal-arg1 (a a1) (b a2) (m n) (n n)))
  :in-theory (enable apply-moves apply-move in-of-insert in-of-delete))

(defrule add-duplicate-c
  (implies (and (schemep sch n)
                (obag::in (summand a1 b1 c1) sch)
                (obag::in (summand a2 b2 c2) sch))
           (let ((path (add-duplicate-c-path a1 b1 c1 a2 b2 c2 n))
                 (z (bit-mat-add c1 c2)))
             (and (path-validp path sch n)
                  (equal (apply-moves path sch n)
                         (insert-all-nonzero (list (summand a1 b1 z)
                                                   (summand a1 b1 z))
                                             sch
                                             n)))))
  :use ((:instance summandp-when-in-summand-listp (s (summand a1 b1 c1)))
        (:instance summandp-when-in-summand-listp (s (summand a2 b2 c2)))
        add-duplicate-c-validp-core
        add-duplicate-c-result-core))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; iterate layer, B position

(define chain-sum-b ((p bit-list-listp) (us mat-triple-listp))
  :returns (q bit-list-listp :hyp :guard)
  (if (atom us)
      p
    (chain-sum-b (bit-mat-add p (cadr (car us))) (cdr us))))

(define partial-sums-okp-b ((p bit-list-listp) (us mat-triple-listp) (n natp))
  :returns (yes/no booleanp)
  :measure (acl2-count us)
  (and (not (equal p (bit-mat0 n n)))
       (if (atom us)
           t
         (partial-sums-okp-b (bit-mat-add p (cadr (car us))) (cdr us) n)))
  ///
  (defrule partial-sums-okp-b-nonzero
    (implies (partial-sums-okp-b p us n)
             (not (equal p (bit-mat0 n n)))))
  (defrule partial-sums-okp-b-of-cdr
    (implies (and (partial-sums-okp-b p us n)
                  (consp us))
             (partial-sums-okp-b (bit-mat-add p (cadr (car us))) (cdr us) n))))

(define grow-chain-b ((a0 bit-list-listp) (p bit-list-listp) (c0 bit-list-listp)
                      (us mat-triple-listp) (n natp))
  :returns (moves move-list-p :hyp :guard)
  (if (atom us)
      nil
    (let ((u (car us))
          (s (summand a0 p c0)))
      (append (append (add-duplicate-b-path a0 p c0 (car u) (cadr u) (caddr u) n)
                      (list (list :flip 0 s s)))
              (grow-chain-b a0 (bit-mat-add p (cadr u)) c0 (cdr us) n)))))

(defruled one-step-b
  (implies (and (schemep sch n)
                (natp n)
                (summandp (summand a0 p c0) n)
                (obag::in u sch)
                (not (equal (bit-mat-add p (cadr u)) (bit-mat0 n n))))
           (let* ((s (summand a0 p c0))
                  (cur (obag::insert s (obag::insert s sch)))
                  (y (bit-mat-add p (cadr u)))
                  (path (append (add-duplicate-b-path a0 p c0
                                                 (car u) (cadr u) (caddr u) n)
                                (list (list :flip 0 s s)))))
             (and (path-validp path cur n)
                  (equal (apply-moves path cur n)
                         (obag::insert (summand a0 y c0)
                                       (obag::insert (summand a0 y c0) sch))))))
  :do-not-induct t
  :use ((:instance add-duplicate-b
                   (sch (obag::insert (summand a0 p c0)
                                      (obag::insert (summand a0 p c0) sch)))
                   (a1 a0) (b1 p) (c1 c0)
                   (a2 (car u)) (b2 (cadr u)) (c2 (caddr u)))
        (:instance bit-mat-add-equal-arg1 (a p) (b (cadr u)) (m n) (n n))
        (:instance summandp-when-in-summand-listp (s u)))
  :enable (apply-moves in-of-insert obag::occs-of-insert)
  :disable (add-duplicate-b add-duplicate-b-path summandp-when-in-summand-listp))

(defrule grow-chain-b-invariant
  (implies (and (schemep sch n)
                (natp n)
                (summandp (summand a0 p c0) n)
                (us-in-schemep us sch)
                (summand-listp us n)
                (partial-sums-okp-b p us n))
           (let ((cur (obag::insert (summand a0 p c0)
                                    (obag::insert (summand a0 p c0) sch)))
                 (y (chain-sum-b p us)))
             (and (path-validp (grow-chain-b a0 p c0 us n) cur n)
                  (equal (apply-moves (grow-chain-b a0 p c0 us n) cur n)
                         (obag::insert (summand a0 y c0)
                                       (obag::insert (summand a0 y c0) sch))))))
  :hints (("Goal"
           :induct (grow-chain-b a0 p c0 us n)
           :do-not-induct t
           :in-theory (e/d (grow-chain-b chain-sum-b apply-moves
                            partial-sums-okp-b bit-mat-add-same
                            in-of-insert obag::occs-of-insert)
                           (add-duplicate-b add-duplicate-b-path
                            summandp-when-in-summand-listp)))
          ("Subgoal *1/2"
           :use ((:instance one-step-b (u (car us)))
                 (:instance summandp-when-in-summand-listp (s (car us)))
                 (:instance bit-mat-add-equal-arg1
                            (a p) (b (cadr (car us))) (m n) (n n))))))

(defrule add-arbitrary-relative-b
  (implies (and (schemep sch n)
                (natp n)
                (obag::in (summand a0 b0 c0) sch)
                (us-in-schemep us sch)
                (summand-listp us n)
                (consp us)
                (partial-sums-okp-b b0 us n))
           (let* ((u1 (car us))
                  (p1 (bit-mat-add b0 (cadr u1)))
                  (path (append (add-duplicate-b-path a0 b0 c0
                                                 (car u1) (cadr u1) (caddr u1) n)
                                (grow-chain-b a0 p1 c0 (cdr us) n)))
                  (y (chain-sum-b b0 us)))
             (and (path-validp path sch n)
                  (equal (apply-moves path sch n)
                         (obag::insert (summand a0 y c0)
                                       (obag::insert (summand a0 y c0) sch))))))
  :do-not-induct t
  :use ((:instance add-duplicate-b
                   (a1 a0) (b1 b0) (c1 c0)
                   (a2 (car (car us))) (b2 (cadr (car us))) (c2 (caddr (car us))))
        (:instance grow-chain-b-invariant
                   (p (bit-mat-add b0 (cadr (car us))))
                   (us (cdr us)))
        (:instance summandp-when-in-summand-listp (s (summand a0 b0 c0)))
        (:instance summandp-when-in-summand-listp (s (car us))))
  :enable (chain-sum-b partial-sums-okp-b in-of-insert obag::occs-of-insert)
  :disable (add-duplicate-b add-duplicate-b-path summandp-when-in-summand-listp
            grow-chain-b-invariant))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; iterate layer, C position

(define chain-sum-c ((p bit-list-listp) (us mat-triple-listp))
  :returns (q bit-list-listp :hyp :guard)
  (if (atom us)
      p
    (chain-sum-c (bit-mat-add p (caddr (car us))) (cdr us))))

(define partial-sums-okp-c ((p bit-list-listp) (us mat-triple-listp) (n natp))
  :returns (yes/no booleanp)
  :measure (acl2-count us)
  (and (not (equal p (bit-mat0 n n)))
       (if (atom us)
           t
         (partial-sums-okp-c (bit-mat-add p (caddr (car us))) (cdr us) n)))
  ///
  (defrule partial-sums-okp-c-nonzero
    (implies (partial-sums-okp-c p us n)
             (not (equal p (bit-mat0 n n)))))
  (defrule partial-sums-okp-c-of-cdr
    (implies (and (partial-sums-okp-c p us n)
                  (consp us))
             (partial-sums-okp-c (bit-mat-add p (caddr (car us))) (cdr us) n))))

(define grow-chain-c ((a0 bit-list-listp) (b0 bit-list-listp) (p bit-list-listp)
                      (us mat-triple-listp) (n natp))
  :returns (moves move-list-p :hyp :guard)
  (if (atom us)
      nil
    (let ((u (car us))
          (s (summand a0 b0 p)))
      (append (append (add-duplicate-c-path a0 b0 p (car u) (cadr u) (caddr u) n)
                      (list (list :flip 0 s s)))
              (grow-chain-c a0 b0 (bit-mat-add p (caddr u)) (cdr us) n)))))

(defruled one-step-c
  (implies (and (schemep sch n)
                (natp n)
                (summandp (summand a0 b0 p) n)
                (obag::in u sch)
                (not (equal (bit-mat-add p (caddr u)) (bit-mat0 n n))))
           (let* ((s (summand a0 b0 p))
                  (cur (obag::insert s (obag::insert s sch)))
                  (z (bit-mat-add p (caddr u)))
                  (path (append (add-duplicate-c-path a0 b0 p
                                                 (car u) (cadr u) (caddr u) n)
                                (list (list :flip 0 s s)))))
             (and (path-validp path cur n)
                  (equal (apply-moves path cur n)
                         (obag::insert (summand a0 b0 z)
                                       (obag::insert (summand a0 b0 z) sch))))))
  :do-not-induct t
  :use ((:instance add-duplicate-c
                   (sch (obag::insert (summand a0 b0 p)
                                      (obag::insert (summand a0 b0 p) sch)))
                   (a1 a0) (b1 b0) (c1 p)
                   (a2 (car u)) (b2 (cadr u)) (c2 (caddr u)))
        (:instance bit-mat-add-equal-arg1 (a p) (b (caddr u)) (m n) (n n))
        (:instance summandp-when-in-summand-listp (s u)))
  :enable (apply-moves in-of-insert obag::occs-of-insert)
  :disable (add-duplicate-c add-duplicate-c-path summandp-when-in-summand-listp))

(defrule grow-chain-c-invariant
  (implies (and (schemep sch n)
                (natp n)
                (summandp (summand a0 b0 p) n)
                (us-in-schemep us sch)
                (summand-listp us n)
                (partial-sums-okp-c p us n))
           (let ((cur (obag::insert (summand a0 b0 p)
                                    (obag::insert (summand a0 b0 p) sch)))
                 (z (chain-sum-c p us)))
             (and (path-validp (grow-chain-c a0 b0 p us n) cur n)
                  (equal (apply-moves (grow-chain-c a0 b0 p us n) cur n)
                         (obag::insert (summand a0 b0 z)
                                       (obag::insert (summand a0 b0 z) sch))))))
  :hints (("Goal"
           :induct (grow-chain-c a0 b0 p us n)
           :do-not-induct t
           :in-theory (e/d (grow-chain-c chain-sum-c apply-moves
                            partial-sums-okp-c bit-mat-add-same
                            in-of-insert obag::occs-of-insert)
                           (add-duplicate-c add-duplicate-c-path
                            summandp-when-in-summand-listp)))
          ("Subgoal *1/2"
           :use ((:instance one-step-c (u (car us)))
                 (:instance summandp-when-in-summand-listp (s (car us)))
                 (:instance bit-mat-add-equal-arg1
                            (a p) (b (caddr (car us))) (m n) (n n))))))

(defrule add-arbitrary-relative-c
  (implies (and (schemep sch n)
                (natp n)
                (obag::in (summand a0 b0 c0) sch)
                (us-in-schemep us sch)
                (summand-listp us n)
                (consp us)
                (partial-sums-okp-c c0 us n))
           (let* ((u1 (car us))
                  (p1 (bit-mat-add c0 (caddr u1)))
                  (path (append (add-duplicate-c-path a0 b0 c0
                                                 (car u1) (cadr u1) (caddr u1) n)
                                (grow-chain-c a0 b0 p1 (cdr us) n)))
                  (z (chain-sum-c c0 us)))
             (and (path-validp path sch n)
                  (equal (apply-moves path sch n)
                         (obag::insert (summand a0 b0 z)
                                       (obag::insert (summand a0 b0 z) sch))))))
  :do-not-induct t
  :use ((:instance add-duplicate-c
                   (a1 a0) (b1 b0) (c1 c0)
                   (a2 (car (car us))) (b2 (cadr (car us))) (c2 (caddr (car us))))
        (:instance grow-chain-c-invariant
                   (p (bit-mat-add c0 (caddr (car us))))
                   (us (cdr us)))
        (:instance summandp-when-in-summand-listp (s (summand a0 b0 c0)))
        (:instance summandp-when-in-summand-listp (s (car us))))
  :enable (chain-sum-c partial-sums-okp-c in-of-insert obag::occs-of-insert)
  :disable (add-duplicate-c add-duplicate-c-path summandp-when-in-summand-listp
            grow-chain-c-invariant))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 5b: the B-position span/basis/chain stack (seeded)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; B components

(define b-components ((l mat-triple-listp))
  :returns (mats bit-mat-list-p :hyp :guard)
  (if (atom l)
      nil
    (cons (cadr (car l)) (b-components (cdr l))))
  ///
  (defrule bit-mat-listnp-of-b-components
    (implies (summand-dim-listp l n)
             (bit-mat-listnp (b-components l) n n))
    :induct (b-components l)
    :enable bit-mat-listnp)
  (defrule len-of-b-components
    (equal (len (b-components l)) (len l)))
  (defruled b-components-of-append
    (equal (b-components (append l1 l2))
           (append (b-components l1) (b-components l2)))
    :induct (cdr-induct l1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Stage 1-B: B components span

(defruled in-spanp-of-b-witness-sum
  (implies (and (summand-dim-listp l n)
                (natp n))
           (in-spanp (b-witness-sum l i j k n) (b-components l) n n))
  :induct (b-witness-sum l i j k n)
  :enable (b-witness-sum b-components in-spanp in-spanp-step))

(defruled unit-in-b-span
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (natp j) (< i n) (< j n))
           (in-spanp (bit-mat-unit i j n n) (b-components sch) n n))
  :do-not-induct t
  :enable (correct-schemep)
  :disable (b-witness-sum bit-mat-unit)
  :use ((:instance b-span-lemma (i 0) (j i) (k j))
        (:instance in-spanp-of-b-witness-sum (l sch) (i 0) (j i) (k j))))

(defruled all-in-spanp-of-unit-row-b
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (< i n) (natp j))
           (all-in-spanp (unit-row i j n n) (b-components sch) n n))
  :induct (unit-row i j n n)
  :enable (unit-row all-in-spanp unit-in-b-span
           bit-mat-unit2-is-bit-mat-unit))

(defruled all-in-spanp-of-all-units-b
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (natp j))
           (all-in-spanp (all-units i j n n) (b-components sch) n n))
  :induct (all-units i j n n)
  :enable (all-units all-in-spanp all-in-spanp-of-append
           all-in-spanp-of-unit-row-b))

(defruled spans-unitsp-of-b-components
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n))
           (spans-unitsp (b-components sch) n n))
  :enable (spans-unitsp)
  :use ((:instance all-in-spanp-of-all-units-b (i 0) (j 0))))

(defruled b-components-span-everything
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (bit-matp y n n))
           (in-spanp y (b-components sch) n n))
  :do-not-induct t
  :enable (correct-schemep)
  :use (spans-unitsp-of-b-components
        (:instance in-spanp-when-spans-unitsp
                   (mats (b-components sch)) (x y) (m n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Stage 2-B: the extracted basis

(define basis-new-b ((l mat-triple-listp) (acc mat-triple-listp) (n natp))
  :returns (ws mat-triple-listp :hyp :guard
               :hints (("Goal" :in-theory (enable mat-triple-listp-of-append))))
  (if (atom l)
      nil
    (if (in-spanp (cadr (car l)) (b-components acc) n n)
        (basis-new-b (cdr l) acc n)
      (append (basis-new-b (cdr l) (cons (car l) acc) n)
              (list (car l)))))
  ///
  (defrule summand-listp-of-basis-new-b
    (implies (and (summand-listp l n)
                  (summand-listp acc n))
             (summand-listp (basis-new-b l acc n) n))
    :induct (basis-new-b l acc n)
    :enable (summand-listp-of-append)))

(defruled us-in-schemep-of-basis-new-b
  (implies (and (us-in-schemep l sch)
                (us-in-schemep acc sch))
           (us-in-schemep (basis-new-b l acc n) sch))
  :induct (basis-new-b l acc n)
  :enable (basis-new-b us-in-schemep us-in-schemep-of-append))

(defruled independentp-of-basis-new-b
  (implies (and (independentp (b-components acc) n n)
                (summand-dim-listp l n)
                (summand-dim-listp acc n)
                (natp n))
           (independentp (b-components (append (basis-new-b l acc n) acc)) n n))
  :induct (basis-new-b l acc n)
  :enable (basis-new-b independentp b-components b-components-of-append))

(defruled summand-dim-listp-of-basis-new-b
  (implies (and (summand-dim-listp l n)
                (summand-dim-listp acc n))
           (summand-dim-listp (basis-new-b l acc n) n))
  :induct (basis-new-b l acc n)
  :enable (basis-new-b summand-dim-listp-of-append))

(defruled basis-new-b-spans
  (implies (and (summand-dim-listp l n)
                (summand-dim-listp acc n)
                (natp n))
           (and (all-in-spanp (b-components l)
                              (b-components (append (basis-new-b l acc n) acc))
                              n n)
                (all-in-spanp (b-components acc)
                              (b-components (append (basis-new-b l acc n) acc))
                              n n)))
  :induct (basis-new-b l acc n)
  :enable (basis-new-b all-in-spanp b-components b-components-of-append
           span-subset-transitive all-in-spanp-reflexive
           summand-dim-listp-of-append summand-dim-listp-of-basis-new-b
           member-in-spanp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Stage 3-B: chains

(define select-chain-okp-b ((p bit-list-listp) (coeffs bit-list-p)
                            (l mat-triple-listp) (n natp))
  :measure (acl2-count l)
  :returns (yes/no booleanp)
  (if (atom l)
      (not (equal p (bit-mat0 n n)))
    (if (equal (car coeffs) 1)
        (and (not (equal p (bit-mat0 n n)))
             (select-chain-okp-b (bit-mat-add p (cadr (car l)))
                                 (cdr coeffs) (cdr l) n))
      (select-chain-okp-b p (cdr coeffs) (cdr l) n))))

(defruled chain-sum-b-of-add
  (equal (chain-sum-b (bit-mat-add p q) us)
         (bit-mat-add p (chain-sum-b q us)))
  :induct (chain-sum-b q us)
  :enable (chain-sum-b bit-mat-add-associative))

(defruled chain-sum-b-select-step
  (equal (chain-sum-b (bit-mat-add p a) us)
         (bit-mat-add a (chain-sum-b p us)))
  :do-not-induct t
  :use ((:instance chain-sum-b-of-add (p a) (q p)))
  :enable (bit-mat-add-commutative))

(defruled chain-sum-b-of-select-summands
  (implies (and (summand-dim-listp l n)
                (bit-matp p n n)
                (natp n))
           (equal (chain-sum-b p (select-summands c l))
                  (bit-mat-add p (lincomb c (b-components l) n n))))
  :induct (select-summands c l)
  :enable (chain-sum-b select-summands lincomb b-components
           chain-sum-b-select-step
           bit-mat-add-commutative bit-mat-add-commutative-2
           bit-mat-add-associative))

(defruled chain-sum-b-of-append
  (equal (chain-sum-b p (append u1 u2))
         (chain-sum-b (chain-sum-b p u1) u2))
  :induct (chain-sum-b p u1)
  :enable (chain-sum-b))

(defruled partial-sums-okp-b-of-append
  (equal (partial-sums-okp-b p (append u1 u2) n)
         (and (partial-sums-okp-b p u1 n)
              (partial-sums-okp-b (chain-sum-b p u1) u2 n)))
  :induct (chain-sum-b p u1)
  :enable (chain-sum-b partial-sums-okp-b))

(defruled chain-sum-b-nonzero-when-partial-sums-okp-b
  (implies (partial-sums-okp-b p us n)
           (not (equal (chain-sum-b p us) (bit-mat0 n n))))
  :induct (chain-sum-b p us)
  :enable (chain-sum-b partial-sums-okp-b))

(defruled select-chain-okp-b-as-partial-sums-okp-b
  (equal (select-chain-okp-b p c l n)
         (partial-sums-okp-b p (select-summands c l) n))
  :induct (select-chain-okp-b p c l n)
  :enable (select-chain-okp-b select-summands partial-sums-okp-b))

(defruled select-chain-okp-b-when-independent
  (implies (and (independentp (cons p (b-components l)) n n)
                (bit-matp p n n)
                (summand-dim-listp l n)
                (natp n))
           (select-chain-okp-b p c l n))
  :induct (select-chain-okp-b p c l n)
  :enable (select-chain-okp-b independentp in-spanp b-components))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; the chosen B objects (seeded)

(define arb-basis-b ((sch mat-triple-listp) (s0 mat-triplep) (n natp))
  :returns (bs mat-triple-listp :hyp :guard
               :hints (("Goal" :in-theory (enable mat-triple-listp-of-append))))
  (append (basis-new-b sch (list s0) n)
          (list s0)))

(define arb-coeffs-b ((sch mat-triple-listp) (s0 mat-triplep) (y bit-list-listp)
                      (n natp))
  :returns (coeffs bit-list-p)
  (span-witness (bit-mat-add y (cadr s0))
                (b-components (arb-basis-b sch s0 n))
                n n))

(define arb-us-b ((sch mat-triple-listp) (s0 mat-triplep) (y bit-list-listp) (n natp))
  :returns (us mat-triple-listp :hyp :guard)
  (select-summands (arb-coeffs-b sch s0 y n) (arb-basis-b sch s0 n)))

(define add-arbitrary-b-path ((sch mat-triple-listp) (s0 mat-triplep)
                              (y bit-list-listp) (n natp))
  :returns (moves move-list-p :hyp :guard
                  :hints (("Goal"
                           :do-not-induct t
                           :in-theory (union-theories (theory 'mat-triple-head-lemmas)
                                                      (disable arb-us-b
                                                               add-duplicate-b-path
                                                               grow-chain-b))
                           :use (mat-triple-listp-of-arb-us-b))))
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (union-theories (theory 'mat-triple-head-lemmas)
                                            (disable arb-us-b))
                 :use (mat-triple-listp-of-arb-us-b)))
  (let* ((a0 (car s0))
         (b0 (cadr s0))
         (c0 (caddr s0))
         (us (arb-us-b sch s0 y n))
         (u1 (car us)))
    (append (add-duplicate-b-path a0 b0 c0 (car u1) (cadr u1) (caddr u1) n)
            (grow-chain-b a0 (bit-mat-add b0 (cadr u1)) c0 (cdr us) n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; the B facts

(defruled arb-basis-b-facts
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch))
           (and (summand-listp (arb-basis-b sch s0 n) n)
                (us-in-schemep (arb-basis-b sch s0 n) sch)
                (independentp (b-components (arb-basis-b sch s0 n)) n n)))
  :do-not-induct t
  :enable (arb-basis-b correct-schemep b-components independentp in-spanp
           us-in-schemep summand-listp-of-append us-in-schemep-of-append
           us-in-schemep-of-basis-new-b)
  :use (us-in-schemep-of-self
        (:instance independentp-of-basis-new-b
                   (l sch) (acc (list s0)))
        (:instance us-in-schemep-of-basis-new-b
                   (l sch) (acc (list s0)))))

(defruled arb-basis-b-spans
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch)
                (bit-matp y n n))
           (in-spanp y (b-components (arb-basis-b sch s0 n)) n n))
  :do-not-induct t
  :enable (arb-basis-b correct-schemep)
  :use (arb-basis-b-facts
        (:instance b-components-span-everything)
        (:instance basis-new-b-spans
                   (l sch) (acc (list s0)))
        (:instance span-subset-transitive
                   (x y) (mats (b-components sch))
                   (mats2 (b-components (arb-basis-b sch s0 n)))
                   (m n))))

(defruled lincomb-of-arb-coeffs-b
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch)
                (bit-matp y n n))
           (equal (lincomb (arb-coeffs-b sch s0 y n)
                           (b-components (arb-basis-b sch s0 n)) n n)
                  (bit-mat-add y (cadr s0))))
  :do-not-induct t
  :enable (arb-coeffs-b correct-schemep)
  :use (arb-basis-b-facts
        (:instance arb-basis-b-spans
                   (y (bit-mat-add y (cadr s0))))
        (:instance lincomb-of-span-witness
                   (x (bit-mat-add y (cadr s0)))
                   (mats (b-components (arb-basis-b sch s0 n)))
                   (m n))))

(defruled arb-us-b-okp
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch)
                (bit-matp y n n)
                (not (equal y (bit-mat0 n n))))
           (and (partial-sums-okp-b (cadr s0) (arb-us-b sch s0 y n) n)
                (equal (chain-sum-b (cadr s0) (arb-us-b sch s0 y n))
                       y)))
  :do-not-induct t
  :enable (arb-us-b arb-basis-b correct-schemep
           b-components b-components-of-append
           select-summands lincomb partial-sums-okp-b chain-sum-b
           chain-sum-b-of-append partial-sums-okp-b-of-append
           select-chain-okp-b-as-partial-sums-okp-b
           independentp bit-mat-listnp
           bit-mat-add-commutative bit-mat-add-commutative-2
           bit-mat-add-associative bit-mat-add-same)
  :use (arb-basis-b-facts
        lincomb-of-arb-coeffs-b
        (:instance select-summands-of-append
                   (c (arb-coeffs-b sch s0 y n))
                   (l1 (basis-new-b sch (list s0) n))
                   (l2 (list s0)))
        (:instance lincomb-of-append-split
                   (c (arb-coeffs-b sch s0 y n))
                   (m1 (b-components (basis-new-b sch (list s0) n)))
                   (m2 (list (cadr s0)))
                   (m n))
        (:instance independentp-of-append-prefix
                   (ws (b-components (basis-new-b sch (list s0) n)))
                   (z (list (cadr s0))))
        (:instance not-in-spanp-last-when-independentp
                   (ws (b-components (basis-new-b sch (list s0) n)))
                   (a (cadr s0)))
        (:instance select-chain-okp-b-when-independent
                   (p (cadr s0))
                   (c (arb-coeffs-b sch s0 y n))
                   (l (basis-new-b sch (list s0) n)))
        (:instance chain-sum-b-of-select-summands
                   (p (cadr s0))
                   (c (arb-coeffs-b sch s0 y n))
                   (l (basis-new-b sch (list s0) n)))
        (:instance chain-sum-b-nonzero-when-partial-sums-okp-b
                   (p (cadr s0))
                   (us (select-summands
                        (arb-coeffs-b sch s0 y n)
                        (basis-new-b sch (list s0) n))))))

(defruled arb-us-b-more-facts
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch))
           (and (us-in-schemep (arb-us-b sch s0 y n) sch)
                (summand-listp (arb-us-b sch s0 y n) n)))
  :do-not-induct t
  :enable (arb-us-b us-in-schemep-of-select-summands
           summand-listp-of-select-summands)
  :use (arb-basis-b-facts))

(defruled consp-of-arb-us-b
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch)
                (bit-matp y n n)
                (not (equal y (bit-mat0 n n)))
                (not (equal (cadr s0) y)))
           (consp (arb-us-b sch s0 y n)))
  :do-not-induct t
  :enable (chain-sum-b)
  :use (arb-us-b-okp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; the B-position theorem

(defrule add-arbitrary-b
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch)
                (bit-matp y n n)
                (not (equal y (bit-mat0 n n)))
                (not (equal (cadr s0) y)))
           (let* ((path (add-arbitrary-b-path sch s0 y n))
                  (s1 (summand (car s0) y (caddr s0)))
                  (sch2 (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal sch2
                         (obag::insert s1 (obag::insert s1 sch)))
                  (correct-schemep sch2 n))))
  :do-not-induct t
  :enable (add-arbitrary-b-path correct-schemep)
  :disable (add-duplicate-b-path grow-chain-b add-arbitrary-relative-b)
  :use (arb-us-b-okp
        arb-us-b-more-facts
        consp-of-arb-us-b
        (:instance add-arbitrary-relative-b
                   (a0 (car s0))
                   (b0 (cadr s0))
                   (c0 (caddr s0))
                   (us (arb-us-b sch s0 y n)))
        (:instance correct-schemep-of-apply-moves
                   (moves (add-arbitrary-b-path sch s0 y n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 5c: the C-position stack, the replace steps, and the full lemma
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; C components

(define c-components ((l mat-triple-listp))
  :returns (mats bit-mat-list-p :hyp :guard)
  (if (atom l)
      nil
    (cons (caddr (car l)) (c-components (cdr l))))
  ///
  (defrule bit-mat-listnp-of-c-components
    (implies (summand-dim-listp l n)
             (bit-mat-listnp (c-components l) n n))
    :induct (c-components l)
    :enable bit-mat-listnp)
  (defrule len-of-c-components
    (equal (len (c-components l)) (len l)))
  (defruled c-components-of-append
    (equal (c-components (append l1 l2))
           (append (c-components l1) (c-components l2)))
    :induct (cdr-induct l1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Stage 1-C

(defruled in-spanp-of-c-witness-sum
  (implies (and (summand-dim-listp l n)
                (natp n))
           (in-spanp (c-witness-sum l i j k n) (c-components l) n n))
  :induct (c-witness-sum l i j k n)
  :enable (c-witness-sum c-components in-spanp in-spanp-step))

(defruled unit-in-c-span
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (natp j) (< i n) (< j n))
           (in-spanp (bit-mat-unit i j n n) (c-components sch) n n))
  :do-not-induct t
  :enable (correct-schemep)
  :disable (c-witness-sum bit-mat-unit)
  :use ((:instance c-span-lemma (i i) (j 0) (k j))
        (:instance in-spanp-of-c-witness-sum (l sch) (i i) (j 0) (k j))))

(defruled all-in-spanp-of-unit-row-c
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (< i n) (natp j))
           (all-in-spanp (unit-row i j n n) (c-components sch) n n))
  :induct (unit-row i j n n)
  :enable (unit-row all-in-spanp unit-in-c-span
           bit-mat-unit2-is-bit-mat-unit))

(defruled all-in-spanp-of-all-units-c
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (natp i) (natp j))
           (all-in-spanp (all-units i j n n) (c-components sch) n n))
  :induct (all-units i j n n)
  :enable (all-units all-in-spanp all-in-spanp-of-append
           all-in-spanp-of-unit-row-c))

(defruled spans-unitsp-of-c-components
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n))
           (spans-unitsp (c-components sch) n n))
  :enable (spans-unitsp)
  :use ((:instance all-in-spanp-of-all-units-c (i 0) (j 0))))

(defruled c-components-span-everything
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (bit-matp y n n))
           (in-spanp y (c-components sch) n n))
  :do-not-induct t
  :enable (correct-schemep)
  :use (spans-unitsp-of-c-components
        (:instance in-spanp-when-spans-unitsp
                   (mats (c-components sch)) (x y) (m n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Stage 2-C

(define basis-new-c ((l mat-triple-listp) (acc mat-triple-listp) (n natp))
  :returns (ws mat-triple-listp :hyp :guard
               :hints (("Goal" :in-theory (enable mat-triple-listp-of-append))))
  (if (atom l)
      nil
    (if (in-spanp (caddr (car l)) (c-components acc) n n)
        (basis-new-c (cdr l) acc n)
      (append (basis-new-c (cdr l) (cons (car l) acc) n)
              (list (car l)))))
  ///
  (defrule summand-listp-of-basis-new-c
    (implies (and (summand-listp l n)
                  (summand-listp acc n))
             (summand-listp (basis-new-c l acc n) n))
    :induct (basis-new-c l acc n)
    :enable (summand-listp-of-append)))

(defruled us-in-schemep-of-basis-new-c
  (implies (and (us-in-schemep l sch)
                (us-in-schemep acc sch))
           (us-in-schemep (basis-new-c l acc n) sch))
  :induct (basis-new-c l acc n)
  :enable (basis-new-c us-in-schemep us-in-schemep-of-append))

(defruled independentp-of-basis-new-c
  (implies (and (independentp (c-components acc) n n)
                (summand-dim-listp l n)
                (summand-dim-listp acc n)
                (natp n))
           (independentp (c-components (append (basis-new-c l acc n) acc)) n n))
  :induct (basis-new-c l acc n)
  :enable (basis-new-c independentp c-components c-components-of-append))

(defruled summand-dim-listp-of-basis-new-c
  (implies (and (summand-dim-listp l n)
                (summand-dim-listp acc n))
           (summand-dim-listp (basis-new-c l acc n) n))
  :induct (basis-new-c l acc n)
  :enable (basis-new-c summand-dim-listp-of-append))

(defruled basis-new-c-spans
  (implies (and (summand-dim-listp l n)
                (summand-dim-listp acc n)
                (natp n))
           (and (all-in-spanp (c-components l)
                              (c-components (append (basis-new-c l acc n) acc))
                              n n)
                (all-in-spanp (c-components acc)
                              (c-components (append (basis-new-c l acc n) acc))
                              n n)))
  :induct (basis-new-c l acc n)
  :enable (basis-new-c all-in-spanp c-components c-components-of-append
           span-subset-transitive all-in-spanp-reflexive
           summand-dim-listp-of-append summand-dim-listp-of-basis-new-c
           member-in-spanp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Stage 3-C

(define select-chain-okp-c ((p bit-list-listp) (coeffs bit-list-p)
                            (l mat-triple-listp) (n natp))
  :measure (acl2-count l)
  :returns (yes/no booleanp)
  (if (atom l)
      (not (equal p (bit-mat0 n n)))
    (if (equal (car coeffs) 1)
        (and (not (equal p (bit-mat0 n n)))
             (select-chain-okp-c (bit-mat-add p (caddr (car l)))
                                 (cdr coeffs) (cdr l) n))
      (select-chain-okp-c p (cdr coeffs) (cdr l) n))))

(defruled chain-sum-c-of-add
  (equal (chain-sum-c (bit-mat-add p q) us)
         (bit-mat-add p (chain-sum-c q us)))
  :induct (chain-sum-c q us)
  :enable (chain-sum-c bit-mat-add-associative))

(defruled chain-sum-c-select-step
  (equal (chain-sum-c (bit-mat-add p a) us)
         (bit-mat-add a (chain-sum-c p us)))
  :do-not-induct t
  :use ((:instance chain-sum-c-of-add (p a) (q p)))
  :enable (bit-mat-add-commutative))

(defruled chain-sum-c-of-select-summands
  (implies (and (summand-dim-listp l n)
                (bit-matp p n n)
                (natp n))
           (equal (chain-sum-c p (select-summands c l))
                  (bit-mat-add p (lincomb c (c-components l) n n))))
  :induct (select-summands c l)
  :enable (chain-sum-c select-summands lincomb c-components
           chain-sum-c-select-step
           bit-mat-add-commutative bit-mat-add-commutative-2
           bit-mat-add-associative))

(defruled chain-sum-c-of-append
  (equal (chain-sum-c p (append u1 u2))
         (chain-sum-c (chain-sum-c p u1) u2))
  :induct (chain-sum-c p u1)
  :enable (chain-sum-c))

(defruled partial-sums-okp-c-of-append
  (equal (partial-sums-okp-c p (append u1 u2) n)
         (and (partial-sums-okp-c p u1 n)
              (partial-sums-okp-c (chain-sum-c p u1) u2 n)))
  :induct (chain-sum-c p u1)
  :enable (chain-sum-c partial-sums-okp-c))

(defruled chain-sum-c-nonzero-when-partial-sums-okp-c
  (implies (partial-sums-okp-c p us n)
           (not (equal (chain-sum-c p us) (bit-mat0 n n))))
  :induct (chain-sum-c p us)
  :enable (chain-sum-c partial-sums-okp-c))

(defruled select-chain-okp-c-as-partial-sums-okp-c
  (equal (select-chain-okp-c p c l n)
         (partial-sums-okp-c p (select-summands c l) n))
  :induct (select-chain-okp-c p c l n)
  :enable (select-chain-okp-c select-summands partial-sums-okp-c))

(defruled select-chain-okp-c-when-independent
  (implies (and (independentp (cons p (c-components l)) n n)
                (bit-matp p n n)
                (summand-dim-listp l n)
                (natp n))
           (select-chain-okp-c p c l n))
  :induct (select-chain-okp-c p c l n)
  :enable (select-chain-okp-c independentp in-spanp c-components))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; the chosen C objects (seeded)

(define arb-basis-c ((sch mat-triple-listp) (s0 mat-triplep) (n natp))
  :returns (bs mat-triple-listp :hyp :guard
               :hints (("Goal" :in-theory (enable mat-triple-listp-of-append))))
  (append (basis-new-c sch (list s0) n)
          (list s0)))

(define arb-coeffs-c ((sch mat-triple-listp) (s0 mat-triplep) (z bit-list-listp)
                      (n natp))
  :returns (coeffs bit-list-p)
  (span-witness (bit-mat-add z (caddr s0))
                (c-components (arb-basis-c sch s0 n))
                n n))

(define arb-us-c ((sch mat-triple-listp) (s0 mat-triplep) (z bit-list-listp) (n natp))
  :returns (us mat-triple-listp :hyp :guard)
  (select-summands (arb-coeffs-c sch s0 z n) (arb-basis-c sch s0 n)))

(define add-arbitrary-c-path ((sch mat-triple-listp) (s0 mat-triplep)
                              (z bit-list-listp) (n natp))
  :returns (moves move-list-p :hyp :guard
                  :hints (("Goal"
                           :do-not-induct t
                           :in-theory (union-theories (theory 'mat-triple-head-lemmas)
                                                      (disable arb-us-c
                                                               add-duplicate-c-path
                                                               grow-chain-c))
                           :use (mat-triple-listp-of-arb-us-c))))
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (union-theories (theory 'mat-triple-head-lemmas)
                                            (disable arb-us-c))
                 :use (mat-triple-listp-of-arb-us-c)))
  (let* ((a0 (car s0))
         (b0 (cadr s0))
         (c0 (caddr s0))
         (us (arb-us-c sch s0 z n))
         (u1 (car us)))
    (append (add-duplicate-c-path a0 b0 c0 (car u1) (cadr u1) (caddr u1) n)
            (grow-chain-c a0 b0 (bit-mat-add c0 (caddr u1)) (cdr us) n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; the C facts

(defruled arb-basis-c-facts
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch))
           (and (summand-listp (arb-basis-c sch s0 n) n)
                (us-in-schemep (arb-basis-c sch s0 n) sch)
                (independentp (c-components (arb-basis-c sch s0 n)) n n)))
  :do-not-induct t
  :enable (arb-basis-c correct-schemep c-components independentp in-spanp
           us-in-schemep summand-listp-of-append us-in-schemep-of-append
           us-in-schemep-of-basis-new-c)
  :use (us-in-schemep-of-self
        (:instance independentp-of-basis-new-c
                   (l sch) (acc (list s0)))
        (:instance us-in-schemep-of-basis-new-c
                   (l sch) (acc (list s0)))))

(defruled arb-basis-c-spans
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch)
                (bit-matp y n n))
           (in-spanp y (c-components (arb-basis-c sch s0 n)) n n))
  :do-not-induct t
  :enable (arb-basis-c correct-schemep)
  :use (arb-basis-c-facts
        (:instance c-components-span-everything)
        (:instance basis-new-c-spans
                   (l sch) (acc (list s0)))
        (:instance span-subset-transitive
                   (x y) (mats (c-components sch))
                   (mats2 (c-components (arb-basis-c sch s0 n)))
                   (m n))))

(defruled lincomb-of-arb-coeffs-c
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch)
                (bit-matp z n n))
           (equal (lincomb (arb-coeffs-c sch s0 z n)
                           (c-components (arb-basis-c sch s0 n)) n n)
                  (bit-mat-add z (caddr s0))))
  :do-not-induct t
  :enable (arb-coeffs-c correct-schemep)
  :use (arb-basis-c-facts
        (:instance arb-basis-c-spans
                   (y (bit-mat-add z (caddr s0))))
        (:instance lincomb-of-span-witness
                   (x (bit-mat-add z (caddr s0)))
                   (mats (c-components (arb-basis-c sch s0 n)))
                   (m n))))

(defruled arb-us-c-okp
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch)
                (bit-matp z n n)
                (not (equal z (bit-mat0 n n))))
           (and (partial-sums-okp-c (caddr s0) (arb-us-c sch s0 z n) n)
                (equal (chain-sum-c (caddr s0) (arb-us-c sch s0 z n))
                       z)))
  :do-not-induct t
  :enable (arb-us-c arb-basis-c correct-schemep
           c-components c-components-of-append
           select-summands lincomb partial-sums-okp-c chain-sum-c
           chain-sum-c-of-append partial-sums-okp-c-of-append
           select-chain-okp-c-as-partial-sums-okp-c
           independentp bit-mat-listnp
           bit-mat-add-commutative bit-mat-add-commutative-2
           bit-mat-add-associative bit-mat-add-same)
  :use (arb-basis-c-facts
        lincomb-of-arb-coeffs-c
        (:instance select-summands-of-append
                   (c (arb-coeffs-c sch s0 z n))
                   (l1 (basis-new-c sch (list s0) n))
                   (l2 (list s0)))
        (:instance lincomb-of-append-split
                   (c (arb-coeffs-c sch s0 z n))
                   (m1 (c-components (basis-new-c sch (list s0) n)))
                   (m2 (list (caddr s0)))
                   (m n))
        (:instance independentp-of-append-prefix
                   (ws (c-components (basis-new-c sch (list s0) n)))
                   (z (list (caddr s0))))
        (:instance not-in-spanp-last-when-independentp
                   (ws (c-components (basis-new-c sch (list s0) n)))
                   (a (caddr s0)))
        (:instance select-chain-okp-c-when-independent
                   (p (caddr s0))
                   (c (arb-coeffs-c sch s0 z n))
                   (l (basis-new-c sch (list s0) n)))
        (:instance chain-sum-c-of-select-summands
                   (p (caddr s0))
                   (c (arb-coeffs-c sch s0 z n))
                   (l (basis-new-c sch (list s0) n)))
        (:instance chain-sum-c-nonzero-when-partial-sums-okp-c
                   (p (caddr s0))
                   (us (select-summands
                        (arb-coeffs-c sch s0 z n)
                        (basis-new-c sch (list s0) n))))))

(defruled arb-us-c-more-facts
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch))
           (and (us-in-schemep (arb-us-c sch s0 z n) sch)
                (summand-listp (arb-us-c sch s0 z n) n)))
  :do-not-induct t
  :enable (arb-us-c us-in-schemep-of-select-summands
           summand-listp-of-select-summands)
  :use (arb-basis-c-facts))

(defruled consp-of-arb-us-c
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch)
                (bit-matp z n n)
                (not (equal z (bit-mat0 n n)))
                (not (equal (caddr s0) z)))
           (consp (arb-us-c sch s0 z n)))
  :do-not-induct t
  :enable (chain-sum-c)
  :use (arb-us-c-okp))

(defrule add-arbitrary-c
  (implies (and (correct-schemep sch n)
                (natp n) (< 0 n)
                (summandp s0 n)
                (obag::in s0 sch)
                (bit-matp z n n)
                (not (equal z (bit-mat0 n n)))
                (not (equal (caddr s0) z)))
           (let* ((path (add-arbitrary-c-path sch s0 z n))
                  (s1 (summand (car s0) (cadr s0) z))
                  (sch2 (apply-moves path sch n)))
             (and (path-validp path sch n)
                  (equal sch2
                         (obag::insert s1 (obag::insert s1 sch)))
                  (correct-schemep sch2 n))))
  :do-not-induct t
  :enable (add-arbitrary-c-path correct-schemep)
  :disable (add-duplicate-c-path grow-chain-c add-arbitrary-relative-c)
  :use (arb-us-c-okp
        arb-us-c-more-facts
        consp-of-arb-us-c
        (:instance add-arbitrary-relative-c
                   (a0 (car s0))
                   (b0 (cadr s0))
                   (c0 (caddr s0))
                   (us (arb-us-c sch s0 z n)))
        (:instance correct-schemep-of-apply-moves
                   (moves (add-arbitrary-c-path sch s0 z n)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; composition: replace-in-place steps

;;; From sch0 + pair(s1), walk to sch0 + pair(s1 with B set to y): run the
;;; B-position argument and then delete the old pair by a self-flip.

(defruled add-arbitrary-b-replace
  (implies (and (obag::bagp sch0)
                (correct-schemep (obag::insert s1 (obag::insert s1 sch0)) n)
                (natp n) (< 0 n)
                (summandp s1 n)
                (bit-matp y n n)
                (not (equal y (bit-mat0 n n)))
                (not (equal (cadr s1) y)))
           (let* ((sch1 (obag::insert s1 (obag::insert s1 sch0)))
                  (path (append (add-arbitrary-b-path sch1 s1 y n)
                                (list (list :flip 0 s1 s1))))
                  (t1 (summand (car s1) y (caddr s1))))
             (and (path-validp path sch1 n)
                  (equal (apply-moves path sch1 n)
                         (obag::insert t1 (obag::insert t1 sch0)))
                  (correct-schemep (apply-moves path sch1 n) n))))
  :do-not-induct t
  :enable (correct-schemep in-of-insert obag::occs-of-insert
           apply-moves)
  :disable (add-arbitrary-b add-arbitrary-b-path delete-pair-result)
  :use ((:instance add-arbitrary-b
                   (sch (obag::insert s1 (obag::insert s1 sch0)))
                   (s0 s1))
        (:instance delete-pair-result
                   (sch (obag::insert (summand (car s1) y (caddr s1))
                                      (obag::insert (summand (car s1) y (caddr s1))
                                                    (obag::insert s1 (obag::insert s1 sch0)))))
                   (s s1) (p 0))
        (:instance correct-schemep-of-apply-moves
                   (sch (obag::insert s1 (obag::insert s1 sch0)))
                   (moves (append (add-arbitrary-b-path
                                 (obag::insert s1 (obag::insert s1 sch0))
                                 s1 y n)
                                (list (list :flip 0 s1 s1)))))))

;;; The C-position analogue.

(defruled add-arbitrary-c-replace
  (implies (and (obag::bagp sch0)
                (correct-schemep (obag::insert s1 (obag::insert s1 sch0)) n)
                (natp n) (< 0 n)
                (summandp s1 n)
                (bit-matp z n n)
                (not (equal z (bit-mat0 n n)))
                (not (equal (caddr s1) z)))
           (let* ((sch1 (obag::insert s1 (obag::insert s1 sch0)))
                  (path (append (add-arbitrary-c-path sch1 s1 z n)
                                (list (list :flip 0 s1 s1))))
                  (t1 (summand (car s1) (cadr s1) z)))
             (and (path-validp path sch1 n)
                  (equal (apply-moves path sch1 n)
                         (obag::insert t1 (obag::insert t1 sch0)))
                  (correct-schemep (apply-moves path sch1 n) n))))
  :do-not-induct t
  :enable (correct-schemep in-of-insert obag::occs-of-insert
           apply-moves)
  :disable (add-arbitrary-c add-arbitrary-c-path delete-pair-result)
  :use ((:instance add-arbitrary-c
                   (sch (obag::insert s1 (obag::insert s1 sch0)))
                   (s0 s1))
        (:instance delete-pair-result
                   (sch (obag::insert (summand (car s1) (cadr s1) z)
                                      (obag::insert (summand (car s1) (cadr s1) z)
                                                    (obag::insert s1 (obag::insert s1 sch0)))))
                   (s s1) (p 0))
        (:instance correct-schemep-of-apply-moves
                   (sch (obag::insert s1 (obag::insert s1 sch0)))
                   (moves (append (add-arbitrary-c-path
                                 (obag::insert s1 (obag::insert s1 sch0))
                                 s1 z n)
                                (list (list :flip 0 s1 s1)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; the full path and theorem

;;; The B leg: from sch + pair(x, b0, c0) to sch + pair(x, y, c0)
;;; (empty when b0 already equals y).

(define arb-path-b ((sch mat-triple-listp) (x bit-list-listp) (y bit-list-listp)
                    (n natp))
  :guard (obag::bagp sch)
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (union-theories (theory 'arb-guard-lemmas)
                                            (enable mat-triple-listp-of-insert))))
  :returns (moves move-list-p :hyp :guard
                  :hints (("Goal"
                           :do-not-induct t
                           :in-theory (union-theories (theory 'arb-guard-lemmas)
                                                      (e/d (mat-triple-listp-of-insert)
                                                           (add-arbitrary-b-path
                                                            find-summand-a-neq))))))
  (let* ((s0 (find-summand-a-neq sch x))
         (b0 (cadr s0))
         (c0 (caddr s0))
         (s1 (summand x b0 c0))
         (sch1 (obag::insert s1 (obag::insert s1 sch))))
    (if (equal b0 y)
        nil
      (append (add-arbitrary-b-path sch1 s1 y n)
              (list (list :flip 0 s1 s1))))))

;;; The C leg: from sch + pair(x, y, c0) to sch + pair(x, y, z).

(define arb-path-c ((sch mat-triple-listp) (x bit-list-listp) (y bit-list-listp)
                    (z bit-list-listp) (n natp))
  :guard (obag::bagp sch)
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (union-theories (theory 'arb-guard-lemmas)
                                            (enable mat-triple-listp-of-insert))))
  :returns (moves move-list-p :hyp :guard
                  :hints (("Goal"
                           :do-not-induct t
                           :in-theory (union-theories (theory 'arb-guard-lemmas)
                                                      (e/d (mat-triple-listp-of-insert)
                                                           (add-arbitrary-c-path
                                                            find-summand-a-neq))))))
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

;;; Generic two-leg composition.

(defruled compose-path-steps
  (implies (and (path-validp p1 sch n)
                (equal (apply-moves p1 sch n) sch1)
                (path-validp p2 sch1 n)
                (equal (apply-moves p2 sch1 n) sch2))
           (and (path-validp (append p1 p2) sch n)
                (equal (apply-moves (append p1 p2) sch n) sch2)))
  :do-not-induct t)

;;; The B leg walks sch + pair(x,b0,c0) to sch + pair(x,y,c0).

(defruled arb-path-b-step
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n)
                (not (equal x (bit-mat0 n n)))
                (bit-matp y n n)
                (not (equal y (bit-mat0 n n))))
           (let* ((s0 (find-summand-a-neq sch x))
                  (s1 (summand x (cadr s0) (caddr s0)))
                  (sch1 (obag::insert s1 (obag::insert s1 sch)))
                  (s2 (summand x y (caddr s0)))
                  (sch2 (obag::insert s2 (obag::insert s2 sch))))
             (and (path-validp (arb-path-b sch x y n) sch1 n)
                  (equal (apply-moves (arb-path-b sch x y n) sch1 n) sch2)
                  (correct-schemep sch2 n))))
  :do-not-induct t
  :enable (arb-path-b apply-moves correct-schemep)
  :disable (add-arbitrary-a add-arbitrary-a-path add-arbitrary-b-path
            apply-moves-of-append path-validp-of-append
            delete-pair-result delete-pair-move-validp)
  :use (add-arbitrary-a
        arb-s0-facts
        (:instance add-arbitrary-b-replace
                   (sch0 sch)
                   (s1 (summand x
                                (cadr (find-summand-a-neq sch x))
                                (caddr (find-summand-a-neq sch x)))))))

;;; The C leg walks sch + pair(x,y,c0) to sch + pair(x,y,z).

(defruled arb-path-c-step
  (implies (and (correct-schemep sch n)
                (natp n) (<= 2 n)
                (bit-matp x n n)
                (not (equal x (bit-mat0 n n)))
                (bit-matp y n n)
                (not (equal y (bit-mat0 n n)))
                (bit-matp z n n)
                (not (equal z (bit-mat0 n n))))
           (let* ((s0 (find-summand-a-neq sch x))
                  (s2 (summand x y (caddr s0)))
                  (sch2 (obag::insert s2 (obag::insert s2 sch)))
                  (s3 (summand x y z))
                  (sch3 (obag::insert s3 (obag::insert s3 sch))))
             (and (path-validp (arb-path-c sch x y z n) sch2 n)
                  (equal (apply-moves (arb-path-c sch x y z n) sch2 n) sch3)
                  (correct-schemep sch3 n))))
  :do-not-induct t
  :enable (arb-path-c apply-moves correct-schemep)
  :disable (add-arbitrary-a add-arbitrary-a-path add-arbitrary-c-path
            apply-moves-of-append path-validp-of-append
            delete-pair-result delete-pair-move-validp)
  :use (arb-path-b-step
        arb-s0-facts
        (:instance add-arbitrary-c-replace
                   (sch0 sch)
                   (s1 (summand x y (caddr (find-summand-a-neq sch x)))))))

