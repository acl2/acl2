; Iteration core of the companion paper's add-arbitrary lemma (relative
; form): starting from a scheme S together with an identical pair of copies
; of (p, B0, C0), and a list us of summands of S whose A-components drive
; the partial sums p, p + A(u1), p + A(u1) + A(u2), ..., all nonzero, the
; grow-chain path walks the pair to the final partial sum:
;
;   each round applies the add-duplicate path from (p, B0, C0) and the next u
;   (adding the pair for the next partial sum) and then deletes the old
;   pair by a flip of (p, B0, C0) with itself (rem:delete-identical-pair).
;
; Main results:
;  - one-step: a single round is a valid path from S + pair(p) to
;    S + pair(p + A(u)).
;  - grow-chain-invariant: the full iteration is a valid path from
;    S + pair(p) to S + pair(chain-sum p us).
;  - add-arbitrary-relative: from a scheme containing (a0, B0, C0) and a
;    nonempty us, one add-duplicate step manufactures the first pair and
;    grow-chain drives it to S + pair(chain-sum a0 us).
;
; The span/basis input of the paper's Lemma 4.6 (choosing us so that the
; partial sums are nonzero) is hypothesized here as the computable
; predicate partial-sums-okp, not proved.

(in-package "ACL2")

(include-book "paths")
(include-book "add-duplicate")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Helper rules
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule list-of-car-when-len-1
  (implies (and (true-listp x)
                (equal (len x) 1))
           (equal (list (car x)) x)))

;;; Rebuild a summand from its accessors; this is what lets the add-duplicate
;;; instance at (car u) (cadr u) (caddr u) reconnect with membership of u.

(defrule summand-of-accessors
  (implies (mat-triplep u)
           (equal (summand (car u) (cadr u) (caddr u))
                  u)))

(defrule move-list-p-of-append
  (implies (move-list-p a)
           (equal (move-list-p (append a b))
                  (move-list-p b)))
  :induct (len a))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Computable hypothesis predicates and the chain witness
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Every u in the chain is a member of the base scheme.

(define us-in-schemep ((us mat-triple-listp) (sch obag::bagp))
  :returns (yes/no booleanp)
  (if (atom us)
      t
    (and (obag::in (car us) sch)
         (us-in-schemep (cdr us) sch)))
  ///
  (defrule us-in-schemep-of-car
    (implies (and (us-in-schemep us sch)
                  (consp us))
             (obag::in (car us) sch)))
  (defrule us-in-schemep-of-cdr
    (implies (us-in-schemep us sch)
             (us-in-schemep (cdr us) sch))))

;;; The final partial sum p + A(u1) + ... + A(uk).

(define chain-sum ((p bit-list-listp) (us mat-triple-listp))
  :returns (q bit-list-listp :hyp :guard)
  (if (atom us)
      p
    (chain-sum (bit-mat-add p (car (car us))) (cdr us))))

;;; All partial sums p, p + A(u1), p + A(u1) + A(u2), ... are nonzero.
;;; This is the hypothesis the span/basis layer will discharge by choosing
;;; the order of us; here it is simply assumed.

(define partial-sums-okp ((p bit-list-listp) (us mat-triple-listp) (n natp))
  :returns (yes/no booleanp)
  :measure (acl2-count us)
  (and (not (equal p (bit-mat0 n n)))
       (if (atom us)
           t
         (partial-sums-okp (bit-mat-add p (car (car us))) (cdr us) n)))
  ///
  (defrule partial-sums-okp-nonzero
    (implies (partial-sums-okp p us n)
             (not (equal p (bit-mat0 n n)))))
  (defrule partial-sums-okp-of-cdr
    (implies (and (partial-sums-okp p us n)
                  (consp us))
             (partial-sums-okp (bit-mat-add p (car (car us))) (cdr us) n))))

;;; The iterated path.  Each round is the one-step path -- the add-duplicate path
;;; from (p, B0, C0) and u, followed by the deletion of the old pair as a
;;; flip of (p, B0, C0) with itself -- kept syntactically as an append of
;;; that round and the rest of the walk, so that path-validp-of-append and
;;; apply-moves-of-append decompose the walk round by round.

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; One round
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; From cur = sch + pair(p, B0, C0), applying the add-duplicate path for
;;; (p, B0, C0) and u and then deleting the (p, B0, C0) pair lands on
;;; sch + pair(p + A(u), B0, C0).  The nonzeroness hypothesis makes the
;;; add-duplicate output pair survive insert-all-nonzero, and it also separates
;;; the new pair summand from the old one, so the two deletions commute
;;; past the two insertions.

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
                                       (obag::insert (summand x b0 c0) sch))))))
  :do-not-induct t
  :use ((:instance add-duplicate
                   (sch (obag::insert (summand p b0 c0)
                                      (obag::insert (summand p b0 c0) sch)))
                   (a1 p) (b1 b0) (c1 c0)
                   (a2 (car u)) (b2 (cadr u)) (c2 (caddr u)))
        (:instance bit-mat-add-equal-arg1 (a p) (b (car u)) (m n) (n n))
        (:instance summandp-when-in-summand-listp (s u)))
  :enable (apply-moves in-of-insert obag::occs-of-insert)
  :disable (add-duplicate add-duplicate-path summandp-when-in-summand-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The invariant
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The pair rides on top of the fixed base scheme sch: from sch + pair(p),
;;; grow-chain is a valid path landing on sch + pair(chain-sum p us).
;;;
;;; Proof engineering: induct with grow-chain's own scheme, and give the
;;; one-step instance (and its supporting facts) on the inductive step
;;; subgoal only.  Supplying them on Goal poisons the induction: the used
;;; instances become part of the inducted formula, so the IH acquires
;;; instantiated copies of them as antecedents that cannot be relieved.
;;; partial-sums-okp and bit-mat-add-same must be enabled so that in the
;;; collision branch p = A(u) the hypothesis exposes the zero partial sum
;;; (bit-mat-add p (car u)) = 0 and closes the branch by contradiction.

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
                                       (obag::insert (summand x b0 c0) sch))))))
  :hints (("Goal"
           :induct (grow-chain p b0 c0 us n)
           :do-not-induct t
           :in-theory (e/d (grow-chain chain-sum apply-moves
                            partial-sums-okp bit-mat-add-same
                            in-of-insert obag::occs-of-insert)
                           (add-duplicate add-duplicate-path
                            summandp-when-in-summand-listp)))
          ("Subgoal *1/2"
           :use ((:instance one-step (u (car us)))
                 (:instance summandp-when-in-summand-listp (s (car us)))
                 (:instance bit-mat-add-equal-arg1
                            (a p) (b (car (car us))) (m n) (n n))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The top-level relative lemma
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; From a scheme containing (a0, B0, C0) and a nonempty chain us of its
;;; summands with all partial sums nonzero, the add-duplicate step for a0 and u1
;;; manufactures the first pair (for a0 + A(u1)) and grow-chain then drives
;;; it to the final partial sum: sch walks to sch + pair(chain-sum a0 us).

(defrule add-arbitrary-relative
  (implies (and (schemep sch n)
                (natp n)
                (obag::in (summand a0 b0 c0) sch)
                (us-in-schemep us sch)
                (summand-listp us n)
                (consp us)
                (partial-sums-okp a0 us n))
           (let* ((u1 (car us))
                  (p1 (bit-mat-add a0 (car u1)))
                  (path (append (add-duplicate-path a0 b0 c0
                                               (car u1) (cadr u1) (caddr u1) n)
                                (grow-chain p1 b0 c0 (cdr us) n)))
                  (x (chain-sum a0 us)))
             (and (path-validp path sch n)
                  (equal (apply-moves path sch n)
                         (obag::insert (summand x b0 c0)
                                       (obag::insert (summand x b0 c0) sch))))))
  :do-not-induct t
  :use ((:instance add-duplicate
                   (a1 a0) (b1 b0) (c1 c0)
                   (a2 (car (car us))) (b2 (cadr (car us))) (c2 (caddr (car us))))
        (:instance grow-chain-invariant
                   (p (bit-mat-add a0 (car (car us))))
                   (us (cdr us)))
        (:instance summandp-when-in-summand-listp (s (summand a0 b0 c0)))
        (:instance summandp-when-in-summand-listp (s (car us))))
  :enable (chain-sum partial-sums-okp in-of-insert obag::occs-of-insert)
  :disable (add-duplicate add-duplicate-path summandp-when-in-summand-listp
            grow-chain-invariant))
