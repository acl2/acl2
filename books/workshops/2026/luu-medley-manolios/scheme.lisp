(in-package "ACL2")

(include-book "bits")
(include-book "bags")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mat-triplep (s)
  :enabled t
  :returns (yes/no booleanp)
  (and (true-listp s)
       (equal (len s) 3)
       (bit-list-listp (car s))
       (bit-list-listp (cadr s))
       (bit-list-listp (caddr s))))

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

;;; A dimensioned summand that may be zero: summandp minus the nonzero
;;; condition.  This is the type of flip/plus outputs -- their factors are
;;; sums of n x n matrices and hence n x n, but any of them may come out
;;; zero, in which case insert-all-nonzero drops the summand.

(define summand-dimp (s (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (and (mat-triplep s)
       (bit-matp (car s) n n)
       (bit-matp (cadr s) n n)
       (bit-matp (caddr s) n n))
  ///

  (defrule summand-dimp-when-summandp
    (implies (summandp s n)
             (summand-dimp s n)))

  ;; Dimensioned in/out theorems for the constructor and accessors: building a
  ;; summand from n x n factors yields an n-summand, and every factor drawn
  ;; from an n-summand is n x n.

  (defrule summand-dimp-of-summand
    (implies (and (bit-matp a n n)
                  (bit-matp b n n)
                  (bit-matp c n n))
             (summand-dimp (summand a b c) n)))

  (defrule bit-matp-of-summand-A
    (implies (summand-dimp s n)
             (bit-matp (summand-A s) n n)))

  (defrule bit-matp-of-summand-B
    (implies (summand-dimp s n)
             (bit-matp (summand-B s) n n)))

  (defrule bit-matp-of-summand-C
    (implies (summand-dimp s n)
             (bit-matp (summand-C s) n n))))

(define summand-dim-listp (l (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (summand-dimp (car l) n)
         (summand-dim-listp (cdr l) n))))

(define summand-listp (x (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (if (atom x)
      (null x)
    (and (summandp (car x) n)
         (summand-listp (cdr x) n)))
  ///

  (defrule true-listp-when-summand-listp
    (implies (summand-listp x n)
             (true-listp x)))

  (defrule summand-dim-listp-when-summand-listp
    (implies (summand-listp l n)
             (summand-dim-listp l n))
    :enable summand-dim-listp)

  ;; The invariant that makes every zero-factor side condition discharge: any
  ;; summand drawn from a scheme is well formed and, in particular, has no
  ;; zero factor.

  (defrule summandp-when-in-summand-listp
    (implies (and (summand-listp sch n)
                  (obag::bagp sch)
                  (obag::in s sch))
             (summandp s n))
    :enable (obag::in obag::head obag::tail
                      obag::emptyp obag::bfix obag::bagp))

  ;; Closure of summand-listp under the obag operations.  These are what let
  ;; every move preserve schemep: a move deletes its consumed summands and
  ;; inserts its (well-formed) outputs.

  (defrule summand-listp-of-insert
    (implies (and (summand-listp sch n)
                  (obag::bagp sch)
                  (summandp x n))
             (summand-listp (obag::insert x sch) n))
    :induct (obag::insert x sch)
    :enable (obag::insert obag::bagp obag::head obag::tail
                          obag::emptyp obag::bfix)
    :disable (summandp))

  (defrule summand-listp-of-delete
    (implies (and (summand-listp sch n)
                  (obag::bagp sch))
             (summand-listp (obag::delete x sch) n))
    :induct (obag::delete x sch)
    :enable (obag::delete obag::bagp obag::head obag::tail
                          obag::emptyp obag::bfix)
    :disable (summandp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemep (x (n natp))
  :enabled t
  :returns (yes/no booleanp)
  (and (obag::bagp x)
       (summand-listp x n)))

(define scheme-rank (x)
  :enabled t
  :returns (r natp)
  (len x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
    (t (caddr s)))
  ///

  (defrule bit-matp-of-summand-get-pos
    (implies (summand-dimp s n)
             (bit-matp (summand-get-pos s p) n n))))

(define summand-set-pos ((s mat-triplep) p (m bit-list-listp))
  :enabled t
  :returns (s1 mat-triplep :hyp :guard)
  (case p
    (0 (summand m (cadr s) (caddr s)))
    (1 (summand (car s) m (caddr s)))
    (t (summand (car s) (cadr s) m)))
  ///

  (defrule summand-dimp-of-summand-set-pos
    (implies (and (summand-dimp s n)
                  (bit-matp m n n))
             (summand-dimp (summand-set-pos s p m) n))))

(define mat-triple-listp (l)
  :enabled t
  :returns (yes/no booleanp)
  (if (atom l)
      (null l)
    (and (mat-triplep (car l))
         (mat-triple-listp (cdr l)))))

;;; Components of the head of a summand list.  These hold for the empty list
;;; too -- (car nil) is nil and (bit-list-listp nil) is true -- which is what
;;; lets the path builders guard-verify without a nonempty-chain hypothesis.

(defruled mat-triplep-of-car-when-mat-triple-listp
  (implies (and (mat-triple-listp l)
                (consp l))
           (mat-triplep (car l))))

(defruled true-listp-of-car-when-mat-triple-listp
  (implies (mat-triple-listp l)
           (true-listp (car l)))
  :rule-classes (:rewrite :type-prescription))

(defruled true-listp-of-cdr-of-car-when-mat-triple-listp
  (implies (mat-triple-listp l)
           (true-listp (cdr (car l))))
  :rule-classes (:rewrite :type-prescription))

(defruled true-listp-of-cddr-of-car-when-mat-triple-listp
  (implies (mat-triple-listp l)
           (true-listp (cddr (car l))))
  :rule-classes (:rewrite :type-prescription))

(defruled mat-triple-listp-of-cdr-when-mat-triple-listp
  (implies (mat-triple-listp l)
           (mat-triple-listp (cdr l))))

(defruled bit-list-listp-of-car-of-car-when-mat-triple-listp
  (implies (mat-triple-listp l)
           (bit-list-listp (car (car l)))))

(defruled bit-list-listp-of-cadr-of-car-when-mat-triple-listp
  (implies (mat-triple-listp l)
           (bit-list-listp (cadr (car l)))))

(defruled bit-list-listp-of-caddr-of-car-when-mat-triple-listp
  (implies (mat-triple-listp l)
           (bit-list-listp (caddr (car l)))))

;;; These are left disabled: as enabled rules they fire on every car/cdr goal
;;; in the development and cost a tenfold blow-up in certification time.  The
;;; guard proofs that need them enable this theory locally.

;;; The same facts as one conjunction, for :use at a specific chain term.
;;; Guard obligations about (car US) for an opaque US are easiest to relieve
;;; by putting these in the hypotheses rather than hoping the rewriter keeps
;;; (mat-triple-listp US) folded long enough for the rules above to match.

(defrule mat-triple-head-facts
  (implies (mat-triple-listp l)
           (and (true-listp l)
                (true-listp (car l))
                (true-listp (cdr (car l)))
                (true-listp (cddr (car l)))
                ;; the car/cdr guard obligations in the exact shape the guard
                ;; prover leaves them: "not a cons" must give "is nil"
                (implies (not (consp l)) (equal l nil))
                (implies (not (consp (car l))) (equal (car l) nil))
                (implies (not (consp (cdr (car l)))) (equal (cdr (car l)) nil))
                (implies (not (consp (cddr (car l)))) (equal (cddr (car l)) nil))
                (bit-list-listp (car (car l)))
                (bit-list-listp (cadr (car l)))
                (bit-list-listp (caddr (car l)))
                (mat-triple-listp (cdr l))))
  :rule-classes nil)

;;; Structural mirror of summand-listp-of-insert below: the dimensioned
;;; closure lemma cannot serve the guard proofs of the path builders, whose
;;; guards are structural.

(defruled mat-triple-listp-of-insert
  (implies (and (mat-triple-listp sch)
                (obag::bagp sch)
                (mat-triplep x))
           (mat-triple-listp (obag::insert x sch)))
  :induct (obag::insert x sch)
  :enable (obag::insert obag::bagp obag::head obag::tail
                        obag::emptyp obag::bfix))

(defruled mat-triple-listp-of-delete
  (implies (and (mat-triple-listp sch)
                (obag::bagp sch))
           (mat-triple-listp (obag::delete x sch)))
  :induct (obag::delete x sch)
  :enable (obag::delete obag::bagp obag::head obag::tail
                        obag::emptyp obag::bfix
                        mat-triple-listp-of-insert))

(deftheory mat-triple-obag-lemmas
  '(mat-triple-listp-of-insert
    mat-triple-listp-of-delete))

(defruled true-listp-when-mat-triple-listp
  (implies (mat-triple-listp l)
           (true-listp l))
  :rule-classes (:rewrite :forward-chaining))

(defruled mat-triple-listp-of-remove1-equal
  (implies (mat-triple-listp l)
           (mat-triple-listp (remove1-equal x l)))
  :induct (remove1-equal x l))

(deftheory mat-triple-head-lemmas
  '(true-listp-when-mat-triple-listp
    mat-triple-listp-of-remove1-equal
    mat-triplep-of-car-when-mat-triple-listp
    true-listp-of-car-when-mat-triple-listp
    true-listp-of-cdr-of-car-when-mat-triple-listp
    true-listp-of-cddr-of-car-when-mat-triple-listp
    mat-triple-listp-of-cdr-when-mat-triple-listp
    bit-list-listp-of-car-of-car-when-mat-triple-listp
    bit-list-listp-of-cadr-of-car-when-mat-triple-listp
    bit-list-listp-of-caddr-of-car-when-mat-triple-listp))

;;; s1 = (A,B,C) ; s2 = (A',B',C') ; p in {0,1,2} ; s1 and s2 agree at p
;;; -->
;;; (A,B,C+C') and (A',B'+B,C')
;;; Both summands are consumed.  Rank is preserved, except that either output
;;; may come out zero and be dropped on insertion.
(define flip ((s1 mat-triplep) (s2 mat-triplep) (p natp))
  :enabled t
  :returns (l mat-triple-listp :hyp :guard)
  (let ((q (pos-next p))
        (r (pos-prev p)))
    (list (summand-set-pos s1 r (bit-mat-add (summand-get-pos s1 r)
                                             (summand-get-pos s2 r)))
          (summand-set-pos s2 q (bit-mat-add (summand-get-pos s2 q)
                                             (summand-get-pos s1 q)))))
  ///
  (defrule summand-dim-listp-of-flip
    (implies (and (summand-dimp s1 n)
                  (summand-dimp s2 n))
             (summand-dim-listp (flip s1 s2 p) n))))

;;; target = (A,B,C) ; pivot = (A',B',C') ; p in {0,1,2}
;;; -->
;;; (A+A',B,C) and (A',B,C)
;;; Only the target is consumed; the pivot is read but left in place, so the
;;; caller deletes the target only.  Sum-preserving since (A+A') + A' = A.
(define plus ((target mat-triplep) (pivot mat-triplep) (p natp))
  :enabled t
  :returns (l mat-triple-listp :hyp :guard)
  (list (summand-set-pos target p (bit-mat-add (summand-get-pos target p)
                                               (summand-get-pos pivot p)))
        (summand-set-pos target p (summand-get-pos pivot p)))
  ///
  (defrule summand-dim-listp-of-plus
    (implies (and (summand-dimp target n)
                  (summand-dimp pivot n))
             (summand-dim-listp (plus target pivot p) n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; move ::= (:op p s1 s2)
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

(define insert-all-nonzero ((l mat-triple-listp) (s obag::bagp) (n natp))
  :enabled t
  :returns (s1 obag::bagp :hyp (obag::bagp s))
  (if (atom l)
      s
    (if (summand0p (car l) n)
        (insert-all-nonzero (cdr l) s n)
      (obag::insert (car l) (insert-all-nonzero (cdr l) s n))))
  ///

  (defrule summand-listp-of-insert-all-nonzero
    (implies (and (obag::bagp s)
                  (summand-listp s n)
                  (summand-dim-listp l n))
             (summand-listp (insert-all-nonzero l s n) n))
    :induct (insert-all-nonzero l s n))

  ;; The size-constrained return theorem: inserting dimensioned summands into
  ;; an n-scheme yields an n-scheme, the zero ones being dropped.
  (defrule schemep-of-insert-all-nonzero
    (implies (and (schemep s n)
                  (summand-dim-listp l n))
             (schemep (insert-all-nonzero l s n) n))
    :enable schemep
    :disable insert-all-nonzero))

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

;;; For :plus, move-s1 is the target (consumed) and move-s2 is the pivot
;;; (read only).  For :flip, both are consumed.
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
    (t sch))
  ///

  ;; A valid move's summands are members of the scheme (via the multiplicity
  ;; bridge in the self-move case), hence summandp; the outputs of plus/flip
  ;; are then dimensioned, and insert-all-nonzero keeps only the nonzero
  ;; ones.

  (defrule summand-listp-of-apply-move
    (implies (and (obag::bagp sch)
                  (summand-listp sch n)
                  (move-validp move sch))
             (summand-listp (apply-move move sch n) n))
    :use ((:instance summandp-when-in-summand-listp (s (move-s1 move)))
          (:instance summandp-when-in-summand-listp (s (move-s2 move))))
    :enable (apply-move in-when-occs-geq-2))

  (defrule schemep-of-apply-move
    (implies (and (schemep sch n)
                  (move-validp move sch))
             (schemep (apply-move move sch n) n))
    :disable (apply-move)))

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
         (path-validp (cdr moves) (apply-move (car moves) sch n) n)))
  ///

  (defrule summand-listp-of-apply-moves
    (implies (and (obag::bagp sch)
                  (summand-listp sch n)
                  (path-validp moves sch n))
             (summand-listp (apply-moves moves sch n) n))
    :induct (apply-moves moves sch n)
    :enable (apply-moves))

  (defrule schemep-of-apply-moves
    (implies (and (schemep sch n)
                  (path-validp moves sch n))
             (schemep (apply-moves moves sch n) n))))
