; Lemma 4.5 of the companion paper (lemma:add-duplicate-sum) and its
; packaging against correctness.
;
; Main results:
;  - add-duplicate: from any scheme containing summands (A1,B1,C1) and (A2,B2,C2),
;    the derived path is valid and lands exactly on the scheme with two added
;    copies of (A1+A2) (x) B1 (x) C1 (zero summands dropped, so the statement
;    holds uniformly, with the empty path when A1 = A2).
;  - correct-schemep-of-apply-moves: instantiating tt at mm-tensor, a valid
;    path preserves correctness.
;  - add-duplicate-correctness: Lemma 4.5 packaged against correctness.

(in-package "ACL2")

(include-book "mm-tensor")
(include-book "preservation")
(local (include-book "std/lists/append" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; Length-based cancellation, local proof machinery for the move-level sum
;; argument: the dimensioned cancel rules cannot fire there because their
;; dimension is a free variable, while this form relieves its hypotheses by
;; computing lengths.
(local
 (defruled bit-list-add-cancel-first
   (implies (and (bit-list-p y)
                 (<= (len y) (len x)))
            (equal (bit-list-add x (bit-list-add x y))
                   y))
   :induct (cdr-cdr-induct x y)
   :enable (bit-list-add)))

;; Not a duplicate of any library rule: the corresponding goal about a bare
;; list is proved by opening len and true-listp, which does not happen for
;; subterms like (cddr s) in context.  As an enabled rule it also lets the
;; simplifier collapse partial summand remakes back onto their source terms,
;; which the move proofs below depend on.
(local
 (defrule list-of-car-when-len-1
   (implies (and (true-listp x)
                 (equal (len x) 1))
            (equal (list (car x)) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;; Lemma 4.5 is proved in three pieces.  The two core lemmas take the
;;; summand well-formedness as explicit hypotheses rather than deriving it
;;; from schemep: supplying summandp via :use does not survive the case
;;; analysis, because the instances get consumed before the branches that
;;; need them are generated.
;;;
;;; Validity and the resulting bag are separated because they need disjoint
;;; machinery -- validity is pure membership reasoning, while the bag
;;; equality needs the insert/delete algebra -- and because their conjunction
;;; makes a poor rewrite rule.

(defruled add-duplicate-validp-core
  (implies (and (obag::bagp sch)
                (summandp (summand a1 b1 c1) n)
                (summandp (summand a2 b2 c2) n)
                (obag::in (summand a1 b1 c1) sch)
                (obag::in (summand a2 b2 c2) sch))
           (path-validp (add-duplicate-path a1 b1 c1 a2 b2 c2 n) sch n))
  :use ((:instance bit-mat-add-equal-arg2 (a b1) (b b2) (m n) (n n))
        (:instance bit-mat-add-equal-arg1 (a a1) (b a2) (m n) (n n))
        (:instance bit-mat-add-equal-arg2 (a a1) (b a2) (m n) (n n))
        (:instance bit-mat-add-equal-arg1 (a b1) (b b2) (m n) (n n)))
  :in-theory (enable apply-move in-of-insert in-of-delete))

(defruled add-duplicate-result-core
  (implies (and (obag::bagp sch)
                (summandp (summand a1 b1 c1) n)
                (summandp (summand a2 b2 c2) n)
                (obag::in (summand a1 b1 c1) sch)
                (obag::in (summand a2 b2 c2) sch))
           (equal (apply-moves (add-duplicate-path a1 b1 c1 a2 b2 c2 n) sch n)
                  (insert-all-nonzero (list (summand (bit-mat-add a1 a2) b1 c1)
                                            (summand (bit-mat-add a1 a2) b1 c1))
                                      sch n)))
  :use ((:instance bit-mat-add-equal-arg2 (a b1) (b b2) (m n) (n n))
        (:instance bit-mat-add-equal-arg1 (a a1) (b a2) (m n) (n n))
        (:instance bit-mat-add-equal-arg2 (a a1) (b a2) (m n) (n n))
        (:instance bit-mat-add-equal-arg1 (a b1) (b b2) (m n) (n n)))
  :in-theory (enable apply-moves apply-move in-of-insert in-of-delete))

;;; Lemma 4.5.  Given any two summands of a scheme S over F2, with
;;; X = A1 + A2, there is a path from S to S together with two further copies
;;; of X (x) B1 (x) C1.  When X is zero the path is empty and the two added
;;; summands are dropped on insertion, so the statement holds uniformly with
;;; no side condition.

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
                                             n)))))
  :use ((:instance summandp-when-in-summand-listp (s (summand a1 b1 c1)))
        (:instance summandp-when-in-summand-listp (s (summand a2 b2 c2)))
        add-duplicate-validp-core
        add-duplicate-result-core))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Correctness packaging
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule correct-schemep-of-apply-moves
  (implies (and (correct-schemep sch n)
                (path-validp moves sch n)
                (natp n))
           (correct-schemep (apply-moves moves sch n) n))
  ;; correct-schemep is enabled here to reproduce the define's /// scope,
  ;; where this theorem originally lived.
  :enable (correct-schemep scheme-sum-of-apply-moves))

;; Lemma 4.5, packaged: from any correct scheme containing two summands,
;; the derived path is valid, lands on the scheme with two added copies of
;; X (x) B (x) C, and correctness is preserved.
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
                  (correct-schemep sch2 n))))
  ;; correct-schemep is enabled here to reproduce the define's /// scope,
  ;; where this theorem originally lived.
  :enable (correct-schemep)
  :use (add-duplicate)
  :disable (add-duplicate))
