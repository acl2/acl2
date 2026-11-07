; Path algebra for flip-graph schemes: composition of paths (append) and the
; deletion of an identical pair of summands (the paper's Observation
; rem:delete-identical-pair).
;
; Main results:
;  - apply-moves-of-append / path-validp-of-append: applying an appended path
;    is applying the pieces in order, and an appended path is valid exactly
;    when the first piece is valid from the start scheme and the second piece
;    is valid from where the first piece lands.
;  - scheme-sum-of-apply-moves-of-append: the sum-preservation corollary for
;    composed paths.
;  - delete-pair-move-validp / delete-pair-result: whenever a scheme holds at
;    least two copies of a summand s, the flip of s with itself (at any
;    position p < 3) is a valid move, and it removes exactly the two copies:
;    both flip outputs carry a factor s_r + s_r = 0, so both are zero
;    summands and insert-all-nonzero drops them.
;  - delete-pair-preserves-schemep-and-sum: after that move the result is
;    still a scheme and the scheme sum is unchanged.

(in-package "ACL2")

(include-book "preservation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Composition of paths
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule apply-moves-of-append
  (equal (apply-moves (append p1 p2) sch n)
         (apply-moves p2 (apply-moves p1 sch n) n))
  :induct (apply-moves p1 sch n)
  :enable (apply-moves))

(defrule path-validp-of-append
  (equal (path-validp (append p1 p2) sch n)
         (and (path-validp p1 sch n)
              (path-validp p2 (apply-moves p1 sch n) n)))
  :induct (apply-moves p1 sch n)
  :enable (apply-moves))

;;; Sum preservation over a composed path.  Stated with the validity of the
;;; two pieces as separate hypotheses (the form path-validp-of-append
;;; produces); each piece preserves the sum by scheme-sum-of-apply-moves, the
;;; intermediate scheme being well formed by summand-listp-of-apply-moves.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Deletion of an identical pair
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A flip of a summand with itself is valid exactly on the multiplicity
;;; condition of move-validp's self-move branch.

(defrule delete-pair-move-validp
  (implies (and (obag::bagp sch)
                (<= 2 (obag::occs s sch))
                (natp p)
                (< p 3))
           (move-validp (list :flip p s s) sch)))

;;; The flip of s = (A,B,C) with itself at position p outputs two summands
;;; each of which repeats a factor of s added to itself; bit-mat-add-same
;;; collapses that factor to the zero matrix (the dimension facts come from
;;; summandp of s, obtained from the multiplicity via in-when-occs-geq-2 and
;;; summandp-when-in-summand-listp), so both outputs are summand0p and
;;; insert-all-nonzero drops them, leaving exactly the two deletions.

(defrule delete-pair-result
  (implies (and (obag::bagp sch)
                (summand-listp sch n)
                (<= 2 (obag::occs s sch))
                (natp n)
                (natp p)
                (< p 3))
           (equal (apply-move (list :flip p s s) sch n)
                  (obag::delete s (obag::delete s sch))))
  :use ((:instance summandp-when-in-summand-listp))
  :enable (apply-move in-when-occs-geq-2 bit-mat-add-same))

;;; Convenience corollary: deleting an identical pair keeps the scheme well
;;; formed (schemep-of-apply-move) and preserves the scheme sum
;;; (scheme-sum-of-apply-move).

(defrule delete-pair-preserves-schemep-and-sum
  (implies (and (schemep sch n)
                (<= 2 (obag::occs s sch))
                (natp p)
                (< p 3)
                (natp n))
           (and (schemep (apply-move (list :flip p s s) sch n) n)
                (equal (scheme-sum (apply-move (list :flip p s s) sch n) n)
                       (scheme-sum sch n))))
  :use ((:instance scheme-sum-of-apply-move (move (list :flip p s s))))
  :disable (delete-pair-result))
