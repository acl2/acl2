;; UTEP - Utrecht Texas Equational Prover
;; A modest first order resolution and paramodulation based theorem prover written in ACL2.
;; Authored by Grant Olney Passmore {grant@math.utexas.edu}.
;; Began on: 12/22/05 at 4:46pm.
;; Last updated: 11/14/06 at 23:48.
;;
;; Note: We treat Skolem Constants as 0-ary functions, so we may
;; always differentiate constants from variables syntactically, as constants are
;; always of the form (CONSTANT-NAME), whereas, since we're first-order,
;; variables never are surrounded immediately (to the left) by parentheses.
;; G. Passmore :: 12/22/05

(in-package "ACL2")

(include-book "general")
(include-book "unification")
(include-book "weighting")
(include-book "resolution")
(include-book "paramod")
(include-book "bewijs")

;; CONTAINS-REFUTATION (proof-moves)
;; Given a structured set of proof-moves (i.e., ((0) (move :AXIOM ... ))),
;; return non nil if a proof of NIL, the refutation, is present.
;; Note: If we do find a proof of the refutation present, we return the
;; line id of the proof that it occurs on.
;; G. Passmore :: 12/23/05

(defun contains-refutation (proof-moves)
  (if (endp proof-moves) nil
    (let ((cur-move (car proof-moves)))
      (let ((cur-move-id (car cur-move))
	    (cur-move-clause (caddr cur-move)))
      (if (equal cur-move-clause nil) cur-move-id
	(contains-refutation (cdr proof-moves)))))))

;; FILTER-DUPLICATES (new-moves sos-moves usable-moves)
;; A mild subsumption check that only checks to see if a newly derived clause in SOS
;; already exists in either SOS or USABLE.  Note, this check is totally nieve, and is
;; not even done modulo variable renaming.  More expensive redundancy and subsumption
;; checking will be done experimentally soon.

(defun filter-duplicates (new-moves sos-moves usable-moves)
  (cond ((endp new-moves) nil)	((or (clause-move-member (extract-clause (car new-moves)) sos-moves)
	     (clause-move-member (extract-clause (car new-moves)) usable-moves))
	 (filter-duplicates (cdr new-moves) sos-moves usable-moves))
	(t (cons (car new-moves)
		 (filter-duplicates (cdr new-moves) sos-moves usable-moves)))))

;; PROVER-LOOP (sos-moves usable-moves prover-settings search-limit)
;; A new experimental loop for the prover, written in the Argonne/Otter SOS fashion.
;; By default, we use a PICK-GIVEN-RATION setting of 1:2 (2) to determine how
;; often SOS/USABLE and SOS/SOS proof-search is alternated.
;; G. Passmore :: 11/14/06

(defun prover-loop (sos-moves usable-moves last-cycle-top-clause top-clause-id prover-settings search-limit)
  (declare (xargs :measure (acl2-count search-limit)))
  (cond ((or (not (posp search-limit)) (contains-refutation sos-moves)) (mv (quad-filter-internal-dups sos-moves) usable-moves))

	;;
	;; PICK-GIVEN-RATIO (for SOS/USABLE and SOS/SOS interlacing) determines the modulus check taking place with ZP below.  Default is 1:2 (2).
	;;

	(t (let ((pick-given-ratio (or (get-setting prover-settings 'PICK-GIVEN-RATIO) 2)))
	     (let ((new-sos-resolvents
		    (if (zp (mod search-limit pick-given-ratio))
			(linear-resolution sos-moves usable-moves last-cycle-top-clause prover-settings)
			(linear-resolution sos-moves sos-moves last-cycle-top-clause prover-settings))))
	       (let ((new-sos-mergers
		      (if (get-setting prover-settings 'NO-MERGING) nil
			  (linear-merging (append new-sos-resolvents sos-moves)
					  (+ top-clause-id (len new-sos-resolvents))
					  last-cycle-top-clause 0))))
		 (let ((new-sos-factors
			(if (get-setting prover-settings 'NO-FACTORING) nil
			    (linear-factoring (append sos-moves new-sos-resolvents new-sos-mergers)
						    (+ top-clause-id (len new-sos-resolvents) (len new-sos-mergers))
						    last-cycle-top-clause 0))))

		   ;;
		   ;; Paramodulation is special here in that it is the only inference rule that is DISABLED by default.
		   ;; To enable paramodulation, USE-PARAMOD must be an enabled configuration flag.
		   ;; When paramodulation is enabled, we will default to RHS being the paramodulus base, but this is
		   ;; configurable as PARAMOD-EQ-SIDE (may be either RHS or LHS).
		   ;; * Paramodulation is still linear right now.  I should think about incorporating an appropriate SOS/USABLE
		   ;;   distinction for paramodulation.  For now, I'll merge SOS,USABLE first and then linearly paramodulate.
		   ;;
		   ;; * A little experimental strategy I'm toying with (11/14/06):
		   ;;   PARAMOD-RES-RATIO, if explicitly set, will act as a PICK-GIVEN-RATIO gate on paramodulation inferences.
		   ;;   This way, if USE-PARAMOD is enabled and PARAMOD-RES-RATIO is set to 3 for instance,
		   ;;   then paramodulation will only be done every 3rd iteration of the main prover loop.
		   ;;

		   (let ((new-sos-paramoduli
			  (if (or (not (get-setting prover-settings 'USE-PARAMOD))
				  (and (get-setting prover-settings 'USE-PARAMOD)
				       (> (nfix (get-setting prover-settings 'PARAMOD-RES-RATIO)) 0)
				       (posp (mod search-limit (get-setting prover-settings 'PARAMOD-RES-RATIO))))) nil

				       (linear-paramodulation (append sos-moves new-sos-resolvents new-sos-mergers new-sos-factors)
							      (or (get-setting prover-settings 'PARAMOD-EQ-SIDE) 'RHS)
							      (+ top-clause-id (len new-sos-resolvents) (len new-sos-mergers) (len new-sos-factors))
							      (get-setting prover-settings 'MAX-WEIGHT)))))

		     ;;
		     ;; The idea here is that if we have a non-redundant merger, factor based upon our new
		     ;; SOS-RESOLVENTS, then chances are it may be more helpful than its parent in SOS-RESOLVENTS.  Thus,
		     ;; we include it first in the append below.  When we have more ex(t/p)ensive subsumption checking,
		     ;; this won't be an important thing to sweat about anymore.
		     ;; * We place paramoduli last as this seems to be best in practice at this current moment.
		     ;;
		     ;; * Note this double reverse here: This is so that we don't throw out the `wrong' duplicate clause.
		     ;;   (I call a clause A which is a duplicate of a clause B the `wrong' one to throw out if A is used to
		     ;;    justify an inference in another proof-move but B is not).

		 (prover-loop (append sos-moves
				      (filter-duplicates
				       (reverse (quad-filter-internal-dups
						 (reverse (append new-sos-factors new-sos-mergers new-sos-resolvents new-sos-paramoduli))))
				       sos-moves usable-moves))
			    usable-moves
			    (+ 1 (len new-sos-resolvents) top-clause-id last-cycle-top-clause)
			    (+ (len new-sos-resolvents) top-clause-id)
			    prover-settings (1- search-limit))))))))))

;;
;; UTEPTHM (input-clauses prover-settings)
;; Given a list of input clauses and prover-settings, attempt to
;; find a proof.
;;

(defun utepthm (sos-clauses usable-clauses prover-settings)
  (mv-let (sos-move-tree usable-move-tree)
	  (prover-loop (raw-clauses-to-axiom-moves* sos-clauses 0 'S)
		       (raw-clauses-to-axiom-moves* usable-clauses (1+ (len sos-clauses)) 'U)
		       (1+ (len sos-clauses)) 0
		       prover-settings
		       (or (get-setting prover-settings 'SEARCH-DEPTH) 5))
	  (let ((refutation-move-id (contains-refutation sos-move-tree)))
	    (cond ((not (equal refutation-move-id nil))
		   (let ((pruned-linear-move-proof-tree (prune-proof-tree* (crop-proof-end-at-line-id (append usable-move-tree sos-move-tree) refutation-move-id))))
		     (list (if (get-setting prover-settings 'VERBOSE-QED)
			       (list (list '**USABLE** usable-move-tree) (list '**SOS** sos-move-tree))
			       (list '(VERBOSE-QED DISABLED)))
			   (list '*** 'PROOF 'FOUND '***)
			   (list pruned-linear-move-proof-tree
				 (list (list '|.:.| 'THEOREM 'PROVED)
				       (list (- (len sos-move-tree) (len sos-clauses)) 'CLAUSES 'GENERATED)
				       (list (len pruned-linear-move-proof-tree) 'CLAUSES 'USED 'IN 'PROOF))))))
		  (t (list
		      (if (get-setting prover-settings 'NO-FAILURE-TREE) '(NO-FAILURE-TREE SETTING IS INHIBITING OUTPUT)
			  (list (list '**USABLE** usable-move-tree) (list '**SOS** sos-move-tree)))
		      (list '********** 'NO 'PROOF 'FOUND '**********)
		      (list '= 'SEARCH-DEPTH (or (get-setting prover-settings 'SEARCH-DEPTH) 5))
		      (list '= 'MAX-WEIGHT (nfix (get-setting prover-settings 'MAX-WEIGHT)))
		      (list '= 'NUM-KEPT-CLAUSES-GENERATED (- (len sos-move-tree) (len sos-clauses)))))))))


;; Some examples:
;;
;; A trivial theorem that was hard to prove (UTEP couldn't!) until I implemented the
;; new top-level loop with SOS/USABLE, WEIGHTING, PICK-GIVEN-RATIO, and
;; PARAMOD-RES-RATIO (seems to be most important, which is nice as this idea just occurred
;; to me tonight!).
;; G.P. :: 11/14/06
;;

#|

(utepthm
 ; SOS
 '(((= x x)) ; Must add this clause when using paramodulation, else no completeness!
   ((not (A x)) (B x))
   ((not (B x)) (= (foo) x))
   ((not (C x)) (D x))
   ((not (D x)) (E x)))
 ; Usable
 '(((A (bar)))
   ((not (= (bar) (foo)))))
 ; Settings
 '((max-weight 20)
   (pick-given-ratio 2)
   (use-paramod t)
   (paramod-res-ratio 3)
   (search-depth 10)))

 Output as of 11/14/06:

ACL2 !>(utepthm
 ; SOS
 '(((= x x))
   ((not (A x)) (B x))
   ((not (B x)) (= (foo) x))
   ((not (C x)) (D x))
   ((not (D x)) (E x)))
 ; Usable
 '(((A (bar)))
   ((not (= (bar) (foo)))))
 ; Settings
 '((max-weight 20)
   (pick-given-ratio 2)
   (use-paramod t)
   (paramod-res-ratio 3)
   (search-depth 10)))

(((VERBOSE-QED DISABLED))
 (*** PROOF FOUND ***)
 ((((U 6) (MOVE :AXIOM) ((A (BAR))))
   ((S 0) (MOVE :AXIOM) ((= X X)))
   ((S 1)
    (MOVE :AXIOM)
    ((NOT (A X)) (B X)))
   ((S 2)
    (MOVE :AXIOM)
    ((NOT (B X)) (= (FOO) X)))
   ((S 10)
    (MOVE :BINARY-RESOLUTION ((S 2) 0)
          ((S 1) 1))
    ((= (FOO) Y) (NOT (A Y))))
   ((S 23)
    (MOVE :PARAMODULATION ((S 0) 0)
          ((S 10) 1 0))
    ((= (FOO) Y) (NOT (A Y)) (NOT (A Y))))
   ((S 23)
    (MOVE :BINARY-RESOLUTION ((S 23) 2)
          ((U 6) 0))
    ((= (FOO) (BAR)) (NOT (A (BAR)))))
   ((S 135)
    (MOVE :PARAMODULATION ((S 0) 0)
          ((S 23) 2 0))
    ((NOT (A Y)) (NOT (A Y)) (NOT (A Y))))
   ((S 2175)
    (MOVE :MERGE-CLAUSE ((S 135) :MERGED-LITERALS (2 1 0)))
    ((NOT (A Y))))
   ((S 2319)
    (MOVE :BINARY-RESOLUTION ((S 2175) 0)
          ((U 6) 0))
    NIL))
  ((|.:.| THEOREM PROVED)
   (255 CLAUSES GENERATED)
   (10 CLAUSES USED IN PROOF))))


;;
;; A hard example that was not possible to prove until tonight (11/14/06)!
;;

;; A non-trivial benchmark/test input - Drawn from OTTER's benchmark suite.
;; The sentential calculus (CN).
;;
;; {CN1, CN2, CN3} (Lukasiewicz), along with condensed detachment,
;; axiomatizes the sentential calculus (the classical propositional calculus).
;; -P(i(x,y)) | -P(x) | P(y).      % condensed detachment
;;

 -P(i(x,y)) | -P(x) | P(y).
 P(i(i(x,y),i(i(y,z),i(x,z)))).  % CN1
 P(i(i(n(x),x),x)).              % CN2
 P(i(x,i(n(x),y))).              % CN3
 -P(i(i(i(a,b),c),i(b,c))).

;;
;; This translates to:

(utepthm
 '(((not (P (i x y))) (not (P x)) (P y))
   ((P (i (i x y) (i (i y z) (i x z)))))
   ((P (i (i (n x) x) x)))
   ((P (i x (i (n x) y)))))
 '(((not (P (i (i (i (a) (b)) (c)) (i (b) (c))))))
   ((not (P (i (a) (a)))))
   ((not (P (i (n (i (a) (a))) (b)))))
   ((not (P (i (i (n (i (a) (b))) (i (a) (b))) (i (i (n (a) (a)) (b))))))))
 '((max-weight 19)
   (pick-given-ratio 2)
   (use-paramod nil)
   (search-depth 10)))

 A proof is found! 11/14/06

(((VERBOSE-QED DISABLED))
 (*** PROOF FOUND ***)
 ((((U 5)
    (MOVE :AXIOM)
    ((NOT (P (I (I (I (A) (B)) (C)) (I (B) (C)))))))
   ((S 0)
    (MOVE :AXIOM)
    ((NOT (P (I X Y))) (NOT (P X)) (P Y)))
   ((S 1)
    (MOVE :AXIOM)
    ((P (I (I X Y) (I (I Y Z) (I X Z))))))
   ((S 6)
    (MOVE :BINARY-RESOLUTION ((S 0) 2)
          ((U 5) 0))
    ((NOT (P (I X (I (I (I (A) (B)) (C)) (I (B) (C))))))
     (NOT (P X))))
   ((S 28)
    (MOVE :BINARY-RESOLUTION ((S 1) 0)
          ((S 6) 0))
    ((NOT (P (I X Y)))))
   ((S 213)
    (MOVE :BINARY-RESOLUTION ((S 1) 0)
          ((S 28) 0))
    NIL))
  ((|.:.| THEOREM PROVED)
   (352 CLAUSES GENERATED)
   (6 CLAUSES USED IN PROOF))))


;;
;; A *seriously* hard example.
;; A 4-basis for the infinitely many-valued sentential calculus.
;; Drawn from Bob Veroff and McCunes CD work with OTTER.
;;

(utepthm
 ; Set-Of-Support Clauses
 '(((not (P (i (n (n (a))) (a)))))                           ; ~MV-24
   ((not (P (i (i (a) (b)) (i (i (c) (a)) (i (c) (b)))))))   ; ~MV-25
   ((not (P (i (a) (n (n (a)))))))                           ; ~MV-26
   ((not (P (i x y))) (not (P x))  (P y)))                   ; condensed detachment
 ; Usable Clauses
 '(((P (i x (i y x))))                               ; MV-1
   ((P (i (i x y) (i (i y z) (i x z)))))             ; MV-2
   ((P (i (i (i x y) y) (i (i y x) x))))             ; MV-3
   ((P (i (i (n x) (n y)) (i y x)))))                ; MV-5
 '((max-weight 19)
   (pick-given-ratio 2)
   (use-paramod nil)
   (search-depth 10)))

 On 11/14/06, at last, a proof is found!!!

ACL2 !>(utepthm
 ; Set-Of-Support Clauses
 '(((not (P (i (n (n (a))) (a)))))                           ; ~MV-24
   ((not (P (i (i (a) (b)) (i (i (c) (a)) (i (c) (b)))))))   ; ~MV-25
   ((not (P (i (a) (n (n (a)))))))                           ; ~MV-26
   ((not (P (i x y))) (not (P x))  (P y)))                   ; condensed detachment
 ; Usable Clauses
 '(((P (i x (i y x))))                               ; MV-1
   ((P (i (i x y) (i (i y z) (i x z)))))             ; MV-2
   ((P (i (i (i x y) y) (i (i y x) x))))             ; MV-3
   ((P (i (i (n x) (n y)) (i y x)))))                ; MV-5
 '((max-weight 19)
   (pick-given-ratio 2)
   (use-paramod nil)
   (search-depth 10)))

(((VERBOSE-QED DISABLED))
 (*** PROOF FOUND ***)
 ((((U 5)
    (MOVE :AXIOM)
    ((P (I X (I Y X)))))
   ((U 8)
    (MOVE :AXIOM)
    ((P (I (I (N X) (N Y)) (I Y X)))))
   ((S 0)
    (MOVE :AXIOM)
    ((NOT (P (I (N (N (A))) (A))))))
   ((S 3)
    (MOVE :AXIOM)
    ((NOT (P (I X Y))) (NOT (P X)) (P Y)))
   ((S 6)
    (MOVE :BINARY-RESOLUTION ((S 3) 0)
          ((U 5) 0))
    ((NOT (P Z)) (P (I U Z))))
   ((S 12)
    (MOVE :BINARY-RESOLUTION ((S 3) 0)
          ((U 8) 0))
    ((NOT (P (I (N Z) (N U)))) (P (I U Z))))
   ((S 12)
    (MOVE :BINARY-RESOLUTION ((S 0) 0)
          ((S 3) 2))
    ((NOT (P (I X (I (N (N (A))) (A)))))
     (NOT (P X))))
   ((S 78)
    (MOVE :BINARY-RESOLUTION ((S 6) 0)
          ((U 5) 0))
    ((P (I U (I X (I Y X))))))
   ((S 96)
    (MOVE :BINARY-RESOLUTION ((S 12) 0)
          ((U 5) 0))
    ((NOT (P Z))))
   ((S 7200)
    (MOVE :BINARY-RESOLUTION ((S 78) 0)
          ((S 96) 0))
    NIL))
  ((|.:.| THEOREM PROVED)
   (2685 CLAUSES GENERATED)
   (10 CLAUSES USED IN PROOF))))


A classic group theory example.
Show that groups of exponent two are abelian:

As of 11/14/06, I can't yet prove this.  This is a good
problem to focus on for improving the prover.
Prover9 gets this without ANY hints, weights, etc.!

(utepthm
 ; Set-Of-Support Clauses
 '(((not (= (f (a) (b)) (f (b) (a)))))  ; Negation of goal (commutativity)
   ((= x x))                            ; For paramodulation completeness
   ((= (f x x) (e)))                    ; This group is of exponent 2
   ((= (f x (i x)) (e)))                ; Groups have a right inverse (deducible that exists a left)
   ((= (f x (e)) x))                    ; Groups have a right identity
   ((= (f (e) x) x))                    ;  which is also a left identity
   ((= (f x (f y z)) (f (f x y) z)))    ; Groups are associative
   ((= (f (f x y) z) (f x (f y z))))    ; Flip of associativity
   ((= (f (e) x) x)))                   ; Groups have a left identity
 ; Usable Clauses
 nil
 ; Prover Settings
 '((max-weight 20)
   (pick-given-ratio 3)
   (use-paramod t)
   (paramod-res-ratio 5)
   (paramod-eq-side RHS)
   (search-depth 10)))

;; New example:

(utepthm
 ; Set-Of-Support Clauses
 '( ((not (P (i (a)) (a) (e)))) )  ; Denial of left inverse.
 ; Usable Clauses
 '(((not (P x y u)) (not (P y z w)) (not (P u z s)) (P x w s)) ; Product is associative
   ((P x (e) x)) ; Right identity
   ((P (e) x x)) ; Left identity
   ((P x (i x) (e)))) ; Right inverse
 ; Prover Settings
 '((max-weight 25)
   (pick-given-ratio 2)
   (use-paramod nil)
   (paramod-res-ratio 5)
   (paramod-eq-side RHS)
   (search-depth 10)))

(((VERBOSE-QED DISABLED))
 (*** PROOF FOUND ***)
 ((((U 2)
    (MOVE :AXIOM)
    ((NOT (P X Y U))
     (NOT (P Y Z W))
     (NOT (P U Z S))
     (P X W S)))
   ((U 3) (MOVE :AXIOM) ((P X (E) X)))
   ((U 4) (MOVE :AXIOM) ((P (E) X X)))
   ((U 5) (MOVE :AXIOM) ((P X (I X) (E))))
   ((S 0)
    (MOVE :AXIOM)
    ((NOT (P (I (A)) (A) (E)))))
   ((S 3)
    (MOVE :BINARY-RESOLUTION ((S 0) 0)
          ((U 2) 3))
    ((NOT (P (I (A)) Y U))
     (NOT (P Y Z (A)))
     (NOT (P U Z (E)))))
   ((S 11)
    (MOVE :BINARY-RESOLUTION ((S 3) 0)
          ((U 3) 0))
    ((NOT (P (E) Z (A)))
     (NOT (P (I (A)) Z (E)))))
   ((S 41)
    (MOVE :BINARY-RESOLUTION ((S 11) 0)
          ((U 4) 0))
    ((NOT (P (I (A)) X (E)))))
   ((S 164)
    (MOVE :BINARY-RESOLUTION ((S 41) 0)
          ((U 5) 0))
    NIL))
  ((|.:.| THEOREM PROVED)
   (41 CLAUSES GENERATED)
   (9 CLAUSES USED IN PROOF))))


;;
;; A propositional example:
;;

(utepthm
 ; Set-Of-Support Clauses
 '(((A))
   ((not (E))))
 ; Usable Clauses
 '(((not (A)) (B))
   ((not (B)) (C))
   ((not (C)) (D))
   ((not (D)) (E)))
 ; Prover Settings
 '((max-weight 19)
   (pick-given-ratio 2)
   (use-paramod nil)
   (search-depth 10)))

;; This finds a proof!
 Output as of 11/14/06:

(((VERBOSE-QED DISABLED))
 (*** PROOF FOUND ***)
 ((((S 0) (MOVE :AXIOM) ((A)))
   ((S 1) (MOVE :AXIOM) ((NOT (E))))
   ((S 4)
    (MOVE :BINARY-RESOLUTION ((S 0) 0)
          ((U 3) 0))
    ((B)))
   ((S 5)
    (MOVE :BINARY-RESOLUTION ((S 1) 0)
          ((U 6) 1))
    ((NOT (D))))
   ((S 12)
    (MOVE :BINARY-RESOLUTION ((S 4) 0)
          ((U 4) 0))
    ((C)))
   ((S 13)
    (MOVE :BINARY-RESOLUTION ((S 5) 0)
          ((U 5) 1))
    ((NOT (C))))
   ((S 17)
    (MOVE :BINARY-RESOLUTION ((S 12) 0)
          ((S 13) 0))
    NIL))
  ((|.:.| THEOREM PROVED)
   (5 CLAUSES GENERATED)
   (7 CLAUSES USED IN PROOF))))

|#


;; ** Old testing notes, examples, and misc. related things **
;;
;; EXAMPLE:
;; A nice example of a few of my above resolution functions in practice:
;;
;; > (find-all-binary-resolvents '((P x (f (a) y)) (Q (g (b)) y) (not (R x z (a))) (not (R x (f x x) (a)))) '((not (P (g (b)) (f u v))) (not (Q v (g u))) (R u u (a))) 0 1 1)
;;
;; ::: The above function call yields the following output :::
;;
;; ((2 (MOVE :BINARY-RESOLUTION (0 0) (1 0))
;;     ((Q (G (B)) V)
;;      (NOT (R (G (B)) Z (A)))
;;      (NOT (R (G (B)) (F (G (B)) (G (B))) (A)))
;;      (NOT (Q V (G (A))))
;;      (R (A) (A) (A))))
;;  (3 (MOVE :BINARY-RESOLUTION (0 1) (1 1))
;;     ((P X (F (A) (G U)))
;;      (NOT (R X Z (A)))
;;      (NOT (R X (F X X) (A)))
;;      (NOT (P (G (B)) (F U (G (B)))))
;;      (R U U (A))))
;;  (4 (MOVE :BINARY-RESOLUTION (0 2) (1 2))
;;     ((P U (F (A) Y))
;;      (Q (G (B)) Y)
;;      (NOT (R U (F U U) (A)))
;;      (NOT (P (G (B)) (F U V)))
;;      (NOT (Q V (G U))))))
;;
;; ... This is correct, excellent!
;;
;; !>(find-all-binary-factors '((P x y) (P (a) z) (P x (b)) (Q (a) y x) (Q z (b) z)) 0 0)
;;
;; (((1 (MOVE :BINARY-FACTORING (0 :PRODUCT-LITERALS (0 1)))
;;      ((P (A) Z)
;;       (P (A) Z)
;;       (P (A) (B))
;;       (Q (A) Z (A))
;;       (Q Z (B) Z)))
;;   (2 (MOVE :BINARY-FACTORING (0 :PRODUCT-LITERALS (0 2)))
;;      ((P X (B))
;;       (P (A) Z)
;;       (P X (B))
;;       (Q (A) (B) X)
;;       (Q Z (B) Z))))
;;   (3 (MOVE :BINARY-FACTORING (0 :PRODUCT-LITERALS (1 2)))
;;      ((P (A) Y)
;;       (P (A) (B))
;;       (P (A) (B))
;;       (Q (A) Y (A))
;;       (Q (B) (B) (B))))
;;   (4 (MOVE :BINARY-FACTORING (0 :PRODUCT-LITERALS (3 4)))
;;      ((P (A) (B))
;;       (P (A) (A))
;;       (P (A) (B))
;;       (Q (A) (B) (A))
;;       (Q (A) (B) (A)))))
;;
;; ... This is correct as well, excellent!
;; G. Passmore :: 12/22/05


