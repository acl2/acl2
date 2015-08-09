;;-------------------------------------------------------------------------
;;-------------------------------------------------------------------------
;;
;;
;; Functional Specification and Validation of the Octagon Network on
;;              Chip using the ACL2 Theorem Prover
;;
;;
;;                          Proof Script
;;
;;
;;                         Julien Schmaltz
;;                     Joseph Fourier University
;;               46, av. Felix Viallet 38031 Grenoble Cedex
;;                             FRANCE
;;                      Julien.Schmaltz@imag.fr
;;
;;-------------------------------------------------------------------------
;;-------------------------------------------------------------------------


;; File: routing_local_lemmas.lisp
;; Contains lemmas needed to prove the main theorem on Route.
;; This book will be included locally in the next one, so that we do
;; not export the lemmas herein in the main proof about Octagon.

(in-package "ACL2")

;; To reason about function "route", I define, for each possible case of
;; (mod (+ dest (- from)) n) a function that computes a list of nodes and
;; that does not use function mod. Then, the properties are generally
;; trivial on these small functions and the properties on route are
;; proved by a simple case split.
;; We divide the Octagon in quarters and bound, according to the value
;; of (- dest from).

;; this strategy is embedded inside a book.
(include-book "getting_rid_of_mod")

;;------------------------

;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------
;;
;;                 CORRECTNESS OF FUNCTION ROUTE
;;
;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------

;; now we have tools and lemmas to prove the correcntess of function route

(defthm true-listp_route
  (true-listp (route from to n))
  :rule-classes :type-prescription)

;------------------------------------------------------------------------
;            Lemma 1: The Last of Route is the Destination
;------------------------------------------------------------------------

(defthm lemma1_last_route_is_to
  (implies (and  (integerp from)
                 (integerp to)
                 (< 0 n)
                 (<= 0 to)
                 (<= 0 from)
                 (< to (* 4 n))
                 (< from (* 4 n))
                 (integerp n))
           (equal (car (last (route from to n)))
                  to))
  :hints (("GOAL"
           :in-theory (e/d (route)
                           (route_=_QUARTER_4_LIST_LEMMA_1
                            route_=_QUARTER_1
                            PREFER-POSITIVE-ADDENDS-<
                            PREFER-POSITIVE-ADDENDS-EQUAL)))))

;;Warnings:  None
;;Time:  74.86 seconds (prove: 74.74, print: 0.09, other: 0.03)
;; LEMMA1_LAST_ROUTE_IS_TO


;;------------------------------------------------------------------------
;;            Lemma 2: The First of Route is the Source
;;------------------------------------------------------------------------


(defthm lemma2_first_of_route_is_from
  (implies (and  (integerp from)
                 (integerp to)
                 (< 0 n)
                 (<= 0 to)
                 (<= 0 from)
                 (< to (* 4 n))
                 (< from (* 4 n))
                 (integerp n))
           (equal (car (route from to n))
                  from))
  :hints (("GOAL"
           :in-theory (e/d (route)
                           (route_=_QUARTER_4_LIST_LEMMA_1
                            route_=_QUARTER_1
                            PREFER-POSITIVE-ADDENDS-<
                            PREFER-POSITIVE-ADDENDS-EQUAL)))))

;;Warnings:  None
;;Time:  13.10 seconds (prove: 13.03, print: 0.04, other: 0.03)
;; LEMMA2_FIRST_OF_ROUTE_IS_FROM

;;------------------------------------------------------------------------
;;    Lemma 3: Every Node of Route is Less Than The Number of Nodes
;;------------------------------------------------------------------------
(defthm lemma3_all_inf_n_route
  (implies (and (integerp from)
                (integerp to)
                (< 0 n)
                (<= 0 to)
                (<= 0 from)
                (< to (* 4 n))
                (< from (* 4 n))
                (integerp n))
           (all_inf_np (route from to n)
                       (* 4 n)))
  :hints (("GOAL"
           :in-theory (e/d (route)
                           (route_=_QUARTER_4_LIST_LEMMA_1
                            route_=_QUARTER_1
                            PREFER-POSITIVE-ADDENDS-<
                            PREFER-POSITIVE-ADDENDS-EQUAL)))))

;;Warnings:  None
;;Time:  34.55 seconds (prove: 34.47, print: 0.05, other: 0.03)
;; LEMMA3_ALL_INF_N_ROUTE


;;------------------------------------------------------------------------
;;         Lemma 4: Route Produces a non-empty Path
;;------------------------------------------------------------------------

(defthm lemma4_consp_route
  (implies (and (integerp from)
                (integerp to)
                (< 0 n)
                (<= 0 to)
                (<= 0 from)
                (< to (* 4 n))
                (< from (* 4 n))
                (integerp n))
           (consp (route from to n)))
  :hints (computed_hint_route))

;;Warnings:  None
;;Time:  3.18 seconds (prove: 3.14, print: 0.04, other: 0.00)
;; LEMMA4_CONSP_ROUTE

;;------------------------------------------------------------------------
;;             Lemma 5: Every Node is an Integer
;;------------------------------------------------------------------------


;; we  prove this on each quarter

(defthm all_intp_quarter_1_list
  (implies (and (integerp from)
                (integerp to))
           (all_intp (quarter_1_list from to))))

(defthm all_intp_quarter_minus_4_list
  (implies (and (integerp from) (integerp to)
                (integerp n))
           (all_intp (quarter_minus_4_list from to n))))

(defthm all_intp_quarter-3-list
  (implies (and (integerp from) (integerp to)
                (integerp n) (< 0 n))
           (all_intp (quarter_3_list from to n))))

(defthm all_intp_quarter-minus-2-list
  (implies (and (integerp from) (integerp to) (integerp n))
           (all_intp (quarter_minus_2_list from to n))))

(defthm all_intp_quarter-minus-1-list
  (implies (and (integerp from) (integerp to))
           (all_intp (quarter_minus_1_list from to))))

(defthm all_intp_quarter-minus-3-list
  (implies (and (integerp from) (integerp to) (integerp n))
           (all_intp (quarter_3_list from to n))))

(defthm all_intp_quarter-4-list
  (implies (and (integerp from) (integerp to) (integerp n))
           (all_intp (quarter_4_list from to n))))

(defthm all_intp_quarter-2-list
  (implies (and (integerp from) (integerp to) (integerp n)
                (< 0 n))
           (all_intp (quarter_2_list from to n))))

(defthm lemma5_all_intp_n-go-to-node-top
  (implies (and (integerp from)
                (<= 0 from)
                (< from (* 4 n))
                (integerp to)
                (<= 0 to)
                (< to (* 4 n))
                (integerp n)
                (< 0 n))
           (all_intp (route from to n)))
  :hints (computed_hint_route))

;;Warnings:  None
;;Time:  3.29 seconds (prove: 3.25, print: 0.04, other: 0.00)
;; LEMMA5_ALL_INTP_N-GO-TO-NODE-TOP


;;------------------------------------------------------------------------
;;             Lemma 6: Every Node is an Positive Integer
;;------------------------------------------------------------------------


;; for every lemma we will need to disable prefer-blah-blah-blah
;; so we do a computed hint, and we want it inherited to children!
;; So, we use the :computed-hint-replacement feature.
(defun computed_hint_prefer_positive_addends (id clause world)
  (declare (ignore clause world))
  (if (equal id '((0) NIL . 0))
      '(:computed-hint-replacement t
        :in-theory (disable prefer-positive-addends-equal
                            reduce-integerp-+
                            prefer-positive-addends-<))
    nil))

;; again we prove a lemma for each part of the Octagon
;; every lemma is proven in less than 1 second

(defthm all_pos_intp_quarter_1_list
  (implies (and (<= 0 from) (<= 0 to))
           (all_pos_intp (quarter_1_list from to)))
  :hints (computed_hint_prefer_positive_addends))

(defthm all_pos_intp_quarter_minus_4_list
  (implies (and (<= 0 from) (<= 0 to) (< 0 n))
           (all_pos_intp (quarter_minus_4_list from to n)))
  :hints (computed_hint_prefer_positive_addends))

(defthm all_pos_intp_quarter_3_list
  (implies (and (<= 0 from) (<= 0 to)
                (< 0 n))
           (all_pos_intp (quarter_3_list from to n)))
  :hints (computed_hint_prefer_positive_addends))

(defthm all_pos_intp_quarter_minus_2_list
  (implies (and (<= 0 from) (<= 0 to) (< 0 n))
           (all_pos_intp (quarter_minus_2_list from to n)))
  :hints (computed_hint_prefer_positive_addends))

(defthm all_pos_intp_quarter_minus_1_list
  (implies (and (<= 0 from) (<= 0 to))
           (all_pos_intp (quarter_minus_1_list from to)))
  :hints (computed_hint_prefer_positive_addends))

(defthm all_pos_intp_quarter_minus_3_list
  (implies (and (<= 0 from) (<= 0 to) (< 0 n)
                (integerp from) (integerp to)
                (integerp n) (< from (* 4 n)) (< to (* 4 n))
                (and (< (* -3 n) (- to from))
                     (< (- to from) (* -2 n))))
           (all_pos_intp (quarter_minus_3_list from to n)))
  :hints (computed_hint_prefer_positive_addends))

(defthm all_pos_intp_quarter_4_list
  (implies (and (<= 0 from) (<= 0 to)
                (integerp n) (< 0 n))
           (all_pos_intp (quarter_4_list from to n)))
  :hints (computed_hint_prefer_positive_addends))

(defthm all_pos_intp_quarter_2_list
  (implies (and (<= 0 from) (<= 0 to) (< 0 n) (integerp from) (integerp to)
                (integerp n))
           (all_pos_intp (quarter_2_list from to n)))
  :hints (computed_hint_prefer_positive_addends))

(defthm lemma6_all_pos_intp_route
  (implies (and (integerp from)
                (<= 0 from)
                (< from (* 4 n))
                (integerp to)
                (<= 0 to)
                (< to (* 4 n))
                (integerp n)
                (< 0 n))
           (all_pos_intp (route from to n)))
  :hints (computed_hint_route))

;;Warnings:  None
;;Time:  3.36 seconds (prove: 3.33, print: 0.02, other: 0.01)
;; LEMMA6_ALL_POS_INTP_ROUTE






;; we import definitions and theorems to work on lists

(include-book "../../../../data-structures/list-defuns")









(include-book "../../../../data-structures/list-defthms")


;;------------------------------------------------------------------------
;;             Lemma 8: Route contains no Duplicate
;;------------------------------------------------------------------------

;; a useful computed hint
;;----------------------

(defun computed_hint_member_and_no_duplicatesp_equal (id clause world)
  (declare (ignore clause world))
  (if (equal id '((0) NIL . 0))
      '(:computed-hint-replacement t ;; to have the hint inherited
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;         :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL
;                             MEMBER->MEMBER-EQUAL)
        )
    nil))

;;------------------------

;; again, we prove the property for every quartert
;; each lemma is proven in less than 1 second

(defthm lemma_member_quarter_1
  (implies (and (integerp a)
                (<= 0 a)
                (< a from)
                (integerp from)
                (<= 0 from)
                (<= 0 to))
           (not (member a (quarter_1_list from to))))
  :hints (computed_hint_prefer_positive_addends))

(defthm no_duplicatesp_quarter_1_list
  (implies (and (integerp from)
                (integerp to)
                (<= 0 from)
                (<= 0 (- to from))
                (<= 0 to))
           (no-duplicatesp (quarter_1_list from to)))
  :hints (computed_hint_member_and_no_duplicatesp_equal))


(defthm lemma_member_quarter_1_0
  (implies (and (integerp to)
                (integerp from)
                (<= from to)
                (< to a)
                (integerp a))
           (not (member a (quarter_1_list from to)))))

(defthm lemma_member_quarter_minus_4
  (implies (and (integerp from) (integerp to)
                (<= 0 from) (<= 0 to)
                (integerp n) (< 0 n)
                (integerp a) (< a from) (< to a))
           (not (member a (quarter_minus_4_list from to n))))
  :hints (computed_hint_member_and_no_duplicatesp_equal))

(defthm no_duplicatesp_quarter_minus_4
  (implies (and (integerp from)
                (integerp to)
                (<= 0 from)
                (<= 0 to)
                (< to (* 4 n))
                (< from (* 4 n))
                (integerp n)
                (and (<= (- to from) (* -3 n))
                     (< (- (* 4 n)) (- to from))))
           (no-duplicatesp (quarter_minus_4_list from to n)))
  :hints (computed_hint_member_and_no_duplicatesp_equal))

(defthm no_duplicatesp_quarter_3_list
  (implies (and (integerp from) (integerp to) (integerp n)
                (<= 0 from) (<= 0 to) (< 0 n)
                (< (* 2 n)  (- to from)))
           (no-duplicatesp (quarter_3_list from to n)))
  :hints (computed_hint_member_and_no_duplicatesp_equal))

(defthm no_dupli_quarter_minus_2_list
  (implies (and (integerp from)
                (integerp to)
                (<= 0 from)
                (<= 0 to)
                (< to (* 4 n))
                (< from (* 4 n))
                (integerp n)
                (< 0 n)
                (and (< (- to from) (- n))
                     (< (* -2 n) (- to from))))
           (no-duplicatesp (quarter_minus_2_list from to n)))
  :hints (computed_hint_member_and_no_duplicatesp_equal))

(defthm lemma_member_quarter_minus_1_list
  (implies (and (integerp from) (integerp to)
                (<= 0 from) (<= 0 to)
                (integerp a) (<= 0 a)
                (< from a))
           (not (member a (quarter_minus_1_list from to)))))

(defthm no_dupli_quarter_minus_1
  (implies (and (integerp from)
                (integerp to)
                (<= 0 from)
                (<= 0 to))
           (no-duplicatesp (quarter_minus_1_list from to)))
  :hints (computed_hint_member_and_no_duplicatesp_equal))

(defthm no_dupli_quarter_minus_3_list
  (implies (and (integerp from)
                (<= 0 from)
                (< from (* 4 n))
                (integerp to)
                (<= 0 to)
                (< to (* 4 n))
                (integerp n)
                (< 0 n)
                (and (< (* -3 n) (- to from))
                     (< (- to from) (* -2 n))))
           (no-duplicatesp (quarter_minus_3_list from to n)))
  :hints (computed_hint_member_and_no_duplicatesp_equal))

(defthm lemma_member_quarter_4
  (IMPLIES (AND (INTEGERP TO)
                (<= 0 TO)
                (<= to from)
                (< a TO))
           (NOT (MEMBER a (QUARTER_MINUS_1_LIST from TO))))
  :hints (("GOAL"
           :in-theory (disable REDUCE-INTEGERP-+))))

(defthm lemma_member_quarter_4_0
  (implies (and (integerp to) (integerp from) (integerp a)
                (< from (* 4 n))
                (< a (+ -1 (* 4 n))) (< to (* 4 n)) (<= 0 from) (<= 0 a)
                (<= (+ a n) to)
                (< from to) (<= 0 to) (integerp n)
                (< from a) (< 0 n))
           (not (member a
                        (quarter_4_list from to n))))
  :hints (computed_hint_prefer_positive_addends))

(defthm no_dupli_quarter_4
  (implies (and  (integerp from)
                 (integerp to)
                 (<= 0 to)
                 (integerp n)
                 (< 0 n)
                 (< from (* 4 n))
                 (< to (* 4 n))
                 (<= 0 from)
                 (and (<= (* 3 n) (- to from))
                      (< (- to from) (* 4 n))))
           (no-duplicatesp (quarter_4_list from to n)))
  :hints (computed_hint_member_and_no_duplicatesp_equal))

(defthm no_dupli_quarter_2_list
  (implies (and (integerp from)
                (<= 0 from)
                (< from (* 4 n))
                (integerp to)
                (<= 0 to)
                (< to (* 4 n))
                (integerp n)
                (< 0 n)
                (and (< n (- to from))
                     (< (- to from) (* 2 n))))
           (no-duplicatesp (quarter_2_list from to n)))
  :hints (computed_hint_member_and_no_duplicatesp_equal))

;; we merge the previous computed hints into one
;;----------------------------------------------

(defun merged_computed_hints_1 (id clause world)
  (declare (ignore clause world))
  (if (equal id '((0) NIL . 0))
      '(:computed-hint-replacement t ;; to have the theory inherited
        :cases ((and (<= (- to from) n)
                     (<= 0 (- to from)))
                (and (<= (- to from) (* -3 n))
                     (< (- (* 4 n)) (- to from)))
                (and (< (- to from) (* 3 n))
                     (< (* 2 n) (- to from)))
                (and (< (- to from) (- n))
                     (< (* -2 n) (- to from)))
                (and (< (- to from) 0)
                     (<= (- n) (- to from)))
                (and (< (* -3 n) (- to from))
                     (< (- to from) (* -2 n)))
                (and (<= (* 3 n) (- to from))
                     (< (- to from) (* 4 n)))
                (and (< n (- to from))
                     (< (- to from) (* 2 n)))
                (equal (+ to (- from)) (* 2 n))
                (equal (+ to (- from)) (* -2 n)))
        :in-theory (disable
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (commented out two rules just below).]
                    ;; NO-DUPLICATESP->NO-DUPLICATESP-EQUAL
                    ;; MEMBER->MEMBER-EQUAL
                    prefer-positive-addends-equal
                    prefer-positive-addends-<))
    nil))

;;--------------------------------------------------


;;--------------- LEMMA 8 ------------------------

(defthm lemma8_no_duplicatesp_route
  (implies (and (integerp from)
                (<= 0 from)
                (< from (* 4 n))
                (integerp to)
                (<= 0 to)
                (< to (* 4 n))
                (integerp n)
                (< 0 n))
           (no-duplicatesp (route from to n)))
  :hints (merged_computed_hints_1))

;;Warnings:  Subsume (?? bad warning from ACL2)
;;Time:  0.99 seconds (prove: 0.95, print: 0.04, other: 0.00)
;; LEMMA8_NO_DUPLICATESP_ROUTE



;;------------------------------------------------------------------------
;;       Lemma 9: Each move is one of the available ones
;;------------------------------------------------------------------------


;;---------------------------------------------------

;; again, we prove this for every quarter
;; and each lemma is proven in less than 1 second

(defthm car_quarter_1_list
  (equal (car (quarter_1_list from to))
         from)
    :hints (computed_hint_prefer_positive_addends))

(defthm AvailableMovep_quarter_1_list
  (AvailableMovep (quarter_1_list from to) n)
  :hints (computed_hint_prefer_positive_addends))

(defthm car_quarter_minus_4_list
  (equal (car (quarter_minus_4_list from to n))
         from)
  :hints (computed_hint_prefer_positive_addends))

(defthm AvailableMovep_quarter_minus_4
  (implies (and (integerp from) (Integerp n)
                (<= 0 from) (< from (* 4 n)))
           (AvailableMovep (quarter_minus_4_list from to n) n))
  :hints (computed_hint_prefer_positive_addends))

(defthm car_quarter_3_list
  (equal (car (quarter_3_list from to n))
         from)
  :hints (computed_hint_prefer_positive_addends))

(defthm AvailableMovep_quarter_3_list
  (AvailableMovep (quarter_3_list from to n) n)
  :hints (computed_hint_prefer_positive_addends))

(defthm car_quarter_minus_2_list
  (equal (car (quarter_minus_2_list from to n))
         from)
  :hints (computed_hint_prefer_positive_addends))

(defthm AvailableMovep_quarter_minus_2_list
  (implies (and (integerp from) (<= 0 from) (< from (* 4 n))
                (integerp n))
           (AvailableMovep (quarter_minus_2_list from to n) n))
  :hints (computed_hint_prefer_positive_addends))

(defthm car_quarter_minus_1_list
  (equal (car (quarter_minus_1_list from to))
         from)
  :hints (computed_hint_prefer_positive_addends))

(defthm AvailableMovep_quarter_minus_1_list
  (implies (and (integerp from) (<= 0 from)
                (integerp to) (<= 0 to))
           (AvailableMovep (quarter_minus_1_list from to) n))
  :hints (computed_hint_prefer_positive_addends))

(defthm car_quarter_minus_3_list
  (equal (car (quarter_minus_3_list from to n))
         from)
  :hints (computed_hint_prefer_positive_addends))

(defthm AvailableMovep_quarter_minus_3_list
  (implies (and (integerp from) (<= 0 from)
                (integerp to) (<= 0 to)
                (and (< (* -3 n) (- to from))
                     (< (- to from) (* -2 n)))
                (integerp n) (< from (* 4 n)))
           (AvailableMovep (quarter_minus_3_list from to n) n))
    :hints (("GOAL"
           :in-theory (disable prefer-positive-addends-equal
                               prefer-positive-addends-<
                               simplify-sums-equal))))

(defthm car_quarter_4_list
  (equal (car (quarter_4_list from to n))
         from)
  :hints (computed_hint_prefer_positive_addends))

(defthm AvailableMovep_quarter_4_list
  (implies (and (integerp from) (<= 0 from)
                (integerp to) (<= 0 to)
                (and (<= (* 3 n) (- to from))
                      (< (- to from) (* 4 n)))
                (integerp n) (< from (* 4 n)))
           (AvailableMovep (quarter_4_list from to n) n))
  :hints (computed_hint_prefer_positive_addends))

(defthm car_quarter_2_list
  (equal (car (quarter_2_list from to n))
         from)
  :hints (computed_hint_prefer_positive_addends))

(defthm AvailableMovep_quarter_2_list
  (implies (and (integerp from) (<= 0 from)
                (integerp to) (<= 0 to)
                (integerp n) (< from (* 4 n))
                (and (< n (- to from))
                     (< (- to from) (* 2 n))))
           (AvailableMovep (quarter_2_list from to n) n))
  :hints (("GOAL"
           :in-theory (disable SIMPLIFY-SUMS-EQUAL
                               prefer-positive-addends-equal
                               prefer-positive-addends-<))))




;;;;---------------------- LEMMA 9 ----------------------

(defthm Lemma9_AvailableMovep_route
  (implies (and (integerp from)
                (<= 0 from)
                (< from (* 4 n))
                (integerp to)
                (<= 0 to)
                (< to (* 4 n))
                (integerp n)
                (< 0 n))
           (AvailableMovep (route from to n) n))
  :hints (merged_computed_hints_1
          ("Subgoal 3"
           :in-theory (disable SIMPLIFY-SUMS-EQUAL
                               prefer-positive-addends-equal
                               prefer-positive-addends-<))))

;;Warnings:  None
;;Time:  1.73 seconds (prove: 1.66, print: 0.04, other: 0.03)
;; LEMMA9_AVAILABLEMOVEP_ROUTE

;;------------------------------------------------------------------------
;;       Lemma 10: The routing terminates in N steps (at most)
;;------------------------------------------------------------------------

;; we prove it for every quarter
;; and we first prove what is the exact length of the route for each quarter
;; each lemma is proven in less than 1 second

(defthm len_quarter_1_list
  (implies (and (integerp from)
                (integerp to)
                (<= 0 from)
                (<= 0 (- to from))
                (<= 0 to))
           (equal (len (quarter_1_list from to))
                  (+ 1 (+ to (- from))))))

(defthm len_quarter_minus_4_list
  (implies (and (integerp from)
                (integerp to)
                (<= 0 from)
                (<= 0 to)
                (< to (* 4 n))
                (< from (* 4 n))
                (integerp n)
                (and (<= (- to from) (* -3 n))
                     (< (- (* 4 n)) (- to from))))
           (equal (len (quarter_minus_4_list from to n))
                  (+ 1 (* 4 n) to (- from)))))

(defthm len_quarter_minus_1_list
  (implies (and (integerp from)
                (integerp to))
           (equal (len (quarter_minus_1_list from to))
                  (if (< to from)
                    (+ 1 from (- to))
                    1)))
  :hints (computed_hint_prefer_positive_addends))

(defthm len_quarter_minus_3_list
  (implies (and (integerp from)
                (<= 0 from)
                (< from (* 4 n))
                (integerp to)
                (<= 0 to)
                (< to (* 4 n))
                (integerp n)
                (< 0 n)
                (and (< (* -3 n) (- to from))
                     (< (- to from) (* -2 n))))
           (equal (len (quarter_minus_3_list from to n))
                  (+ 1 1 (* -2 n) (- to) from))))

(defthm len_quarter_4_list
  (implies  (and (integerp from)
                 (integerp to)
                 (<= 0 to)
                 (integerp n)
                 (< 0 n)
                 (< from (* 4 n))
                 (< to (* 4 n))
                 (<= 0 from)
                 (and (<= (* 3 n) (- to from))
                      (< (- to from) (* 4 n))))
            (equal (len (quarter_4_list from to n))
                   (+ 1 (* 4 n) from (- to)))))

(defthm len_quarter_2_list
  (implies (and (integerp from)
                (<= 0 from)
                (< from (* 4 n))
                (integerp to)
                (<= 0 to)
                (< to (* 4 n))
                (integerp n)
                (< 0 n)
                (and (< n (- to from))
                     (< (- to from) (* 2 n))))
           (equal (len (quarter_2_list from to n))
                  (+ 1 1 (* 2 n) from (- to)))))

;; we prove the exact value of the length of the route, for every possible
;; quarter

(defthm len_route_lemma1
  (implies (and (integerp from)
                (integerp to)
                (<= 0 from)
                (<= 0 to)
                (< to (* 4 n))
                (< from (* 4 n))
                (integerp n)
                (< 0 n))
           (equal (len (route from to n))
                  (cond ((and (<= (- to from) N)
                              (<= 0 (- to from))) ;; Q 1
                         (+ 1 to (- from)))
                        ((AND (<= (- TO FROM) (* -3 N))
                              (< (- (* 4 N)) (- TO FROM))) ;; Q -4
                         (+ 1 (* 4 n) to (- from)))
                        ((AND (< (- TO FROM) (* 3 N))
                              (< (* 2 N) (- TO FROM))) ;; Q 3
                         (+ 1 1 (* -2 n) to (- from)))
                        ((AND (< (- TO FROM) (- N))
                              (< (* -2 N) (- TO FROM))) ;; Q -2
                         (+ 1 1 (* 2 n) to (- from)))
                        ((AND (< (- TO FROM) 0)
                              (<= (- N) (- TO FROM))) ;;Q -1
                         (+ 1 from (- to)))
                        ((AND (< (* -3 N) (- TO FROM))
                              (< (- TO FROM) (* -2 N))) ;; Q -3
                         (+ 1 1 (* -2 n) (- to) from))
                        ((AND (<= (* 3 N) (- TO FROM))
                              (< (- TO FROM) (* 4 N))) ;; Q 4
                         (+ 1 (* 4 n) from (- to)))
                        ((AND (< N (- TO FROM))
                              (< (- TO FROM) (* 2 N))) ;; Q 2
                         (+ 1 1 (* 2 n) from (- to)))
                        ((EQUAL (+ TO (- FROM)) (* 2 N))
                         2)
                        ((EQUAL (+ TO (- FROM)) (* -2 N))
                         2)
                        (t 0))))
  :otf-flg t
  :hints (merged_computed_hints_1
          ("Subgoal 5"
           :in-theory (disable quarter_minus_3_list))
          ("Subgoal 3"
           :in-theory (disable quarter_2_list))))

;;Warnings:  None
;;Time:  2.61 seconds (prove: 2.27, print: 0.19, other: 0.15)
;; LEN_ROUTE_LEMMA1


;;-----------------------------------------------------------
;; Now we can consider we have enough properties on route
;; So, we disable all the rules that map route to lists

(in-theory (disable ROUTE_=_QUARTER_1
                    ROUTE_=_QUARTER_2_LIST
                    ROUTE_=_QUARTER_3
                    ROUTE_=_QUARTER_4_LIST
                    ROUTE_=_QUARTER_MINUS_1_LIST
                    ROUTE_=_QUARTER_MINUS_2_LIST
                    ROUTE_=_QUARTER_MINUS_3_LIST
                    ROUTE_=_QUARTER_MINUS_4_LIST
                    ROUTE_=_BOUNDS))
;;------------------------------------------------------------

;; But the last theorem we want is that the length is less than 1+N


(defthm bound_route_lemma
  (implies (and (integerp from)
                (<= 0 from)
                (< from (* 4 n))
                (integerp to)
                (<= 0 to)
                (< to (* 4 n))
                (integerp n)
                (< 0 n))
           (< (len (route from to n))
              (+ 1 1 n)))
  :hints (merged_computed_hints_1)
  :rule-classes :linear)

;;Warnings:  None
;;Time:  1.28 seconds (prove: 1.11, print: 0.17, other: 0.00)
;; BOUND_ROUTE_LEMMA

;; This rule is fine to export but does not state the theorem we want.
;; The final directly follows but is not stored as a rule

;; Moreover we need to disable the rule LEN_ROUTE_LEMMA1, because
;; it will remove (len ...) and the rule above will never be applied.

(in-theory (disable LEN_ROUTE_LEMMA1))

(defthm bound_route-main
  (implies (and (integerp from)
                (<= 0 from)
                (< from (* 4 n))
                (integerp to)
                (<= 0 to)
                (< to (* 4 n))
                (integerp n)
                (< 0 n))
           (<= (len (route from to n))
               (+ 1 N)))
  :rule-classes nil)

;;Warnings:  None
;;Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
;; BOUND_ROUTE-MAIN

