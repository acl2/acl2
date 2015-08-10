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

;; August 15th
;; JS: I update this file to match the last version of GeNoC
;; I remove the proof that there is no duplicate and everything
;; in relation with the predicate availablemovep, which is no
;; longer present in GeNoC.
(in-package "ACL2")
;; we import definitions and theorems to work on lists
(include-book "data-structures/list-defuns" :dir :system)
(include-book "data-structures/list-defthms" :dir :system)

;; To reason about function "route", I define, for each possible case of
;; (mod (+ dest (- from)) n) a function that computes a list of nodes and
;; that does not use function mod. Then, the properties are generally
;; trivial on these small functions and the properties on route are
;; proved by a simple case split.
;; We divide the Octagon in quarters and bound, according to the value
;; of (- dest from).
;; this strategy is embedded inside a book.
(include-book "getting_rid_of_mod")

;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------
;;
;;                 CORRECTNESS OF FUNCTION ROUTE
;;
;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------

;; we first prove some useful lemmas about the different moves
(defthm natp_n_across
  (implies (and (natp x) (integerp n) (< 0 n))
           (natp (n_across x n))))

(defthm n_across_<_n
  (implies (and (natp x) (integerp n) (< 0 n))
           (< (n_across x n) (* 4 n))))

(defthm natp_counterclockwise
  (implies (and (natp x) (integerp n) (< 0 n))
           (natp (n_counter_clockwise x n))))

(defthm n_counter_clockwise_<_n
  (implies (and (natp x) (integerp n) (< 0 n))
           (< (n_counter_clockwise x n) (* 4 n))))

;;------------------------------------------------------------------------
;;  1. true-listp, consp, len
;;------------------------------------------------------------------------

(defthm true-listp_route
  ;; route produces a true-listp
  (true-listp (route from to n))
  :rule-classes :type-prescription)

(defthm consp_route
  ;; route is a consp
  (implies (and (natp from) (natp to) (integerp n) (< 0 n)
                (< to (* 4 n)) (< from (* 4 n)))
           (consp (route from to n)))
  :hints (("GOAL"
           :in-theory (enable route)
           :induct (route from to n))))

(defthm len_route_>=_2
  ;; if from /= to, then route produces a path with at least
  ;; two nodes
  (implies (and (natp from) (natp to)
                (integerp n) (< 0 n)
                (< to (* 4 n)) (< from (* 4 n))
                (not (equal from to)))
           (<= 2 (len (route from to n))))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :in-theory (e/d (route) (n_across n_counter_clockwise))
           :do-not '(eliminate-destructors generalize fertilize)
           :induct (route from to n))))

;------------------------------------------------------------------------
; 2. Last of route(from,to) is to
;------------------------------------------------------------------------
(defthm lemma1_last_route_is_to
  ;; any route ends with the correct destination
  (implies (and (natp from) (< from (* 4 n))
                (natp to)   (< to (* 4 n))
                (< 0 n) (integerp n))
           (equal (car (last (route from to n)))
                  to))
  :hints (("GOAL"
           :in-theory (e/d (route)
                           (route_=_QUARTER_4_LIST_LEMMA_1
                            route_=_QUARTER_1
                            PREFER-POSITIVE-ADDENDS-<
                            PREFER-POSITIVE-ADDENDS-EQUAL)))))

;;------------------------------------------------------------------------
;; 3. First of route(from,to) is from
;;------------------------------------------------------------------------
(defthm lemma2_first_of_route_is_from
  (implies (and (natp from) (< from (* 4 n))
                (natp to)   (< to (* 4 n))
                (< 0 n)     (integerp n))
           (equal (car (route from to n))
                  from))
  :hints (("GOAL"
           :in-theory (e/d (route)
                           (route_=_QUARTER_4_LIST_LEMMA_1
                            route_=_QUARTER_1
                            PREFER-POSITIVE-ADDENDS-<
                            PREFER-POSITIVE-ADDENDS-EQUAL)))))

;;------------------------------------------------------------------------
;; 4. Every node is less that 4*n
;;------------------------------------------------------------------------
(defun all_inf_np (l n)
  ;; recognizes a list in which every element is less than n
  (if (endp l)
      t
    (and (< (car l) n)
         (all_inf_np (cdr l) n))))

(defthm lemma3_all_inf_n_route
  ;; we prove that each node is less than the number of nodes
  (implies (and (natp from) (< from (* 4 n))
                (natp to)   (< to (* 4 n))
                (< 0 n)     (integerp n))
           (all_inf_np (route from to n)
                       (* 4 n)))
  :hints (("GOAL"
           :in-theory (e/d (route)
                           (route_=_QUARTER_4_LIST_LEMMA_1
                            route_=_QUARTER_1
                            PREFER-POSITIVE-ADDENDS-<
                            PREFER-POSITIVE-ADDENDS-EQUAL)))))

;;------------------------------------------------------------------------
;; 5. every node is recognized by OctagonNodeSetp
;;------------------------------------------------------------------------

(include-book "../../nodeset/octagon-nodeset")

;; to prove this we use the strategy that considers
;; the problem quarter by quarter.
;; We first prove that each quarter is OK.

(defthm OctagonNodeSetp_quarter_1_list
  (implies (and (natp from) (natp to))
           (OctagonNodeSetp (quarter_1_list from to))))

(defthm OctagonNodeSetp_quarter_minus_4_list
  (implies (and (natp from) (natp to)
                (integerp n))
           (OctagonNodeSetp (quarter_minus_4_list from to n))))

(defthm OctagonNodeSetp_quarter-3-list
  (implies (and (natp from) (natp to)
                (integerp n) (< 0 n))
           (OctagonNodeSetp (quarter_3_list from to n))))

(defthm OctagonNodeSetp_quarter-minus-2-list
  (implies (and (natp from) (natp to) (integerp n))
           (OctagonNodeSetp (quarter_minus_2_list from to n))))

(defthm OctagonNodeSetp_quarter-minus-1-list
  (implies (and (natp from) (natp to))
           (OctagonNodeSetp (quarter_minus_1_list from to))))

(defthm OctagonNodeSetp_quarter-minus-3-list
  (implies (and (natp from) (natp to) (integerp n) (< 0 n))
           (OctagonNodeSetp (quarter_3_list from to n))))

(defthm OctagonNodeSetp_quarter-4-list
  (implies (and (natp from) (natp to) (integerp n) (< 0 n))
           (OctagonNodeSetp (quarter_4_list from to n))))

(defthm OctagonNodeSetp_quarter-2-list
  (implies (and (natp from) (natp to) (integerp n) (< 0 n))
           (OctagonNodeSetp (quarter_2_list from to n))))

(defthm lemma5_OctagonNodeSetp_n-go-to-node-top
  (implies (and (natp from) (< from (* 4 n))
                (natp to)   (< to (* 4 n))
                (integerp n) (< 0 n))
           (OctagonNodeSetp (route from to n)))
  :hints (computed_hint_route))

;;------------------------------------------------------------------------
;; 6. Routing terminates in N steps
;;------------------------------------------------------------------------

;; we prove it for every quarter
;; and we first prove what is the exact length of
;; the route for each quarter
;; each lemma is proven in less than 1 second

(defthm len_quarter_1_list
  (implies (and (natp from)
                (natp to)
                (<= 0 (- to from)))
           (equal (len (quarter_1_list from to))
                  (+ 1 (+ to (- from))))))

(defthm len_quarter_minus_4_list
  (implies (and (natp from) (< from (* 4 n))
                (natp to)   (< to (* 4 n))
                (integerp n)
                (and (<= (- to from) (* -3 n))
                     (< (- (* 4 n)) (- to from))))
           (equal (len (quarter_minus_4_list from to n))
                  (+ 1 (* 4 n) to (- from)))))

;; for some lemma we will need to disable prefer-blah-blah-blah
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

(defthm len_quarter_minus_1_list
  (implies (and (integerp from)
                (integerp to))
           (equal (len (quarter_minus_1_list from to))
                  (if (< to from)
                    (+ 1 from (- to))
                    1)))
  :hints (computed_hint_prefer_positive_addends))

(defthm len_quarter_minus_3_list
  (implies (and (natp from) (< from (* 4 n))
                (natp to)   (< to (* 4 n))
                (integerp n)
                (< 0 n)
                (and (< (* -3 n) (- to from))
                     (< (- to from) (* -2 n))))
           (equal (len (quarter_minus_3_list from to n))
                  (+ 1 1 (* -2 n) (- to) from))))

(defthm len_quarter_4_list
  (implies  (and (natp from) (< from (* 4 n))
                 (natp to)   (< to (* 4 n))
                 (< 0 n) (integerp n)
                 (and (<= (* 3 n) (- to from))
                      (< (- to from) (* 4 n))))
            (equal (len (quarter_4_list from to n))
                   (+ 1 (* 4 n) from (- to)))))

(defthm len_quarter_2_list
  (implies (and (natp from) (< from (* 4 n))
                (natp to)   (< to (* 4 n))
                (< 0 n) (integerp n)
                (and (< n (- to from))
                     (< (- to from) (* 2 n))))
           (equal (len (quarter_2_list from to n))
                  (+ 1 1 (* 2 n) from (- to)))))

;; we prove the exact value of the length of the route,
;; for every possible


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
        :in-theory (disable prefer-positive-addends-equal
                            prefer-positive-addends-<))
    nil))


(defthm len_route_lemma1
  (implies (and (natp from) (< from (* 4 n))
                (natp to)   (< to (* 4 n))
                (< 0 n) (integerp n))
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

;; For the last theorem we want is that the length is
;; less than 1+N

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

