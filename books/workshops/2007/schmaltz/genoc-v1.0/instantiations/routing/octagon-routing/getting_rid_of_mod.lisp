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

;; File: getting_rid_of_mod.lisp
;; Implements a strategy to rewrite the function Route to functions that
;; create lists and do not use the function mod

(in-package "ACL2")

;; we import the definition of the functio Route
(include-book "routing_defuns")

(set-non-linearp t)

;;----------------------------------------------------------------------
;;----------------------------------------------------------------------
;;
;;                  GETTING RID OF MOD
;;
;;----------------------------------------------------------------------
;;----------------------------------------------------------------------


;; To reason about function "route", I define, for each possible case of
;; (mod (+ dest (- from)) n) a function that computes a list of nodes and
;; that does not use function mod. Then, the properties are generally
;; trivial on these small functions and the properties on route are
;; proved by a simple case split.

;; We divide the Octagon in quarters and bound, according to the value
;; of (- dest from).

;;-----------------------------------------------------------------------
;;
;;                          Quarter 1
;;               (and (<= (- to from) n)
;;                    (<= 0 (- to from))))
;;
;;-----------------------------------------------------------------------


(defun quarter_1_list (from to)
  (declare (xargs :measure (nfix (+ to (- from)))
                  :hints
                  (("GOAL"
                    :in-theory (disable prefer-positive-addends-<
                                        simplify-sums-<
                                        prefer-positive-addends-equal)))))
  (if (zp (- to from))
      (cons from nil)
    (cons from (quarter_1_list (+ 1 from) to))))


;; I prove that route is equal to this function in this quarter

(defthm route_=_quarter_1
  (implies (and (natp from) (natp to)
                (< to (* 4 n)) (< from (* 4 n))
                (integerp n) (< 0 n)
                (and (<= (- to from) n)
                     (<= 0 (- to from))))
           (equal (route from to n)
                  (quarter_1_list from to)))
  :hints (("GOAL"
           :in-theory (disable
                       (:REWRITE MOD-POSITIVE . 1)
                       prefer-positive-addends-<
                       prefer-positive-addends-equal)
           :do-not '(eliminate-destructors generalize))))

;;-----------------------------------------------------------------------
;;
;;                         Quarter -4
;;               (and (<= (- to from) (* -3 n))
;;                    (< (- (* 4 n)) (- to from))))
;;
;;-----------------------------------------------------------------------

;; comes next because defined using quarter_1_list

(defun quarter_minus_4_list (from to n)
  (declare (xargs :measure (nfix (- (+ -1 (* 4 n)) from))
                  :hints
                  (("GOAL"
                    :in-theory (disable prefer-positive-addends-<
                                        simplify-sums-<
                                        prefer-positive-addends-equal)))))
  (cond ((equal (- to from) 0) (cons from nil))
        ((zp (- (+ (* 4 n) -1) from))
         (cons from (quarter_1_list 0 to)))
        (t
         (cons from (quarter_minus_4_list (+ 1 from) to n)))))

(defthm route_=_quarter_minus_4_list
  (implies (and (integerp from)
                (integerp to)
                (<= 0 to)
                (<= 0 from)
                (< to (* 4 n))
                (< from (* 4 n))
                (integerp n)
                (and (<= (- to from) (* -3 n))
                     (< (- (* 4 n)) (- to from))))
           (equal (route from to n)
                  (quarter_minus_4_list from to n)))
  :hints (("GOAL"
           :in-theory (disable (:REWRITE MOD-POSITIVE . 1)))))

;;-----------------------------------------------------------------------
;;
;;                         Quarter 3
;;               (and (< (- to from) (* 3 n))
;;                    (< (* 2 n) (- to from))))
;;
;;-----------------------------------------------------------------------


(defun quarter_3_list (from to n)
  (cons from
        (cons (+ from (* 2 n))
              (quarter_1_list (+ from (* 2 n) 1) to))))

(defthm route_=_quarter_3
  (implies (and (integerp from)
                (integerp to)
                (<= 0 to)
                (<= 0 from)
                (< to (* 4 n))
                (< from (* 4 n))
                (integerp n)
                (and (< (- to from) (* 3 n))
                     (< (* 2 n) (- to from))))
            (equal (route from to n)
                   (quarter_3_list from to n)))
   :hints (("GOAL" :in-theory (disable prefer-positive-addends-<
                                       prefer-positive-addends-equal))))

;;-----------------------------------------------------------------------
;;
;;                         Quarter -2
;;              (and (< (- to from) (- n))
;;                   (< (* -2 n) (- to from))))
;;
;;-----------------------------------------------------------------------


(defun quarter_minus_2_list (from to n)
  (if (<= (* 2 n) from)
      (cons from
            (cons (+ from (* -2 n))
                  (quarter_1_list (+ 1 from (* -2 n)) to)))
    (cons from
          (quarter_minus_4_list (+ from (* 2 n)) to n))))

(defthm route_=_quarter_minus_2_list
  (implies (and (integerp from)
                (integerp to)
                (<= 0 to)
                (<= 0 from)
                (< to (* 4 n))
                (< from (* 4 n))
                (integerp n)
                (and (< (- to from) (- n))
                     (< (* -2 n) (- to from))))
           (equal (route from to n)
                  (quarter_minus_2_list from to n)))
  :hints (("GOAL"
           :in-theory (disable
                       prefer-positive-addends-equal
                       prefer-positive-addends-<))))

;;-----------------------------------------------------------------------
;;
;;                         Quarter -1
;;              (and (< (- to from) 0)
;;                   (<= (- n) (- to from))))
;;
;;-----------------------------------------------------------------------


(defun quarter_minus_1_list (from to)
  (declare (xargs :measure (nfix (- from to))
                  :hints
                  (("GOAL"
                    :in-theory (disable prefer-positive-addends-<
                                        prefer-positive-addends-equal)))))
  (if (zp (- from to))
      (cons from nil)
    (cons from (quarter_minus_1_list (+ -1 from) to))))


(defthm route_=_quarter_minus_1_list
  (implies  (and (integerp from)
                 (integerp to)
                 (<= 0 to)
                 (integerp n)
                 (< from (* 4 n))
                 (< to (* 4 n))
                 (and (< (- to from) 0)
                      (<= (- n) (- to from))))
            (equal (route from to n)
                   (quarter_minus_1_list from to)))
  :hints (("GOAL" :in-theory (disable prefer-positive-addends-<
                                      prefer-positive-addends-equal))))

;;-----------------------------------------------------------------------
;;
;;                         Quarter -3
;;                (and (< (* -3 n) (- to from))
;;                     (< (- to from) (* -2 n))))
;;
;;-----------------------------------------------------------------------

(defun quarter_minus_3_list (from to n)
  (cons from
        (cons (+ from (* -2 n))
              (quarter_minus_1_list (+ -1 from (* -2 n)) to))))

(defthm route_=_quarter_minus_3_list
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
           (equal (route from to n)
                  (quarter_minus_3_list from to n)))
  :hints (("GOAL" :in-theory (disable prefer-positive-addends-<
                                      prefer-positive-addends-equal))))

;;-----------------------------------------------------------------------
;;
;;                         Quarter 4
;;             (and (<= (* 3 n) (- to from))
;;                   (< (- to from) (* 4 n))))
;;
;;-----------------------------------------------------------------------

(defun quarter_4_list (from to n)
  (declare (xargs :hints (("GOAL"
                           :in-theory (disable prefer-positive-addends-<
                                               prefer-positive-addends-equal
                                               simplify-sums-<)))))
  (cond ((zp from)
         (cons from (quarter_minus_1_list (+ -1 (* 4 n)) to)))
        ((equal (- to from) 0)
         (cons from nil))
        (t
         (cons from (quarter_4_list (+ -1 from) to n)))))

(defthm route_=_quarter_4_list_lemma_1
  (implies  (and (integerp from)
                 (integerp to)
                 (<= 0 to)
                 (integerp n)
                 (< 0 n)
                 (< from (* 4 n))
                 (< to (* 4 n))
                 (<= 0 from)
                 (and (< (- to from) 1)
                      (<= (+ 1 (- n)) (- to from))))
            (equal (route from to n)
                   (quarter_minus_1_list from to)))
  :hints (("GOAL" :in-theory (disable prefer-positive-addends-<
                                      prefer-positive-addends-equal))))

(defthm route_=_quarter_4_list
  (implies (and (integerp from)
                (<= 0 from)
                (< from (* 4 n))
                (integerp to)
                (<= 0 to)
                (< to (* 4 n))
                (< 0 n)
                (integerp n)
                (< 0 n)
                (and (<= (* 3 n) (- to from))
                     (< (- to from) (* 4 n))))
           (equal (route from to n)
                  (quarter_4_list from to n)))
  :hints (("GOAL" :in-theory (disable prefer-positive-addends-<
                                      prefer-positive-addends-equal))))

;;-----------------------------------------------------------------------
;;
;;                         Quarter -2
;;              (and (<  n (- to from))
;;                   (< (- to from) (* 2 n))))
;;
;;-----------------------------------------------------------------------

(defun quarter_2_list (from to n)
  (if (< from (* 2 n))
      (cons from
        (cons (+ from (* 2 n))
              (quarter_minus_1_list (+ -1 from (* 2 n)) to)))
    (cons from
          (quarter_4_list (+ from (* -2 n)) to n))))


(defthm route_=_quarter_2_list
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
           (equal (route from to n)
                  (quarter_2_list from to n)))
  :hints (("GOAL"
           :in-theory (disable prefer-positive-addends-<
                               prefer-positive-addends-equal))))

;;-----------------------------------------------------------------------
;;
;;                         BOUNDS
;;                       +/- (* 2 n)
;;
;;-----------------------------------------------------------------------


(defun bounds (from n)
  (if (<= (* 2 n) from)
      (cons from (cons (+ from (* -2 n)) nil))
    (cons from
          (cons (+ from (* 2 n)) nil))))

(defthm route_=_bounds
  (implies (and (integerp from)
                (<= 0 from)
                (< from (* 4 n))
                (integerp to)
                (<= 0 to)
                (< to (* 4 n))
                (integerp n)
                (< 0 n)
                (or (equal (+ to (- from)) (* 2 n))
                    (equal (+ to (- from)) (* -2 n))))
           (equal (route from to n)
                  (bounds from n))))

;; End of the "splitting"
;;-----------------------

;; now we have rules for all the possible cases, we can disable route

(in-theory (disable route))

;;------------------------

;; A useful computed hint


;; and for all theorem we will split into all these cases
;; To help, we define the following computed hint:

(defun computed_hint_route (id clause world)
  (declare (ignore clause world))
  (if (equal id '((0) NIL . 0))
             '(:cases ((and (<= (- to from)  n)
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
                       (and (<  n (- to from))
                            (< (- to from) (* 2 n)))
                       (equal (+ to (- from)) (* 2 n))
                       (equal (+ to (- from)) (* -2 n))))
    nil))


