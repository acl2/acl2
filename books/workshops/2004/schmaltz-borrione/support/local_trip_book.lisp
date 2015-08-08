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

;; File: local_trip_book.lisp
;; Contains lemmas for the proofs in the book trip_thms.lisp

(in-package "ACL2")

;; we import some definitions (nth_travel_step and first_travel_step
(include-book "trip_book")

(defthm first_travel_=_msg
  ;; we prove that this function does not modify messages
  (implies (and (no-duplicatesp route_pair)
                (integerp N) (< 0 N)
                (all_intp route_pair)
                (all_pos_intp route_pair)
                (all_inf_np route_pair (* 4 N))
                (availableMovep route_pair N)
                (equal (len route_pair) 2))
           (equal (first_travel_step msg route_pair N)
                  msg))
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;   :hints (("GOAL"
;            :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL)))
  )

(local
 (include-book "../../../../arithmetic-3/bind-free/top"))

(set-non-linearp t)

(local
 (include-book "../../../../arithmetic-3/floor-mod/floor-mod"))

(local
 (defthm lemma_null_cddr_x_len_x_2
   (implies (and (integerp (car x))
                 (integerp (nth 1 x))
                 (true-listp x)
                 (equal (len x) 2))
           (null (cddr x))))
 )

(local
 (defthm lemma_avail1
   (implies (and (equal (car route_pair) 0)
                 (equal (len route_pair) 2)
                 (true-listp route_pair)
                 (equal (nth 1 route_pair) 1))
            (availableMovep route_pair N))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_2
                            (x route_pair))
            :in-theory (disable lemma_null_cddr_x_len_x_2)
            :expand (availableMovep route_pair N)
            :do-not '(eliminate-destructors generalize fertilize))))
)



(local
 (defthm lemma_avail2
   (implies (and (equal (car route_pair) 0)
                 (equal (len route_pair) 2)
                 (true-listp route_pair)
                 (integerp N)
                 (equal (nth 1 route_pair) (+ -1 (* 4 N))))
            (availableMovep route_pair N))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_2
                            (x route_pair))
            :in-theory (disable lemma_null_cddr_x_len_x_2)
            :expand (availableMovep route_pair N)
            :do-not '(eliminate-destructors generalize fertilize))))
)

(local
 (defthm lemma_avail3
   (implies (and (equal (car route_pair) 0)
                 (equal (len route_pair) 2)
                 (true-listp route_pair)
                 (integerp N)
                 (equal (nth 1 route_pair) (* 2 N)))
            (availableMovep route_pair N))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_2
                            (x route_pair))
            :in-theory (disable lemma_null_cddr_x_len_x_2)
            :expand (availableMovep route_pair N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail4
   (implies (and (equal (car route_pair) (+ -1 (* 4 N)))
                 (equal (len route_pair) 2)
                 (true-listp route_pair)
                 (integerp N)
                 (equal (nth 1 route_pair) 0))
            (availableMovep route_pair N))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_2
                            (x route_pair))
            :in-theory (disable lemma_null_cddr_x_len_x_2)
            :expand (availableMovep route_pair N)
            :do-not '(eliminate-destructors generalize fertilize))))
)

(local
 (defthm lemma_avail5
   (implies (and (equal (car route_pair) (+ -1 (* 4 N)))
                 (equal (len route_pair) 2)
                 (true-listp route_pair)
                 (integerp N)
                 (equal (nth 1 route_pair) (+ -1 (car route_pair))))
            (availableMovep route_pair N))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_2
                            (x route_pair))
            :in-theory (disable lemma_null_cddr_x_len_x_2)
            :expand (availableMovep route_pair N)
            :do-not '(eliminate-destructors generalize fertilize))))
)



(local
 (defthm lemma_avail6
   (implies (and (equal (car route_pair) (+ -1 (* 4 N)))
                 (equal (len route_pair) 2)
                 (true-listp route_pair)
                 (integerp N)
                 (equal (nth 1 route_pair) (+ -1 (* 2 N))))
            (availableMovep route_pair N))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_2
                            (x route_pair))
            :in-theory (disable lemma_null_cddr_x_len_x_2)
            :expand (availableMovep route_pair N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail7
   (implies (and (integerp (car route_pair))
                 (equal (len route_pair) 2)
                 (true-listp route_pair)
                 (integerp N)
                 (equal (nth 1 route_pair) (+ 1 (car route_pair))))
            (availableMovep route_pair N))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_2
                            (x route_pair))
            :in-theory (disable lemma_null_cddr_x_len_x_2)
            :expand (availableMovep route_pair N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail8
   (implies (and (integerp (car route_pair))
                 (equal (len route_pair) 2)
                 (true-listp route_pair)
                 (integerp N)
                 (equal (nth 1 route_pair) (+ -1 (car route_pair))))
            (availableMovep route_pair N))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_2
                            (x route_pair))
            :in-theory (disable lemma_null_cddr_x_len_x_2)
            :expand (availableMovep route_pair N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail9
   (implies (and (integerp (car route_pair))
                 (equal (len route_pair) 2)
                 (true-listp route_pair)
                 (integerp N)
                 (equal (nth 1 route_pair) (+ (car route_pair) (* 2 N))))
            (availableMovep route_pair N))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_2
                            (x route_pair))
            :in-theory (disable lemma_null_cddr_x_len_x_2)
            :expand (availableMovep route_pair N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail10
   (implies (and (integerp (car route_pair))
                 (equal (len route_pair) 2)
                 (true-listp route_pair)
                 (integerp N)
                 (equal (nth 1 route_pair) (+ (car route_pair) (* -2 N))))
            (availableMovep route_pair N))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_2
                            (x route_pair))
            :in-theory (disable lemma_null_cddr_x_len_x_2)
            :expand (availableMovep route_pair N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(defthm first_travel_=_msg_not
  ;; we prove that we lose the message if the route is not made of
  ;; available moves
  ;; the lemmas are local so that we only export the main theorems
  (implies (and (no-duplicatesp route_pair)
                (equal (len route_pair) 2)
                (true-listp route_pair)
                (integerp N) (< 0 N)
                (all_intp route_pair)
                (all_pos_intp route_pair)
                (all_inf_np route_pair (* 4 N))
                (not (availableMovep route_pair N)))
           (not (first_travel_step msg route_pair N)))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :expand (not (availableMovep route_pair (* 4 N)))
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;            :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL)
           )
          ("Subgoal 2"
           :expand (all_intp route_pair))))

(local
 (defthm lemma_null_cddr_x_len_x_3
   (implies (and (integerp (car x))
                 (integerp (nth 1 x))
                 (integerp (nth 2 x))
                 (true-listp x)
                 (equal (len x) 3))
           (null (cdddr x))))
 )

(local
 (defthm lemma_avail_nth_1
   (implies (and (equal (car route_triple) 0)
                 (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (equal (nth 1 route_triple) (+ -1 (* 4 N)))
                 (not (equal (nth 2 route_triple)
                             (+ -1 (nth 1 route_triple))))
                 (not (equal (nth 2 route_triple) (+ -1 (* 2 N))))
                 (not (equal (nth 2 route_triple) 0)))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_2
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (equal (car route_triple) (+ -1 (nth 1 route_triple)))
                 (equal (nth 1 route_triple) (+ -1 (* 4 N)))
                 (not (equal (nth 2 route_triple)
                             (+ -1 (nth 1 route_triple))))
                 (not (equal (nth 2 route_triple) (+ -1 (* 2 N))))
                 (not (equal (nth 2 route_triple) 0)))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_3
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (equal (car route_triple) (+ 1 (nth 1 route_triple)))
                 (<= (* 2 N) (nth 1 route_triple))
                 (not (equal (nth 2 route_triple)
                             (+ -1 (nth 1 route_triple))))
                 (not (equal (nth 2 route_triple)
                             (+ (nth 1 route_triple) (* -2 N))))
                 (not (equal (nth 2 route_triple)
                             (+ 1 (nth 1 route_triple)))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_4
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_pos_intp route_triple)
                 (all_intp route_triple)
                 (equal (car route_triple) (+ 1 (nth 1 route_triple)))
                 (< (nth 1 route_triple) (* 2 N))
                 (not (equal (nth 1 route_triple) 0))
                 (not (equal (nth 1 route_triple) (+ -1 (* 4 N))))
                 (not (equal (nth 2 route_triple)
                             (+ -1 (nth 1 route_triple))))
                 (not (equal (nth 2 route_triple)
                             (+ (nth 1 route_triple) (* 2 N))))
                 (not (equal (nth 2 route_triple)
                             (+ 1 (nth 1 route_triple)))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_5
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_pos_intp route_triple)
                 (all_intp route_triple)
                 (equal (car route_triple) (+ -1 (nth 1 route_triple)))
                 (< (nth 1 route_triple) (* 2 N))
                 (not (equal (nth 1 route_triple) 0))
                 (not (equal (nth 1 route_triple) (+ -1 (* 4 N))))
                 (not (equal (nth 2 route_triple)
                             (+ -1 (nth 1 route_triple))))
                 (not (equal (nth 2 route_triple)
                             (+ (nth 1 route_triple) (* 2 N))))
                 (not (equal (nth 2 route_triple)
                             (+ 1 (nth 1 route_triple)))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_6
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_pos_intp route_triple)
                 (all_intp route_triple)
                 (equal (car route_triple) (+ -1 (nth 1 route_triple)))
                 (<= (* 2 N) (nth 1 route_triple))
                 (not (equal (nth 1 route_triple) 0))
                 (not (equal (nth 1 route_triple) (+ -1 (* 4 N))))
                 (not (equal (nth 2 route_triple)
                             (+ -1 (nth 1 route_triple))))
                 (not (equal (nth 2 route_triple)
                             (+ (nth 1 route_triple) (* -2 N))))
                 (not (equal (nth 2 route_triple)
                             (+ 1 (nth 1 route_triple)))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_7
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_pos_intp route_triple)
                 (all_intp route_triple)
                 (no-duplicatesp route_triple)
                 (equal (nth 1 route_triple) 0)
                 (not (equal (car route_triple) 1))
                 (not (equal (car route_triple) (+ -1 (* 4 N))))
                 (not (equal (nth 2 route_triple) 1))
                 (not (equal (nth 2 route_triple) (+ -1 (* 4 N)))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_8
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_pos_intp route_triple)
                 (all_intp route_triple)
                 (no-duplicatesp route_triple)
                 (equal (nth 1 route_triple) 0)
                 (not (equal (car route_triple) 1))
                 (not (equal (car route_triple) (* 2 N)))
                 (equal (nth 2 route_triple) (+ -1 (* 4 N))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_9
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_pos_intp route_triple)
                 (integerp (car route_triple))
                 (no-duplicatesp route_triple)
                 (equal (nth 1 route_triple) 0)
                 (not (equal (car route_triple) (+ -1 (* 4 N))))
                 (not (equal (car route_triple) (* 2 N)))
                 (equal (nth 2 route_triple) 1))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_10
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_pos_intp route_triple)
                 (no-duplicatesp route_triple)
                 (equal (nth 1 route_triple) 0)
                 (not (equal (nth 2 route_triple) (+ -1 (* 4 N))))
                 (not (equal (nth 2 route_triple) 1))
                 (not (equal (nth 2 route_triple) (* 2 N))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_11
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_pos_intp route_triple)
                 (no-duplicatesp route_triple)
                 (equal (nth 2 route_triple) (+ -1 (nth 1 route_triple)))
                 (equal (nth 1 route_triple) (+ -1 (* 4 N)))
                 (not (equal (car route_triple) 0))
                 (not (equal (car route_triple) (+ -1 (* 2 N)))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_12
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_pos_intp route_triple)
                 (no-duplicatesp route_triple)
                 (equal (nth 1 route_triple) (+ -1 (* 4 N)))
                 (not (equal (nth 2 route_triple) 0))
                 (not (equal (nth 2 route_triple)
                             (+ -1 (nth 1 route_triple))))
                 (not (equal (car route_triple) 0))
                 (not (equal (car route_triple)
                             (+ -1 (nth 1 route_triple)))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_13
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_pos_intp route_triple)
                 (no-duplicatesp route_triple)
                 (equal (nth 1 route_triple) (+ -1 (* 4 N)))
                 (equal (nth 2 route_triple) 0)
                 (not (equal (car route_triple) 0))
                 (not (equal (car route_triple) (+ -1 (* 2 N))))
                 (not (equal (car route_triple)
                             (+ -1 (nth 1 route_triple)))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_14
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_intp route_triple)
                 (all_pos_intp route_triple)
                 (no-duplicatesp route_triple)
                 (not (equal (nth 1 route_triple) 0))
                 (not (equal (nth 1 route_triple) (+ -1 (* 4 N))))
                 (not (equal (nth 2 route_triple)
                             (+ 1 (nth 1 route_triple))))
                 (not (equal (nth 2 route_triple)
                             (+ -1 (nth 1 route_triple))))
                 (not (equal (car route_triple)
                             (+ -1 (nth 1 route_triple))))
                 (not (equal (car route_triple)
                             (+ 1 (nth 1 route_triple)))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_15
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_intp route_triple)
                 (all_pos_intp route_triple)
                 (no-duplicatesp route_triple)
                 (not (equal (nth 1 route_triple) 0))
                 (not (equal (nth 1 route_triple) (+ -1 (* 4 N))))
                 (equal (nth 2 route_triple)
                        (+ -1 (nth 1 route_triple)))
                 (not (equal (car route_triple)
                             (+ (nth 1 route_triple) (* 2 N))))
                 (< (nth 1 route_triple) (* 2 N))
                 (not (equal (car route_triple)
                             (+ 1 (nth 1 route_triple)))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_16
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_intp route_triple)
                 (all_pos_intp route_triple)
                 (no-duplicatesp route_triple)
                 (not (equal (nth 1 route_triple) 0))
                 (not (equal (nth 1 route_triple) (+ -1 (* 4 N))))
                 (equal (nth 2 route_triple)
                        (+ -1 (nth 1 route_triple)))
                 (not (equal (car route_triple)
                             (+ (nth 1 route_triple) (* -2 N))))
                 (<= (* 2 N) (nth 1 route_triple))
                 (not (equal (car route_triple)
                             (+ 1 (nth 1 route_triple)))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_17
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_intp route_triple)
                 (all_pos_intp route_triple)
                 (no-duplicatesp route_triple)
                 (not (equal (nth 1 route_triple) 0))
                 (not (equal (nth 1 route_triple) (+ -1 (* 4 N))))
                 (equal (nth 2 route_triple)
                        (+ 1 (nth 1 route_triple)))
                 (not (equal (car route_triple)
                             (+ (nth 1 route_triple) (* -2 N))))
                 (<= (* 2 N) (nth 1 route_triple))
                 (not (equal (car route_triple)
                             (+ -1 (nth 1 route_triple)))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)


(local
 (defthm lemma_avail_nth_18
   (implies (and (equal (len route_triple) 3)
                 (true-listp route_triple)
                 (integerp N) (< 0 N)
                 (all_inf_np route_triple (* 4 N))
                 (all_intp route_triple)
                 (all_pos_intp route_triple)
                 (no-duplicatesp route_triple)
                 (not (equal (nth 1 route_triple) 0))
                 (not (equal (nth 1 route_triple) (+ -1 (* 4 N))))
                 (equal (nth 2 route_triple)
                        (+ 1 (nth 1 route_triple)))
                 (not (equal (car route_triple)
                             (+ (nth 1 route_triple) (* 2 N))))
                 (< (nth 1 route_triple) (* 2 N))
                 (not (equal (car route_triple)
                             (+ -1 (nth 1 route_triple)))))
            (not (availableMovep route_triple N)))
   :hints (("GOAL"
            :do-not-induct t
            :use (:instance lemma_null_cddr_x_len_x_3
                            (x route_triple))
            :in-theory (disable lemma_null_cddr_x_len_x_3)
            :expand (availableMovep route_triple N)
            :do-not '(eliminate-destructors generalize fertilize))))
)



(defthm nth_travel_=_msg
  (implies (and (no-duplicatesp route_triple)
                (integerp N) (< 0 N)
                (all_intp route_triple)
                (true-listp route_triple)
                (availableMovep route_triple N)
                (all_pos_intp route_triple)
                (all_inf_np route_triple (* 4 N))
                (equal (len route_triple) 3))
           (equal (nth_travel_step msg route_triple N)
                  msg))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;            :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL)
           :do-not '(eliminate-destructors generalize fertilize))
; Subgoal hints modified by Matt K. after ACL2 Version 3.6.1 for changes in
; too-many-ifs heuristic.  The first of these is just for backward
; compatibility and is irrelevant in modern proofs; the second is for the new ACL2.
          ("Subgoal 25"
           :expand (availablemovep route_triple n))
; fcd/Satriani v3.7 Moore - used to be Subgoal 2.26
          ("Subgoal 2.22"
           :expand (all_intp route_triple))))


(defthm nth_travel_=_msg_not
  ;; if the route is not made of valid moves we lose the message
  (implies (and (no-duplicatesp route_triple)
                (integerp N) (< 0 N)
                (all_intp route_triple)
                (true-listp route_triple)
                (not (availableMovep route_triple N))
                (all_pos_intp route_triple)
                (all_inf_np route_triple (* 4 N))
                (equal (len route_triple) 3))
           (not (nth_travel_step msg route_triple N)))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :in-theory (disable
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (commented out rule just below).]
                       ;; NO-DUPLICATESP->NO-DUPLICATESP-EQUAL
                       prefer-positive-addends-equal
                       prefer-positive-addends-<))))
(set-non-linearp nil)
