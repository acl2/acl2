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

;; File: routing_main.lisp
;; Proof of the main theorem of Route
;; Definition of a constrained function in an encapsulate to show that the
;; proof of the overall system relies only on the theorem and not on the
;; definition of Route. Every function that will satisfy the theorem will not
;; modify the rest of the proof

(in-package "ACL2")

;; we import some definitions
(include-book "predicatesNCie")

(encapsulate
 (((myroute * * *) => *))

 (local (include-book "routing_local_lemmas"))

 (local (defun myroute (from to n)
          (route from to n)))

 (local
  (defthm consp_len_>_0
    (implies (consp x)
             (< 0 (len x))))
  )

 (defthm true-listp_myroute
   (true-listp (myroute from to n))
   :rule-classes :type-prescription
 )

 (defthm CORRECTNESS_OF_MYROUTE
   (implies (and (integerp from)
                 (<= 0 from)
                 (< from (* 4 n))
                 (integerp to)
                 (<= 0 to)
                 (< to (* 4 n))
                 (integerp n)
                 (< 0 n))
            (and ;; Route contains at least one element
;                 (< 0 (len (myroute from to n)))
                 ;; it is a consp
                 (consp (myroute from to n))
                 ;; every node is an integer
                 (all_intp (myroute from to n))
                 ;; every node number is positive
                 (all_pos_intp (myroute from to n))
;                 ;; every route is shorter than or equal to (* 4 N)
;                 (< (len (myroute from to n)) (+ 1 1 (* 4 N)))
                 ;; every route contains no duplicate
                 (no-duplicatesp (myroute from to n))
                 ;; every node is less than the maximum of nodes
                 (all_inf_np (myroute from to n) (* 4 n))
                 ;; a route is made of available moves
                 (AvailableMovep (myroute from to n) n)
                 ;; the first node is the starting node
                 (equal (car (myroute from to n)) from)
                 ;; the last node is the final node
                 (equal (car (last (myroute from to n))) to)))
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;    :hints (("GOAL"
;             :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL)))
   )
)