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

;; File: routing.lisp
;; Proof of the Routing Algorithm

(in-package "ACL2")


;; we import all the predicates and other thins needed for this book
(include-book "predicatesNCie")

;;----------------------------------------------------------------------
;;----------------------------------------------------------------------
;;
;;           DEFINITION OF THE AVAILABLE MOVES IN THE NETWORK
;;
;;----------------------------------------------------------------------
;;----------------------------------------------------------------------

(defun n_clockwise (from n)
  (mod (+ from 1) (* 4 n)))

(defun n_counter_clockwise (from n)
  (mod (- from 1) (* 4 n)))

(defun n_across (from n)
  (mod (+ from (* 2 n)) (* 4 n)))

;;--------------------------------------------------------------------
;;              IMPORTING LEMMAS ABOUT MOD
;;--------------------------------------------------------------------
(include-book "mod_lemmas")

;; this book also import the books on Arithmetic

;;--------------------------------------------------------------------
;;             USEFUL LOCAL LEMMAS
;;-------------------------------------------------------------------

;; the following lemmas are used to force some behavior of ACL2

(local
(defthm force_case_split
  (implies (and (integerp dest)
                (integerp from)
                (<= 0 dest)
                (<= 0 from))
            (iff (not (equal dest from))
                  (or (< (+ dest (- from)) 0)
                      (< 0 (+ dest (- from))))))
  :rule-classes nil)
)

(local
(defthm <=_=_<_or_=
  (implies (and (acl2-numberp a)
                (acl2-numberp b)
                )
           (equal (<= a b)
                  (or (< a b)
                      (= a b))))
  :rule-classes nil)
)


;;----------------------------------------------------------------------
;;----------------------------------------------------------------------
;;
;;                  DEFINITION OF THE ROUTING ALGORITHM
;;
;;----------------------------------------------------------------------
;;----------------------------------------------------------------------

;; to simplify a little the ACL2 proof, n represents the number of nodes
;; in one quarter of the Octagon. So, there are 4*n nodes in the network!

(defun route (from dest n)
  (declare (xargs :measure (min (nfix (mod (- dest from) (* 4 n)))
                                (nfix (mod (- from dest) (* 4 n))))
                  :hints
                  (("GOAL"
                    :use ((:instance force_case_split)
                          (:instance <=_=_<_or_=
                                     (a dest) (b (+ -1 (* 4 n))))
                          (:instance <=_=_<_or_=
                                     (a from) (b (+ -1 (* 4 n))))
                          (:instance mod-+-n/2-pos
                                     (n (* 4 n))
                                     (x (+ (- dest) from))))
                    :in-theory (disable PREFER-POSITIVE-ADDENDS-<
                                        prefer-positive-addends-equal
                                        reduce-integerp-+
                                        mod-+-n/2-pos))
                   ("Subgoal 330.4" :cases ((<= 0 (+ -1 from))
                                            (< (+ -1 from) 0))))))
  (cond ((or
          (not (integerp dest)) ;; dest must be an integer
          (< dest 0) ;; dest must be positive
          (< (- (* 4 n) 1) dest) ;; dest must be lower than the number of nodes
          (not (integerp from)) ;; from must be an integer
          (< from 0) ;; from must be positive
          (< (- (* 4 n) 1) from) ;; from must be lower than the number of nodes
          (not (integerp n)) ;; the number of nodes must be an integer
          (<= n 0)) ;; n must be positive
         nil) ;; if all the conditions are not OK then we return nil
        ((equal (- dest from) 0) (cons from nil));; process at node
        ((and (< 0 (mod (- dest from) (* 4 n)))
              (<= (mod (- dest from) (* 4 n)) n))
         ;;If we go clock wise the dest is the next of the next next
         ;;but dest is in the same quarter
         (cons from (route (n_clockwise from n) dest n)))
        (;(and (<= (* 3 n) (mod (- dest from) (* 4 n)))
         ;     (< (mod (- dest from) (* 4 n)) (* 4 n)))
	 (<= (* 3 n) (mod (- dest from) (* 4 n)))
         ;;If we go cc dest is in the same quarter too
         (cons from (route (n_counter_clockwise from n) dest n)))
        (t
         ;; else we cross and then the dest will be in the same quarter
         (cons from (route (n_across from n) dest n)))))

;; ACL2 finds the :type-prescription (TRUE-LISTP (N_GO_TO_NODE FROM DEST N))

;;Warnings:  None
;;Time:  85.04 seconds (prove: 80.95, print: 4.02, other: 0.07)
;; ROUTE

