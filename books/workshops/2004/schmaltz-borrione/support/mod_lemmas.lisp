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

;; File: mod_lemmas.lisp
;; all the lemmas about mod needed to prove that the routing algorithm
;; terminates

(in-package "ACL2")

(include-book "../../../../arithmetic-3/bind-free/top")

(set-non-linearp t)

(include-book "../../../../arithmetic-3/floor-mod/floor-mod")

(defthm mod-x-=-x
  (implies (and (rationalp x)
                (integerp n)
                (<= 0 x)
                (< 0 n)
                (< x n))
           (equal (mod x n) x)))

(local
 (defthm lemma_for_next_theorem
   (implies (and (rationalp x)
                 (< 0 x)
                 (< x n)
                 (integerp n)
                 (< 0 n))
            (equal (mod (- x) n)
                   (+ (- x) n))))
)

(defthm mod-x-=-x-+-n
  (implies (and (rationalp x)
                (< x 0)
                (< (- x) n)
                (integerp n)
                (< 0 n))
           (equal (mod x n)
                  (+ x n)))
  :hints (("GOAL"
           :use (:instance lemma_for_next_theorem
                           (x (- x))))))


(defthm abs-<-1-imp-not-int
  (implies (and (< (abs x) 1)
                (not (equal x 0)))
           (not (integerp x))))

(defthm mod-x-=-minusx-pos
  (implies (and (rationalp x)
                (integerp n)
                (< 0 n)
                (<= n x)
                (< x (* 2 n)))
           (equal (mod x n)
                  (- x n))))

(defthm mod-+-n/2-pos
  (implies (and (< x n)
                (rationalp x)
                (integerp n)
                (<= (* 1/2 n) x)
                (< 2 n)
                )
           (< (mod (+ x (* 1/2 n)) n)
              (mod x n))))

(defthm mod-+-n/2-neg
  (implies (and (< x 0)
                (< (- x) n)
                (rationalp x)
                (<= (- x) (* 1/2 n))
                (integerp n)
                (< 0 n))
           (<  (mod (+ x (* 1/2 n)) n)
               (mod x n))))

(defthm mod-+-1/2-=-mod-minus-1/2
  (implies (and (integerp n)
                (< 0 n)
                (rationalp x)
                (< (abs x) n))
           (equal (mod (+ x (* -1/2 n)) n)
                  (mod (+ x (* 1/2 n)) n)))
  :hints (("GOAL" :in-theory (enable mod))))

(defthm mod-n/2-pos
  (implies (and (< 0 x)
                (< x n)
                (rationalp x)
                (integerp n)
                (<= (* 1/2 n) x)
                (< 0 n)
                )
           (< (mod (+ x (* -1/2 n)) n)
              (mod x n))))

(defthm mod-n/2-neg
  (implies (and (< x 0)
                (< (- x) n)
                (rationalp x)
                (<= (- x) (* 1/2 n))
                (integerp n)
                (< 0 n))
           (<  (mod (+ x (* -1/2 n)) n)
               (mod x n))))

;;Summary
;;Form:  (CERTIFY-BOOK "mod_lemmas" ...)
;;Rules: NIL
;;Warnings:  Guards
;;Time:  2.91 seconds (prove: 0.84, print: 0.04, other: 2.03)
;; "/home/julien/work/ProofReplayOctagonFMCAD04/mod_lemmas.lisp"
