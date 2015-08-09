; The Tail Recursion Book
; Copyright (C) 2004 John R. Cowles, University of Wyoming

; This program is free software; you can redistribute it and/or
; modify it under the terms of the GNU General Public License as
; published by the Free Software Foundation; either version 2 of
; the License, or (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free
; Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139,
; USA.

; Written by:
; John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071 U.S.A.

#|
(defpkg "TAIL-REC"
        (union-eq *acl2-exports*
		  *common-lisp-symbols-from-main-lisp-package*))

(certify-book "tail-rec" 1)
|#

(in-package "TAIL-REC")

;; This is the Defpun book by Manolios and Moore.

(include-book "../../../../misc/defpun")

;; Defpun is in the ACL2 package, so it is added by macro to the
;; TAIL-REC package.

(defmacro defpun (g args &rest tail)
  `(acl2::defpun ,g ,args ,@tail))
;;=====================================================================
;; Let test, base, and step be unary functions.
;; A total ACL2 function f is said to satisfy the defining tail recursion
;; axiom for the proposed definition

;; (defun
;;   f (x)
;;   (if (test x)
;;       (base x)
;;       (f (step x))))

;; provided the following is true

;; ((FORALL x)(EQUAL (f x)
;;                   (if (test x)
;;                       (base x)
;;                       (f (step x)))))

;; J and Pete's DEFPUN paper shows that there is always at least one total ACL2
;; function that satisfies the defining tail recursion axiom for any such proposed
;; tail recursive definition.
;; --------------------------------------------------------------------------
;; Let rel be a well-founded binary relation on the set of objects
;; recognized by the predicate mp.

;; That is, there is a rel-order-preserving function fn that embeds
;; objects recognized by mp into ACL2's ordinals:

;; (AND (IMPLIES (mp x) (O-P (fn x)))              ; Property 1
;;      (IMPLIES (AND (mp x)                       ; Property 2
;;                    (mp y)
;;                    (rel x y))
;;               (O< (fn x) (fn y)))).

;; Let test1, base1, and step1 be unary functions.
;; The tail recursion in the proposed definition

;; (defun
;;   f1 (x)
;;   (if (test1 x)
;;       (base1 x)
;;       (f1 (step1 x))))

;; is said to satisfy the mp-meaure conjecture for measure m provided the
;; following goals are true.

;; (AND (mp (m x))                                  ; Defun-goal-1
;;      (IMPLIES (NOT (test1 x))                    ; Defun-goal-2
;;               (rel (m (step1 x))
;;                    (m x))).

;; THEOREM 1. If the tail recursion satisfies the mp-measure conjecture for
;;            measure m, then there is exactly one total function satisfying
;;            the defining tail recursion axiom.

;;            That is, (IMPLIES ((FORALL x)(AND (IMPLIES (mp x)
;;                                                       (O-P (fn x)))
;;                                              ((FORALL y)(IMPLIES
;;                                                            (AND (mp x)
;;                                                                 (mp y)
;;                                                                 (rel x y))
;;                                                            (O< (fn x)(fn y))))
;;                                              (mp (m x))
;;                                              (IMPLIES (NOT (test1 x))
;;                                                       (rel (m (step1 x))
;;                                                            (m x)))))
;;                               ((EXISTS UNIQUE FUNCTION f1)
;;                                ((FORALL x)(EQUAL (f1 x)
;;                                                  (if (test1 x)
;;                                                      (base1 x)
;;                                                      (f1 (step1 x)))))))

;; The conclusion of THEOREM 1,

;;       ((EXISTS UNIQUE FUNCTION f1)
;;        ((FORALL x)(EQUAL (f1 x)
;;                          (if (test1 x)
;;                              (base1 x)
;;                              (f1 (step1 x)))),

;; expands to this equivalent formulation:

;;       (AND ((EXISTS FUNCTION f1)
;;             ((FORALL x)(EQUAL (f1 x)
;;                               (if (test1 x)
;;                                   (base1 x)
;;                                   (f1 (step1 x))))))
;;            ((FORALL FUNCTIONS g1 and h1)
;;             (IMPLIES (AND ((FORALL x)(EQUAL (g1 x)
;;                                             (if (test1 x)
;;                                                 (base1 x)
;;                                                 (g1 (step1 x)))))
;;                           ((FORALL x)(EQUAL (h1 x)
;;                                             (if (test1 x)
;;                                                 (base1 x)
;;                                                 (h1 (step1 x))))))
;;                      ((FORALL x)(EQUAL (g1 x)
;;                                        (h1 x))))))
;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;; PROOF OF THEOREM 1.

;; Assume the hypothesis of THEOREM 1.
;; That is, assume

;;      (IMPLIES ((FORALL x)(AND (IMPLIES (mp x)
;;                                        (O-P (fn x)))
;;                               ((FORALL y)(IMPLIES
;;                                           (AND (mp x)
;;                                                (mp y)
;;                                                (rel x y))
;;                                           (O< (fn x)(fn y))))
;;                               (mp (m x))
;;                               (IMPLIES (NOT (test1 x))
;;                                        (rel (m (step1 x))
;;                                             (m x)))))

;; Let rel, mp, fn, m, test1, and step1 be functions satisfying the
;; given hypothesis.

(encapsulate
 (((rel * *) => *)
  ((mp *)    => *)
  ((fn *)    => *)
  ((m *)     => *)
  ((test1 *) => *)
  ((step1 *) => *))

 (local (defun rel (x y)
	  (O< x y)))

 (local (defun mp (x)
	  (O-p x)))

 (local (defun fn (x)
	  x))

 (local (defun m (x)
	  (acl2-count x)))

 (local (defun test1 (x)
	  (zp x)))

 (local (defun step1 (x)
	  (- x 1)))

 (defthm
   rel-is-well-founded-relation
   (and (implies (mp x)(O-P (fn x)))
	(implies (and (mp x)
		      (mp y)
		      (rel x y))
		 (O< (fn x)(fn y))))
   :rule-classes :well-founded-relation)

 (defthm
   measure-conjecture
   (and (mp (m x))
	(implies (not (test1 x))
		 (rel (m (step1 x))
		      (m x)))))
 ) ;; end encapsulate

;; Let base1 be an arbitrary unary function.

(defstub
  base1 (*) => *)

;; Prove the conclusion of THEOREM 1.
;; That is, prove each of the two conjuncts of the conclusion.

;; Conjunct 1..

;;        ((EXISTS FUNCTION f1)
;;         ((FORALL x)(EQUAL (f1 x)
;;                           (if (test1 x)
;;                               (base1 x)
;;                               (f1 (step1 x))))))

;; Show a function, called f1, exists with the desired property.

(defun
  f1 (x)
  (declare (xargs :measure (m x)
		  :well-founded-relation rel))
  (if (test1 x)
      (base1 x)
      (f1 (step1 x))))

;; Explicitly verify that f1 has the desired property.

(defthm
  f1-def
  (equal (f1 x)
	 (if (test1 x)
	     (base1 x)
	     (f1 (step1 x))))
  :rule-classes nil)

;; Conjunct 2.

;;           ((FORALL FUNCTIONS g1 and h1)
;;            (IMPLIES (AND ((FORALL x)(EQUAL (g1 x)
;;                                            (if (test1 x)
;;                                                (base1 x)
;;                                                (g1 (step1 x)))))
;;                          ((FORALL x)(EQUAL (h1 x)
;;                                            (if (test1 x)
;;                                                (base1 x)
;;                                                (h1 (step1 x))))))
;;                     ((FORALL x)(EQUAL (g1 x)
;;                                       (h1 x)))))

;; Let g1 and h1 be arbitrary functions satisfying the hypothesis of
;; Conjunct 2.

(encapsulate
 (((g1 *) => *)
  ((h1 *) => *))

 (local (defun g1 (x)
	  (f1 x)))

 (local (defun h1 (x)
	  (f1 x)))

 (defthm
   g1-def
   (equal (g1 x)
	  (if (test1 x)
	      (base1 x)
	      (g1 (step1 x))))
  :rule-classes :definition)

 (defthm
   h1-def
   (equal (h1 x)
	  (if (test1 x)
	      (base1 x)
	      (h1 (step1 x))))
   :rule-classes :definition)
 ) ;; end encapsulate

;; Prove the conclusion of Conjunct 2.

(defthm
  g1=h1
  (equal (g1 x)
	 (h1 x))
  :rule-classes nil
  :hints (("Goal"
	   :induct (f1 x))))

;; This concludes the proof of THEOREM 1.
;; -------------------------------------------------------------------------
#|
;; Let test2, base2, and step2 be unary functions.

;; Let (step2n x n) be the result of applying step2 n times with initial input x.
;; That is,

;; (defun
;;   step2n (x n)
;;   (if (zp n)
;;       x
;;       (step2n (step2 x)(- n 1))))

;; The tail recursion in the proposed definition

;; (defun
;;   f2 (x)
;;   (if (test2 x)
;;       (base2 x)
;;       (f2 (step2 x))))

;; is said to always terminate provided the following holds.

;; For all inputs x, there is an n such that (test2 (step2n x n)) is not NIL.

;; THEOREM 2. If there is exactly one total function satisfying the defining
;;            tail recursion axiom, then the recursion always terminates.

;;            That is, (IMPLIES ((EXISTS UNIQUE FUNCTION f2)
;;                               ((FORALL x)(EQUAL (f2 x)
;;                                                 (if (test2 x)
;;                                                     (base2 x)
;;                                                     (f2 (step2 x))))))
;;                               ((FORALL x)((EXISTS n)(test2 (step2n x n)))))

;; The hypothesis of THEOREM 2,

;;       ((EXISTS UNIQUE FUNCTION f2)
;;        ((FORALL x)(EQUAL (f2 x)
;;                          (if (test2 x)
;;                              (base2 x)
;;                              (f2 (step2 x)))),

;; expands to this equivalent formulation:

;;       (AND ((EXISTS FUNCTION f2)
;;             ((FORALL x)(EQUAL (f2 x)
;;                               (if (test2 x)
;;                                   (base2 x)
;;                                   (f2 (step2 x))))))
;;            ((FORALL FUNCTIONS g2 and h2)
;;             (IMPLIES (AND ((FORALL x)(EQUAL (g2 x)
;;                                             (if (test2 x)
;;                                                 (base2 x)
;;                                                 (g2 (step2 x)))))
;;                           ((FORALL x)(EQUAL (h2 x)
;;                                             (if (test2 x)
;;                                                 (base2 x)
;;                                                 (h2 (step2 x))))))
;;                      ((FORALL x)(EQUAL (g2 x)
;;                                        (h2 x))))))
;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;; PROOF OF THEOREM 2.

;; Assume the hypothesis of THEOREM 2.
;; That is, assume each of the two conjuncts of the hypothesis.

;; Conjunct 1.
;; Assume there is a function, called f2, with the desired property.

(encapsulate
 (((test2 *) => *)
  ((base2 *) => *)
  ((step2 *) => *)
  ((f2 *)    => *))

 (local (defun test2 (x)
	  (zp x)))

 (local (defun base2 (x)
	  (declare (ignore x))
	  0))

 (local (defun step2 (x)
	  (- x 1)))

 (local (defun f2 (x)
	  (if (test2 x)
	      (base2 x)
	      (f2 (step2 x)))))

 (defthm
   f2-def
   (equal (f2 x)
	  (if (test2 x)
	      (base2 x)
	      (f2 (step2 x))))
   :rule-classes :definition)
 ) ;; end encapsulate

;; Conjunct 2
;; Assume
;;            ((FORALL FUNCTIONS g2 and h2)
;;             (IMPLIES (AND ((FORALL x)(EQUAL (g2 x)
;;                                             (if (test2 x)
;;                                                 (base2 x)
;;                                                 (g2 (step2 x)))))
;;                           ((FORALL x)(EQUAL (h2 x)
;;                                             (if (test2 x)
;;                                                 (base2 x)
;;                                                 (h2 (step2 x))))))
;;                      ((FORALL x)(EQUAL (g2 x)
;;                                        (h2 x))))))

;; That is, whenever g2 and h2 are functions that satisfy the hypthesis
;; of Conjunct 2, they also satisfy the conclusion.

;; Let g2 and h2 be arbitrary functions satisfying the hypothesis of
;; Conjunct 2.

(encapsulate
 (((g2 *) => *)
  ((h2 *) => *))

 (local (defun g2 (x)
	  (f2 x)))

 (local (defun h2 (x)
	  (f2 x)))

 (defthm
   g2-def
   (equal (g2 x)
	  (if (test2 x)
	      (base2 x)
	      (g2 (step2 x))))
   :rule-classes nil)

 (defthm
   h2-def
   (equal (h2 x)
	  (if (test2 x)
	      (base2 x)
	      (h2 (step2 x))))
   :rule-classes nil)
 ) ;; end encasulate

;; Now, ensure that ACL2 can conclude the conclusion of Conjunct 2,
;; namely that the functions g2 and h2 are equal, whenever the
;; hypothesis of conjunct 2 holds. This is done with a SKIP-PROOFS!

(skip-proofs
 (defthm
   g2=h2
   (equal (g2 x)
	  (h2 x))
   :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; WARNING: This use of skip-proofs will render ACL2 unsound.
;; This is because the purported theorem g2=h2 does NOT logically
;; follow from the two constrained axioms g2-def and h2-def.
;; [See below for a ``proof'' of NIL. Search for (defun k ...)]

;; However, the current proof would be sound in any circumstances
;; where g2=h2 does logically follow. For example, since g1=h1 is
;; a theorem, as shown above, this proof (with g1 replacing g2 and
;; h1 replacing h2) shows that the recursion in the definition of
;; f1 (and g1 & h1) always terminates.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Prove the conclusion of THEOREM 2.
;; That is, prove the recursion always halts
;; Prove ((FORALL x)((EXISTS n)(test2 (step2n x n))))

;; At this point the proof closely follows the proof, given by
;; J and Pete, in their DEFPUN work, that tail recursive definitions
;; are always satisfied by at least one total ACL2 function.

(defun
  step2n (x n)
  (if (zp n)
      x
      (step2n (step2 x)(- n 1))))

(defchoose
  nbr-step2 (n)(x)
  (test2 (step2n x n)))

(defun
  f2n (x n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (test2 x))
      (base2 x)
      (f2n (step2 x)(- n 1))))

(defun
  g2a (x)
  (if (test2 (step2n x (nbr-step2 x)))
      (f2n x (nbr-step2 x))
      nil))

(defun
  h2a (x)
  (if (test2 (step2n x (nbr-step2 x)))
      (f2n x (nbr-step2 x))
      t))

;; This encapsulate merely hides some tedious details of the proof.
(encapsulate
 nil

 (local
  (defthm
    test2-nbr-step2
    (implies (test2 x)
	     (test2 (step2n x (nbr-step2 x))))
    :hints (("Goal"
	     :use (:instance
		   nbr-step2
		   (n 0))))))

 (local
  (defthm
    test2-g2a-def
    (implies (test2 x)
	     (equal (g2a x)(base2 x)))))

 (local
  (defthm
    test2-h2a-def
    (implies (test2 x)
	     (equal (h2a x)(base2 x)))))

 (local
  (defthm
    open-step2n
    (implies (and (integerp n)
		  (> n 0))
	     (equal (step2n x n)
		    (step2n (step2 x)(- n 1))))))

 (local
  (defthm +1-1
    (equal (+ -1 +1 x) (fix x))))

 (local
  (defthm
    step2-step2n-nbr-step2
    (implies (test2 (step2n (step2 x)(nbr-step2 (step2 x))))
	     (test2 (step2n x (nbr-step2 x))))
    :hints (("Goal"
	     :use (:instance
		   nbr-step2
		   (n (+ 1 (nfix (nbr-step2 (step2 x))))))))
    :rule-classes :forward-chaining))

 (local
  (defthm
    not-test2-nbr-step2
    (implies (not (test2 x))
	     (iff (test2 (step2n (step2 x)(nbr-step2 (step2 x))))
		  (test2 (step2n x (nbr-step2 x)))))
    :hints (("Subgoal 2"
	     :use (:instance
		   nbr-step2
		   (x (step2 x))
		   (n (+ -1 (nbr-step2 x))))))))

 (local
  (defthm
    f2n-step2
    (implies (and (test2 (step2n x n))
		  (test2 (step2n x m)))
	     (equal (f2n x n)(f2n x m)))
    :rule-classes nil))

 (defthm
   g2a-g2-def
   (equal (g2a x)
	  (if (test2 x)
	      (base2 x)
	      (g2a (step2 x))))
   :hints (("Subgoal 1"
	    :expand (f2n x (nbr-step2 x)))
	   ("Subgoal 1.2"
	    :use (:instance
		  f2n-step2
		  (x (step2 x))
		  (n (+ -1 (nbr-step2 x)))
		  (m (nbr-step2 (step2 x))))))
   :rule-classes nil)

 (defthm
   h2a-h2-def
   (equal (h2a x)
	  (if (test2 x)
	      (base2 x)
	      (h2a (step2 x))))
   :hints (("Subgoal 1"
	    :expand (f2n x (nbr-step2 x)))
	   ("Subgoal 1.2"
	    :use (:instance
		  f2n-step2
		  (x (step2 x))
		  (n (+ -1 (nbr-step2 x)))
		  (m (nbr-step2 (step2 x))))))
   :rule-classes nil)
 ) ;; end encapsulate

(defthm
  g2a=h2a
  (equal (g2a x)
	 (h2a x))
  :rule-classes nil
  :hints (("Goal"
	   :by (:functional-instance
		g2=h2
		(g2 g2a)
		(h2 h2a)))
	  ("Subgoal 2"
	   :by h2a-h2-def)
	  ("Subgoal 1"
	   :by g2a-g2-def)))

(defthm
  recursion-halts
  (test2 (step2n x (nbr-step2 x)))
  :hints (("Goal"
	   :use g2a=h2a)))

(defun-sk
  exists-n-recursion-halts (x)
  (exists n (test2 (step2n x n))))

(defthm
  exist-n-recursion-halts-thm
  (exists-n-recursion-halts x)
  :hints (("Goal"
	   :use (:instance
		 exists-n-recursion-halts-suff
		 (n (nbr-step2 x))))))

;; This concludes the proof of THEOREM 2.
;; = = = = = = = = = = = = = = = = = = = =
;; The following example shows that the above SKIP-PROOFS
;; renders ACL2 unsound!

(defpun
  k (x)
  (if (zp x)
      0
      (k (+ 1 x))))

(defun
  k-step-n (x n)
  (if (zp n)
      x
      (k-step-n (+ 1 x)(- n 1))))

(defun-sk
  exists-n-recursion-halts-k (x)
  (exists n (zp (k-step-n x n))))

(defthm
  exist-n-recursion-halts-k-thm
  (exists-n-recursion-halts-k x)
  :rule-classes nil
  :hints (("Goal"
	   :by (:functional-instance
		exist-n-recursion-halts-thm
		(test2 zp)
		(base2 (lambda (x) 0))
		(step2 (lambda (x)(+ 1 x)))
		(step2n k-step-n)
		(f2 k)
		(exists-n-recursion-halts
		 exists-n-recursion-halts-k)
		(exists-n-recursion-halts-witness
		 exists-n-recursion-halts-k-witness)))))

(defthm
  k-never-halts-on-non-zp
  (implies (not (zp x))
	   (not (zp (k-step-n x n))))
  :rule-classes nil)

(thm
 nil
 :hints (("Goal"
	  :use ((:instance
		 exist-n-recursion-halts-k-thm
		 (x 1))
		(:instance
		 k-never-halts-on-non-zp
		 (x 1)
		 (n (exists-n-recursion-halts-k-witness 1)))))))

;; Summary
;; Form:  ( THM ...)
;; Rules: ((:COMPOUND-RECOGNIZER ACL2::ZP-COMPOUND-RECOGNIZER)
;;         (:DEFINITION EXISTS-N-RECURSION-HALTS-K)
;;         (:DEFINITION NOT)
;;         (:EXECUTABLE-COUNTERPART NOT)
;;         (:EXECUTABLE-COUNTERPART ZP)
;;         (:TYPE-PRESCRIPTION K-STEP-N))
;; Warnings:  None
;; Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)

;; Proof succeeded.
|#
;; The above example demonstrates that the application of THEOREM 2
;; via FUNCTIONAL INSTANTIATION is NOT to be trusted. However, by
;; carefully following the proof of THEOREM 2, consistent results can
;; be obtained. This is illustrated by showing that the tail recursion
;; in the definition of f1 always terminates.
;; -------------------------------------------------------------------------
;; COROLLARY 2. The tail recursion in the definition of f1,

;;              (defun
;;                f1 (x)
;;                (if (test1 x)
;;                    (base1 x)
;;                    (f1 (step1 x)))),

;; always terminates.

;; That is,
;; For all inputs x, there is an n such that (test1 (step1n x n)) is not NIL.

;; The ``proof'' given above for THEOREM 2 is carefully followed, replacing
;; f2 with f1, g2 with g1, h2 with h1, step2 with step1, etc.
;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;; PROOF OF COROLLARY 2.

;; Prove the recursion always halts in f1.
;; That is, prove ((FORALL x)((EXISTS n)(test1 (step1n x n))))

;; At this point the proof closely follows the proof, given by
;; J and Pete, in their DEFPUN work, that tail recursive definitions
;; are always satisfied by at least one total ACL2 function.

(defun
  step1n (x n)
  (if (zp n)
      x
      (step1n (step1 x)(- n 1))))

(defchoose
  nbr-step1 (n)(x)
  (test1 (step1n x n)))

(defun
  f1n (x n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (test1 x))
      (base1 x)
      (f1n (step1 x)(- n 1))))

(defun
  g1a (x)
  (if (test1 (step1n x (nbr-step1 x)))
      (f1n x (nbr-step1 x))
      nil))

(defun
  h1a (x)
  (if (test1 (step1n x (nbr-step1 x)))
      (f1n x (nbr-step1 x))
      t))

;; This encapsulate merely hides some tedious details of the proof.
(encapsulate
 nil

 (local
  (defthm
    test1-nbr-step1
    (implies (test1 x)
	     (test1 (step1n x (nbr-step1 x))))
    :hints (("Goal"
	     :use (:instance
		   nbr-step1
		   (n 0))))))

 (local
  (defthm
    test1-g1a-def
    (implies (test1 x)
	     (equal (g1a x)(base1 x)))))

 (local
  (defthm
    test1-h1a-def
    (implies (test1 x)
	     (equal (h1a x)(base1 x)))))

 (local
  (defthm
    open-step1n
    (implies (and (integerp n)
		  (> n 0))
	     (equal (step1n x n)
		    (step1n (step1 x)(- n 1))))))

 (local
  (defthm +1-1
    (equal (+ -1 +1 x) (fix x))))

 (local
  (defthm
    step1-step1n-nbr-step1
    (implies (test1 (step1n (step1 x)(nbr-step1 (step1 x))))
	     (test1 (step1n x (nbr-step1 x))))
    :hints (("Goal"
	     :use (:instance
		   nbr-step1
		   (n (+ 1 (nfix (nbr-step1 (step1 x))))))))
    :rule-classes :forward-chaining))

 (local
  (defthm
    not-test1-nbr-step1
    (implies (not (test1 x))
	     (iff (test1 (step1n (step1 x)(nbr-step1 (step1 x))))
		  (test1 (step1n x (nbr-step1 x)))))
    :hints (("Subgoal 2"
	     :use (:instance
		   nbr-step1
		   (x (step1 x))
		   (n (+ -1 (nbr-step1 x))))))))

 (local
  (defthm
    f1n-step1
    (implies (and (test1 (step1n x n))
		  (test1 (step1n x m)))
	     (equal (f1n x n)(f1n x m)))
    :rule-classes nil))

 (defthm
   g1a-g1-def
   (equal (g1a x)
	  (if (test1 x)
	      (base1 x)
	      (g1a (step1 x))))
   :hints (("Subgoal 1"
	    :expand (f1n x (nbr-step1 x)))
	   ("Subgoal 1.2"
	    :use (:instance
		  f1n-step1
		  (x (step1 x))
		  (n (+ -1 (nbr-step1 x)))
		  (m (nbr-step1 (step1 x))))))
   :rule-classes nil)

 (defthm
   h1a-h1-def
   (equal (h1a x)
	  (if (test1 x)
	      (base1 x)
	      (h1a (step1 x))))
   :hints (("Subgoal 1"
	    :expand (f1n x (nbr-step1 x)))
	   ("Subgoal 1.2"
	    :use (:instance
		  f1n-step1
		  (x (step1 x))
		  (n (+ -1 (nbr-step1 x)))
		  (m (nbr-step1 (step1 x))))))
   :rule-classes nil)
 ) ;; end encapsulate

(defthm
  g1a=h1a
  (equal (g1a x)
	 (h1a x))
  :rule-classes nil
  :hints (("Goal"
	   :by (:functional-instance
		g1=h1
		(g1 g1a)
		(h1 h1a)))
	  ("Subgoal 2"
	   :by h1a-h1-def)
	  ("Subgoal 1"
	   :by g1a-g1-def)))

(defthm
  recursion-halts-f1
  (test1 (step1n x (nbr-step1 x)))
  :hints (("Goal"
	   :use g1a=h1a)))

(defun-sk
  exists-n-recursion-halts-f1 (x)
  (exists n (test1 (step1n x n))))

(defthm
  exist-n-recursion-halts-f1-thm
  (exists-n-recursion-halts-f1 x)
  :hints (("Goal"
	   :use (:instance
		 exists-n-recursion-halts-f1-suff
		 (n (nbr-step1 x))))))

;; This concludes the proof of COROLLARY 2.
;; -------------------------------------------------------------------------
;; Let test3, base3, and step3 be unary functions.

;; Let (step3n x n) be the result of applying step3 n times with initial input x.
;; That is,

;; (defun
;;   step3n (x n)
;;   (if (zp n)
;;       x
;;       (step3n (step3 x)(- n 1))))

;; The tail recursion in the proposed definition

;; (defun
;;   f3 (x)
;;   (if (test3 x)
;;       (base3 x)
;;       (f3 (step3 x))))

;; is said to always terminate provided the following holds.

;; For all inputs x, there is an n such that (test3 (step3n x n)) is not NIL.

;; The tail recursion in the proposed definition of f3 is said to satisfy
;; the meaure conjecture for nonnegative-integer-valued measure im provided
;; the following goals are true.

;; (AND (integerp (im x))               ; Goal 1
;;      (>= (im x) 0)                   ; Goal 2
;;      (IMPLIES (NOT (test3 x))        ; Goal 3
;;               (< (im (step3 x))
;;                  (im x))).

;; THEOREM 3. If the tail recursion proposed in the definition of f3 always
;;            terminates, then the tail recursion satisfies the measure
;;            conjecture for some nonnegative-integer-valued measure m.

;;             That is, (IMPLIES ((FORALL x)
;;                                ((EXISTS n)(test3 (step3n x n))))
;;                               ((EXISTS FUNCTION im)
;;                                ((FORALL x)(AND (integerp (im x))
;;                                                (>= (im x) 0)
;;                                                (IMPLIES (NOT (test3 x))
;;                                                         (< (im (step3 x))
;;                                                            (im x)))))))
;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;; PROOF OF THEOREM 3.

;; Assume the hypothesis of THEOREM 3.
;; That is, assume

;;           ((FORALL x)
;;            ((EXISTS n)(test3 (step3n x n))))

;; Replace this assumption with the result of Skolemizing the assumption.

;; ((EXISTS FUNCTION n)
;;  ((FORALL x)(test3 (step3n x (n x)))))

;; Let test3, step3, and n be functions satisfying the given hypothesis.

(encapsulate
 (((test3 *) => *)
  ((step3 *) => *)
  ((n     *) => *))

 (local (defun test3 (x)
	  (zp x)))

 (local (defun step3 (x)
	  (- x 1)))

 (defun
   step3n (x n)
   (if (zp n)
       x
       (step3n (step3 x)(- n 1))))

 (local (defun n (x)
	  (if (zp x)
	      0
	      x)))

 (defthm
   recursion-halts-f3
   (test3 (step3n x (n x))))
 ) ;; end encapsulate

;; Prove the conclusion of THEOREM 3.
;; That is, prove the following

;; ((EXISTS FUNCTION im)
;;  ((FORALL x)(AND (integerp (im x))
;;                  (>= (im x) 0)
;;                  (IMPLIES (NOT (test3 x))
;;                           (< (im (step3 x))
;;                              (im x)))))))

(defun
  n1 (x)
  (nfix (n x)))

(defthm
  recursion-halts-f3-a
  (test3 (step3n x (n1 x)))
  :hints (("Goal"
	   :in-theory (disable recursion-halts-f3)
	   :use recursion-halts-f3)))

(in-theory (disable n1))

(defthm
  n1-0-test3
  (implies (equal (n1 x) 0)
	   (test3 x))
  :hints (("Goal"
	   :in-theory (disable recursion-halts-f3-a)
	   :use recursion-halts-f3-a)))

(defun
  im-loop (x k)
  (declare (xargs :measure (let ((k (nfix k)))
			     (cond ((>= k (n1 x))
				    0)
				   ((test3 (step3n x k))
				    0)
				   (t (- (n1 x) k))))))
  (let ((k (nfix k)))
    (cond ((>= k (n1 x))
	   (n1 x))
	  ((test3 (step3n x k))
	   k)
	  (t (im-loop x (+ 1 k))))))

(defthm
  test3-step3n-im-loop
  (test3 (step3n x (im-loop x k))))

(defthm
  im-loop-0-test3
  (implies (equal (im-loop x k) 0)
	   (test3 x)))

(defthm
  im-loop-is-least
  (implies (and (integerp k)
		(>= k 0)
		(integerp i)
		(<= k i)
		(< i (im-loop x k)))
	   (not (test3 (step3n x i)))))

(defun
  im (x)
  (im-loop x 0))

(defthm
  test3-step3n-im
  (test3 (step3n x (im x))))

(defthm
  im-is-least
  (implies (and (integerp i)
		(<= 0 i)
		(< i (im x)))
	   (not (test3 (step3n x i))))
  :hints (("Goal"
	   :in-theory (disable im-loop-is-least)
	   :use (:instance
		 im-loop-is-least
		 (k 0)))))

(defthm
  pos-im
  (implies (not (test3 x))
	   (> (im x) 0))
  :rule-classes (:rewrite :linear))

(in-theory (disable im))

(defthm
  im-decreases-step3
  (implies (not (test3 x))
	   (< (im (step3 x))
	      (im x)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal"
	   :in-theory (disable test3-step3n-im
			       im-is-least)
	   :use (test3-step3n-im
		 (:instance
		  im-is-least
		  (x (step3 x))
		  (i (- (im x) 1)))))))

(defthm
  im-is-measure
  (AND (integerp (im x))
       (>= (im x) 0)
       (IMPLIES (NOT (test3 x))
		(< (im (step3 x))
		   (im x))))
  :rule-classes nil)

;; This concludes the proof of THEOREM 3.
;; -------------------------------------------------------------------------
;; Use the measure im to get ACL2 to accept the proposed definition of f3

;; (defun
;;   f3 (x)
;;   (if (test3 x)
;;       (base3 x)
;;       (f3 (step3 x))))

;; Let base3 be an arbitrary unary function.

(defstub
  base3 (*) => *)

(defun
  f3 (x)
  (declare (xargs :measure (im x)))
  (if (test3 x)
      (base3 x)
      (f3 (step3 x))))
;; -------------------------------------------------------------------------
#|
;; Let test4, base4, and step4 be unary functions.
;; Let (a) and (b) be constants.

;; Let (step4n x n) be the result of applying step4 n times with initial input x.
;; That is,

;; (defun
;;   step4n (x n)
;;   (if (zp n)
;;       x
;;       (step4n (step4 x)(- n 1))))

;; The tail recursion in the proposed definition

;; (defun
;;   f4 (x)
;;   (if (test4 x)
;;       (base4 x)
;;       (f4 (step4 x))))

;; is said to terminate on input (a) provided the following holds.

;; There is an n such that (test4 (step4n (a) n)) is not NIL.

;; THEOREM 4. If ACL2 can prove (EQUAL (f4 (a))(b)) from the defining
;;            axiom for the tail recursion defining f4, then the
;;            recursion terminates on input (a).

;;            That is, (IMPLIES
;;                      (((FORALL x)
;;                        (EQUAL (f4 x)
;;                               (if (test4 x)
;;                                   (base4 x)
;;                                   (f4 (step4 x))))) |= (EQUAL (f4 (a))(b)))
;;                      ((EXISTS n)(test4 (step4n (a) n))))
;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;; PROOF OF THEOREM 4.

;; Assume the hypothesis of THEOREM 4.
;; That is, assume

;; (EQUAL (f4 (a))(b)) is a logical consequence of the defining tail
;; recursive axiom for f4

;;    ((FORALL x)
;;     (EQUAL (f4 x)
;;            (if (test4 x)
;;                (base4 x)
;;                (f4 (step4 x)))))

;; Assume there is a function, called f4, with the desired definition.

(encapsulate
 (((test4 *) => *)
  ((base4 *) => *)
  ((step4 *) => *)
  ((f4 *)    => *))

 (local (defun test4 (x)
	  (zp x)))

 (local (defun base4 (x)
	  (declare (ignore x))
	  0))

 (local (defun step4 (x)
	  (- x 1)))

 (local (defun f4 (x)
	  (if (test4 x)
	      (base4 x)
	      (f4 (step4 x)))))

 (defthm
   f4-def
   (equal (f4 x)
	  (if (test4 x)
	      (base4 x)
	      (f4 (step4 x))))
   :rule-classes :definition)
 );; end encapsulate

;; Now, ensure that ACL2 can conclude the ``logical consequence'',
;; namely that (EQUAL (f4 (a))(b)).  This is done with a SKIP-PROOFS!

(defstub
  a () => *)

(defstub
  b () => *)

(skip-proofs
 (defthm
   f4-a=b
   (equal (f4 (a))
	  (b))
   :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; WARNING: This use of skip-proofs will render ACL2 unsound.
;; This is because the purported theorem f4-a=b is NOT really a
;; logical consequence of the constrained axiom f4-def.
;; [See below for a ``proof'' of NIL. Search for (defun k1 ...)]

;; However, the current proof would be sound in any circumstances
;; where f4-a=b does logically follow. For example, see the
;; application in the WyoM1 Correctness Without a Clock book, in
;; the file WyoM1-correct.lisp, that relates a correctness result
;; for a ``clockless'' tail recursive formal intepreter, used to
;; model the stack machine WyoM1, to the same result for a ``clocked''
;; version of a formal intepreter of WyoM1.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Prove the conclusion of THEOREM 4.
;; That is, prove the recursion halts for input (a).

;;  ((EXISTS n)(test4 (step4n (a) n)))

;; At this point the proof closely follows the proof, given by
;; J and Pete, in their DEFPUN work, that tail recursive definitions
;; are always satisfied by at least one total ACL2 function.

(defun
  step4n (x n)
  (if (zp n)
      x
      (step4n (step4 x)(- n 1))))

(defchoose
  nbr-step4 (n)(x)
  (test4 (step4n x n)))

(defun
  f4n (x n)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (test4 x))
      (base4 x)
      (f4n (step4 x)(- n 1))))

(defun
  f4a (x)
  (if (test4 (step4n x (nbr-step4 x)))
      (f4n x (nbr-step4 x))
      (if (equal (b) nil)
	  t
	  nil)))

;; This encapsulate merely hides some tedious details of the proof.
(encapsulate
 nil

 (local
  (defthm
    test4-nbr-step4
    (implies (test4 x)
	     (test4 (step4n x (nbr-step4 x))))
    :hints (("Goal"
	     :use (:instance
		   nbr-step4
		   (n 0))))))

 (local
  (defthm
    test4-f4a-def
    (implies (test4 x)
	     (equal (f4a x)(base4 x)))))

 (local
  (defthm
    open-step4n
    (implies (and (integerp n)
		  (> n 0))
	     (equal (step4n x n)
		    (step4n (step4 x)(- n 1))))))

 (local
  (defthm +1-1
    (equal (+ -1 +1 x) (fix x))))

 (local
  (defthm
    step4-step4n-nbr-step4
    (implies (test4 (step4n (step4 x)(nbr-step4 (step4 x))))
	     (test4 (step4n x (nbr-step4 x))))
    :hints (("Goal"
	     :use (:instance
		   nbr-step4
		   (n (+ 1 (nfix (nbr-step4 (step4 x))))))))
    :rule-classes :forward-chaining))

 (local
  (defthm
    not-test4-nbr-step4
    (implies (not (test4 x))
	     (iff (test4 (step4n (step4 x)(nbr-step4 (step4 x))))
		  (test4 (step4n x (nbr-step4 x)))))
    :hints (("Subgoal 2"
	     :use (:instance
		   nbr-step4
		   (x (step4 x))
		   (n (+ -1 (nbr-step4 x))))))))

 (local
  (defthm
    f4n-step4
    (implies (and (test4 (step4n x n))
		  (test4 (step4n x m)))
	     (equal (f4n x n)(f4n x m)))
    :rule-classes nil))

 (defthm
   f4a-f4-def
   (equal (f4a x)
	  (if (test4 x)
	      (base4 x)
	      (f4a (step4 x))))
   :hints (("Subgoal 3"
	    :expand (f4n x (nbr-step4 x)))
	   ("Subgoal 3.2"
	    :use (:instance
		  f4n-step4
		  (x (step4 x))
		  (n (+ -1 (nbr-step4 x)))
		  (m (nbr-step4 (step4 x))))))
   :rule-classes nil)
 ) ;; end encapsulate

(defthm
  f4a-a=b
  (equal (f4a (a))
	 (b))
  :rule-classes nil
  :hints (("Goal"
	   :by (:functional-instance
		f4-a=b
		(f4 f4a)))
	  ("Goal'"
	   :by f4a-f4-def)))

(defthm
  recursion-halts
  (test4 (step4n (a)(nbr-step4 (a))))
  :hints (("Goal"
	   :use f4a-a=b)))

(defun-sk
  exists-n-recursion-halts ()
  (exists n (test4 (step4n (a) n))))

(defthm
  exist-n-recursion-halts-thm
  (exists-n-recursion-halts)
  :hints (("Goal"
	   :use (:instance
		 exists-n-recursion-halts-suff
		 (n (nbr-step4 (a)))))))

;; This concludes the proof of THEOREM 4.
;; = = = = = = = = = = = = = = = = = = = =
;; The following example shows that the above SKIP-PROOFS
;; renders ACL2 unsound!

(defpun
  k1 (x)
  (if (zp x)
      0
      (k1 (+ 1 x))))

(defun
  k1-step-n (x n)
  (if (zp n)
      x
      (k1-step-n (+ 1 x)(- n 1))))

(defun-sk
  exists-n-recursion-halts-k1 ()
  (exists n (zp (k1-step-n 1 n))))

(defthm
  exist-n-recursion-halts-k1-thm
  (exists-n-recursion-halts-k1)
  :rule-classes nil
  :hints (("Goal"
	   :in-theory (disable exists-n-recursion-halts-k1)
	   :by (:functional-instance
		exist-n-recursion-halts-thm
		(test4 zp)
		(base4 (lambda (x) 0))
		(step4 (lambda (x)(+ 1 x)))
		(step4n k1-step-n)
		(f4 k1)
		(a (lambda () 1))
		(exists-n-recursion-halts
		 exists-n-recursion-halts-k1)
		(exists-n-recursion-halts-witness
		 exists-n-recursion-halts-k1-witness)))
	  ("Subgoal 3"
	   :in-theory (enable exists-n-recursion-halts-k1))))

(defthm
  k1-never-halts-on-non-zp
  (implies (not (zp x))
	   (not (zp (k1-step-n x n))))
  :rule-classes nil)

(thm
 nil
 :hints (("Goal"
	  :use (exist-n-recursion-halts-k1-thm
		(:instance
		 k1-never-halts-on-non-zp
		 (x 1)
		 (n (exists-n-recursion-halts-k1-witness)))))))

;; Summary
;; Form:  ( THM ...)
;; Rules: ((:DEFINITION EXISTS-N-RECURSION-HALTS-K1)
;;         (:DEFINITION NOT)
;;         (:EXECUTABLE-COUNTERPART NOT)
;;         (:EXECUTABLE-COUNTERPART ZP))
;; Warnings:  None
;; Time:  0.01 seconds (prove: 0.00, print: 0.01, other: 0.00)

;; Proof succeeded.
|#
;; The above example demonstrates that the application of THEOREM 4
;; via FUNCTIONAL INSTANTIATION is NOT to be trusted. However, by
;; carefully following the proof of THEOREM 4, consistent results can
;; be obtained. This is illustrated by showing how to relate
;; corrrectness results obtained using an interpreter without a clock
;; to the same results using an intepreter with a clock. See the
;; WyoM1 Correctness Without a Clock book in the file
;; WyoM1-correct.lisp
