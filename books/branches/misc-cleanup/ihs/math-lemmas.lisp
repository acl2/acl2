; math-lemmas.lisp -- more math lemmas for IHS
; Copyright (C) 1997  Computational Logic, Inc.

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    math-lemmas.lisp
;;;
;;;    Arthur Flatau
;;;    Computational Logic, Inc.
;;;    1717 West 6th Street, Suite 290
;;;    Austin, Texas 78703
;;;    (512) 322-9951
;;;    flatau@cli.com
;;;
;;;    Modified for ACL2 Version_2.6 by: 
;;;    Jun Sawada, IBM Austin Research Lab. sawada@us.ibm.com
;;;    Matt Kaufmann, kaufmann@cs.utexas.edu
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

;; This book is greatly simplified from the book that Bishop Brock used
;; with the same name.  Instead of constructing different lemmas than
;; Matt Kaufmann does for the arithmetic libriaries, we just use his
;; arithmetic libraries to the extent we can.  There are a few lemmas from
;; the original math-lemmas.lisp.

(in-package "ACL2")

(include-book "../arithmetic/top")
(include-book "ihs-init")

(deflabel math-lemmas
  :doc ":doc-section math-lemmas
  A book of theories about +, -, *, /, and EXPT, built on the
  arithmetic package of Matt Kaufmann.~/

  This book defines the following theories.
  ~/~/")

(defthm cancel-equal-+-*
  (and (equal (equal (+ x y) x)
	      (and (acl2-numberp x) (equal (fix y) 0)))
       (equal (equal (+ y x) x)
	      (and (acl2-numberp x) (equal (fix y) 0)))
       (equal (equal (* x y) x)
	      (and (acl2-numberp x)
		   (or (equal x 0) (equal y 1))))
       (equal (equal (* x y) y)
	      (and (acl2-numberp y)
		   (or (equal y 0) (equal x 1)))))
  :hints (("Goal" :in-theory (enable equal-*-x-y-x)))
  :doc ":doc-section cancel-equal-+-*
   Rewrite: x + y = x EQUAL y = 0;
            x * y = x EQUAL x = 0 or y = 1;
            also commutative forms.
   ~/~/~/")

(defthm normalize-equal-0
  (and (equal (equal (- x) 0) (equal (fix x) 0))
       (equal (equal (+ x y) 0) (equal (fix x) (- y)))
       (equal (equal (* x y) 0) (or (equal (fix x) 0) (equal (fix y) 0))))
  :doc ":doc-section normalize-equal-0
  Rewrite: -x = 0 EQUAL x = 0;
           x + y = 0 EQUAL x = -y;
           x * y = 0 EQUAL x = 0 or y = 0.
  ~/~/~/")

(deftheory acl2-numberp-algebra
  (union-theories
   (defun-theory
     '(EQUAL EQL = /= IFF FORCE BINARY-+ BINARY-* UNARY-- UNARY-/
	     ACL2-NUMBERP
             ;; 1+ 1- ; removed in 1.8
             ZEROP FIX ZP ZIP))
   '(eqlablep-recog
     commutativity-of-+ COMMUTATIVITY-OF-* inverse-of-+
     associativity-of-+ associativity-of-* commutativity-2-of-+
     commutativity-2-of-* unicity-of-0 functional-self-inversion-of-minus
     unicity-of-1 default-*-1 default-*-2
     default-<-1 default-<-2 default-+-1 default-+-2
     inverse-of-* functional-self-inversion-of-/ minus-cancellation-on-right
     minus-cancellation-on-left /-cancellation-on-left
     /-cancellation-on-right
     equal-*-x-y-y cancel-equal-+-* normalize-equal-0
     left-cancellation-for-* left-cancellation-for-+
     equal-minus-0 zero-is-only-zero-divisor
     equal-minus-minus equal-/-/ default-unary-minus equal-/ equal-*-/-2
     functional-commutativity-of-minus-*-left
     functional-commutativity-of-minus-*-right
     reciprocal-minus equal-minus-minus distributivity-of-/-over-*
     distributivity
     distributivity-of-minus-over-+))
  :doc ":doc-section math-lemmas
  A basic theory of algebra for all ACL2-NUMBERPs.
  ~/
  
  This theory includes the following lemmas:
  ~/

  The ACL2-NUMBERP-ALGEBRA theory is designed to be a simple, compact basis
  for building other theories.  This theory contains a minimal set of rules
  for basic algebraic manipulation including associativity and commutativity,
  simplification, cancellation, and normalization.  It is extended by the
  theories RATIONALP-ALGEBRA and INTEGERP-ALGEBRA to include selected linear
  rules and rules for integers respectively.  This theory also contains the
  DEFUN-THEORY (which see) of all built-in function symbols that would
  normally occur during reasoning about the ACL2-NUMBERPs.

  We used keep this theory (and book) separate but roughly equal to the books
  maintained by Matt K. in order to have a solid, simple, and predictable
  foundation on which to build the rest of the books in the IHS
  hierarchy.  However it was decided that this was too much trouble
  and we just select the rules of Matt K. that we want.~/

  :cite cancel-equal-+-*")

(defthm rewrite-linear-equalities-to-iff
   (equal (equal (< w x) (< y z))
	  (iff (< w x) (< y z)))
   :doc ":doc-section rewrite-linear-equalities-to-iff
    Rewrite: (EQUAL (< w x) (< y z)) = (IFF (< w x) (< y z)).
    ~/~/

   Some proofs of linear equalities don't work when presented as equalities
   because they need to be proved by linear arithmetic, but linear arithmetic
   only works at the literal level.  This lemma allows you to state the
   equality as an equality rewrite rule, but breaks the equality into
   literals for the proof.")

(defthm normalize-<-minus-/
  (and (equal (< (- x) 0)     (< 0 x))
       (equal (< 0 (- x))     (< x 0))

       (equal (< (- x) (- y)) (> x y))

       (implies (real/rationalp x)
		(and (equal (< 0 (/ x)) (< 0 x))
		     (equal (< (/ x) 0) (< x 0)))))
  :doc ":doc-section normalize-<-minus-/
  Rewrite: -x < 0 EQUAL 0 < x;
          -x < -y EQUAL y < x;
          0 < 1/x EQUAL 0 < x; 
          1/x < 0 EQUAL x < 0.
  ~/~/~/")

(deftheory rationalp-algebra
  (union-theories
   (theory 'ACL2-NUMBERP-ALGEBRA)
   (union-theories
    (defun-theory '(NUMERATOR DENOMINATOR < ABS PLUSP MINUSP MIN MAX SIGNUM
			      RFIX))
    '(equal-*-/-1 *-r-denominator-r
      default-denominator numerator-minus
      equal-denominator-1 numerator-when-integerp
      <-y-*-y-x <-*-y-x-y <-*-/-right <-*-/-right-commuted
      <-*-/-left <-*-/-left-commuted
      <-*-left-cancel <-0-minus /-preserves-positive /-preserves-negative
      rewrite-linear-equalities-to-iff
      normalize-<-minus-/
      <-unary-/-negative-left <-unary-/-negative-right
      <-unary-/-positive-left <-unary-/-positive-right)))
  :doc ":doc-section math-lemmas
  A basic theory of algebra for all RATIONALPs.
  ~/

  This theory includes the ACL2-NUMBERP-ALGEBRA theory, along with the
  following lemmas about the rationals:
  ~/

  This theory extends ACL2-NUMBERP-ALGEBRA to include theorems about
  NUMERATOR and DENOMINATOR, and simple cancellationn and normalization
  theorems and other simple theorems for inequalities.")

(defthm normalize-<-/-to-*
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(not (equal y 0)))
	   (and (equal (< x (/ y)) (if (< y 0) (< 1 (* x y)) (< (* x y) 1)))
		(equal (< (/ y) x) (if (< y 0) (< (* x y) 1) (< 1 (* x y))))))
  :doc ":doc-section normalize-<-/-to-*
  Rewrite: Replace x < 1/y with x*y < 1 or x*y > 1, based on the sign of y.
  ~/~/~/")

(defthm normalize-<-/-to-*-3
  (implies (and (real/rationalp x)
		(real/rationalp y)
		(real/rationalp z)
		(not (equal z 0)))
	   (and (equal (< x (* y (/ z)))
		       (if (< z 0) (< y (* x z)) (< (* x z) y)))
		(equal (< x (* (/ z) y))
		       (if (< z 0) (< y (* x z)) (< (* x z) y)))
		(equal (< (* y (/ z)) x)
		       (if (< z 0) (< (* x z) y) (< y (* x z))))
		(equal (< (* (/ z) y) x)
		       (if (< z 0) (< (* x z) y) (< y (* x z))))))
  :hints
  (("Goal"
    ;;  Disable base lemmas and use cancel-<-* instead.
    :in-theory (disable <-unary-/-negative-left <-unary-/-negative-right
			<-unary-/-positive-left <-unary-/-positive-left
			<-*-right-cancel)
    :use (:instance <-*-right-cancel (x (* x z)) (y y) (z (/ z)))))
  :doc ":doc-section normalize-<-/-to-*-3
  Rewrite: Replace x < y/z and x > y/z with x*z < y or x*z > y, depending on
  the sign of z.
  ~/~/~/")

(defthm normalize-equal-/-to-*
  (implies (and (acl2-numberp z)
		(not (equal z 0)))
	   (and (equal (equal x (* y (/ z)))
		       (and (acl2-numberp x)
			    (equal (* x z) (fix y))))
		(equal (equal x (* (/ z) y))
		       (and (acl2-numberp x)
			    (equal (* x z) (fix y))))))
  :doc ":doc-section normalize-equal-/-to-*
  Rewrite: Replace x = y/z with x*z = y.
  ~/~/~/")

(deftheory prefer-*-to-/
  '(normalize-<-/-to-* normalize-<-/-to-*-3 normalize-equal-/-to-*)
  :doc ":doc-section math-lemmas
  A small theory of lemmas that eliminate / in favor of *.
  ~/

  This is a small theory of rules that eliminate / from equalites and
  inequalities in favor of *, e.g., x < y/z is rewritten to x*y < z for
  positive z.  This theory is comaptible with the ALGEBRA theories, i.e., it
  should not cause looping.  The following lemmas are included:
  ~/

  These rules are not included in RATIONALP-ALGEBRA bacause it is not clear
  that we should prefer x*y < z to x < y/z, or x*y = z to x = y/z. In the
  case of the lemma NORMALIZE-EQUAL-/-TO-*, there is no reason to suspect
  that `y' is a better term than `x'; in fact, the whole point of the proofs
  using these libraries may have to do with a representation involving /.
  So, unless someone provides a convincing reason to the contrary, these
  rules will remain separate from the RATIONALP-ALGEBRA theory.

  Note, however, that in certain cases this theory is just the thing that
  needs to be ENABLEd to make the proofs work.  Keep it in mind.~/

  :cite normalize-<-/-to-* 
  :cite normalize-<-/-to-*-3
  :cite normalize-equal-/-to-*
  ")

(in-theory (disable prefer-*-to-/))

(defthm integerp-+-minus-*
  (and
   (implies
    (integerp i)
    (integerp (- i)))

   (implies
    (and (integerp i)
	 (integerp j))
    (and
     (integerp (+ i j))
     (integerp (- i j))
     (integerp (* i j)))))
  :doc ":doc-section integerp-+-minus-*
  Rewrite: -i, i + j, i - j, and i * j are integers, when i and j are
  integers.
  ~/~/

  The system has powerful enough type reasoning to `get' these facts
  automatically most of the time.  There are cases, however, where we need to
  bring the full power of the rewriter to bear on the problem.  In general
  one would like to keep lemmas like this to a minimum so as to avoid
  swamping the rewriter.~/")

(deftheory integerp-algebra
  (union-theories
   (theory 'RATIONALP-ALGEBRA)
   (union-theories
    (defun-theory '(INTEGERP INTEGER-ABS))
    '(integerp-+-minus-* integerp==>denominator=1 <-minus-zero natp-rw posp-rw)))
  :doc ":doc-section math-lemmas
  A basic theory of algebra for all INTEGERPs.
  ~/

  This theory consists of the ACL2-NUMBERP-ALGEBRA and RATIONALP-ALGEBRA
  theories, aloing with the follwing lemmas about the integers.
  ~/
 
  This theory extends ACL2-RATIONALP-ALGEBRA to include theorems about
  NUMERATOR and DENOMINATOR for integers, and other special theorems about
  integers.")

(deftheory expt-algebra
  '((expt) (:type-prescription expt)
    expt-type-prescription-nonzero
    expt-type-prescription-positive
    expt-type-prescription-integerp
    right-unicity-of-1-for-expt functional-commutativity-of-expt-/-base
    expt-minus exponents-add exponents-multiply
    expt->-1 
    expt-is-increasing-for-base>1 expt-is-decreasing-for-pos-base<1
    expt-is-weakly-increasing-for-base>1
    expt-is-weakly-decreasing-for-pos-base<1)
    :doc ":doc-section math-lemmas
  A theory of EXPT which is compatible with the ALGEBRA theories.~/

  This theory contains the following documeted lemmas:
  ~/

  This theory contains :TYPE-PRESCRIPTIONS, simpification, normalization and
  selected :LINEAR rules for EXPT.  This theory will not be useful unless the
  INTEGERP-ALGEBRA theory, or something similar is ENABLEd.")

(deftheory ihs-math
  (union-theories (theory 'integerp-algebra)
		  (theory 'expt-algebra))
  :doc ":doc-section math-lemmas
  The default theory of +, -, *, /, and EXPT for the IHS library.
  ~/

  This theory simply consists of the theories INTEGERP-ALGEBRA and
  EXPT-ALGEBRA. 
  ~/

  This theory is the default theory exported by this book.  This theory will
  normally be ENABLEd by every book in the IHS library.~/

  :cite integerp-algebra
  :cite expt-algebra
  ")
