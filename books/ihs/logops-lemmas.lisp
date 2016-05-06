; logops-lemmas.lisp  --  lemma support for logical operations on integers
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    logops-lemmas.lisp
;;;
;;;    This book, along with "logops-definitions", includes a theory of the
;;;    Common Lisp logical operations on numbers, a portable implementation
;;;    of the Common Lisp byte operations, and extensions to those theories.
;;;    This book contains a few definitions (of induction schemes) in
;;;    addition to the lemmas.
;;;
;;;    Bishop Brock
;;;    Computational Logic, Inc.
;;;    1717 West Sixth Street, Suite 290
;;;    Austin, Texas 78703
;;;    (512) 322-9951
;;;    brock@cli.com
;;;
;;;    Modified for ACL2 Version_2.6 by:
;;;    Jun Sawada, IBM Austin Research Lab. sawada@us.ibm.com
;;;    Matt Kaufmann, kaufmann@cs.utexas.edu
;;;
;;;    Modified for ACL2 Version_2.7 by:
;;;    Matt Kaufmann, kaufmann@cs.utexas.edu
;;;
;;;    Modified October 2014 by Jared Davis <jared@centtech.com>
;;;    Ported documentation to XDOC
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")

;;;****************************************************************************
;;;
;;;    ENVIRONMENT -- All of the rules necessary to prove the theorems of this
;;;    book.
;;;
;;;****************************************************************************

;;;  Global rules.

(include-book "ihs-init")
(include-book "ihs-theories")
(local (include-book "math-lemmas"))
(local (include-book "quotient-remainder-lemmas"))
(include-book "logops-definitions")
(include-book "std/util/defrule" :dir :system)

(local (in-theory nil))

; From ihs-theories.
(local (in-theory (enable basic-boot-strap)))

; From math-lemmas
(local (in-theory (enable ihs-math)))

; From quotient-remainder-lemmas
(local (in-theory (enable quotient-remainder-rules)))

; From logops-definitions
(local (in-theory (enable logops-definitions-theory)))


;;;****************************************************************************
;;;
;;;    Introduction
;;;
;;;****************************************************************************

(defxdoc logops-lemmas
  :parents (logops)
  :short "A book of lemmas about logical operations on numbers.")

(deflabel begin-logops-lemmas)


;;;****************************************************************************
;;;
;;;    Local Lemmas
;;;
;;;****************************************************************************

;  The rules that show (EXPT r i) <= (EXPT r j) in the general case aren't
;  useful as linear rules due to the free variable problem.

(local
 (defthm <-mod-expt-2-crock
   (implies
    (and (not (< size1 size))
	 (not (< size 0))
	 (integerp size1)
	 (integerp size)
	 (integerp i))
    (< (mod i (expt 2 size))
       (expt 2 size1)))
   :hints
   (("Goal"
     :in-theory (disable expt-is-weakly-increasing-for-base>1)
     :use ((:instance expt-is-weakly-increasing-for-base>1
		      (r 2) (i size) (j size1)))))))

;  We need this as several special rules because we need to be able to satisfy
;  the hypotheses by `type reasoning'.

(local
 (defthm integerp-expt/expt
   (implies
    (and (>= i j)
	 (not (equal r 0))
	 (integerp i)
	 (integerp j)
	 (integerp r))
    (integerp (* (/ (expt r j)) (expt r i))))
   :rule-classes
   ((:type-prescription)
    (:type-prescription :corollary
			(implies (and (< j i)
				      (not (equal r 0))
				      (integerp r)
				      (integerp i)
				      (integerp j))
				 (integerp (* (expt r i) (/ (expt r j))))))
    (:type-prescription :corollary
			(implies (and (not (< i j))
				      (not (equal r 0))
				      (integerp r)
				      (integerp i)
				      (integerp j))
				 (integerp (* (expt r i) (/ (expt r j))))))
    (:type-prescription :corollary
			(implies (and (< j i)
				      (not (equal r 0))
				      (integerp r)
				      (integerp i)
				      (integerp j))
				 (integerp (* (/ (expt r j)) (expt r i))))))
   :hints (("Goal" :in-theory (disable expt-type-prescription-integerp)
	    :use ((:instance expt-type-prescription-integerp
					  (r r) (i (- i j))))))))

;;;  Fri Feb 10 15:10:05 1995 bb -- Something VERY fishy is going on here.
;;;  Why was this suddenly needed?

(local
 (defthm integerp-expt-minus
   (implies
    (and (integerp size1)
	 (not (< size1 0))
	 (integerp size)
	 (< size1 size))
    (integerp (expt 2 (+ size (- size1)))))
   :rule-classes :type-prescription))

(local
 (defthm not-integerp-/x
   (implies
    (> x 1)
    (not (integerp (/ x))))
   :rule-classes :type-prescription
   :hints
   (("Goal"
     :in-theory (disable <-*-right-cancel
			 <-unary-/-positive-right
			 <-*-y-x-y
			 <-y-*-y-x)
     :use ((:instance <-unary-/-positive-right (y 1) (x (/ x))))))))

(local
 (defthm not-integerp-expt
   (implies
    (and (< 0 i)
	 (< 1 r)
	 (integerp r)
	 (integerp i))
    (not (integerp (/ (expt r i)))))
   :rule-classes :type-prescription
   :hints
   (("Goal"
     :induct (expt r i)
     :in-theory (enable expt ifix)))))

; We leave these local here because we don't want to swamp linear with every
; variant of inequalties about FLOOR and MOD.

(local
 (defthm mod-bounds-x
   (implies
    (and (>= x 0)
	 (> y 0)
	 (qr-guard x y))
    (<= (mod x y) x))
   :rule-classes
   ((:linear :trigger-terms ((mod x y))))
   :hints
   (("Goal"
     :in-theory (enable linearize-mod)))))

(local
 (defthm floor-bounds-x
   (implies
    (and (>= x 0)
	 (>= y 1)
	 (qr-guard x y))
    (<= (floor x y) x))
   :hints
   (("Goal"
     :in-theory (disable floor-recursion)
     :use ((:instance floor-recursion))))))

;  DISABLE theories implicated in :LINEAR thrashing.

(local (in-theory (disable floor-type-linear mod-type-linear floor-bounded-by-/)))

;  Some very useful results

(local
 (defthm loghead-logapp-expansion-lemma
   (implies
    (and (integerp i) (integerp j)
	 (integerp size1) (not (< size1 0))
	 (integerp size) (not (< size 0))
	 (<= size size1))
    (and
     (equal (mod (+ (* j (expt 2 size))
		    (mod i (expt 2 size)))
		 (expt 2 size1))
	    (+ (mod i (expt 2 size))
	       (* (expt 2 size) (mod j (expt 2 (- size1 size))))))
     (equal (mod (+ (mod i (expt 2 size))
		    (* (expt 2 size) j))
		 (expt 2 size1))
	    (+ (mod i (expt 2 size))
	       (* (expt 2 size) (mod j (expt 2 (- size1 size))))))))
   :hints
   (("Goal"
     :in-theory (disable mod-x+i*k-i*j)
     :use ((:instance mod-x+i*k-i*j
		      (x (mod i (expt 2 size))) (i (expt 2 size))
		      (k j) (j (expt 2 (- size1 size)))))))))

(local
 (defthm logtail-logapp-expansion-lemma
   (implies
    (and (integerp i) (integerp j)
	 (integerp size1) (not (< size1 0))
	 (integerp size) (not (< size 0))
	 (<= size size1))
    (and
     (equal (floor (+ (* j (expt 2 size))
		    (mod i (expt 2 size)))
		 (expt 2 size1))
	    (floor j (expt 2 (- size1 size))))))
   :hints
   (("Goal"
     :in-theory (disable floor-x+i*k-i*j)
     :use ((:instance floor-x+i*k-i*j
		      (x (mod i (expt 2 size))) (i (expt 2 size))
		      (k j) (j (expt 2 (- size1 size)))))))))


(local
 (defthm integerp-*-2-fact
   (implies
    (and (integerp (* i j))
	 (integerp k))
    (integerp (* i j k)))
   :rule-classes :type-prescription
   :hints
   (("Goal"
     :use ((:instance integerp-+-minus-* (i (* i j)) (j k)))))))

(local
 (defthm logtail-loghead-expansion-lemma
   (implies
    (and (real/rationalp x)
	 (integerp i)
	 (integerp j)
	 (>= i 0)
	 (>= j 0))
    (equal (floor (mod x (expt 2 i)) (expt 2 j))
	   (if (< j i)
	       (mod (floor x (expt 2 j))
		    (expt 2 (- i j)))
	     0)))
   :hints
   (("Goal"
     :do-not '(eliminate-destructors)
     :in-theory (set-difference-theories
		 (enable mod)
		 '(rewrite-floor-mod mod-bounded-by-modulus mod-type
				     expt-is-weakly-increasing-for-base>1))
     :use ((:instance mod-bounded-by-modulus (x x) (y (expt 2 i)))
	   (:instance (:linear mod-type . 4) ;(MOD x y) >= 0.
		      (x x) (y (expt 2 i)))
	   (:instance expt-is-weakly-increasing-for-base>1
		      (r 2) (i i) (j j)))))))


;;;****************************************************************************
;;;
;;;   Lemmas, Round 1 -- A simple theory of ASH, LOGNOT, LOGAND, and LOGIOR.
;;;   Also a lemma about the LOGOPS-BIT-FUNCTIONS.
;;;
;;;****************************************************************************

(local (in-theory (enable ash lognot lognotu logand logior logxor logeqv
			  logorc1 ifix nfix)))

;;;  ASH

(defsection ihs/ash-lemmas
  :parents (ash logops-lemmas)
  :short "Lemmas about @(see ash) from the @(see logops-lemmas) book."

  (defthm ash-0
    (implies (zip i)
             (equal (ash i count)
                    0))))


(defsection ihs/lognot-lemmas
  :parents (lognot logops-lemmas)
  :short "Lemmas about @(see lognot) from the @(see logops-lemmas) book."

  (defthm lognot-lognot
    (implies (case-split (integerp i))
             (equal (lognot (lognot i))
                    i)))

  (defthm cancel-equal-lognot
    (equal (equal (lognot i) (lognot j))
           (equal (ifix i) (ifix j)))
    :rule-classes
    ((:rewrite)
     (:rewrite :corollary (implies (and (syntaxp (constant-syntaxp j))
                                        (integerp j))
                                   (equal (equal (lognot i) j)
                                          (equal (ifix i) (lognot j)))))))

  (theory-invariant
   (implies
    (active-runep '(:rewrite cancel-equal-lognot . 2))
    (active-runep '(:executable-counterpart lognot)))))



(defsection ihs/lognotu-lemmas
  :parents (lognotu logops-lemmas)
  :short "Lemmas about @(see lognotu) from the @(see logops-lemmas) book."

  (defthm lognotu-lognotu
    (implies (and (<= size1 size)
                  (>= size1 0)
                  (integerp size1)
                  (lognotu-guard size i))
             (equal (lognotu size1 (lognotu size i))
                    (loghead size1 i)))
    :hints (("Goal" :in-theory (enable loghead))))

  (defthm cancel-equal-lognotu
    (implies (and (unsigned-byte-p size i)
                  (unsigned-byte-p size j))
             (equal (equal (lognotu size i) (lognotu size j))
                    (equal i j)))
    :hints
   (("Goal" :in-theory (enable unsigned-byte-p integer-range-p lognot loghead)))))



(defsection ihs/logand-lemmas
  :parents (logand logops-lemmas)
  :short "Lemmas about @(see logand) from the @(see logops-lemmas) book."

  (defthm commutativity-of-logand
    (equal (logand i j)
           (logand j i)))

  (defthm simplify-logand
    (and (equal (logand 0 i) 0)
         (equal (logand -1 i) (ifix i)))))



(defsection ihs/logior-lemmas
  :parents (logior logops-lemmas)
  :short "Lemmas about @(see logior) from the @(see logops-lemmas) book."

  (defthm commutativity-of-logior
    (equal (logior i j)
           (logior j i)))

  (defthm simplify-logior
    (and (equal (logior 0 i) (ifix i))
         (equal (logior -1 i) -1))))


(defsection ihs/logxor-lemmas
  :parents (logxor logops-lemmas)
  :short "Lemmas about @(see logxor) from the @(see logops-lemmas) book."

  (defthm commutativity-of-logxor
    (equal (logxor i j) (logxor j i)))

  (defthm simplify-logxor
    (and (equal (logxor 0 i) (ifix i))
         (equal (logxor -1 i) (lognot i)))))

(defsection ihs/logite-lemmas
  :parents (logite logops-lemmas)
  :short "Lemmas about @(see logite) from the @(see logops-lemmas) book."

  (defthm simplify-logite
    (and (equal (logite 0 then else) (ifix else))
         (equal (logite -1 then else) (ifix then)))))

(local (in-theory (disable ash lognot lognotu logand logior logxor logeqv logorc1)))


(defrule simplify-bit-functions
  :parents (logops-bit-functions)
  :short "Rewrite: Simplification rules for all binary @('b-') functions
  including commutative rules, reductions with 1 explicit value, and reductions
  for identical agruments and complemented arguments."

  (and (equal (b-and x y) (b-and y x))
       (equal (b-and 0 x) 0)
       (equal (b-and 1 x) (bfix x))
       (equal (b-and x x) (bfix x))
       (equal (b-and x (b-not x)) 0)

       (equal (b-ior x y) (b-ior y x))
       (equal (b-ior 0 x) (bfix x))
       (equal (b-ior 1 x) 1)
       (equal (b-ior x x) (bfix x))
       (equal (b-ior x (b-not x)) 1)

       (equal (b-xor x y) (b-xor y x))
       (equal (b-xor 0 x) (bfix x))
       (equal (b-xor 1 x) (b-not x))
       (equal (b-xor x x) 0)
       (equal (b-xor x (b-not x)) 1)

       (equal (b-eqv x y) (b-eqv y x))
       (equal (b-eqv 0 x) (b-not x))
       (equal (b-eqv 1 x) (bfix x))
       (equal (b-eqv x x) 1)
       (equal (b-eqv x (b-not x)) 0)

       (equal (b-nand x y) (b-nand y x))
       (equal (b-nand 0 x) 1)
       (equal (b-nand 1 x) (b-not x))
       (equal (b-nand x x) (b-not x))
       (equal (b-nand x (b-not x)) 1)

       (equal (b-nor x y) (b-nor y x))
       (equal (b-nor 0 x) (b-not x))
       (equal (b-nor 1 x) 0)
       (equal (b-nor x x) (b-not x))
       (equal (b-nor x (b-not x)) 0)

       (equal (b-andc1 0 x) (bfix x))
       (equal (b-andc1 x 0) 0)
       (equal (b-andc1 1 x) 0)
       (equal (b-andc1 x 1) (b-not x))
       (equal (b-andc1 x x) 0)
       (equal (b-andc1 x (b-not x)) (b-not x))
       (equal (b-andc1 (b-not x) x) (bfix x))

       (equal (b-andc2 0 x) 0)
       (equal (b-andc2 x 0) (bfix x))
       (equal (b-andc2 1 x) (b-not x))
       (equal (b-andc2 x 1) 0)
       (equal (b-andc2 x x) 0)
       (equal (b-andc2 x (b-not x)) (bfix x))
       (equal (b-andc2 (b-not x) x) (b-not x))

       (equal (b-orc1 0 x) 1)
       (equal (b-orc1 x 0) (b-not x))
       (equal (b-orc1 1 x) (bfix x))
       (equal (b-orc1 x 1) 1)
       (equal (b-orc1 x x) 1)
       (equal (b-orc1 x (b-not x)) (b-not x))
       (equal (b-orc1 (b-not x) x) (bfix x))

       (equal (b-orc2 0 x) (b-not x))
       (equal (b-orc2 x 0) 1)
       (equal (b-orc2 1 x) 1)
       (equal (b-orc2 x 1) (bfix x))
       (equal (b-orc2 x x) 1)
       (equal (b-orc2 x (b-not x)) (bfix x))
       (equal (b-orc2 (b-not x) x) (b-not x))

       (equal (b-ite 1 then else) (bfix then))
       (equal (b-ite 0 then else) (bfix else))
       (equal (b-ite test 1 0) (bfix test))
       (equal (b-ite test 0 1) (b-not test))
       (equal (b-ite test then then) (bfix then))
       (equal (b-ite test then 0)    (b-and test then))
       (equal (b-ite test then 1)    (b-ior (b-not test) then))
       (equal (b-ite test then test) (b-and test then))
       (equal (b-ite test 1 else) (b-ior test else))
       (equal (b-ite test 0 else) (b-and (b-not test) else))
       (equal (b-ite test test else) (b-ior test else)))

  :enable (bitp b-and b-ior b-xor b-not b-eqv b-nand b-nor
                b-andc1 b-andc2 b-orc1 b-orc2 b-ite))


;;;****************************************************************************
;;;
;;;    Lemmas, Round 2 -- UNSIGNED-BYTE-P, SIGNED-BYTE-P, LOGHEAD, LOGTAIL,
;;;    LOGAPP, LOGRPL
;;;
;;;****************************************************************************

(local (in-theory (enable unsigned-byte-p
                          integer-range-p ; added by Matt K. for Version_2.7
                          signed-byte-p loghead logtail
			  logapp logrpl logextu)))


(defsection ihs/unsigned-byte-p-lemmas
  :parents (unsigned-byte-p logops-lemmas)
  :short "Lemmas about @(see unsigned-byte-p) from the @(see logops-lemmas) book."

  (defthm unsigned-byte-p-base-case
    (equal (unsigned-byte-p size 0)
           (and (integerp size)
                (<= 0 size))))

  (defthm unsigned-byte-p-0
    (equal (unsigned-byte-p 0 x)
           (equal x 0)))

  (defthm unsigned-byte-p-plus
    (implies (and (unsigned-byte-p size i)
                  (>= j 0)
                  (integerp j))
             (and (unsigned-byte-p (+ size j) i)
                  (unsigned-byte-p (+ j size) i)))
    :hints (("Goal" :in-theory (disable expt-is-weakly-increasing-for-base>1)
             :use ((:instance expt-is-weakly-increasing-for-base>1
                    (r 2) (i size) (j (+ size j)))))))

  (defthm difference-unsigned-byte-p
    (implies (and (unsigned-byte-p size i)
                  (<= j i)
                  (>= j 0)
                  (integerp j))
             (and (unsigned-byte-p size (- i j))
                  (unsigned-byte-p size (+ (- j) i)))))

; Make JFR a linear rule?

  (defthm floor-unsigned-byte-p
    ;; [Jared] BOZO I suspect it'd be better to have the (unsigned-byte-p size i)
    ;; hyp first
    (implies (and (> x 1)
                  (force (real/rationalp x))
                  (unsigned-byte-p size i))
             (unsigned-byte-p size (floor i x)))
    :hints (("Goal" :in-theory (disable floor-recursion)
             :use ((:instance floor-recursion (x i) (y x)))))))

(defsection ihs/signed-byte-p-lemmas
  :parents (signed-byte-p logops-lemmas)
  :short "Lemmas about @(see signed-byte-p) from the @(see logops-lemmas) book."

  (defthm signed-byte-p-base-cases
    (and (equal (signed-byte-p size 0)
                (and (integerp size)
                     (< 0 size)))
         (equal (signed-byte-p size -1)
                (and (integerp size)
                     (< 0 size))))
    :hints (("Goal" :in-theory (enable signed-byte-p))))

  (defthm backchain-signed-byte-p-to-unsigned-byte-p
    (implies (and (syntaxp (constant-syntaxp size))
                  (< 0 size)
                  (unsigned-byte-p (1- size) i))
             (signed-byte-p size i))
    :hints (("Goal" :in-theory (enable signed-byte-p unsigned-byte-p)))))




(defsection ihs/loghead-lemmas
  :parents (loghead logops-lemmas)
  :short "Lemmas about @(see loghead) from the @(see logops-lemmas) book."

  (defthm loghead-identity
    (implies (unsigned-byte-p size i)
             (equal (loghead size i)
                    i)))

  (defthm loghead-loghead
    (implies (and (>= size1 0)
                  (integerp size1)
                  (loghead-guard size i))
             (equal (loghead size1 (loghead size i))
                    (if (< size1 size)
                        (loghead size1 i)
                      (loghead size i))))
    :hints (("Goal" :in-theory (disable mod-bounded-by-modulus mod-bounds-x))))

  (defthm loghead-0-i
    (implies (integerp i)
             (equal (loghead 0 i)
                    0)))

  (defthm loghead-size-0
    (implies (and (integerp size)
                  (>= size 0))
             (equal (loghead size 0)
                    0)))

  (defthm loghead-leq
    (implies (and (>= i 0)
                  (loghead-guard size i))
             (<= (loghead size i) i))
  :rule-classes ((:linear :trigger-terms ((loghead size i)))))

  (defthm loghead-logapp
    (implies (and (<= size1 size)
                  (force (>= size1 0))
                  (force (integerp size1))
                  (logapp-guard size i j))
             (equal (loghead size1 (logapp size i j))
                    (loghead size1 i))))

  (defthm loghead-logrpl
    (implies (and (logrpl-guard size1 i j)
                  (force (integerp size))
                  (force (>= size 0)))
             (equal (loghead size (logrpl size1 i j))
                    (if (< size1 size)
                        (logrpl size1 i (loghead size j))
                      (loghead size i))))
    :hints (("Goal" :in-theory (disable exponents-add mod-bounded-by-modulus))))

  (defthm bitp-loghead-1
    (bitp (loghead 1 i))
    ;; [Jared] 2016-04-08: changing this to a type-prescription now that bitp
    ;; is a good type-prescription
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable bitp loghead)))))



(defsection ihs/logtail-lemmas
  :parents (logtail logops-lemmas)
  :short "Lemmas about @(see logtail) from the @(see logops-lemmas) book."

  (defthm logtail-identity
    (implies (unsigned-byte-p size i)
             (equal (logtail size i) 0)))

  (defthm logtail-logtail
    (implies (and (force (>= pos1 0))
                  (force (integerp pos1))
                  (logtail-guard pos i))
             (equal (logtail pos1 (logtail pos i))
                    (logtail (+ pos pos1) i))))

  (defthm logtail-0-i
    (implies (integerp i)
             (equal (logtail 0 i)
                    i)))

  (defthm logtail-size-0
    (implies (and (integerp size)
                  (>= size 0))
             (equal (logtail size 0)
                    0)))

  (defthm logtail-leq
    (implies (and (>= i 0)
                  (logtail-guard pos i))
             (<= (logtail pos i) i))
    :rule-classes ((:linear :trigger-terms ((logtail pos i)))))

  (defthm logtail-equal-0
    (implies (logtail-guard pos i)
             (equal (equal (logtail pos i) 0)
                    (unsigned-byte-p pos i))))

  (defthm logtail-lessp
    (implies (and (logtail-guard pos i)
                  (force (integerp j)))
             (equal (< (logtail pos i) j)
                    (< i (* j (expt 2 pos)))))
    :hints (("Goal"
             :in-theory (set-difference-theories (enable logtail)
                                                 '(<-*-left-cancel
                                                   floor-bounded-by-/
                                                   <-*-/-left))
             :use ((:instance <-*-left-cancel
                    (z (/ (expt 2 pos))) (x i) (y (* j (expt 2 pos))))
                   (:instance floor-bounded-by-/ (x i) (y (expt 2 pos)))))))

  (defthm logtail-unsigned-byte-p
    (implies (and (>= size1 0)
                  (integerp size1)
                  (logtail-guard size i))
             (equal (unsigned-byte-p size1 (logtail size i))
                    (unsigned-byte-p (+ size size1) i)))
    :hints(("Goal" :in-theory (disable logtail))))

  (defthm logtail-loghead
    (implies (and (>= size1 0)
                  (force (integerp size1))
                  (loghead-guard size i))
             (equal (logtail size1 (loghead size i))
                    (loghead (max 0 (- size size1)) (logtail size1 i))))
    :hints (("Goal" :in-theory (disable exponents-add mod-bounded-by-modulus
                                        mod-bounds-x))))

  (defthm logtail-logapp
    (implies (and (logapp-guard size1 i j)
                  (force (integerp size))
                  (force (>= size 0)))
             (equal (logtail size (logapp size1 i j))
                    (if (< size size1)
                        (logapp (- size1 size) (logtail size i) j)
                      (logtail (- size size1) j))))
    :hints (("Goal" :in-theory (disable mod-x-i*j-of-positives))))

  (defthm logtail-logrpl
    (implies (and (logrpl-guard size1 i j)
                  (force (integerp size))
                  (force (>= size 0)))
             (equal (logtail size (logrpl size1 i j))
                    (if (< size size1)
                        (logrpl (- size1 size) (logtail size i) (logtail size j))
                      (logtail size j))))
    :hints (("Goal" :in-theory (disable logapp logtail)))))



(defsection ihs/logapp-lemmas
  :parents (logapp logops-lemmas)
  :short "Lemmas about @(see logapp) from the @(see logops-lemmas) book."

  (defthm logapp-0
    (and (implies (logapp-guard size i 0)
                  (equal (logapp size i 0)
                         (loghead size i)))
         (implies (logapp-guard size 0 i)
                  (equal (logapp size 0 i)
                         (* i (expt 2 size))))
         (implies (logapp-guard 0 i j)
                  (equal (logapp 0 i j)
                         j))))

  (defsection unsigned-byte-p-logapp

  ;; The following comment and lemma were replaced for Version  2.6 by the
  ;; lemmas below that lead up to (and include) the new crock0 below.
#|
  ;;  !!!! AXIOM !!! Fri Feb 10 15:11:06 1995 bb -- Why won't this prove
  ;;  anymore !!!

  (local
   (skip-proofs
    (defthm crock0
      (implies (and (not (< size size1))
		    (not (< j 0))
		    (integerp i)
		    (integerp size1)
		    (not (< size1 0))
		    (integerp j)
		    (integerp size)
		    (not (< size 0))
		    (< (* j (expt 2 size1)) (expt 2 size)))
	       (< (+ (* j (expt 2 size1))
		     (mod i (expt 2 size1)))
		  (expt 2 size)))
      :hints (("Goal"
	       :do-not '(eliminate-destructors)
	       :in-theory (disable <-*-left-cancel <-*-/-left)
	       :use ((:instance <-*-left-cancel
				(z (/ (expt 2 size1)))
				(y (+ (* j (expt 2 size1))
				      (loghead size1 i)))
				(x (expt 2 size)))))))))
|#

  (local
   (defthm crock0-0
     (implies (and (<= size1 size)
                   (<= 0 j)
                   (integerp size1)
                   (<= 0 size1)
                   (integerp j)
                   (integerp size)
                   (<= 0 size)
                   (> (expt 2 size)
                      (* j (expt 2 size1))))
              (> (expt 2 (- size size1))
                 j))
     :rule-classes nil))

  (local
   (defthm integerp-expt-2
     (implies (and (force (integerp i))
                   (force (<= 0 i)))
              (and (integerp (expt 2 i))
                   (<= 0 (expt 2 i))))
     :rule-classes :type-prescription))

  (local
   (defthm crock0-1
     (implies (and (<= size1 size)
                   (<= 0 j)
                   (integerp size1)
                   (<= 0 size1)
                   (integerp j)
                   (integerp size)
                   (<= 0 size)
                   (> (expt 2 size)
                      (* j (expt 2 size1))))
              (>= (expt 2 (- size size1))
                  (+ 1 j)))
     :rule-classes nil
     :hints (("Goal" :use crock0-0
              :in-theory (disable exponents-add)))))

  (local
   (defthm distrib-left
     (equal (* (+ a b) c)
            (+ (* a c) (* b c)))))

  (local
   (defthm crock0
     (implies (and (<= size1 size)
                   (<= 0 j)
                   (integerp size1)
                   (<= 0 size1)
                   (integerp i)
                   (integerp j)
                   (integerp size)
                   (<= 0 size)
                   (> (expt 2 size)
                      (* j (expt 2 size1))))
              (> (expt 2 size)
                 (+ (* j (expt 2 size1))
                    (mod i (expt 2 size1)))))
     :hints (("Goal" :use crock0-1))))

  (defthm unsigned-byte-p-logapp
    (implies (and (<= size1 size)
                  (>= j 0)
                  (logapp-guard size1 i j)
                  (force (integerp size))
                  (force (>= size 0)))
             (equal (unsigned-byte-p size (logapp size1 i j))
                    (unsigned-byte-p (- size size1) j)))
    :hints (("Goal"
	     :do-not '(eliminate-destructors)
	     :in-theory
	     (union-theories (disable <-*-left-cancel <-*-/-left)
			     '(logapp unsigned-byte-p
				      rewrite-linear-equalities-to-iff))))))

  (defthm associativity-of-logapp
    (implies (and (logapp-guard size1 j k)
                  (logapp-guard size i (logapp size1 j k)))
             (equal (logapp size i (logapp size1 j k))
                    (logapp (+ size size1) (logapp size i j) k))))

  (defthm logapp-loghead-logtail
    (implies (logapp-guard size i i)
             (equal (logapp size (loghead size i) (logtail size i))
                    i))
    :hints (("Goal" :in-theory (enable logapp loghead logtail))))

  ;; Candidate for crock  -- Used only to prove READ-WRITE-MEM2.

  (defthm loghead-logapp-loghead-logtail
    (implies (and (loghead-guard size i)
                  (loghead-guard size1 i))
             (equal (logapp size (loghead size i) (loghead size1 (logtail size i)))
                    (loghead (+ size size1) i)))
    :hints
    (("Goal"
      :in-theory (disable loghead logtail logapp logapp-loghead-logtail)
      :use ((:instance logapp-loghead-logtail (size size)
             (i (loghead (+ size size1) i))))))))


(defsection ihs/logrpl-lemmas
  :parents (logrpl logops-lemmas)
  :short "Lemmas about @(see logrpl) from the @(see logops-lemmas) book."

  (defthm logrpl-0
    (and (implies (logrpl-guard 0 i j)
                  (equal (logrpl 0 i j)
                         j))
         (implies (logrpl-guard size i 0)
                  (equal (logrpl size i 0)
                         (loghead size i)))
         (implies (and (unsigned-byte-p size j)
                       (integerp i))
                  (equal (logrpl size i j)
                         (loghead size i)))))

  (defthm unsigned-byte-p-logrpl
    (implies (and (<= size1 size)
                  (>= j 0)
                  (logrpl-guard size1 i j)
                  (force (integerp size))
                  (force (>= size 0)))
             (equal (unsigned-byte-p size (logrpl size1 i j))
                    (unsigned-byte-p size j)))
    :hints (("Goal"
             :in-theory (union-theories (disable <-*-left-cancel
                                                 <-*-right-cancel
                                                 <-*-/-left
                                                 <-*-/-right
                                                 floor-bounded-by-/
                                                 logapp)
                                        '(rewrite-linear-equalities-to-iff))
             :use ((:instance <-*-right-cancel
                    (z (/ (expt 2 size1))) (y j) (x (expt 2 size)))
                   (:instance floor-bounded-by-/ (x j) (y (expt 2 size1)))))))

  (defthm logrpl-i-i
    (implies (logrpl-guard size i i)
             (equal (logrpl size i i)
                    i)))

  (defthm logrpl-loghead-i-i
    (implies (and (<= size size1)
                  (loghead-guard size1 i)
                  (force (integerp size))
                  (force (>= size 0)))
             (equal (logrpl size (loghead size1 i) i)
                    i)))

  ;; [Jared] BOZO somehow ACL2's definition rule gets stored differently
  ;; because of define's binding of __function__.  The old rule is stored as
  ;; class DEFINITION but the new rule is stored as class ABBREVIATION.  This
  ;; difference somehow screws up the proof of logrpl-logrpl-right.  Blaaaaah.
  ;; This was painful to track down.
  (local (defthm old-definition-of-logrpl
           (equal (logrpl size i j)
                  (LOGAPP SIZE I (LOGTAIL SIZE J)))
           :rule-classes :definition))
  (local (in-theory (disable (:definition logrpl))))

  (defthm logrpl-logrpl-right
    (implies (and (logrpl-guard size1 j k)
                  (logrpl-guard size i (logrpl size1 j k))
                  (<= size1 size))
             (equal (logrpl size i (logrpl size1 j k))
                    (logrpl size i k)))
    :hints (("Goal" :in-theory (disable logapp)
             :do-not '(eliminate-destructors generalize fertilize)
             :do-not-induct t)))

  (defthm logrpl-logrpl-left
    (implies (and (logrpl-guard size1 i j)
                  (logrpl-guard size (logrpl size1 i j) k)
                  (<= size size1))
             (equal (logrpl size (logrpl size1 i j) k)
                    (logrpl size i k)))))



(defsection ihs/logextu-lemmas
  :parents (logextu logops-lemmas)
  :short "Lemmas about @(see logextu) from the @(see logops-lemmas) book."

  (defthm logextu-0
    (implies (logextu-guard 0 ext-size i)
             (equal (logextu 0 ext-size i)
                    0))))


(local (in-theory (disable unsigned-byte-p signed-byte-p loghead logtail
                           logapp logrpl logextu)))




;;;****************************************************************************
;;;
;;;    Lemmas, Round 3 -- The theory of LOGCAR, LOGCDR, and LOGCONS.  A few
;;;    lemmas are kept local, as they are only useful to prove others.
;;;
;;;****************************************************************************

(local (in-theory (enable logcar logcdr logcons bitp)))

(defsection ihs/logcons-lemmas
  :parents (logcons logops-lemmas)
  :short "Basic lemmas relating @(see logcons) to @(see logcar) and @(see
logcdr), from the @(see logops-lemmas) book."

  (defthm logcar-logcons
    (implies (and (bitp b)
                  (integerp i))
             (equal (logcar (logcons b i))
                    b)))

  (defthm logcdr-logcons
    (implies (and (bitp b)
                  (integerp i))
             (equal (logcdr (logcons b i))
                    i)))

  (defthm equal-logcons
    (implies (and (integerp i)
                  (integerp logcdr)
                  (bitp logcar))
             (equal (equal (logcons logcar logcdr) i)
                    (and (equal (logcar i) logcar)
                         (equal (logcdr i) logcdr)))))

  (defthm logcar-logcdr-elim
    (implies (integerp i)
             (equal (logcons (logcar i) (logcdr i))
                    i))
    :rule-classes (:rewrite :elim)))

(local (defthm evenp-and-oddp-as-logcar
         (implies (integerp i)
                  (and (equal (evenp i)
                              (equal (logcar i) 0))
                       (equal (oddp i)
                              (equal (logcar i) 1))))
         :hints (("Goal"
                  :in-theory (e/d (evenp oddp) (bitp-mod-2))
                  :use bitp-mod-2))))


(defsection ihs/logcar-lemmas
  :parents (logcar logops-lemmas)
  :short "Lemmas about @(see logcar) from the @(see logops-lemmas) book."

  (defthm logcar-2*i
    (implies (integerp i)
             (equal (logcar (* 2 i))
                    0)))

  (defthm logcar-i+2*j
    (implies (and (integerp i)
                  (integerp j))
             (and (equal (logcar (+ i (* 2 j))) (logcar i))
                  (equal (logcar (+ (* 2 j) i)) (logcar i)))))

  (defthm logcdr-2*i
    (implies (integerp i)
             (equal (logcdr (* 2 i))
                    i)))

  (defthm logcdr-i+2*j
    (implies (and (integerp i)
                  (integerp j))
             (and (equal (logcdr (+ i (* 2 j))) (+ (logcdr i) j))
                  (equal (logcdr (+ (* 2 j) i)) (+ (logcdr i) j)))))

  (defthm logcar-loghead
    (implies (loghead-guard size i)
             (equal (logcar (loghead size i))
                    (if (equal size 0) 0 (logcar i))))
    :hints (("Goal" :in-theory (e/d (ifix loghead)
                                    (expt mod-bounded-by-modulus mod-bounds-x
                                          loghead-upper-bound
                                          exponents-add
                                          mod-x-y-=-x+y-for-rationals
                                          rewrite-mod-mod))
             :expand (expt 2 size))))

  (defthm logcar-logapp
    (implies (logapp-guard size i j)
             (equal (logcar (logapp size i j))
                    (if (equal size 0) (logcar j) (logcar i))))
    :hints (("Goal" :in-theory (e/d (ifix logapp)
                                    (expt logcar mod-bounded-by-modulus mod-bounds-x
                                          exponents-add))
             :expand (expt 2 size))))

  (defthm logcar-logrpl
    (implies (logrpl-guard size i j)
             (equal (logcar (logrpl size i j))
                    (if (equal size 0) (logcar j) (logcar i))))
    :hints (("Goal" :in-theory (e/d (ifix logrpl)
                                    (expt logcar mod-bounded-by-modulus exponents-add))
             :expand (expt 2 size)))))

(local (in-theory (disable logcar logcdr logcons bitp)))

(local (in-theory (enable logbitp logbit)))

(defsection ihs/logbitp-lemmas
  :parents (logbitp logbit logops-lemmas)
  :short "Lemmas about @(see logbitp) and @(see logbit) from the @(see
logops-lemmas) book."
  :long "<p>We prove a set of lemmas about @(see logbitp), then prove the
analogous lemmas about @(see logbit), which is defined in terms of @(see
logbitp).</p>"

  (defthm logbitp-0-minus-1
    (implies (and (integerp pos)
                  (>= pos 0))
             (and (not (logbitp pos 0))
                  (logbitp pos -1)))
    :hints (("Goal" :cases ((equal pos 0)))))

  (defthm logbit-0-minus-1
    (implies (and (integerp pos)
                  (>= pos 0)
                  (integerp i))
             (and (equal (logbit pos 0) 0)
                  (equal (logbit pos -1) 1)))
    :hints(("Goal" :in-theory (disable logbitp))))

  ;;  For the following, we provide an alternate definition of LOGBITP.

  (local (defthm alt-logbitp
           (implies (and (integerp pos)
                         (>= pos 0)
                         (integerp i))
                    (equal (logbitp pos i)
                           (equal (logcar (logtail pos i)) 1)))
           :hints (("Goal" :in-theory (e/d (logcar logtail) (mod-bounded-by-modulus mod-bounds-x))))
           :rule-classes :definition))

  (local (in-theory (disable logbitp)))

  (defthm logbitp-loghead
    (implies (and (loghead-guard size i)
                  (force (integerp pos))
                  (force (>= pos 0)))
             (equal (logbitp pos (loghead size i))
                    (if (< pos size)
                        (logbitp pos i)
                      nil))))

  (defthm logbit-loghead
    (implies (and (loghead-guard size i)
                  (force (integerp pos))
                  (force (>= pos 0))
                  (< pos size))
             (equal (logbit pos (loghead size i))
                    (if (< pos size)
                        (logbit pos i)
                      0)))
    :hints (("Goal" :in-theory (disable alt-logbitp))))

  (defthm logbitp-logtail
    (implies (and (logtail-guard pos i)
                  (force (integerp pos1))
                  (force (>= pos1 0)))
             (equal (logbitp pos1 (logtail pos i))
                    (logbitp (+ pos pos1) i))))

  (defthm logbit-logtail
    (implies (and (logtail-guard pos i)
                  (force (integerp pos1))
                  (force (>= pos1 0)))
             (equal (logbit pos1 (logtail pos i))
                    (logbit (+ pos pos1) i)))
    :hints (("Goal" :in-theory (disable alt-logbitp))))

  (defthm logbitp-logapp
    (implies (and (logapp-guard size i j)
                  (force (integerp pos))
                  (force (>= pos 0)))
             (equal (logbitp pos (logapp size i j))
                    (if (< pos size)
                        (logbitp pos i)
                      (logbitp (- pos size) j)))))

  (defthm logbit-logapp
    (implies (and (logapp-guard size i j)
                  (force (integerp pos))
                  (force (>= pos 0)))
             (equal (logbit pos (logapp size i j))
                    (if (< pos size)
                        (logbit pos i)
                      (logbit (- pos size) j))))
    :hints (("Goal" :in-theory (disable alt-logbitp))))

  (defthm logbitp-logrpl
    (implies (and (logrpl-guard size i j)
                  (force (integerp pos))
                  (force (>= pos 0)))
             (equal (logbitp pos (logrpl size i j))
                    (if (< pos size)
                        (logbitp pos i)
                      (logbitp pos j)))))

  (defthm logbit-logrpl
    (implies (and (logrpl-guard size i j)
                  (force (integerp pos))
                  (force (>= pos 0)))
             (equal (logbit pos (logrpl size i j))
                    (if (< pos size)
                        (logbit pos i)
                      (logbit pos j))))))

(local (in-theory (disable logbitp logbit)))


;;;****************************************************************************
;;;
;;;    Lemmas, Round 4 --  Inductive proofs about LOGNOT, LOGAND, LOGIOR,
;;;    LOGXOR, UNSIGNED-BYTE-P, LOGHEAD, and LOGMASKP.
;;;
;;;    There are certain properties of the above functions that have nice
;;;    inductive proofs.  However, of the above only LOGAND has a recursive
;;;    definition in ACL2.  (Its probably arguable that it's simpler to do
;;;    many of the previous proofs, which involve complicated facts about
;;;    FLOOR and MOD, as inductive proofs.)
;;;
;;;    At first I tried defining recursive versions of LOGNOT, LOGIOR, and
;;;    LOGXOR to get these proofs.  This was a disaster.  No matter what I
;;;    tried I could not get the prover to open up the recursive definitions
;;;    in what I thought was an efficient manner.  The proofs were long and
;;;    tedious, e.g., LOGAND-LOGXOR took over 10 minutes on a SPARCStation
;;;    20!
;;;
;;;    So, what I have done in this section is defined a number of
;;;    :DEFINITION lemmas that give selected functions a `recursive'
;;;    definition.  This allows me to do proofs by induction on the integers
;;;    for these functions.  This works surprisingly well.  These proofs are
;;;    quite fast, with minimal case splitting.
;;;
;;;    Originally, all of the recursive definitions were LOCAL to this book.
;;;    However, we occasionally had to prove new rules that had nice
;;;    inductive proofs, but didn't have these recursive definitions around.
;;;    So, all of the recursive definitions and a couple of supporting lemmas
;;;    ara available as the theory LOGOPS-RECURSIVE-DEFINITIONS-THEORY.  If
;;;    this theory is ENABLEd, then potentially every logical operation in
;;;    sight is going to be treated as if it were a recursive function.
;;;
;;;    A number of induction schemes are exported as well.
;;;
;;;****************************************************************************

(defxdoc logops-recursive-definitions-theory
  :parents (logops-lemmas)
  :short "Recursive equivalents of logical operations."
  :long "<p>The logical operations on numbers, e.g., @(see LOGHEAD), @(see
LOGAPP), etc., are defined in terms of modular arithmetic.  It is often useful,
however, to consider these functions as if they were recursive in terms of
@(see LOGCAR) and @(see LOGCDR).  This theory provides that alternate view of
the functions.  When this theory is @(see ENABLE)d, lemmas are enabled that
rewrite all of the logical operations listed above into an equivalent recursive
form.  It is then possible to do inductive proofs using these definitions.
Note, however, that you will have to explicitly select an induction scheme.</p>

<p>Note that this theory is @(see disable)d by default.  It should only be
@(see enable)d during proofs about logical operations where their recursive
counterparts are to be used.</p>")

;; Be mindful that everything is DISABLEd at this point.

(defsection basic-logops-induction-schemes
  :parents (logops-recursive-definitions-theory)
  :short "Some typical ways to induct when proving theorems about logical
operations."

  (defun logcdr-induction-1 (i)
    (declare (xargs :guard (integerp i)))
    (cond ((zip i) t)
          ((equal i -1) t)
          (t (logcdr-induction-1 (logcdr i)))))

  (defun logcdr-induction-2 (i j)
    (declare (xargs :guard (and (integerp i)
                                (integerp j))))
    (cond ((zip i) t)
          ((zip j) t)
          ((equal i -1) t)
          ((equal j -1) t)
          (t (logcdr-induction-2 (logcdr i) (logcdr j)))))

  (defun logcdr-induction-3 (i j k)
    (declare (xargs :guard (and (integerp i)
                                (integerp j)
                                (integerp k))))
    (cond ((zip i) t)
          ((equal i -1) t)
          (t (logcdr-induction-3 (logcdr i) (logcdr j) (logcdr k)))))

  (defun sub1-logcdr-induction-1 (size i)
    "The elaborate base case is for the benefit of UNSIGNED-BYTE-P, which has no guards."
    (cond ((or (not (integerp size))
               (< size 0)
               (not (integerp i)))
           t)
          ((equal size 0) t)
          (t (sub1-logcdr-induction-1 (1- size) (logcdr i)))))

  (defun sub1-logcdr-induction-2 (size i j)
    "The elaborate base case is for the benefit of UNSIGNED-BYTE-P, which has no guards."
    (cond ((or (not (integerp size))
               (< size 0)
               (not (integerp i))
               (not (integerp j)))
           t)
          ((equal size 0) t)
          (t (sub1-logcdr-induction-2 (1- size) (logcdr i) (logcdr j)))))

  (defun sub1-logcdr-induction-2-w/carry (size i j c)
    "The elaborate base case is for the benefit of SIGNED-BYTE-P, which has no guards."
    (cond ((or (not (integerp size))
               (<= size 0)
               (not (integerp i))
               (not (integerp j))
               (not (bitp c)))
           t)
          ((equal size 1) t)
          (t (sub1-logcdr-induction-2-w/carry
              (1- size) (logcdr i) (logcdr j) (b-and c (logcar i))))))

  (defun sub1-logcdr-induction-3 (size i j k)
    "The elaborate base case is for the benefit of SIGNED-BYTE-P, which has no guards."
    (cond ((or (not (integerp size))
               (<= size 0)
               (not (integerp i))
               (not (integerp j))
               (not (integerp k)))
           t)
          ((equal size 1) t)
          (t (sub1-logcdr-induction-3 (1- size) (logcdr i) (logcdr j) (logcdr k))))))


(defsection logops-recursive-helpers
  :parents (logops-recursive-definitions-theory)
  :short "Some additional lemmas that are included in @(see
logops-recursive-definitions-theory) to help with inducting over the
definitions of logical operations."

  (defthm falsify-unsigned-byte-p
    (implies (or (not (integerp size))
                 (< size 0)
                 (not (integerp i)))
             (not (unsigned-byte-p size i)))
    :hints (("Goal" :in-theory (enable unsigned-byte-p))))

  (defthm falsify-signed-byte-p
    (implies (or (not (integerp size))
                 (not (> size 0))
                 (not (integerp i)))
             (not (signed-byte-p size i)))
    :hints (("Goal" :in-theory (enable signed-byte-p)))))

(local (defthm eliminate-logical-masks-forward
         (implies (and (equal mask (+ -1 (expt 2 n)))
                       (force (integerp n))
                       (> n 0))
                  (and (equal (logcar mask) 1)
                       (equal (logcdr mask) (+ -1 (expt 2 (1- n))))))
         :rule-classes :forward-chaining
         :hints (("Goal" :expand (expt 2 n)
                  :in-theory (union-theories (disable exponents-add) '(ifix))))))

;  Recursive :DEFINITION rules.

(defrule lognot*
  :parents (lognot logops-recursive-definitions-theory)
  :short "Recursive definition of @(see lognot)."
  (implies (force (integerp i))
	   (equal (lognot i)
		  (logcons (b-not (logcar i)) (lognot (logcdr i)))))
  :rule-classes ((:definition
                  :clique (lognot)
                  :controller-alist ((lognot t))))
  :hints (("Goal" :in-theory (enable lognot logcons b-not))))

(defrule logand*
  :parents (logand logops-recursive-definitions-theory)
  :short "Recursive definition of @(see logand)."
  (implies (and (force (integerp i))
                (force (integerp j)))
           (equal (logand i j)
                  (logcons (b-and (logcar i) (logcar j))
                           (logand (logcdr i) (logcdr j)))))
  :rule-classes ((:definition
                  :clique (binary-logand)
                  :controller-alist ((binary-logand t t))))
  :hints (("Goal"
           :expand (logand i j)
	   :in-theory (enable b-and ifix logcdr))))

(defrule logior*
  :parents (logior logops-recursive-definitions-theory)
  :short "Recursive definition of @(see logior)."
  (implies (and (force (integerp i))
                (force (integerp j)))
           (equal (logior i j)
                  (logcons (b-ior (logcar i) (logcar j))
                           (logior (logcdr i) (logcdr j)))))
  :rule-classes ((:definition
                  :clique (binary-logior)
                  :controller-alist ((binary-logior t t))))
  :enable logior)

(defrule logxor*
  :parents (logxor logops-recursive-definitions-theory)
  :short "Recursive definition of @(see logxor)."
  (implies (and (force (integerp i))
                (force (integerp j)))
           (equal (logxor i j)
                  (logcons (b-xor (logcar i) (logcar j))
                           (logxor (logcdr i) (logcdr j)))))
  :rule-classes ((:definition
                  :clique (binary-logxor)
                  :controller-alist ((binary-logxor t t))))
  :enable (logxor logeqv logorc1))

(defrule unsigned-byte-p*
  :parents (unsigned-byte-p logops-recursive-definitions-theory)
  :short "Recursive definition of @(see unsigned-byte-p)."
  (implies (and (integerp size)
                (> size 0))
           (equal (unsigned-byte-p size i)
                  (and (integerp size)
                       (>= size 0)
                       (integerp i)
                       (>= i 0)
                       (unsigned-byte-p (1- size) (logcdr i)))))
  :rule-classes ((:definition
                  :clique (unsigned-byte-p)
                  :controller-alist ((unsigned-byte-p t t))))
  :expand (expt 2 size)
  :enable (ifix logcdr unsigned-byte-p floor-bounded-by-/ rewrite-linear-equalities-to-iff)
  :disable exponents-add)

(defrule signed-byte-p*
  :parents (signed-byte-p logops-recursive-definitions-theory)
  :short "Recursive definition of @(see signed-byte-p)."
  (equal (signed-byte-p size i)
         (and (integerp size)
              (> size 0)
              (integerp i)
              (or (equal i 0)
                  (equal i -1)
                  (signed-byte-p (1- size) (logcdr i)))))
  :rule-classes ((:definition
                  :clique (signed-byte-p)
                  :controller-alist ((signed-byte-p t t))))
  :expand (expt 2 (+ -1 size))
  :enable (ifix logcons signed-byte-p fold-consts-in-+ rewrite-linear-equalities-to-iff)
  :disable (exponents-add)
  :prep-lemmas
  ((defthm crock0
     (implies (and (integerp size)
                   (< 0 size)
                   (not (equal 1 size)))
              (integerp (expt 2 (+ -2 size))))
     :rule-classes :type-prescription
     :hints (("Goal" :in-theory (disable expt-type-prescription-integerp)
              :use ((:instance expt-type-prescription-integerp
                     (r 2) (i (+ -2 size)))))))))

(defrule integer-length*
  :parents (integer-length logops-recursive-definitions-theory)
  :short "Recursive definition of @(see integer-length)."
  (equal (integer-length i)
	 (cond ((zip i) 0)
	       ((equal i -1) 0)
	       (t (1+ (integer-length (logcdr i))))))
  :rule-classes ((:definition
                  :clique (integer-length)
                  :controller-alist ((integer-length t))))
  :enable (integer-length logcdr))

(defrule loghead*
  :parents (loghead logops-recursive-definitions-theory)
  :short "Recursive definition of @(see loghead)."
  (implies (loghead-guard size i)
           (equal (loghead size i)
                  (if (equal size 0)
                      0
                    (logcons (logcar i) (loghead (1- size) (logcdr i))))))
  :rule-classes ((:definition
                  :clique (loghead$inline)
                  :controller-alist ((loghead$inline t t))))
  :expand (expt 2 size)
  :enable (ifix loghead logcar logcdr logcons)
  :disable (exponents-add mod-bounded-by-modulus mod-bounds-x))

(defrule logtail*
  :parents (logtail logops-recursive-definitions-theory)
  :short "Recursive definition of @(see logtail)."
  (implies (logtail-guard pos i)
           (equal (logtail pos i)
                  (cond ((equal pos 0) i)
                        (t (logtail (1- pos) (logcdr i))))))
  :rule-classes ((:definition
                  :clique (logtail$inline)
                  :controller-alist ((logtail$inline t t))))
  :disable (exponents-add)
  :enable (ifix expt logtail logcdr))

(defrule logmaskp*
  :parents (logmaskp logops-recursive-definitions-theory)
  :short "Recursive definition of @(see logmaskp)."
  (equal (logmaskp i)
	 (cond ((not (integerp i)) nil)
               ((equal i 0) t)
               ((equal i -1) nil)
               (t (and (equal (logcar i) 1)
                       (logmaskp (logcdr i))))))
  :rule-classes ((:definition
                  :clique (logmaskp)
                  :controller-alist ((logmaskp t))))
  :expand (expt 2 (+ 1 (integer-length (logcdr i))))
  :enable (logmaskp))

(defrule logbitp*
  :parents (logbitp logops-recursive-definitions-theory)
  :short "Recursive definition of @(see logbitp)."
  (implies (and (integerp pos)
		(>= pos 0)
		(integerp i))
	   (equal (logbitp pos i)
		  (cond ((equal pos 0) (equal (logcar i) 1))
			(t (logbitp (1- pos) (logcdr i))))))
  :rule-classes ((:definition
                  :clique (logbitp)
                  :controller-alist ((logbitp t t))))
  :enable (ifix expt logbitp logcar logcdr)
  :disable (exponents-add mod-bounded-by-modulus mod-bounds-x
                          floor-type-1 floor-type-2 floor-type-3
                          floor-type-4))

(defrule logapp*
  :parents (logapp logops-recursive-definitions-theory)
  :short "Recursive definition of @(see logapp)."
  (implies (logapp-guard size i j)
           (equal (logapp size i j)
                  (cond
                   ((equal size 0) j)
                   (t (logcons (logcar i) (logapp (1- size) (logcdr i) j))))))
  :rule-classes ((:definition
                  :clique (logapp)
                  :controller-alist ((logapp t t nil))))
  :enable (ifix expt logapp)
  :disable (exponents-add))

(defrule logext*
  :parents (logext logops-recursive-definitions-theory)
  :short "Recursive definition of @(see logext)."
  (implies (logext-guard size i)
           (equal (logext size i)
                  (cond
                   ((equal size 1) (if (equal (logcar i) 0) 0 -1))
                   (t (logcons (logcar i) (logext (1- size) (logcdr i)))))))
  :rule-classes ((:definition
                  :clique (logext)
                  :controller-alist ((logext t t))))
  :enable (logext))



;;;  The trick to this recursive definition of ASH is to rearrange the term
;;;  so that the lemma FLOOR-FLOOR-INTEGER will fire.

(encapsulate ()

  (local (in-theory (disable exponents-add expt-minus))) ;!@#$^%

  (local
   (defthm crock0
     (equal (/ (expt 2 n))
	    (expt 2 (- n)))
     :hints
     (("Goal"
       :in-theory (enable expt-minus)))))

  (local
   (defthm crock1
     (implies
      (and (integerp i)
	   (integerp count)
	   (< count 0))
      (equal (floor (* 1/2 i (expt 2 (+ 1 count))) 1)
	     (floor (* i (expt 2 (+ 1 count))) 2)))
     :hints
     (("goal"
       :in-theory (enable rewrite-floor-x*y-z-left)))))

  (local
   (defthm crock2
     (implies
      (and (integerp i)
	   (real/rationalp j)
	   (not (equal j 0)))
      (equal (floor (* i (expt 2 (+ 1 count))) j)
	     (floor i (/ j (expt 2 (+ 1 count))))))
     :hints
     (("goal"
       :in-theory (enable rewrite-floor-x*y-z-right)))))

  (defrule ash*
    :parents (ash logops-recursive-definitions-theory)
    :short "Recursive definition of @(see ash)."
    (equal (ash i count)
	   (cond ((zip count) (ifix i))
                 ((< count 0) (ash (logcdr i) (1+ count)))
                 (t (logcons 0 (ash i (1- count))))))
    :rule-classes ((:definition
                    :clique (ash)
                    :controller-alist ((ash nil t))))
    :enable (ash logcdr)
    :expand (expt 2 count)))

(deftheory logops-recursive-definitions-theory
  '(falsify-unsigned-byte-p
    falsify-unsigned-byte-p
    unsigned-byte-p* signed-byte-p*
    lognot* logand* logior* logior* logxor*
    integer-length* loghead* logtail* logmaskp* logbitp*
    logapp* logext* ash*))

;;;  Lemmas for LOGNOT

(local (defthm signed-byte-p-lognot
         (implies (signed-byte-p size i)
                  (signed-byte-p size (lognot i)))
         :hints (("Goal" :induct (sub1-logcdr-induction-1 size i)))))


;;;  Lemmas for LOGAND

(local (defthm equal-logand-0
         (implies (or (not (integerp i))
                      (not (integerp j)))
                  (equal (logand i j) 0))
         :hints (("Goal" :in-theory (enable logand)))))

(defsection more-logand-lemmas
  :extension ihs/logand-lemmas

  (defthm logand-=-minus-1
    (equal (equal (logand i j) -1)
           (and (equal i -1) (equal j -1)))
    :hints (("Goal"
             :induct (logcdr-induction-2 i j)
             :in-theory (enable ifix))))

  (defthm unsigned-byte-p-logand
    (implies (and (or (unsigned-byte-p size i)
                      (unsigned-byte-p size j))
                  (force (integerp i))
                  (force (integerp j)))
             (unsigned-byte-p size (logand i j)))
    :hints (("Goal"
             :expand (expt 2 size)
             :induct (sub1-logcdr-induction-2 size i j)
             :in-theory (disable exponents-add)))))

(local (defthm signed-byte-p-logand
         (implies (and (signed-byte-p size i)
                       (signed-byte-p size j))
                  (signed-byte-p size (logand i j)))
         :hints (("Goal" :induct (sub1-logcdr-induction-2 size i j)))))

(defsection more-logand-lemmas
  :extension ihs/logand-lemmas

  (defthm logand-upper-bound
    (implies (and (>= i 0)
                  (integerp j))
             (<= (logand i j) i))
    :rule-classes ((:linear :corollary (implies (and (>= i 0)
                                                     (integerp j))
                                                (<= (logand i j) i)))
                   (:linear :corollary (implies (and (>= i 0)
                                                     (integerp j))
                                                (<= (logand j i) i))))
    :hints (("Goal"
             :in-theory (enable ifix logcons)
             :induct (logcdr-induction-2 i j))))

  (encapsulate ()
    (local (defthm logand-logior-lemma
             (implies (and (bitp i) (bitp j) (bitp k))
                      (equal (b-and i (b-ior j k))
                             (b-ior (b-and i j) (b-and i k))))
             :hints (("Goal" :in-theory (enable b-and b-ior)))))

    (defthm logand-logior
      (implies (and (integerp x)
                    (integerp y)
                    (integerp z))
               (equal (logand x (logior y z))
                      (logior (logand x y) (logand x z))))
      :hints (("Goal" :induct (logcdr-induction-3 x y z)
               :in-theory (enable ifix bfix)))))

  (encapsulate ()
    (local (defthm logand-logxor-lemma
             (implies (and (bitp i) (bitp j) (bitp k))
                      (equal (b-and i (b-xor j k))
                             (b-xor (b-and i j) (b-and i k))))
             :hints (("Goal" :in-theory (enable b-and b-xor)))))

    (defthm logand-logxor
      (implies (and (force (integerp i))
                    (force (integerp j))
                    (force (integerp k)))
               (equal (logand i (logxor j k))
                      (logxor (logand i j) (logand i k))))
      :hints (("Goal"
               :induct (logcdr-induction-3 i j k)
               :in-theory (enable ifix))))))

;;;  Lemmas for LOGIOR

(defsection more-logior-lemmas
  :extension ihs/logior-lemmas

  (defthm logior-=-0
    (implies (and (force (integerp i))
                  (force (integerp j)))
             (equal (equal (logior i j) 0)
                    (and (equal i 0)
                         (equal j 0))))
    :hints (("Goal" :induct (logcdr-induction-2 i j))))

  (defthm unsigned-byte-p-logior
    (implies (and (force (integerp i))
                  (force (integerp j)))
             (equal (unsigned-byte-p size (logior i j))
                    (and (unsigned-byte-p size i)
                         (unsigned-byte-p size j))))
    :hints (("Goal" :expand (expt 2 size)
             :induct (sub1-logcdr-induction-2 size i j)))))

;;;  Lemmas for LOGXOR

(defsection more-logxor-lemmas
  :extension ihs/logxor-lemmas

  (defthm logxor-=-0
    (implies (and (force (integerp i))
                  (force (integerp j)))
             (equal (equal (logxor i j) 0)
                    (equal i j)))
    :hints (("Goal"
             :induct (logcdr-induction-2 i j)
             :in-theory (enable ifix))))

  (defthm unsigned-byte-p-logxor
    (implies (and (unsigned-byte-p size i)
                  (unsigned-byte-p size j)
                  (force (integerp i))
                  (force (integerp j)))
             (unsigned-byte-p size (logxor i j)))
    :hints (("Goal"
             :expand (expt 2 size)
             :induct (sub1-logcdr-induction-2 size i j)
             :in-theory (disable exponents-add)))))

;;;  Lemmas for INTEGER-LENGTH

(defsection ihs/integer-length-lemmas
  :parents (integer-length logops-lemmas)
  :short "Lemmas about @(see integer-length) from the @(see logops-lemmas) book."

  (defthm equal-integer-length-0
    (equal (equal (integer-length i) 0)
           (or (zip i)
               (equal i -1)))
    :hints (("Goal" :induct (logcdr-induction-1 i)))))

;;;  Lemmas for LOGMASKP

(defsection ihs/logmaskp-lemmas
  :parents (logmaskp logops-lemmas)
  :short "Lemmas about @(see logmaskp) from the @(see logops-lemmas) book."

  (local
   (defthm logmaskp-expt-2-n-minus-1-crock
     (implies
      (and (force (integerp n))
	   (>= n 0)
	   (equal mask (+ -1  (expt 2 n))))
      (logmaskp mask))
     :rule-classes nil
     :hints (("Goal" :expand (expt 2 n)
	      :induct (sub1-logcdr-induction-1 n mask)
	      :in-theory (disable exponents-add)))))

  (defthm logmaskp-expt-2-n-minus-1
    (implies (and (force (integerp n))
                  (>= n 0))
             (logmaskp (+ -1 (expt 2 n))))
    :hints (("Goal" :use ((:instance logmaskp-expt-2-n-minus-1-crock
                           (mask (+ -1 (expt 2 n))))))))

  (defthm logmaskp-logmask
    (implies (logmask-guard n)
             (logmaskp (logmask n)))
    :hints (("Goal" :in-theory (enable logmask)
             :use ((:instance logmaskp-expt-2-n-minus-1-crock
                    (mask (+ -1 (expt 2 n))))))))

  (defthm logand-with-mask
    (implies (and (logmaskp mask)
                  (equal size (integer-length mask))
                  (force (integerp i)))
             (equal (logand mask i)
                    (loghead size i)))
    :hints (("Goal" :induct (sub1-logcdr-induction-2 size mask i)))))


;;;  Lemmas for LOGBITP and LOGBIT

(defsection more-logbitp-lemmas
  :extension ihs/logbitp-lemmas

  (defthm logbitp-lognot
    (implies (and (integerp pos)
                  (>= pos 0)
                  (integerp i))
             (equal (logbitp pos (lognot i))
                    (not (logbitp pos i))))
    :hints (("Goal"
             :in-theory (enable logbitp*)
             :induct (sub1-logcdr-induction-1 pos i))))

  (defthm logbit-lognot
    (implies (and (integerp pos)
                  (>= pos 0)
                  (integerp i))
             (equal (logbit pos (lognot i))
                    (b-not (logbit pos i))))
    :hints (("Goal" :in-theory (enable logbit))))

  (defthm logbitp-lognotu
    (implies (and (integerp pos)
                  (>= pos 0)
                  (integerp i)
                  (force (integerp size))
                  (force (>= size 0)))
             (equal (logbitp pos (lognotu size i))
                    (if (< pos size)
                        (not (logbitp pos i))
		      nil)))
    :hints (("Goal" :in-theory (enable lognotu))))

  (defthm logbit-lognotu
    (implies (and (integerp pos)
                  (>= pos 0)
                  (integerp i)
                  (force (integerp size))
                  (force (>= size 0)))
             (equal (logbit pos (lognotu size i))
                    (if (< pos size)
                        (b-not (logbit pos i))
                      0)))
    :hints (("Goal" :in-theory (enable logbit)))))


;;;  Lemmas for LOGEXT

(defsection ihs/logext-lemmas
  :parents (logext logops-lemmas)
  :short "Lemmas about @(see logext) from the @(see logops-lemmas) book."

  (defthm logext-identity
    (implies (signed-byte-p size i)
             (equal (logext size i)
                    i))
    :hints (("Goal" :induct (sub1-logcdr-induction-1 size i)))))

;;;  Lemmas for LOGEXTU

(defsection more-logextu-lemmas
  :extension ihs/logextu-lemmas

  (local (defun logextu-induction (final-size ext-size i)
           (declare (xargs :guard (and (integerp final-size)
                                       (>= final-size 0)
                                       (integerp ext-size)
                                       (> ext-size 0)
                                       (integerp i))))
           (cond ((zp final-size) t)
                 ((equal ext-size 1) t)
                 (t (logextu-induction (1- final-size) (1- ext-size) (logcdr i))))))

  (defthm logextu-as-loghead
    (implies (and (logextu-guard final-size ext-size i)
                  (<= final-size ext-size))
             (equal (loghead final-size (logext ext-size i))
                    (loghead final-size i)))
    :hints (("Goal" :in-theory (disable loghead-upper-bound logext-bounds)
             :induct (logextu-induction final-size ext-size i))))

  (defthm loghead-logextu
    (implies (and (<= ext-size final-size)
                  (<= size ext-size)
                  (logextu-guard final-size ext-size i)
                  (force (integerp size))
                  (force (>= size 0)))
             (equal (loghead size (logextu final-size ext-size i))
                    (loghead size i)))
    :hints (("Goal" :in-theory (e/d (logextu)
                                    (loghead-upper-bound logext-bounds))))))

;;;  Lemmas for UN/SIGNED-BYTE-P and INTEGER-LENGTH.

(defsection more-integer-length-lemmas
  :extension ihs/integer-length-lemmas

  (defthm unsigned-byte-p-integer-length
    (implies (and (integerp i)
                  (>= i 0)
                  (equal size (integer-length i)))
             (unsigned-byte-p size i))
    :rule-classes nil
    :hints (("Goal" :induct (sub1-logcdr-induction-1 size i))))

  (defthm integer-length-unsigned-byte
    (implies (unsigned-byte-p size i)
             (<= (integer-length i) size))
    :rule-classes nil
    :hints (("Goal" :induct (sub1-logcdr-induction-1 size i))))

  (defthm signed-byte-p-integer-length
    (implies (and (integerp i)
                  (integerp size)
                  (> size 0)
                  (equal size (+ (integer-length i) 1)))
             (signed-byte-p size i))
    :rule-classes nil
    :hints (("Goal" :induct (sub1-logcdr-induction-1 size i))))

  (local (defun integer-length-size-i-induction (size i)
           (declare (xargs :guard (and (integerp size)
                                       (integerp i))))
           (if (zip i)
               0
             (if (= i -1)
                 0
               (integer-length-size-i-induction (1- size) (logcdr i))))))

  (defthm integer-length-signed-byte
    (implies (signed-byte-p size i)
             (<= (+ (integer-length i) 1) size))
    :rule-classes nil
    :hints (("Goal" :induct (integer-length-size-i-induction size i)))))



;;;  Lemmas for ASH

(defsection more-ash-lemmas
  :extension ihs/ash-lemmas

  (local (defun ash-goes-to-0-induction (size count i)
           (cond ((or (not (integerp size)) ; This is for the benefit of
                      (< size 0)            ; UNSIGNED-BYTE-P, which has no guards.
                      (not (integerp i)))
                  t)
                 ((equal size 0) t)
                 ((zip count) t)
                 (t (ash-goes-to-0-induction (1- size) (1+ count) (logcdr i))))))

  ;; Added for Version_2.6:
  (local (in-theory (enable exponents-add-unrestricted)))

  (local (defthm unsigned-byte-p-1-crock
           (implies (unsigned-byte-p (+ -1 size) i)
                    (unsigned-byte-p size i))
           :hints (("Goal" :in-theory (enable unsigned-byte-p)))))

  (defthm unsigned-byte-p-ash
    (implies (and (unsigned-byte-p size i)
                  (integerp count)
                  (<= count 0))
             (unsigned-byte-p size (ash i count)))
    :hints (("Goal" :induct (ash-goes-to-0-induction size count i))))

  (defthm ash-goes-to-0
    (implies (and (unsigned-byte-p size i)
                  (integerp count)
                  (<= count 0)
                  (<= size (- count)))
             (equal (ash i count)
                    0))
    :hints (("Goal" :induct (ash-goes-to-0-induction size count i)))))

(in-theory (disable logops-recursive-definitions-theory))

; We can now use lemmas about LOGAND and LOGNOT to characterize all of the
; LOGOPS.


(defrule signed-byte-p-logops
  :parents (signed-byte-p logops-lemmas)
  :short "Lemmas showing the basic preservation of @(see signed-byte-p) by
 operations like @(see logand), @(see logior), etc."
  (and (implies (signed-byte-p size i)
                (signed-byte-p size (lognot i)))
       (implies (and (signed-byte-p size i)
                     (signed-byte-p size j))
                (and (signed-byte-p size (logior i j))
                     (signed-byte-p size (logxor i j))
                     (signed-byte-p size (logand i j))
                     (signed-byte-p size (logeqv i j))
                     (signed-byte-p size (lognand i j))
                     (signed-byte-p size (lognor i j))
                     (signed-byte-p size (logandc1 i j))
                     (signed-byte-p size (logandc2 i j))
                     (signed-byte-p size (logorc1 i j))
                     (signed-byte-p size (logorc2 i j)))))
  :enable (logior logxor logeqv lognand lognor logandc1 logandc2
                  logorc1 logorc2))




;;;****************************************************************************
;;;
;;;  Lemmas, round 5.  Byte functions.
;;;
;;;****************************************************************************

(defsection ihs/wrb-lemmas
  :parents (wrb logops-lemmas)

  (defthm unsigned-byte-p-wrb
    (implies (and (unsigned-byte-p n j)
                  (<= (+ (bsp-size bsp) (bsp-position bsp)) n)
                  (integerp i)
                  (integerp n)
                  (bspp bsp))
             (unsigned-byte-p n (wrb i bsp j)))
    :hints (("Goal" :in-theory (enable wrb bspp bsp-size bsp-position)))))


;;;****************************************************************************
;;;
;;;    Theory of truncation and extension of addition.
;;;
;;;****************************************************************************

;  We first prove the LOCAL lemma MOD-+-CASES, a very important lemma for
;  reasoning about truncating addition.

(local
 (encapsulate ()

   (local
    (defun local-sub (x y)
      (declare (xargs :guard (and (real/rationalp x)
				  (real/rationalp y))))
      (- x y)))

   (local
    (defthm local-sub-type-crock
      (implies (and (real/rationalp x)
		    (real/rationalp y))
	       (real/rationalp (local-sub x y)))))

   (local
    (defthm crock0
      (implies
       (and (real/rationalp x)
	    (real/rationalp y))
       (equal (equal (local-sub x y) (- x y))
	      t))
      :hints
      (("Goal"
	:in-theory (enable local-sub)))))

   (local
    (defthm crock1
      (implies
       (and (>= (+ x y) z)
	    (syntaxp (eq x 'x))
	    (syntaxp (eq y 'y))
	    (real/rationalp x)
	    (real/rationalp y)
	    (real/rationalp z))
       (equal (mod (+ x y) z) (mod (+ z (local-sub (+ x y) z)) z)))))

   (local
    (defthm crock2
      (implies
       (and (< x z)
	    (< y z)
	    (>= (+ x y) z)
	    (real/rationalp x)
	    (real/rationalp y)
	    (real/rationalp z))
       (and (>= (local-sub (+ x y) z) 0)
	    (< (local-sub (+ x y) z) z)))))

   (local (in-theory (disable local-sub)))

   (local
    (defthm crock3
      (implies
       (and (< x z)
	    (< y z)
	    (real/rationalp x)
	    (>= x 0)
	    (real/rationalp y)
	    (>= y 0)
	    (real/rationalp z)
	    (> z 0))
       (equal (mod (+ x y) z)
	      (if (< (+ x y) z)
		  (+ x y)
		(- (+ x y) z))))
      :hints
      (("Goal" :in-theory (disable associativity-of-+
				   commutativity-of-+
				   associativity-of-*
				   commutativity-of-*)))))

   (local
    (defthm crock4
      (implies
       (and (syntaxp (eq x 'x))
	    (syntaxp (eq y 'y))
	    (force (real/rationalp x))
	    (force (real/rationalp y))
	    (force (real/rationalp z))
	    (force (not (equal z 0))))
       (equal (mod (+ x y) z)
	      (mod (+ (mod x z) (mod y z)) z)))
      :hints
      (("Goal"
	:use mod-+))))

   (defthm mod-+-cases
     (implies (and (real/rationalp x)
                   (real/rationalp y)
                   (real/rationalp z)
                   (> z 0))
              (equal (mod (+ x y) z)
                     (if (< (+ (mod x z) (mod y z)) z)
                         (+ (mod x z) (mod y z))
                       (- (+ (mod x z) (mod y z)) z)))))))

(local (in-theory (disable mod-+-cases)))

(defsection more-loghead-lemmas
  :extension ihs/loghead-lemmas

  (defthm loghead-+-cancel-0
    (implies (and (force (integerp j))
                  (loghead-guard size i))
             (equal (equal (loghead size (+ i j)) (loghead size i))
                    (equal (loghead size j) 0)))
    :hints (("Goal" :in-theory (enable loghead mod-+-cases))))

  (defthm loghead-+-cancel
    (implies (and (force (integerp size))
                  (>= size 0)
                  (force (integerp i))
                  (force (integerp j))
                  (force (integerp k)))
             (equal (equal (loghead size (+ i j)) (loghead size (+ i k)))
                    (equal (loghead size j) (loghead size k))))
    :hints (("Goal" :in-theory (enable loghead mod-+-cases))))

  (defthm loghead-+-loghead
    (implies (and (force (integerp size))
                  (>= size 0)
                  (force (integerp i))
                  (force (integerp j)))
             (equal (loghead size (+ i (loghead size j)))
                    (loghead size (+ i j))))))

; Now the analogous lemmas for LOGEXT.  These are hideous proofs! Can you do
; better?

(defsection more-logext-lemmas
  :extension ihs/logext-lemmas

  (local (defthm sum-constants
           (implies (and (syntaxp (constant-syntaxp x))
                         (syntaxp (constant-syntaxp y))
                         (equal sum (+ x y)))
                    (equal (+ x y z) (+ sum z)))))

  (local (defthm open-logcons
           (implies (syntaxp (constant-syntaxp b))
                    (equal (logcons b i)
                           (let ((b (bfix b)) (i (ifix i)))
                             (+ b (* 2 i)))))
           :hints (("Goal" :in-theory (enable logcons)))))

  (local (defthm logcar-i+j+2*k
           (implies (and (integerp i)
                         (integerp j)
                         (integerp k))
                    (equal (logcar (+ i j (* 2 k)))
                           (logcar (+ i j))))
           :hints (("Goal" :use ((:instance logcar-i+2*j (i (+ i j)) (j k)))))))

  (local (defthm logcar-+
     (implies (and (integerp i)
	   (integerp j))
      (equal (logcar (+ i j))
	     (b-xor (logcar i) (logcar j))))
     :hints (("Goal" :in-theory (enable b-xor)))))

  (local (defthm distributivity-reverse
     (equal (+ (* i j) (* i k))
	    (* i (+ j k)))))

  (local (in-theory (disable distributivity)))

  (local (defthm logext-+
           (implies (and (integerp size)
                         (< 0 size)
                         (integerp i)
                         (integerp j))
                    (equal (logext size (+ i j))
                           (cond ((equal size 1)
                                  (if (equal (b-xor (logcar i) (logcar j)) 0)
                                      0
                                    -1))
                                 (t (logcons (b-xor (logcar i) (logcar j))
                                             (logext (1- size)
                                                     (+ (logcdr i) (logcdr j)
                                                        (b-and (logcar i) (logcar j)))))))))
           :hints (("Goal" :in-theory (enable logext* b-and b-xor)))))

  (local (defthm not-equal-1+2*/2*
           (implies (and (integerp i)
                         (integerp j))
                    (not (equal (+ 1 (* 2 i)) (* 2 j))))
           :hints (("Goal" :in-theory (disable logcar-i+2*j)
                    :use ((:instance logcar-i+2*j (i 1) (j i))
                          (:instance logcar-i+2*j (i 0) (j j)))))))

  (local (defthm logext-+-cancel-bit
           (implies (and (integerp size)
                         (> size 0)
                         (integerp i)
                         (integerp j)
                         (bitp c))
                    (equal (equal (logext size (+ c i)) (logext size (+ c j)))
                           (equal (logext size i) (logext size j))))
           :hints (("Goal"
                    :in-theory (e/d (logext* bitp) ())
                    :restrict ((logext-+ ((size size) (i 2) (j (* 2 l)))
                                         ((size size) (i 2) (j (* 2 m)))))
                    :induct (sub1-logcdr-induction-2-w/carry size i j c)))))

  (defthm logext-+-cancel
    (implies (and (integerp size)
                  (> size 0)
                  (integerp i)
                  (integerp j)
                  (integerp k))
             (equal (equal (logext size (+ i j)) (logext size (+ i k)))
                    (equal (logext size j) (logext size k))))
    :hints (("Goal"
             :in-theory (e/d (bitp b-and b-xor logext*)
; Modified April 2016 by Matt K. with addition of type-set bit for {1}.
                             ((:t b-not$inline)))
             :restrict ((logext-+ ((size size) (i i) (j j))
                                  ((size size) (i i) (j k))
                                  ((size size) (i 1) (j (* 2 l)))
                                  ((size size) (i 1) (j (* 2 m)))))
             :induct (sub1-logcdr-induction-3 size i j k))))

  (defthm logext-+-logext
    (implies (and (integerp size)
                  (> size 0)
                  (integerp i)
                  (integerp j))
             (equal (logext size (+ i (logext size j)))
                    (logext size (+ i j))))
    :hints (("Goal"
             :in-theory (e/d (logext*) (logext-+))
             :induct (sub1-logcdr-induction-3 size i j j)))))


;;;****************************************************************************
;;;
;;;  Theories
;;;
;;;****************************************************************************

(defsection logops-lemmas-theory
  :parents (logops-lemmas)
  :short "The \"minimal\" theory for the @(see logops-lemmas) book."
  :long "<p>This theory contains the theory @(see logops-definitions-theory),
plus all of the lemmas meant to be exported by the @(see logops-lemmas)
book.</p>"

  (deftheory logops-lemmas-theory
    (union-theories
     (theory 'logops-definitions-theory)
     (set-difference-theories (current-theory :here)
                              (current-theory 'begin-logops-lemmas)))))
