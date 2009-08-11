; logops-definitions.lisp  --  extensions to Common Lisp logical operations
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

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    "logops-definitions.lisp"
;;;
;;;    This book, along with "logops-lemmas", includes a theory of the Common
;;;    Lisp logical operations on numbers, a portable implementation of the
;;;    Common Lisp byte operations, extensions to those theories, and some
;;;    useful macros.  This book contains only definitions, lemmas
;;;    necessary to admit those definitions, and selected type lemmas.
;;;
;;;    Large parts of this work were inspired by Yuan Yu's Nqthm
;;;    specification of the Motorola MC68020.
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
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")

(deflabel logops
  :doc ":doc-section logops

   Definitions and lemmas about logical operations on integers.~/~/

   The books \"logops-definitions\" and \"logops-lemmas\" contain a theory of
   the logical operations on numbers defined by CLTL (Section 12.7), and a
   portable implementation of the CLTL byte manipulation functions (Section
   12.8).  These books also extend the CLTL logical operations and byte
   manipulation theory with a few new definitions, lemmas supporting
   those definitions, and useful macros.

   These books were developed as a basis for the formal specification and
   verification of hardware, where integers are used to represent binary
   signals and busses.  These books should be general enough, however, to be
   used as a basis for reasoning about packed data structures, bit-encoded
   sets, and other applications of logical operations on integers.~/")

(deflabel logops-definitions
  :doc ":doc-section logops
  A book a definitions of logical operations on numbers.
  ~/

  This book, along with \"logops-lemmas\", includes a theory of the Common Lisp
  logical operations on numbers, a portable implementation of the Common Lisp
  byte operations, extensions to those theories, and some useful macros.
  This book contains only definitions, lemmas necessary to admit those
  definitions, and selected type lemmas.  By `type lemmas' we mean any lemmas
  about the logical operations that we have found necessary to admit
  functions that use these operations as GOLD.  We have separated these `type
  lemmas' from the large body of other lemmas in \"logops-lemmas\" to allow a
  user to use this book to define GOLD functions without having to also
  include the extensive theory in \"logops-lemmas\".
  ~/

  The standard Common Lisp logical operations on numbers are defined on the
  signed integers, and return signed integers as appropriate.  This allows a
  high level, signed interpretation of hardware operations if that is
  appropriate for the specification at hand.  We also provide unsigned
  versions of several of the standard logical operations for use in
  specifications where fixed-length unsigned integers are used to model
  hardware registers and busses.  This view of hardware is used, for example,
  in Yuan Yu's Nqthm specification of the Motorola MC68020.~/")


;;;****************************************************************************
;;;
;;;    Environment.
;;;
;;;****************************************************************************

;;;  Global rules.

(include-book "ihs-init")
(include-book "ihs-theories")

(local (include-book "math-lemmas"))
(local (include-book "quotient-remainder-lemmas"))

(local (in-theory nil))

; From ihs-theories
(local (in-theory (enable basic-boot-strap)))

; From math-lemmas
(local (in-theory (enable ihs-math)))

; From integer-quotient-lemmas
(local (in-theory (enable quotient-remainder-rules)))


;;;****************************************************************************
;;;
;;;    Local Lemmas.
;;;
;;;****************************************************************************


(local
 (defthm x*y->-1
   (implies
    (and (force (real/rationalp x))
         (force (real/rationalp y))
         (or (and (> x 1) (>= y 1))
             (and (>= x 1) (> y 1))))
    (> (* x y) 1))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable x*y>1-positive)
	    :cases ((equal y 1)
		    (equal x 1))))))

(local
 (defthm x*y->=-1
   (implies (and (force (real/rationalp x))
		 (force (real/rationalp y))
		 (>= x 1)
		 (>= y 1))
	    (>= (* x y) 1))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable <-*-left-cancel)
     :use ((:instance <-*-left-cancel (z y) (x 1) (y x)))))))

(local
 (defthm x-<-y*z
   (implies (and (force (real/rationalp x))
		 (force (real/rationalp y))
		 (force (real/rationalp z))
		 (or (and (<= 0 y) (< x y) (<= 1 z))
		     (and (< 0 y) (<= x y) (< 1 z))))
	    (and (< x (* y z))
		 (< x (* z y))))
   :hints (("Goal" :in-theory (disable <-*-left-cancel <-y-*-y-x)
	    :use ((:instance <-*-left-cancel (z y) (x 1) (y z)))))))

(local
 (defthm x-<=-y*z
   (implies (and (force (real/rationalp x))
		 (force (real/rationalp y))
		 (force (real/rationalp z))
		 (<= x y)
		 (<= 0 y)
		 (<= 1 z))
	    (and (<= x (* y z))
		 (<= x (* z y))))
   :hints (("Goal" :in-theory (disable <-*-left-cancel <-y-*-y-x)
	    :use ((:instance <-*-left-cancel (z y) (x 1) (y z)))))))


;;;****************************************************************************
;;;
;;;    Basic type lemmas for built-ins:
;;;
;;;  LOGAND i j
;;;  LOGANDC1 i j
;;;  LOGANDC2 i j
;;;
;;;  Note that these functions are all DISABLED at this point
;;;
;;;****************************************************************************

(deflabel begin-logops-definitions)

;;;  The system can't guess that LOGAND is always an integer, and thus
;;;  LOGANDC1 and LOGANDC2 don't have good type precriptions either.

(defthm logand-type
  (integerp (logand i j))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :in-theory (enable logand)))
  :doc ":doc-section logand-type
  Type-Prescription: (INTEGERP (LOGAND I J)).
  ~/~/~/")

(defthm logandc1-type
  (integerp (logandc1 i j))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :in-theory (enable logandc1)))
  :doc ":doc-section logandc1-type
  Type-Prescription: (INTEGERP (LOGANDC1 I J)).
  ~/~/~/")

(defthm logandc2-type
  (integerp (logandc2 i j))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :in-theory (enable logandc2)))
  :doc ":doc-section logandc2-type
  Type-Prescription: (INTEGERP (LOGANDC2 I J)).
  ~/~/~/")


;;;****************************************************************************
;;;
;;;    Definitions -- Round 1.
;;;
;;;  Type predicates and functions.
;;;
;;;  BITP b
;;;  BFIX b
;;;  ZBP x
;;;  UNSIGNED-BYTE-P bits i
;;;  SIGNED-BYTE-P bits i
;;;
;;;****************************************************************************

(defun bitp (b)
  ":doc-section logops-definitions
  A predicate form of the type declaration (TYPE BIT b).
  ~/~/~/"
  (declare (xargs :guard t))
  (or (equal b 0) (equal b 1)))

(defun bfix (b)
  ":doc-section logops-definitions
  (BFIX b) coerces any object to a bit (0 or 1) by coercing non-1 objects to 0.
  ~/~/~/"
  (declare (xargs :guard t))
  (if (equal b 1) 1 0))

(defun zbp (x)
  ":doc-section logops-definitions
  (ZBP x) tests for `zero bits'.  Any object other than 1 is considered a
  zero bit.
  ~/~/~/"
  (declare (xargs :guard (bitp x)))
  (equal (bfix x) 0))

#| Deleted by Matt K. for v2-7 as unsigned-byte-p becomes built-in in ACL2.
   Note that the documentation for unsigned-byte-p will be missing in
   a small image, so we instead introduce a new :doc-section just below.
   Also, we locally enable this function and also its subfunction,
   integer-range-p, in order for this book to certify much as it did before.
(defun unsigned-byte-p (bits i)
  ":doc-section logops-definitions
  A predicate form of the type declaration (TYPE (UNSIGNED-BYTE bits) i).
  ~/~/~/"
  (declare (xargs :guard t))
  (and (integerp bits)
       (>= bits 0)
       (integerp i)
       (>= i 0)
       (< i (expt 2 bits))))
|#

(defdoc unsigned-byte-p-lemmas
  ":doc-section logops-definitions
  Lemmas about unsigned-byte-p.
  ~/~/~/")

#| Deleted by Matt K. for v2-7 as signed-byte-p becomes built-in in ACL2.
   Note that the documentation for signed-byte-p will be missing in
   a small image, so we instead introduce a new :doc-section just below.
   Also, we locally enable this function and also its subfunction,
   integer-range-p, in order for this book to certify much as it did before.
(defun signed-byte-p (bits i)
  ":doc-section logops-definitions
  A predicate form of the type declaration (TYPE (SIGNED-BYTE bits) i).
  ~/~/~/"
  (declare (xargs :guard t))
  (and (integerp bits)
       (> bits 0)
       (integerp i)
       (>= i (- (expt 2 (- bits 1))))
       (< i (expt 2 (- bits 1)))))
|#

(defdoc signed-byte-p-lemmas
  ":doc-section logops-definitions
  Lemmas about signed-byte-p.
  ~/~/~/")

(local (in-theory (enable unsigned-byte-p signed-byte-p integer-range-p)))

;;;  Type rules for BITP.

(defthm bitp-forward
  (implies
   (bitp i)
   (and (integerp i)
        (>= i 0)
        (< i 2)))
  :rule-classes :forward-chaining
  :doc ":doc-section bitp
  Forward: (BITP i) implies i is an integer and 0 <= i < 2.
  ~/~/~/")

(defthm bitp-bfix
  (bitp (bfix b))
  :doc ":doc-section bitp
  Rewrite: (BITP (BFIX b)).
  ~/~/~/")

(defthm bitp-mod-2
  (implies
   (integerp i)
   (bitp (mod i 2)))
  :rule-classes
  ((:rewrite)
   (:generalize
    :corollary
    (implies
     (integerp i)
     (or (equal (mod i 2) 0)
	 (equal (mod i 2) 1)))))
  :hints
  (("Goal" :in-theory (enable linearize-mod)))
  :doc ":doc-section bitp
  Rewrite: (BITP (MOD i 2)).
  ~/
  This rule is also stored as a :GENERALIZE rule for MOD.~/~/")

(local (in-theory (disable bitp)))

;;;  Type rules for BFIX

(defthm bfix-bitp
  (implies
   (bitp b)
   (equal (bfix b) b))
  :hints
  (("Goal"
    :in-theory (enable bitp)))
  :doc ":doc-section bfix
  Rewrite: (BFIX b) = b, when b is a bit.
  ~/~/~/")

(local (in-theory (disable bfix)))

;;;  Type rules for UNSIGNED-BYTE-P

(defthm unsigned-byte-p-forward
  (implies
   (unsigned-byte-p bits i)
   (and (integerp i)
        (>= i 0)
        (< i (expt 2 bits))))
  :rule-classes :forward-chaining
  :doc ":doc-section unsigned-byte-p-lemmas
  Forward: (UNSIGNED-BYTE-P bits i) implies 0 <= i < 2**bits.
  ~/~/~/")

(defthm unsigned-byte-p-unsigned-byte-p
  (implies
   (and (unsigned-byte-p size i)
	(integerp size1)
	(>= size1 size))
   (unsigned-byte-p size1 i))
  :rule-classes nil
  :hints
  (("Goal" :in-theory (disable expt-is-weakly-increasing-for-base>1)
    :use ((:instance expt-is-weakly-increasing-for-base>1
		     (r 2) (i size) (j size1)))))
  :doc ":doc-section logops-definitions
  NIL: (UNSIGNED-BYTE-P size i) implies (UNSIGNED-BYTE-P size1 i), 
  when size1 >= size.
  ~/~/~/")

(local (in-theory (disable unsigned-byte-p)))

;;;  SIGNED-BYTE-P-FORWARD

(defthm signed-byte-p-forward
  (implies
   (signed-byte-p bits i)
   (and (integerp i)
        (>= i (- (expt 2 (- bits 1))))
        (< i (expt 2 (- bits 1)))))
  :rule-classes :forward-chaining
  :doc ":doc-section logops-definitions
  Forward: (SIGNED-BYTE-P bits i) -(2**(bits - 1)) <= i < 2**(bits - 1).
  ~/~/~/")

(local (in-theory (disable signed-byte-p)))

;;;****************************************************************************
;;;
;;;  Definition -- Round 2.
;;;
;;;  Extensions to the CLTL logical operations and byte functions.
;;;
;;;  IFLOOR i j
;;;  IMOD i j
;;;  EXPT2 n
;;;
;;;  LOGCAR i
;;;  LOGCDR i
;;;  LOGCONS b i
;;;  LOGBIT pos i
;;;  LOGMASK size
;;;  LOGMASKP i
;;;  LOGHEAD size i
;;;  LOGTAIL pos i
;;;  LOGAPP size i j
;;;  LOGRPL size i j
;;;  LOGEXT size i
;;;  LOGREV size i
;;;  LOGSAT size i
;;;
;;;  LOGEXTU final-size ext-size i
;;;  LOGNOTU size i
;;;  ASHU size i cnt
;;;  LSHU size i cnt
;;;
;;;  After the definitions, we define a guard macro for each that has a
;;;  non-trivial guard, and then define :TYPE-PRESCRIPTIONS for them.  We
;;;  always define our own :TYPE-PRESCRIPTIONS in insure that we always have
;;;  the strongest ones possible when this book is loaded.  Note that we
;;;  consider IFLOOR, IMOD, and EXPT2 to be abbreviations.
;;;  
;;;****************************************************************************

(defun ifloor (i j)
  ":doc-section logops-definitions
  (IFLOOR i j) is the same as floor, except that it coerces its
  arguments to integers.
  ~/~/~/"
  (declare (xargs :guard (and (integerp i)
                              (integerp j)
                              (not (= 0 j)))))
  (floor (ifix i) (ifix j)))

(defun imod (i j)
  ":doc-section logops-definitions
  (IMOD i j) is the same as mod, except that it coerces its
  arguments to integers.
  ~/~/~/"
  (declare (xargs :guard (and (integerp i)
                              (integerp j)
                              (not (= 0 j)))))
  (mod (ifix i) (ifix j)))

(defun expt2 (n)
  ":doc-section logops-definitions
  (EXPT2 n) is the same as 2^n, except that it coerces its
  argument to a natural.
  ~/~/~/"
  (declare (xargs :guard (and (integerp n)
                              (<= 0 n))))
  (expt 2 (nfix n)))

(defun logcar (i)
  ":doc-section logops-definitions
  (LOGCAR i) is the CAR of an integer conceptualized as a bit-vector.
  ~/~/~/"
  (declare (xargs :guard (integerp i)))
  (imod i 2))

(defun logcdr (i)
  ":doc-section logops-definitions
  (LOGCDR i) is the CDR of an integer conceptualized as a bit-vector.
  ~/~/~/"
  (declare (xargs :guard (integerp i)))
  (ifloor i 2))

(defun logcons (b i)
  ":doc-section logops-definitions
  (LOGCONS b i) is the CONS operation for integers conceptualized as
  bit-vectors.
  ~/
  For clarity and efficiency, b is required to be BITP.~/~/"
  (declare (xargs :guard (and (bitp b)
                              (integerp i))))
  (let ((b (bfix b))
	(i (ifix i)))
    (+ b (* 2 i))))

(defun logbit (pos i)
  ":doc-section logops-definitions
  (LOGBIT pos i) returns the bit of i at bit-position pos.
  ~/
  This is a binary equivalent to the Common Lisp function (LOGBITP pos i).~/~/"
  (declare (xargs :guard (and (integerp pos)
                              (>= pos 0)
                              (integerp i))))
  (if (logbitp pos i) 1 0))

(defun logmask (size)
  ":doc-section logops-definitions
  (LOGMASK size) creates a low-order, size-bit mask.
  ~/~/~/"
  (declare (xargs :guard (and (integerp size)
                              (>= size 0))))
  (- (expt2 size) 1))

(defun logmaskp (i)
  ":doc-section logops-definitions
  (LOGMASKP i) recognizes positive masks.
  ~/~/~/"
  (declare (xargs :guard t))
  (and (integerp i)
       (>= i 0)
       (equal i (- (expt2 (integer-length i)) 1))))

(defun loghead (size i)
  ":doc-section logops-definitions
  (LOGHEAD size i) returns the size low-order bits of i.
  ~/~/
  By convention we define (LOGHEAD 0 i) as 0, but this definition is a bit
  arbitrary.~/"   
  (declare (xargs :guard (and (integerp size)
                              (>= size 0)
                              (integerp i))))
  (imod i (expt2 size)))

(defun logtail (pos i)
  ":doc-section logops-definitions
  (LOGTAIL pos i) returns the high-order part of i starting at bit position
  pos.
  ~/~/~/"
  (declare (xargs :guard (and (integerp pos)
                              (>= pos 0)
                              (integerp i))))
  (ifloor i (expt2 pos)))

(defun logapp (size i j) 
  ":doc-section logops-definitions
  (LOGAPP size i j) is a binary append of i to j.
  ~/~/
  LOGAPP is a specification for merging integers.  Note that i is truncated 
  to size bits before merging with j.~/"
  (declare (xargs :guard (and (integerp size)
                              (>= size 0)
                              (integerp i)
                              (integerp j))))
  (let ((j (ifix j)))
    (+ (loghead size i) (* j (expt2 size)))))

(defun logrpl (size i j) 
  ":doc-section logops-definitions
  (LOGRPL size i j) replaces the size low-order bits of j with the size
  low-order bits of i.
  ~/
  LOGRPL is a common specification for the result of storing short values into
  long words, i.e., the short value simply replaces the head of the long
  word.  This function is equivalent to (WRB i (BSP size 0) j).~/~/"
  (declare (xargs :guard (and (integerp size)
                              (>= size 0)
                              (integerp i)
                              (integerp j))))
  (logapp size i (logtail size j)))

(defun logext (size i)
  ":doc-section logops-definitions
  (LOGEXT size i) \"sign-extends\" i to an integer with size - 1 significant
  bits. 
  ~/
  LOGEXT coerces any integer i into a signed integer by `sign extending'
  the bit at size - 1 to infinity.  We specify LOGEXT in terms of the `size'
  of the result instead of as a bit position because we normally specify
  integer subranges by the number of significant (including sign) bits.

  Note that for consistency with SIGNED-BYTE-P, size must be strictly greater
  than 0.~/~/"
  (declare (xargs :guard (and (integerp size)
                              (> size 0)
                              (integerp i))))
  (logapp (1- size) i (if (logbitp (1- size) i) -1 0)))

(defun logrev1 (size i j)
  ":doc-section logrev1
  Helper function for LOGREV.
  ~/~/~/"
  (declare (xargs :guard (and (integerp size)
                              (>= size 0)
                              (integerp i)
                              (integerp j))))
  (if (zp size)
      (ifix j)
      (logrev1 (- size 1) (logcdr i) (logcons (logcar i) j))))

(defun logrev (size i)
  ":doc-section logops-definitions
  (LOGREV size i) bit-reverses the size low-order bits of i, discarding the
  high-order bits.
  ~/~/
  Normally we don't think of bit-reversing as a logical operation,
  even though its hardware implementation is trivial: simply reverse the
  wires leading from the source to the destination.  LOGREV is included as a
  logical operation to support the specification of DSPs, which may 
  provide bit-reversing in their address generators to improve the
  performance of the FFT.

  LOGREV entails a recursive definition of bit-reversing via the helper
  function LOGREV1.~/"
  (declare (xargs :guard (and (integerp size)
                              (>= size 0)
                              (integerp i))))
  (logrev1 size i 0))

(defun logsat (size i)
  ":doc-section logops-definitions
  (LOGSAT size i) coerces i to a size-bit signed integer by saturation.
  ~/~/
  If i can be represented as a size-bit signed integer, then i is returned.
  Otherwise, (LOGSAT size i) returns the size-bit signed integer closest to
  i. For positive i, this will be 2^(size-1) - 1.  For negative i, this will
  be -(2^(size - 1)).

  Note that for consistency with SIGNED-BYTE-P, size must be strictly
  greater than 0.~/"

  (declare (xargs :guard (and (integerp size)
			      (< 0 size)
			      (integerp i))))

  (let* ((i (ifix i))			;?
	 (val (expt2 (1- size)))
	 (maxval (1- val))
	 (minval (- val)))

    (if (>= i maxval)
	maxval
      (if (<= i minval)
	  minval
	i))))

(defun logextu (final-size ext-size i)
  ":doc-section logops-definitions
  (LOGEXTU final-size ext-size i) \"sign-extends\" i with (LOGEXT ext-size i),
  then truncates the result to final-size bits, creating an unsigned integer.
  ~/~/~/"
  (declare (xargs :guard (and (integerp final-size)
                              (>= final-size 0)
                              (integerp ext-size)
                              (> ext-size 0)
                              (integerp i))
		  :guard-hints (("Goal" :in-theory (disable exponents-add)))))
  (loghead final-size (logext ext-size i)))

(defun lognotu (size i)
  ":doc-section logops-definitions
  (LOGNOTU size i) is an unsigned logical NOT, truncating (LOGNOT i) to size
  bits. 
  ~/~/~/"
  (declare (xargs :guard (and (integerp size)
                              (>= size 0)
                              (integerp i))))
  (loghead size (lognot i)))

(defun ashu (size i cnt)
  ":doc-section logops-definitions
  (ASHU size i cnt) is an unsigned version of ASH.
  ~/
  ASHU is a fixed-width version of ASH. The integer i is first coerced to a
  signed integer by sign-extension, then shifted with ASH, and finally
  truncated back to a size-bit unsigned integer.~/~/"
  (declare (xargs :guard (and (integerp size)
                              (> size 0)
                              (integerp i)
                              (integerp cnt))
		  :guard-hints (("Goal" :in-theory (disable exponents-add)))))
  (loghead size (ash (logext size i) cnt)))

(defun lshu (size i cnt)
  ":doc-section logops-definitions
  (LSHU size i cnt) is an unsigned logical shift.
  ~/
  LSHU shifts i by cnt bits by first coercing i to an unsigned integer,
  performing the shift, and coercing the result to an unsigned integer.
  For cnt >= 0, (LSHU size i cnt) = (ASHU size i cnt).  This is a model
  of a size-bit logical shift register.~/~/"
  (declare (xargs :guard (and (integerp size)
                              (>= size 0)
                              (integerp i)
                              (integerp cnt))))
  (loghead size (ash (loghead size i) cnt)))

;;;Matt: You will find instances of these throughout "logops-lemmas". These
;;;should all be redundant now, but in case they aren't I'll leave them in.


;;;  Guard macros

(defmacro logbit-guard (pos i)
  ":doc-section logops-definitions
   (LOGBIT-GUARD pos i) is a macro form of the guards for LOGBIT.
   ~/~/~/"
  `(AND (FORCE (INTEGERP ,pos))
        (FORCE (>= ,pos 0))
        (FORCE (INTEGERP ,i))))

(defmacro logmask-guard (size)
  ":doc-section logops-definitions
  (LOGMASK-GUARD size) is a macro form of the guards for LOGMASK.
  ~/~/~/"
  `(AND (FORCE (INTEGERP ,size))
        (FORCE (>= ,size 0))))

(defmacro loghead-guard (size i)
  ":doc-section logops-definitions
   (LOGHEAD-GUARD size i) is a macro form of the guards for LOGHEAD.
   ~/~/~/"
  `(AND (FORCE (INTEGERP ,size))
        (FORCE (>= ,size 0))
        (FORCE (INTEGERP ,i))))

(defmacro logtail-guard (pos i)
  ":doc-section logops-definitions
   (LOGTAIL-GUARD pos i) is a macro form of the guards for LOGTAIL.
   ~/~/~/"
  `(AND (FORCE (INTEGERP ,pos))
        (FORCE (>= ,pos 0))
        (FORCE (INTEGERP ,i))))

(defmacro logapp-guard (size i j)
  ":doc-section logops-definitions
   (LOGAPP-GUARD size i j) is a macro form of the guards for LOGAPP.
   ~/~/~/"
  `(AND (FORCE (INTEGERP ,size))
        (FORCE (>= ,size 0))
        (FORCE (INTEGERP ,i))
        (FORCE (INTEGERP ,j))))

(defmacro logrpl-guard (size i j)
  ":doc-section logops-definitions
   (LOGRPL-GUARD size i j) is a macro form of the guards for LOGRPL.
   ~/~/~/"
  `(AND (FORCE (INTEGERP ,size))
        (FORCE (>= ,size 0))
        (FORCE (INTEGERP ,i))
        (FORCE (INTEGERP ,j))))

(defmacro logext-guard (size i)
  ":doc-section logops-definitions
   (LOGEXT-GUARD size i) is a macro form of the guards for LOGEXT.
   ~/~/~/"
  `(AND (FORCE (INTEGERP ,size))
        (FORCE (> ,size 0))
        (FORCE (INTEGERP ,i))))

(defmacro logrev-guard (size i)
  ":doc-section logops-definitions
  (LOGREV-GUARD size i) is a macro form of the guards for LOGREV.
  ~/~/~/"
  `(AND (FORCE (INTEGERP ,size))
        (FORCE (>= ,size 0))
        (FORCE (INTEGERP ,i))))

(defmacro logextu-guard (final-size ext-size i)
  ":doc-section logops-definitions
   (LOGEXTU-GUARD final-size ext-size i) is a macro form of the guards for
   LOGEXTU.~/~/~/"
  `(AND (FORCE (INTEGERP ,final-size))
        (FORCE (>= ,final-size 0))
        (FORCE (INTEGERP ,ext-size))
        (FORCE (> ,ext-size 0))
        (FORCE (INTEGERP ,i))))

(defmacro lognotu-guard (size i)
  ":doc-section logops-definitions
   (LOGNOTU-GUARD size i) is a macro form of the guards for LOGNOTU.
   ~/~/~/"
  `(AND (FORCE (INTEGERP ,size))
        (FORCE (>= ,size 0))
        (FORCE (INTEGERP ,i))))

(defmacro ashu-guard (size i cnt)
  ":doc-section logops-definitions
  (ASHU-GUARD size i cnt) is a macro form of the guards for ASHU.
  ~/~/~/"
  `(AND (FORCE (INTEGERP ,size))
        (FORCE (> ,size 0))
        (FORCE (INTEGERP ,i))
        (FORCE (INTEGERP ,cnt))))

(defmacro lshu-guard (size i cnt)
  ":doc-section logops-definitions
  (LSHU-GUARD size i cnt) is a macro form of the guards for LSHU.
  ~/~/~/"
  `(AND (FORCE (INTEGERP ,size))
        (FORCE (>= ,size 0))
        (FORCE (INTEGERP ,i))
        (FORCE (INTEGERP ,cnt))))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;    Type Lemmas for the new LOGOPS.  Each function is DISABLEd after we
;;;    have enough information about it (except for IFLOOR, IMOD, and EXPT2,
;;;    which are considered abbreviations).  We prove even the most obvious
;;;    type lemmas because you never know what theory this book will be
;;;    loaded into, and unless the theory is strong enough you may not get
;;;    everthing you need.
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

;;; IFLOOR

(defthm ifloor-type
  (integerp (ifloor i j))
  :rule-classes :type-prescription
  :doc ":doc-section ifloor
  Type-prescription: (INTEGERP (IFLOOR I J)).
  ~/~/~/")

;;; IMOD

(defthm imod-type
  (integerp (imod i j))
  :rule-classes :type-prescription
  :doc ":doc-section imod
  Type-prescription: (INTEGERP (IMOD I J)).
  ~/~/~/")

;;; EXPT2

(defthm expt2-type
  (and (integerp (expt2 n))
       (< 0 (expt2 n)))
  :rule-classes :type-prescription
  :doc ":doc-section expt2
  Type-prescription: (AND (INTEGERP (EXPT2 N)) (< 0 (EXPT2 N))).
  ~/~/~/")

;;; LOGCAR

(defthm logcar-type
  (bitp (logcar i))
  :rule-classes
  ((:rewrite)
   (:type-prescription
    :corollary
    (and (integerp (logcar i))
	 (<= 0 (logcar i))))
   (:generalize
    :corollary
    (or (equal (logcar i) 0) (equal (logcar i) 1))))
  :doc ":doc-section logcar
  Rewrite: (BITP (LOGCAR i)).
  ~/
  This rule is also stored as appropriate :TYPE-PRESCRIPTION and
  :GENERALIZE rules.~/~/")

(local (in-theory (disable logcar)))

;;;  LOGCDR

(defthm logcdr-type
  (integerp (logcdr i))
  :rule-classes :type-prescription
  :doc ":doc-section logcdr
  Type-Prescription: (INTEGERP (LOGCDR I)).
  ~/~/~/")

(defthm logcdr-<-0
  (equal (< (logcdr i) 0)
	 (and (integerp i)
	      (< i 0)))
  :doc ":doc-section logcdr
  Rewrite: (LOGCDR i) < 0  EQUAL  i is an integer < 0.
  ~/~/~/")

(defthm justify-logcdr-induction
  (and (implies (> i 0)
		(< (logcdr i) i))
       (implies (< i -1)
		(< i (logcdr i))))
  :hints
  (("Goal"
    :in-theory (enable logcdr)))
  :doc ":doc-section logcdr
  Rewrite: (LOGCDR i) < i, when i > 0; (LOGCDR i) > i, when i < -1.
  ~/~/~/")

(local (in-theory (disable logcdr)))

;;;  LOGCONS

(defthm logcons-type
  (integerp (logcons b i))
  :rule-classes :type-prescription
  :doc ":doc-section logcons
  Type-prescription: (INTEGERP (LOGCONS b i)).
  ~/~/~/")

(defthm logcons-<-0
  (equal (< (logcons b i) 0)
	 (and (integerp i)
	      (< i 0)))
  :hints
  (("Goal"
    :in-theory (enable bfix))))

(local (in-theory (disable logcons)))

;;;  LOGBIT

(defthm logbit-type
  (bitp (logbit pos i))
  :rule-classes
  ((:rewrite)
   (:type-prescription
    :corollary
    (and (integerp (logbit pos i))
	 (>= (logbit pos i) 0))))
  :doc ":doc-section logbit
  Rewrite: (BITP (LOGBIT pos i)).
  ~/
  This rule is also stored as an appropriate :TYPE-PRESCRIPTION.~/~/")

(local (in-theory (disable logbit)))

;;;  LOGMASK

(defthm logmask-type
  (and (integerp (logmask i))
       (>= (logmask i) 0))
  :rule-classes :type-prescription
  :doc ":doc-section logmask
  Type-Prescription: (LOGMASK i) >= 0.
  ~/~/~/")

(local (in-theory (disable logmask)))

;;;  LOGMASKP

(local (in-theory (disable logmaskp)))          ;An obvious predicate.

;;;  LOGHEAD

(defthm loghead-type
  (and (integerp (loghead size i))
       (>= (loghead size i) 0))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :in-theory (enable imod)))
  :doc ":doc-section loghead
  Type-prescription: (LOGHEAD size i) >= 0.
  ~/~/~/")

(defthm unsigned-byte-p-loghead
  (implies
   (and (>= size1 size)
	(integerp size)
	(>= size 0)
	(integerp size1))
   (unsigned-byte-p size1 (loghead size i)))
  :hints
  (("Goal"
    :in-theory (e/d (unsigned-byte-p) (expt-is-weakly-increasing-for-base>1))
    :use ((:instance expt-is-weakly-increasing-for-base>1
		     (r 2) (i size) (j size1)))))
  :doc ":doc-section loghead
  Rewrite: (UNSIGNED-BYTE-P size1 (LOGHEAD size i)), when size1 >= size.
  ~/~/~/")

(defthm loghead-upper-bound
   (< (loghead size i) (expt 2 size))
  :rule-classes (:linear :rewrite)
  :doc ":doc-section loghead
  Linear: (LOGHEAD size i) < 2**size.
  ~/~/~/")

(local (in-theory (disable loghead)))

;;;  LOGTAIL

(defthm logtail-type
  (integerp (logtail pos i))
  :rule-classes :type-prescription
  :doc ":doc-section logcons
  Type-prescription: (INTEGERP (LOGTAIL POS I)).
  ~/~/~/")

(local (in-theory (disable logtail)))

;;;  LOGAPP

(defthm logapp-type
  (integerp (logapp size i j))
  :rule-classes :type-prescription
  :doc ":doc-section logcons
  Type-prescription: (INTEGERP (LOGAPP SIZE I J)).
  ~/~/~/")

(defthm logapp-<-0
  (implies
   (logapp-guard size i j)
   (equal (< (logapp size i j) 0)
	  (< j 0)))
  :hints
  (("Goal"
    :in-theory (e/d (loghead) (x-<-y*z))
    :use ((:instance x-<-y*z
                     (x (mod i (expt 2 size)))
                     (y (expt 2 size)) (z (abs j))))))
  :doc ":doc-section logapp
  Rewrite: (LOGAPP size i j) < 0 EQUAL j < 0.
  ~/~/~/")

(local (in-theory (disable logapp)))

;;;  LOGRPL

(defthm logrpl-type
  (integerp (logrpl size i j))
  :rule-classes :type-prescription
  :doc ":doc-section logcons
  Type-prescription: (INTEGERP (LOGRPL SIZE I J)).
  ~/~/~/")

(local (in-theory (disable logrpl)))

;;;  LOGEXT

(defthm logext-type
  (integerp (logext size i))
  :rule-classes :type-prescription
  :doc ":doc-section logext
  Type-Prescription: (INTEGERP (LOGEXT size i)).
  ~/~/~/")

;;;4 Misplaced Lemmas
(defthm expt-with-violated-guards
  (and
   (implies
    (not (integerp i))
    (equal (expt r i) 1))
   (implies
    (not (acl2-numberp r))
    (equal (expt r i)
	   (expt 0 i))))
  :hints
  (("Goal"
    :in-theory (enable expt))))

(defthm reduce-integerp-+-constant
  (implies
   (and (syntaxp (constant-syntaxp i))
	(integerp i))
   (iff (integerp (+ i j))
	(integerp (fix j)))))

(defthm how-could-this-have-been-left-out??
  (equal (* 0 x) 0)) 

(defthm this-needs-to-be-added-to-quotient-remainder-lemmas
  (implies
   (zerop y)
   (equal (mod x y)
	  (fix x)))
  :hints
  (("Goal"
    :in-theory (enable mod))))

(defthm logext-bounds
  (implies
   (< 0 size)
   (and
    (>= (logext size i) (- (expt 2 size)))
    (< (logext size i) (expt 2 size))))
  :rule-classes
  ((:linear :trigger-terms ((logext size i)))
   (:rewrite))
  :hints
  (("Goal"
    :in-theory (e/d (logapp loghead)
		    (expt-is-increasing-for-base>1 exponents-add))
    :use ((:instance expt-is-increasing-for-base>1
		     (r 2) (i (1- size)) (j size)))))
  :doc ":doc-section logext
  Linear: -(2**size) <= (LOGEXT size i) < 2**size.
  ~/~/~/")

(defthm signed-byte-p-logext
  (implies
   (and (>= size1 size)
	(> size 0)
        (integerp size1)
	(integerp size))
   (signed-byte-p size1 (logext size i)))
  :hints
  (("Goal"
    :in-theory (e/d (signed-byte-p logapp loghead)
                    (expt-is-weakly-increasing-for-base>1 exponents-add))
    :do-not '(eliminate-destructors)
    :use ((:instance expt-is-weakly-increasing-for-base>1
                     (r 2) (i (1- size)) (j (1- size1))))))
  :doc ":doc-section logext
  Rewrite: (SIGNED-BYTE-P size1 (LOGEXT size i)), when size1 >= size.
  ~/~/~/")

(local (in-theory (disable logext)))

;;;  LOGREV

(local
 (defthm logrev1-type
  (implies
   (>= j 0)
   (and (integerp (logrev1 size i j))
	(>= (logrev1 size i j) 0)))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :in-theory (enable logcons)))))

(defthm logrev-type
  (and (integerp (logrev size i))
       (>= (logrev size i) 0))
  :rule-classes :type-prescription
  :doc ":doc-section logrev
  Type-prescription: (LOGREV size i) >= 0.
  ~/~/~/")

(encapsulate ()

  (local
   (defun crock-induction (size size1 i j)
     (cond
      ((zp size) (+ size1 i j))		;To avoid irrelevance
      (t (crock-induction (1- size) (1+ size1) (logcdr i)
			  (logcons (logcar i) j))))))

  ;; This lemma could have used one of the deleted Type-Prescriptions, I
  ;; think the one for LOGCDR.

  (local
   (defthm unsigned-byte-p-logrev1
     (implies
      (and (unsigned-byte-p size1 j)
	   (integerp size)
	   (>= size 0))
      (unsigned-byte-p (+ size size1) (logrev1 size i j)))
     :rule-classes nil
     :hints
     (("Goal"
       :in-theory (e/d (expt logcar logcons unsigned-byte-p) (exponents-add))
       :induct (crock-induction size size1 i j)))))

  (defthm unsigned-byte-p-logrev
    (implies
     (and (>= size1 size)
	  (>= size 0)
	  (integerp size)
	  (integerp size1))
     (unsigned-byte-p size1 (logrev size i)))
    :hints
    (("Goal"
      :use ((:instance unsigned-byte-p-logrev1
		       (size size) (size1 0) (i i) (j 0))
	    (:instance unsigned-byte-p-unsigned-byte-p
		       (size size) (size1 size1) (i (logrev size i))))))
    :doc ":doc-section logrev
  Rewrite: (UNSIGNED-BYTE-P size1 (LOGREV size i)), when size1 >= size.
  ~/~/~/"))

(local (in-theory (disable logrev)))

;;;  LOGSAT

(defthm logsat-type
  (integerp (logsat size i))
  :rule-classes :type-prescription
  :doc ":doc-section logsat
  Type-Prescription: (INTEGERP (LOGSAT size i)).
  ~/~/~/")

; Added for Version_2.6.  Without it the following defthm appears to loop,
; though not within a single goal -- rather, by creating subgoal after subgoal
; after ....
(local (in-theory (enable exponents-add-unrestricted)))

(defthm logsat-bounds
  (implies
   (< 0 size)
   (and
    (>= (logsat size i) (- (expt 2 size)))
    (< (logsat size i) (expt 2 size))))
  :rule-classes
  ((:linear :trigger-terms ((logsat size i)))
   (:rewrite))
  :doc ":doc-section logsat
  Linear: -(2**size) <= (LOGSAT size i) < 2**size.
  ~/~/~/")

; Now we disable this rule; necessary for signed-byte-p-logsat.
(local (in-theory (disable exponents-add-unrestricted)))

(defthm signed-byte-p-logsat
  (implies
   (and (>= size1 size)
	(> size 0)
        (integerp size1)
	(integerp size))
   (signed-byte-p size1 (logsat size i)))
  :hints
  (("Goal"
    :in-theory (e/d (signed-byte-p)
                    (expt-is-weakly-increasing-for-base>1 exponents-add))
    :do-not '(eliminate-destructors)
    :use ((:instance expt-is-weakly-increasing-for-base>1
                     (r 2) (i (1- size)) (j (1- size1))))))
  :doc ":doc-section logsat
  Rewrite: (SIGNED-BYTE-P size1 (LOGSAT size i)), when size1 >= size.
  ~/~/~/")

(local (in-theory (disable logsat)))

;;;  LOGEXTU

(defthm logextu-type
  (and (integerp (logextu final-size ext-size i))
       (>= (logextu final-size ext-size i) 0))
  :rule-classes :type-prescription
  :doc ":doc-section logextu
  Type-prescription: (LOGEXTU final-size ext-size i) >= 0.
  ~/~/~/")

(defthm unsigned-byte-p-logextu
  (implies
   (and (>= size1 final-size)
	(>= final-size 0)
	(integerp final-size)
        (integerp size1))
   (unsigned-byte-p size1 (logextu final-size ext-size i)))
  :doc ":doc-section logextu
  Rewrite: (UNSIGNED-BYTE-P size1 (LOGEXTU final-size ext-size i)), 
           when size1 >= final-size.
  ~/~/~/")

(local (in-theory (disable logextu)))

;;;  LOGNOTU

(defthm lognotu-type
  (and (integerp (lognotu size i))
       (>= (lognotu size i) 0))
  :rule-classes :type-prescription
  :doc ":doc-section lognotu
  Type-prescription: (LOGNOTU size i) >= 0.
  ~/~/~/")

(defthm unsigned-byte-p-lognotu
  (implies
   (and (>= size1 size)
	(>= size 0)
	(integerp size)
        (integerp size1))
   (unsigned-byte-p size1 (lognotu size i)))
  :doc ":doc-section lognotu
  Rewrite: (UNSIGNED-BYTE-P size1 (LOGNOTU size i)), when size1 >= size.
  ~/~/~/")

(local (in-theory (disable lognotu)))

;;;  ASHU

(defthm ashu-type
  (and (integerp (ashu size i cnt))
       (>= (ashu size i cnt) 0))
  :rule-classes :type-prescription
  :doc ":doc-section ashu
  Type-prescription: (ASHU size i cnt) >= 0.
  ~/~/~/")

(defthm unsigned-byte-p-ashu
  (implies
   (and (>= size1 size)
	(>= size 0)
	(integerp size)
        (integerp size1))
   (unsigned-byte-p size1 (ashu size i cnt)))
  :doc ":doc-section ashu
  Rewrite: (UNSIGNED-BYTE-P size1 (ASHU size i cnt)), when size1 >= size.
  ~/~/~/")

(local (in-theory (disable ashu)))

;;;  LSHU

(defthm lshu-type
  (and (integerp (lshu size i cnt))
       (>= (lshu size i cnt) 0))
  :rule-classes :type-prescription
  :doc ":doc-section lshu
  Type-prescription: (LSHU size i cnt) >= 0.
  ~/~/~/")

(defthm unsigned-byte-p-lshu
  (implies
   (and (>= size1 size)
	(>= size 0)
	(integerp size)
        (integerp size1))
   (unsigned-byte-p size1 (lshu size i cnt)))
  :doc ":doc-section lshu
  Rewrite: (UNSIGNED-BYTE-P size1 (LSHU size i cnt)), when size1 >= size.
  ~/~/~/")

(local (in-theory (disable lshu)))


;;;****************************************************************************
;;;
;;;    DEFINITIONS -- Round 3.
;;;
;;;    A portable implementation and extension of the CLTL byte operations.
;;;    After the function definitions, we introduce a guard macro for those
;;;    with non-trivial guards.
;;;
;;;  BSP size pos
;;;  BSPP bsp
;;;  BSP-SIZE bsp
;;;  BSP-POS bsp
;;;  RDB bsp i
;;;  WRB i bsp j
;;;  RDB-TEST bsp i
;;;  RDB-FIELD bsp i
;;;  WRB-FIELD i bsp j
;;;  
;;;****************************************************************************

(deflabel logops-byte-functions
  :doc ":doc-section logops-definitions

  A portable implementation and extension of Common Lisp byte functions.
  ~/~/ 

  The proposed Common Lisp standard [X3J13 Draft 14.10] defines a number of
  functions that operate on subfields of integers.  These subfields are
  specified by (BYTE size position), which \"indicates a byte of width size
  and whose bits have weights 2^{position+size-1} through 2^{pos}, and whose
  representation is implementation dependent\".  Unfortunately, the standard
  does not specify what BYTE returns, only that whatever is returned is
  understood by the byte manipulation functions LDB, DPB, etc.

  This lack of complete specification makes it impossible for ACL2 to specify
  the byte manipulation functions of Common Lisp in a portable way.  For
  example AKCL uses (CONS size position) as a byte specifier, whereas another
  implementation might use a special data structure to represent (BYTE size
  position).  Since any theorem about the ACL2 built-ins is meant to be a
  theorem for all Common Lisp implementations, Acl2 cannot define BYTE.

  Therefore, we have provided a portable implementation of the byte
  operations specified by the draft standard.  This behavior of this
  implementation should be consistent with every Common Lisp that provides
  the standard byte operations.  Our byte specifier (BSP size pos) is
  analogous to CLTL's (BYTE size pos), where size and pos are nonnegative
  integers.  Note that the standard indicates that reading a byte of size 0
  returns 0, and writing a byte of size 0 leaves the destination unchanged.

  This table indicates the correspondance between the Common Lisp byte
  operations and our portable implementation:

  Common Lisp                               This Implementation
  ------ ----                               ---- --------------

  (BYTE size position)                      (BSP size position)
  (BYTE-SIZE bytespec)                      (BSP-SIZE bsp)
  (BYTE-POSITION bytespec)                  (BSP-POSITION bsp)
  (LDB bytespec integer)                    (RDB bsp integer)
  (DPB newbyte bytespec integer)            (WRB newbyte bsp integer)
  (LDB-TEST bytespec integer)               (RDB-TEST bsp integer)
  (MASK-FIELD bytespec integer)             (RDB-FIELD bsp integer)
  (DEPOSIT-FIELD newbyte bytespec integer)  (WRB-FIELD newbyte bsp integer)

  For more information, see the :DOC entries for the functions listed above.
  If you are concerned about the efficiency of this implementation, see 
  :DOC LOGOPS-EFFICIENCY-HACK.~/")

(defmacro bsp (size pos)
  ":doc-section logops-byte-functions
  (BSP size pos) returns a byte-specifier.
  ~/
  This specifier designates a byte whose width is size and whose bits have
  weights 2^(pos) through 2^(pos+size-1). Both size and pos must be
  nonnegative integers.
  ~/
  BSP is mnemonic for Byte SPecifier or Byte Size and Position, and is
  analogous to Common Lisp's (BYTE size position).

  BSP is implemented as a macro for simplicity and convenience.  One should
  always use BSP in preference to CONS, however, to ensure compatibility with
  future releases.~/" 
  `(CONS ,size ,pos))

(defun bspp (bsp)
  ":doc-section logops-byte-functions
  (BSPP bsp) recognizes objects produced by (BSP size pos).
  ~/~/~/"
  (declare (xargs :guard t))
  (and (consp bsp)
       (integerp (car bsp))
       (>= (car bsp) 0)
       (integerp (cdr bsp))
       (>= (cdr bsp) 0)))

(defun bsp-size (bsp)
 ":doc-section logops-byte-functions
  (BSP-SIZE (BSP size pos)) = size.
  ~/~/
  (BSP-SIZE bsp) is analogous to Common Lisp's (BYTE-SIZE bytespec).~/"
 (declare (xargs :guard (bspp bsp)))
 (car bsp))

(defun bsp-position (bsp) 
  ":doc-section logops-byte-functions
  (BSP-POSITION (BSP size pos)) = pos.
  ~/~/
  (BSP-POSITION bsp) is analogous to Common Lisp's (BYTE-POSITION bytespec).~/"
  (declare (xargs :guard (bspp bsp)))
  (cdr bsp))

(defun rdb (bsp i)
  ":doc-section logops-byte-functions
  (RDB bsp i) returns the byte of i specified by bsp.
  ~/~/
  (RDB bsp i) is analogous to Common Lisp's (LDB bytespec integer).~/"
  (declare (xargs :guard (and (bspp bsp)
                              (integerp i))))
  (loghead (bsp-size bsp) (logtail (bsp-position bsp) i)))

(defun wrb (i bsp j)
  ":doc-section logops-byte-functions
  (WRB i bsp j) writes the (BSP-SIZE bsp) low-order bits of i into the byte
  of j specified by bsp.
  ~/
  WRB is mnemonic for WRite Byte.~/
  (WRB i bsp j) is analogous to Common Lisp's (DPB newbyte bytespec integer).~/"
  (declare (xargs :guard (and (integerp i)
                              (bspp bsp)
                              (integerp j))))
  (logapp (bsp-position bsp)
          (loghead (bsp-position bsp) j)
          (logapp (bsp-size bsp)
                  i
                  (logtail (+ (bsp-size bsp) (bsp-position bsp)) j))))

(defun rdb-test (bsp i)
  ":doc-section logops-byte-functions
  (RDB-TEST bsp i) is true iff the field of i specified by bsp is nonzero.
  ~/~/
  (RDB-TEST bsp i) is analogous to Common Lisp's (LDB-TEST bytespec integer).~/"
  
  (declare (xargs :guard (and (bspp bsp)
                              (integerp i))))
  (not (equal (rdb bsp i) 0)))

(defun rdb-field (bsp i)
  ":doc-section logops-byte-functions
  (RDB-FIELD bsp i) is analogous to Common Lisp's (MASK-FIELD bytespec integer).
  ~/~/~/"
  (declare (xargs :guard (and (bspp bsp)
                              (integerp i))))
  (logand i (wrb -1 bsp 0)))

(defun wrb-field (i bsp j)
  ":doc-section logops-byte-functions
  (WRB-FIELD i bsp j) is analogous to Common Lisp's
  (DEPOSIT-FIELD newbyte bytespec integer).
  ~/~/~/"
  (declare (xargs :guard (and (integerp i)
                              (bspp bsp)
                              (integerp j))))
  (wrb (rdb bsp i) bsp j))

;;;Matt:  These should be redundant now.

;  Guard macros. 

(defmacro rdb-guard (bsp i)
  ":doc-section logops-byte-functions
  (RDB-GUARD bsp i) is a macro form of the guards for RDB, RDB-TEST, and
  RDB-FIELD.
  ~/~/~/"
  `(AND (FORCE (BSPP ,bsp))
        (FORCE (INTEGERP ,i))))

(defmacro wrb-guard (i bsp j)
  ":doc-section logops-byte-functions
  (WRB-GUARD i bsp j) is a macro form of the guards for WRB and WRB-FIELD.
  ~/~/~/"
  `(AND (FORCE (INTEGERP ,i))
        (FORCE (BSPP ,bsp))
        (FORCE (INTEGERP ,j))))


;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
;;;
;;;  Type lemmas for the byte functions.  Each function is DISABLED after we
;;;  have enough information about it.
;;;
;;;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

;;;  BSPP

(defthm bspp-bsp
  (implies
   (and (integerp size)
	(>= size 0)
	(integerp pos)
	(>= pos 0))
   (bspp (bsp size pos)))
  :hints
  (("Goal"
    :in-theory (enable bspp)))
  :doc ":doc-section bsp
  Rewrite: (BSPP (BSP size pos)).
  ~/~/~/")

(local (in-theory (disable bspp)))              ;An obvious Boolean.

;;;  BSP-SIZE

(defthm bsp-size-type
  (implies
   (bspp bsp)
   (and (integerp (bsp-size bsp))
        (>= (bsp-size bsp) 0)))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :in-theory (enable bspp)))
  :doc ":doc-section bsp-size
  Type-prescription: (BSP-SIZE bsp) > 0.
  ~/~/~/")

(local (in-theory (disable bsp-size)))

;;;  BSP-POSITION

(defthm bsp-position-type
  (implies
   (bspp bsp)
   (and (integerp (bsp-position bsp))
        (>= (bsp-position bsp) 0)))
  :rule-classes :type-prescription
  :hints
  (("Goal"
    :in-theory (enable bspp)))
  :doc ":doc-section bsp-position
  Type-prescription: (BSP-POSITION bsp) >= 0.
  ~/~/~/")

(local (in-theory (disable bsp-position)))

;;;  RDB

(defthm rdb-type
  (and (integerp (rdb bsp i))
       (>= (rdb bsp i) 0))
  :rule-classes :type-prescription
  :doc ":doc-section rdb
  Type-prescription: (RDB bsp i) >= 0.
  ~/~/~/")

(defthm unsigned-byte-p-rdb
  (implies
   (and (>= size (bsp-size bsp))
        (force (>= size 0))
        (force (integerp size))
	(force (bspp bsp)))
   (unsigned-byte-p size (rdb bsp i)))
  :doc ":doc-section rdb
  Rewrite: (UNSIGNED-BYTE-P size (RDB bsp i)), when size >= (BSP-SIZE bsp).
  ~/~/~/")

(defthm rdb-upper-bound
  (implies
   (force (bspp bsp))
   (< (rdb bsp i) (expt 2 (bsp-size bsp))))
  :rule-classes (:linear :rewrite)
  :doc ":doc-section rdb
  Linear: (RDB bsp i) < 2**(bsp-size bsp).
  ~/~/~/")

(defthm bitp-rdb-bsp-1
  (implies
   (equal (bsp-size bsp) 1)
   (bitp (rdb bsp i)))
  :hints
  (("Goal"
    :in-theory (enable bitp loghead)))
  :doc ":doc-section rdb
  Rewrite: (BITP (RDB bsp i)), when (BSP-SIZE bsp) = 1.
  ~/~/~/")

(local (in-theory (disable rdb)))

;;; WRB

(defthm wrb-type
  (integerp (wrb i bsp j))
  :rule-classes :type-prescription
  :doc ":doc-section wrb
  Type-Prescription: (INTEGERP (WRB i bsp j)).
  ~/~/~/")

(local (in-theory (disable wrb)))

;;;  RDB-TEST

(local (in-theory (disable rdb-test)))          ;An obvious predicate.

;;;  RDB-FIELD

#|

Need Type-Prescriptions to prove this.  I don't think we ever use this
function. 

(defthm rdb-field-type
  (and (integerp (rdb-field bsp i))
       (>= (rdb-field bsp i) 0))
  :rule-classes :type-prescription
  :doc ":doc-section rdb-field
  Type-prescription: (RDB-FIELD bsp i) >= 0.
  ~/~/~/")

|#

(local (in-theory (disable rdb-field)))

;;;  WRB-FIELD

(defthm wrb-field-type
  (integerp (wrb-field i bsp j))
  :rule-classes :type-prescription
  :doc ":doc-section wrb-field
  Type-Prescription: (INTEGERP (WRB-FIELD i bsp j)).
  ~/~/~/")

(local (in-theory (disable wrb-field)))


;;;****************************************************************************
;;;
;;;   Definitions -- Round 4.
;;;
;;;  Logical operations on single bits.
;;;
;;;  B-NOT i
;;;  B-AND i j
;;;  B-IOR i j
;;;  B-XOR i j
;;;  B-EQV i j
;;;  B-NAND i j
;;;  B-NOR i j
;;;  B-ANDC1 i j
;;;  B-ANDC2 i j
;;;  B-ORC1 i j
;;;  B-ORC2 i j
;;;
;;;****************************************************************************

(deflabel logops-bit-functions
 :doc ":doc-section logops-definitions
 Versions of the standard logical operations that operate on single bits.
 ~/~/

 We provide versions of the non-trivial standard logical operations that
 operate on single bits.  The reason that it is necessary to introduce these
 operations separate from the standard operations is the fact that LOGNOT
 applied to a BITP object never returns a BITP.  All arguments to these
 functions must be BITP, and we prove that each returns a BITP integer.  We
 define each function explicitly in terms of 0 and 1 to simplify
 reasoning.~/")

(defun b-not (i)
  ":doc-section logops-bit-functions
  B-NOT ~/~/~/"
  (declare (xargs :guard (bitp i)))
  (if (zbp i) 1 0))

(defun b-and (i j)
  ":doc-section logops-bit-functions
  B-AND ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (if (zbp i) 0 (if (zbp j) 0 1)))

(defun b-ior (i j)
  ":doc-section logops-bit-functions
  B-IOR ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (if (zbp i) (if (zbp j) 0 1) 1))

(defun b-xor (i j)
  ":doc-section logops-bit-functions
  B-XOR ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (if (zbp i) (if (zbp j) 0 1) (if (zbp j) 1 0)))

(defun b-eqv (i j)
  ":doc-section logops-bit-functions
  B-EQV ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (if (zbp i) (if (zbp j) 1 0) (if (zbp j) 0 1)))

(defun b-nand (i j)
  ":doc-section logops-bit-functions
  B-NAND ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (if (zbp i) 1 (if (zbp j) 1 0)))

(defun b-nor (i j)
  ":doc-section logops-bit-functions
  B-NOR ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (if (zbp i) (if (zbp j) 1 0) 0))

(defun b-andc1 (i j)
  ":doc-section logops-bit-functions
  B-ANDC1 ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (if (zbp i) (if (zbp j) 0 1) 0))

(defun b-andc2 (i j)
  ":doc-section logops-bit-functions
  B-ANDC2 ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (if (zbp i) 0 (if (zbp j) 1 0)))

(defun b-orc1 (i j)
  ":doc-section logops-bit-functions
  B-ORC1 ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (if (zbp i) 1 (if (zbp j) 0 1)))

(defun b-orc2 (i j)
  ":doc-section logops-bit-functions
  B-ORC2 ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (if (zbp i) (if (zbp j) 1 0) 1))

(defthm bit-functions-type
  (and (bitp (b-not i))
       (bitp (b-and i j))
       (bitp (b-ior i j))
       (bitp (b-xor i j))
       (bitp (b-eqv i j))
       (bitp (b-nand i j))
       (bitp (b-nor i j))
       (bitp (b-andc1 i j))
       (bitp (b-andc2 i j))
       (bitp (b-orc1 i j))
       (bitp (b-orc2 i j)))
  :rule-classes
  ((:rewrite)
   (:type-prescription :corollary (and (integerp (b-not i))
				       (>= (b-not i) 0)))
   (:type-prescription :corollary (and (integerp (b-and i j))
				       (>= (b-and i j) 0)))
   (:type-prescription :corollary (and (integerp (b-ior i j))
				       (>= (b-ior i j) 0)))
   (:type-prescription :corollary (and (integerp (b-xor i j))
				       (>= (b-xor i j) 0)))
   (:type-prescription :corollary (and (integerp (b-eqv i j))
				       (>= (b-eqv i j) 0)))
   (:type-prescription :corollary (and (integerp (b-nand i j))
				       (>= (b-nand i j) 0)))
   (:type-prescription :corollary (and (integerp (b-nor i j))
				       (>= (b-nor i j) 0)))
   (:type-prescription :corollary (and (integerp (b-andc1 i j))
				       (>= (b-andc1 i j) 0)))
   (:type-prescription :corollary (and (integerp (b-andc2 i j))
				       (>= (b-andc2 i j) 0)))
   (:type-prescription :corollary (and (integerp (b-orc1 i j))
				       (>= (b-orc1 i j) 0)))
   (:type-prescription :corollary (and (integerp (b-orc2 i j))
				       (>= (b-orc2 i j) 0))))
  :doc ":doc-section logops-bit-functions
  Rewrite: All of the bit functions return BITP integers
  ~/
  We also prove an appropriate :TYPE-PRESCRIPTION for each.~/~/")


;;;****************************************************************************
;;;
;;;    Theories
;;;
;;;****************************************************************************

(defconst *logops-functions*
  '(binary-LOGIOR
    binary-LOGXOR binary-LOGAND binary-LOGEQV LOGNAND LOGNOR LOGANDC1
    LOGANDC2 LOGORC1 LOGORC2 LOGNOT LOGTEST LOGBITP ASH
    LOGCOUNT INTEGER-LENGTH
    BITP SIGNED-BYTE-P UNSIGNED-BYTE-P
    LOGCAR LOGCDR LOGCONS LOGBIT LOGMASK LOGMASKP LOGHEAD LOGTAIL
    LOGAPP LOGRPL LOGEXT LOGREV1 LOGREV LOGSAT
    LOGNOTU LOGEXTU ASHU LSHU
    BSPP BSP-SIZE BSP-POSITION RDB WRB RDB-TEST RDB-FIELD WRB-FIELD
    B-NOT B-AND B-IOR B-XOR B-EQV B-NAND B-NOR B-ANDC1 B-ANDC2 B-ORC1 B-ORC2)
  ":doc-section logops-definitions
  A list of all functions considered to be part of the theory of logical
  operations on numbers.
  ~/~/~/")

(deftheory logops-functions *logops-functions*
  :doc ":doc-section logops-definitions
  A theory consisting of all function names of functions considered to be
  logical operations on numbers.
  ~/~/

  If you are using the book \"logops-lemmas\", you will need to DISABLE this
  theory in order to use the lemmas contained therein, as most of the logical
  operations on numbers are non-recursive.~/")

(deftheory logops-definitions-theory
  (union-theories
   (set-difference-theories
    (set-difference-theories            ;Everything in this book ...
     (universal-theory :here)
     (universal-theory 'begin-logops-definitions))
    *logops-functions*)                 ;Minus all of the definitions.
    (defun-type/exec-theory *logops-functions*))        ;Plus basic type info
                                                        ;and executables. 
  :doc ":doc-section logops-definitions
  The `minimal' theory for the book \"logops-definitions\".
  ~/~/

  This theory contains the DEFUN-TYPE/EXEC-THEORY (which see) of all
  functions considered to be logical operations on numbers, and all lemmas
  (predominately `type lemmas') proved in this book.  All functions in the
  list *LOGOPS-FUNCTIONS* are DISABLEd.~/")



;;;****************************************************************************
;;;
;;;  DEFBYTETYPE name size s/u &key saturating-coercion doc.
;;;
;;;****************************************************************************

(defmacro defbytetype (name size s/u &key saturating-coercion doc)
  ":doc-section logops-definitions
  A macro for defining integer subrange types.
  ~/

  The \"byte types\" defined by DEFBYTETYPE correspond to the Common LISP
  concept of a \"byte\", that is, an integer with a fixed number of
  bits.  We extend the Common LISP concept to allow signed bytes.

  Example:

  (DEFBYTETYPE WORD 32 :SIGNED)

  Defines a new integer type of 32-bit signed integers, recognized by
  (WORD-P i).
  ~/

  General Form:

  (DEFBYTETYPE name size s/u &key saturating-coercion doc)

  The argument name should be a symbol, size should be a constant expression
  (suitable for DEFCONST) for an integer > 0, s/u is either :SIGNED or
  :UNSIGNED, saturating-coercion should be a symbol (default NIL) and doc
  should be a string.

  Each data type defined by DEFBYTETYPE produces a number of events:

  o  A constant *<name>-MAX*, set to the maximum value of the type.

  o  A constant *<name>-MIN*, set to the minimum value of the type.

  o  A predicate, (<pred> x), that recognizes either (UNSIGNED-BYTE-P size x)
     or (SIGNED-BYTE-P size x), depending on whether s/u was :UNSIGNED or
     :SIGNED respectively. This predicate is DISABLED.  The name of the
     predicate will be <name>-P.

  o  A coercion function, (<name> i), that coerces any object i to the correct
     type by LOGHEAD and LOGEXT for unsigned and signed integers
     respectively.  This function is DISABLED.  Any :DOC string provided will
     be placed with this function.

  o  A lemma showing that the coercion function actually does the correct
     coercion.

  o  A lemma that reduces calls of the coercion function when its argument
     satisfies the predicate.

  o  A forward chaining lemma from the predicate to the appropriate type
     information.

  o If :SATURATING-COERCION is specified, the value of this keyword argument
  should be a symbol.  A function of this name will be defined to provide a
  saturating coercion.  `Saturation' in this context means that values
  outside of the legal range for the type are coerced to the type by setting
  them to the nearest legal value, which will be either the minimum or
  maximum value of the type. This function will be DISABLEd, and a lemma will
  be generated that proves that this function returns the correct type.  Note
  that the :SATURATING-COERCION option is only valid for :SIGNED types.

  o  A theory named <name>-THEORY that includes the lemmas and the
  DEFUN-TYPE/EXEC-THEORY of the functions.~/"

  (declare (xargs :guard (and (symbolp name)
                              ;; How to say that SIZE is a constant expression?
                              (or (eq s/u :SIGNED) (eq s/u :UNSIGNED))
                              (implies saturating-coercion
				       (and (symbolp saturating-coercion)
					    (eq s/u :SIGNED)))
                              (implies doc (stringp doc)))))

  (let*
    ((max-constant (pack-intern name "*" name "-MAX*"))
     (min-constant (pack-intern name "*" name "-MIN*"))
     (predicate (pack-intern name name "-P"))
     (predicate-lemma (pack-intern name predicate "-" name))
     (coercion-lemma (pack-intern name "REDUCE-" name))
     (forward-lemma (pack-intern predicate predicate "-FORWARD"))
     (sat-lemma (pack-intern name predicate "-" saturating-coercion))
     (theory (pack-intern name name "-THEORY")))
  
    `(ENCAPSULATE ()
       (LOCAL (IN-THEORY (THEORY 'BASIC-BOOT-STRAP)))
       (LOCAL (IN-THEORY (ENABLE LOGOPS-DEFINITIONS-THEORY)))

       ;;  NB! These two ENABLEs mean that we have to have "logops-lemmas"
       ;;  loaded to do a DEFBYTETYPE.

       (LOCAL (IN-THEORY (ENABLE LOGHEAD-IDENTITY LOGEXT-IDENTITY)))

       (DEFCONST ,max-constant ,(case s/u
                                  (:SIGNED `(- (EXPT2 (- ,size 1)) 1))
                                  (:UNSIGNED `(- (EXPT2 ,size) 1))))
       (DEFCONST ,min-constant ,(case s/u
                                  (:SIGNED `(- (EXPT2 (- ,size 1))))
                                  (:UNSIGNED 0)))
       (DEFUN ,predicate (X)
	 (DECLARE (XARGS :GUARD T))
         ,(case s/u
            (:SIGNED `(SIGNED-BYTE-P ,size X))
            (:UNSIGNED `(UNSIGNED-BYTE-P ,size X))))
       (DEFUN ,name (I)
         ,@(when$ doc (list doc))
         (DECLARE (XARGS :GUARD (INTEGERP I)))
         ,(case s/u
            (:SIGNED `(LOGEXT ,size I))
            (:UNSIGNED `(LOGHEAD ,size I))))
       (DEFTHM ,predicate-lemma
	 (,predicate (,name I)))
       (DEFTHM ,coercion-lemma
	 (IMPLIES
	  (,predicate I)
	  (EQUAL (,name I) I)))
       (DEFTHM ,forward-lemma
         (IMPLIES
          (,predicate X)
          ,(case s/u
             (:SIGNED `(INTEGERP X))
             (:UNSIGNED `(AND (INTEGERP X)
			      (>= X 0)))))
         :RULE-CLASSES :FORWARD-CHAINING)
       ,@(when$ saturating-coercion
           (list
            `(DEFUN ,saturating-coercion (I)
               (DECLARE (XARGS :GUARD (INTEGERP I)))
	       (LOGSAT ,size I))
            `(DEFTHM ,sat-lemma
	       (,predicate (,saturating-coercion I)))))
       (IN-THEORY (DISABLE ,predicate ,name ,@(when$ saturating-coercion
                                                (list saturating-coercion))))
       (DEFTHEORY ,theory
         (UNION-THEORIES
          (DEFUN-TYPE/EXEC-THEORY
            '(,predicate ,name ,@(when$ saturating-coercion
                                   (list saturating-coercion))))
          '(,predicate-lemma ,coercion-lemma ,forward-lemma
			     ,@(when$ saturating-coercion
				 (list sat-lemma))))))))


;;;****************************************************************************
;;;
;;;  DEFWORD
;;;
;;;****************************************************************************

;;;  Recognizers for valid structure definitions and code generators.  See
;;;  the grammar in the :DOC for DEFWORD.

(defun defword-tuple-p (tuple)
  (or (and (true-listp tuple)
	   (or (equal (length tuple) 3)
	       (equal (length tuple) 4))
	   (symbolp (first tuple))
	   (integerp (second tuple))
	   (> (second tuple) 0)
	   (integerp (third tuple))
	   (>= (third tuple) 0)
	   (implies (fourth tuple) (stringp (fourth tuple))))
      (er hard 'defword
	  "A field designator for DEFWORD must be a list, the first ~
             element of which is a symbol, the second a positive integer, ~
             and the third a non-negative integer.  If a fouth element is ~
             provided it must be a string.  This object violates these ~
             constraints: ~p0" tuple)))

(defun defword-tuple-p-listp (struct)
  (cond
   ((null struct) t)
   (t (and (defword-tuple-p (car struct))
	   (defword-tuple-p-listp (cdr struct))))))

(defun defword-struct-p (struct)
  (cond
   ((true-listp struct) (defword-tuple-p-listp struct))
   (t (er hard 'defword
	  "The second argument of DEFWORD must be a true list. ~
           This object is not a true list: ~p0" struct))))

(defun defword-guards (name struct conc-name set-conc-name keyword-updater
			    doc) 
  (and
   (or (symbolp name)
       (er hard 'defword
	   "The name must be a symbol.  This is not a symbol: ~p0" name))
   (defword-struct-p struct)
   (or (symbolp conc-name)
       (er hard 'defword
	   "The :CONC-NAME must be a symbol. This is not a symbol: ~
            ~p0" conc-name))
   (or (symbolp set-conc-name)
       (er hard 'defword
	   "The :SET-CONC-NAME must be a symbol. This is not a symbol: ~
            ~p0" conc-name))
   (or (symbolp keyword-updater)
       (er hard 'defword
	   "The :KEYWORD-UPDATER must be a symbol. This is not a symbol: ~
            ~p0" conc-name))
   (or (implies doc (stringp doc))
       (er hard 'defword
	   "The :DOC must be a string.  This is not a string: ~p0" doc))))

(defun defword-accessor-name (name conc-name field)
  (pack-intern name conc-name field))

(defun defword-updater-name (name set-conc-name field)
  (pack-intern name set-conc-name field))

(defun defword-accessor-definitions (rdb name conc-name tuples)
  (cond ((consp tuples)
	 (let*
	   ((tuple (car tuples))
	    (field (first tuple))
	    (size (second tuple))
	    (pos (third tuple))
	    (doc (fourth tuple))
	    (accessor (defword-accessor-name name conc-name field)))
	   (cons
	    `(DEFMACRO ,accessor (WORD)
	       ,@(if doc (list doc) nil)
	       (LIST ',rdb (LIST 'BSP ,size ,pos) WORD))
	    (defword-accessor-definitions rdb name conc-name (cdr tuples)))))
	(t ())))

(defun defword-updater-definitions (wrb name set-conc-name tuples)
  (cond ((consp tuples)
	 (let*
	   ((tuple (car tuples))
	    (field (first tuple))
	    (size (second tuple))
	    (pos (third tuple))
	    (updater (defword-updater-name name set-conc-name field)))
	   (cons
	    `(DEFMACRO ,updater (VAL WORD)
	       (LIST ',wrb VAL (LIST 'BSP ,size ,pos) WORD))
	    (defword-updater-definitions wrb name set-conc-name
	      (cdr tuples))))) 
	(t ())))

(defloop defword-keyword-field-alist (name set-conc-name field-names)
  (for ((field-name in field-names))
    (collect (cons (intern-in-package-of-symbol (string field-name) :keyword)
		   (defword-updater-name name set-conc-name field-name)))))

(defun defword-keyword-updater-body (val args keyword-field-alist)
  (cond
   ((atom args) val)
   (t `(,(cdr (assoc (car args) keyword-field-alist)) ,(cadr args)
	,(defword-keyword-updater-body val (cddr args) keyword-field-alist)))))

(defun defword-keyword-updater-fn (form val args keyword-updater
					keyword-field-alist)
  (declare (xargs :mode :program))
  (let*
    ((keyword-field-names (strip-cars keyword-field-alist)))
    (cond
     ((not (keyword-value-listp args))
      (er hard keyword-updater
	  "The argument list in the macro invocation ~p0 ~
           does not match the syntax of a keyword argument ~
           list because ~@1."
	  form (reason-for-non-keyword-value-listp args)))
     ((not (subsetp (evens args) keyword-field-names))
      (er hard keyword-updater
	  "The argument list in the macro invocation ~p0 is not ~
           a valid keyword argument list because it contains the ~
           ~#1~[keyword~/keywords~] ~&1, which ~#1~[is~/are~] ~
            not the keyword ~#1~[form~/forms~] of any of the ~
            field names ~&2." 
	  FORM (set-difference-equal (evens args) keyword-field-names)
	  keyword-field-names))
     (t (defword-keyword-updater-body val args keyword-field-alist)))))

(defun defword-keyword-updater (name keyword-updater set-conc-name
				     field-names)
  `(DEFMACRO ,keyword-updater (&WHOLE FORM VAL &REST ARGS)
     (DEFWORD-KEYWORD-UPDATER-FN
       FORM VAL ARGS ',keyword-updater
       ',(defword-keyword-field-alist name set-conc-name field-names))))


(defmacro defword (name struct &key conc-name set-conc-name keyword-updater
			 doc) 
  ":doc-section logops-definitions
  A macro to define packed integer data structures.
  ~/

  Example:

  (DEFWORD FM9001-INSTRUCTION-WORD
    ((RN-A 4 0) (MODE-A 2 4) (IMMEDIATE 9 0) (A-IMMEDIATE 1 9)
     (RN-B 4 10) (MODE-B 2 14)
     (SET-FLAGS 4 16) (STORE-CC 4 20) (OP-CODE 4 24))
    :CONC-NAME ||
    :SET-CONC-NAME SET-
    :DOC \"Instruction word layout for the FM9001.\")

  The above example defines the instruction word layout for the FM9001.  The
  macro defines accessing macros (RN-A i), ... ,(OP-CODE i),
  updating macros (SET-RN-A val i), ... ,(SET-OP-CODE val i), and a keyword
  updating macro (UPDATE-FM9001-INSTRUCTION-WORD val &rest args).
  ~/

  General form:

  (DEFWORD name struct &key conc-name set-conc-name keyword-updater doc)

  The DEFWORD macro defines a packed integer data structure, for example an
  instruction word for a programmable processor or a status word.  DEFWORD is
  a simple macro that defines accessing and updating macros for the fields of
  the data structure. The utility of DEFWORD is mainly to simplify the
  specification of packed integer data structures, and to improve the
  readability of code manipulating these data structures without affecting
  performance. As long as the book \"logops-lemmas\" is loaded all of the
  important facts about the macro expansions should be available to the
  theorem prover.

  Arguments 

  name:  The name of the data structure, a symbol.

  struct : The field structure of the word. The form of this argument is
  given by the following grammar: 

  <tuple>  := (<field> <size> <pos> [ <doc> ])
  <struct> := () | (<tuple> . <struct>)

  where:

  (SYMBOLP <field>)
  (AND (INTEGERP <size>) (> <size> 0))
  (AND (INTEGERP <pos>) (>= <pos> 0))
  (STRINGP <doc>)

  In other words, a list of tuples, the first element being a symbol, the 
  second a positive integer, the third a nonnegative integer, and the
  optional fourth a string.

  Note that there are few other requirements on the <struct> other than the
  syntactic ones above.  For example, the FM9001 DEFWORD shows that a word
  may have more than one possible structure - the first 9 bits of the FM9001
  instruction word are either an immediate value, or they include the RN-A
  and MODE-A fields.  

  conc-name, set-conc-name: These are symbols whose print names will be
  concatenated with the field names to produce the name of the accessors and
  updaters respectively.  The default is <name>- and SET-<name>- respectively.
  The access and update macro names will be interned in the package of
  name.

  keyword-updater:  This is a symbol, and specifies the name of the keyword
  updating macro (see below).  The default is UPDATE-<name>.

  doc:  An optional documentation string.  If supplied, it will be attached
  to the label (see below).

  Interpretation

  DEFWORD creates an ACL2 DEFLABEL event named <name>, and attaches the <doc>
  to that label if it is supplied.

  Each tuple (<field> <size> <pos> [ <doc> ]) represents a <size>-bit field
  of a word at the bit position indicated.  Each field tuple produces an
  accessor macro 

  (<accessor> word) 

  where <accessor> is computed from the :conc-name (see above).  This
  accessor will expand into: 

  (RDB (BSP <size> <pos>) word).

  If the optional <doc> string is provided it will be attached to the
  accessor. 

  DEFWORD also generates an updating macro 

  (<updater> val word),

   where <updater> is computed from the :set-conc-name (see above).  This
  macro will expand to

  (WRB val (BSP <size> <pos>) word).

  The keyword updater

  (<keyword-updater> word &rest args)

  is equivalent to multiple nested calls of the updaters on the initial word.
  For example,

  (UPDATE-FM9001-INSTRUCTION-WORD WORD :RN-A 10 :RN-B 12)

  is the same as (SET-RN-A 10 (SET-RN-B 12 WORD)).~/"

  (cond
   ((not
     (defword-guards name struct conc-name set-conc-name keyword-updater doc)))
   (t
    (let*
      ((conc-name (if conc-name
                      conc-name
                    (pack-intern name name "-")))
       (set-conc-name (if set-conc-name
                          set-conc-name
                        (pack-intern name "SET-" name "-")))
       (keyword-updater (if keyword-updater
			    keyword-updater
			  (pack-intern name "UPDATE-" name)))
       (accessor-definitions
        (defword-accessor-definitions 'RDB name conc-name struct))
       (updater-definitions
        (defword-updater-definitions 'WRB name set-conc-name struct))
       (field-names (strip-cars struct)))

      `(ENCAPSULATE ()                  ;Only to make macroexpansion pretty.
         (DEFLABEL ,name ,@(if doc `(:DOC ,doc) nil))
         ,@accessor-definitions
         ,@updater-definitions
         ,(defword-keyword-updater
	    name keyword-updater set-conc-name field-names))))))

#|
Example:

(DEFWORD FM9001-INSTRUCTION
  ((RN-A 4 0) (MODE-A 2 4) (IMMEDIATE 9 0) (A-IMMEDIATE 1 9)
   (RN-B 4 10) (MODE-B 2 14)
   (SET-FLAGS 4 16) (STORE-CC 4 20) (OP-CODE 4 24))
  :CONC-NAME ||
  :SET-CONC-NAME SET-
  :DOC "Instruction word layout for the FM9001.")

|#


;;;****************************************************************************
;;;
;;;  Word/Bit Macros
;;;
;;;****************************************************************************

(deflabel word/bit-macros
  :doc ":doc-section logops-definitions
  Macros for manipulating integer words defined as contguous bits.
  ~/~/
  These macros were defined to support the functions produced by translating
  SPW .eqn files to ACL2 functions.~/")

(defun bind-word-to-bits-fn (bit-names n word)
  (cond
   ((endp bit-names) ())
   (t (cons `(,(car bit-names) (LOGBIT ,n ,word))
	    (bind-word-to-bits-fn (cdr bit-names) (1+ n) word)))))

(defmacro bind-word-to-bits (bit-names word &rest forms)
  ":doc-section word/bit-macros
  Bind variables to the contiguous low-order bits of word.
  ~/
  Example:

  (BIND-WORD-TO-BITS (A B C) I (B-AND A (B-IOR B C)))

  The above macro call will bind A, B, and C to the 0th, 1st, and 2nd bit
  of I, and then evaluate the logical expression under those bindings.
  The list of bit names is always intrepreted from low to high order.~/~/"

  (declare (xargs :guard (and (symbol-listp bit-names)
			      (no-duplicatesp bit-names))))

  `(LET ,(bind-word-to-bits-fn bit-names 0 word) ,@forms))

(defmacro make-word-from-bits (&rest bits)
  ":doc-section word/bit-macros
  Update the low-order bits of word with the indicated values.
  ~/
  Example:

  (MAKE-WORD-FROM-BITS A B C)

  The above macro call will build an unsigned integer from the bits A
  B, and C.  The list of bits is always intrepreted from low to high
  order. Note that the expression generated by this macro will coerce the
  values to bits before building the word.~/~/" 

  (cond
   ((endp bits) 0)
   (t `(LOGAPP 1 ,(car bits) (MAKE-WORD-FROM-BITS ,@(cdr bits))))))



;;;****************************************************************************
;;;
;;;    Efficiency Hack
;;;
;;;****************************************************************************

(deflabel logops-efficiency-hack
  :doc ":doc-section logops
  A hack that may increase the efficiency of logical operations and byte
  operations.~/

  WARNING: USING THIS HACK MAY RENDER ACL2 UNSOUND AND/OR CAUSE HARD LISP
  ERRORS.  Note that this warning only applies if we have made a mistake
  in programming this hack, or if you are calling these functions on values
  that do not satisfy their guards.~/

  Our extensions to the CLTL logical operations, and the portable
  implementations of byte functions are coded to simplify formal reasoning.
  Thus they are specified in terms of +, -, *, FLOOR, MOD, and EXPT.  One would
  not expect that these definitions provide the most efficient implementations
  of these functions, however.  Therefore, we have provided the following hack,
  which may decrease the runtime for large applications written in terms of the
  functions defined in this library.
  
  The hack consists of redefining the logical operations and byte
  functions \"behind the back\" of ACL2.  There is no guarantee that using
  this hack will improve efficiency.  There is also no formal guarantee that
  these new definitions are equivalent to those formally defined in the
  \"logops-definitions\" book, or that the guards are satisfied for these new
  definitions.  Thus, using this hack may render ACL2 unsound, or cause hard
  lisp errors if we have coded this hack incorrectly.  The hack consists of
  a set of definitions which are commented out in the source code for the
  book \"logops-definitions.lisp\".  To use this hack, do the following:

  1.  Locate the source code for \"logops-definitions.lisp\".
  
  2.  Look at the very end of the file.

  3.  Copy the hack definitions into another file.

  4.  Leave the ACL2 command loop and enter the Common Lisp ACL2 package.
  
  5.  Compile the hack definitions file and load the object code just created
      into an ACL2 session. 
  ")

#|
;;  Begin Efficiency Hack Definitions

;;  The heuristic behind this hack is that logical operations are faster than
;;  arithmetic operations (esp. FLOOR and MOD), and the idea that it is
;;  faster to look up a value from a table than to create new integers.  We
;;  believe that for typical hardware specification applications that many of
;;  the integers presented to LOGHEAD and LOGEXT will already be in their
;;  normalized forms.
;;
;;  We define macros, e.g., |logmask|, that represent a simple efficient
;;  definition of the functions for use when the second heuristic fails.  We
;;  define macros, e. g., |fast-logmask| that define the table
;;  lookup-versions given certain preconditions.

#+monitor-logops (defvar |*loghead-monitor*| #(0 0 0 0))
#+monitor-logops (defvar |*logext-monitor*| #(0 0 0 0))
#+monitor-logops (defvar |*rdb-monitor*| #(0 0 0 0 0 0 0))
#+monitor-logops (defvar |*wrb-monitor*| #(0 0 0 0 0 0 0))

#+monitor-logops
(defun |reset-logops-monitors| ()
  (setf |*loghead-monitor*| #(0 0 0 0))
  (setf |*logext-monitor*| #(0 0 0 0))
  (setf |*rdb-monitor*| #(0 0 0 0 0 0 0))
  (setf |*wrb-monitor*| #(0 0 0 0 0 0 0)))

#+monitor-logops
(defun |print-logops-monitors| ()
  (|print-size-monitor| 'LOGHEAD |*loghead-monitor*|)
  (|print-size-monitor| 'LOGEXT |*logext-monitor*|)
  (|print-bsp-monitor| 'RDB |*rdb-monitor*|)
  (|print-bsp-monitor| 'WRB |*wrb-monitor*|))

#+monitor-logops
(defun |size-monitor| (monitor size i)
  (incf (aref monitor 0))		
  (if (eq (type-of i) 'BIGNUM) (incf (aref monitor 1)))
  (if (< i 0) (incf (aref monitor 2))) 
  (if (< size 32) (incf (aref monitor 3))))

#+monitor-logops
(defun |print-size-monitor| (fn monitor)
  (format t "~s was called: ~d times, on ~d BIGNUMS, on ~d negative ~
	       numbers,~%and ~d times with size < 32.~%~%"
	    fn (aref monitor 0) (aref monitor 1) (aref monitor 2)
	    (aref monitor 3)))

#+monitor-logops
(defun |bsp-monitor| (monitor bsp i)
  (let ((size (car bsp))
	  (pos (cdr bsp)))
    (incf (aref monitor 0))		
    (if (eq (type-of i) 'BIGNUM) (incf (aref monitor 1)))
    (if (< i 0) (incf (aref monitor 2))) 
    (if (< size 32) (incf (aref monitor 3)))
    (if (< pos 32) (incf (aref monitor 4)))
    (if (< (+ size pos) 32) (incf (aref monitor 5)))
    (if (= size 1) (incf (aref monitor 6)))))
  
#+monitor-logops
(defun |print-bsp-monitor| (fn monitor)
  (format t "~s was called: ~d times, on ~d BIGNUMS, on ~d negative ~
	       numbers,~%~
	       ~d times with size < 32, ~d times with pos < 32, ~%~
	       ~d times with size+pos < 32, and ~d times with size = 1.~%~%"
	    fn (aref monitor 0) (aref monitor 1) (aref monitor 2)
	    (aref monitor 3) (aref monitor 4) (aref monitor 5)
	    (aref monitor 6)))


(defconstant *logops-efficiency-hack-mask-table*
  #(#x00000000 #x00000001 #x00000003 #x00000007
	#x0000000F #x0000001F #x0000003F #x0000007F
	#x000000FF #x000001FF #x000003FF #x000007FF
	#x00000FFF #x00001FFF #x00003FFF #x00007FFF
	#x0000FFFF #x0001FFFF #x0003FFFF #x0007FFFF
	#x000FFFFF #x001FFFFF #x003FFFFF #x007FFFFF
	#x00FFFFFF #x01FFFFFF #x03FFFFFF #x07FFFFFF
	#x0FFFFFFF #x1FFFFFFF #x3FFFFFFF #x7FFFFFFF))

(defconstant *logops-efficiency-hack-mask-bar-table*
  #(#x-00000001 #x-00000002 #x-00000004 #x-00000008
	#x-00000010 #x-00000020 #x-00000040 #x-00000080
	#x-00000100 #x-00000200 #x-00000400 #x-00000800
	#x-00001000 #x-00002000 #x-00004000 #x-00008000
	#x-00010000 #x-00020000 #x-00040000 #x-00080000
	#x-00100000 #x-00200000 #x-00400000 #x-00800000
	#x-01000000 #x-02000000 #x-04000000 #x-08000000
	#x-10000000 #x-20000000 #x-40000000 #x-80000000))

(defconstant *logops-efficiency-hack-bit-mask-table*
  #(#x00000001 #x00000002 #x00000004 #x00000008
	#x00000010 #x00000020 #x00000040 #x00000080
	#x00000100 #x00000200 #x00000400 #x00000800
	#x00001000 #x00002000 #x00004000 #x00008000
	#x00010000 #x00020000 #x00040000 #x00080000
	#x00100000 #x00200000 #x00400000 #x00800000
	#x01000000 #x02000000 #x04000000 #x08000000
	#x10000000 #x20000000 #x40000000 #x80000000))

(defconstant *logops-efficiency-hack-bit-mask-bar-table*
  #(#x-00000002 #x-00000003 #x-00000005 #x-00000009
	#x-00000011 #x-00000021 #x-00000041 #x-00000081
	#x-00000101 #x-00000201 #x-00000401 #x-00000801
	#x-00001001 #x-00002001 #x-00004001 #x-00008001
	#x-00010001 #x-00020001 #x-00040001 #x-00080001
	#x-00100001 #x-00200001 #x-00400001 #x-00800001
	#x-01000001 #x-02000001 #x-04000001 #x-08000001
	#x-10000001 #x-20000001 #x-40000001 #x-80000001))

(defmacro |mask| (size)
  ;; size < 32
  `(AREF *LOGOPS-EFFICIENCY-HACK-MASK-TABLE* ,size))

(defmacro |mask-bar| (size)
  ;; size < 32
  `(AREF *LOGOPS-EFFICIENCY-HACK-MASK-BAR-TABLE* ,size))

(defmacro |bit-mask| (pos)
  ;; pos < 32
  `(AREF *LOGOPS-EFFICIENCY-HACK-BIT-MASK-TABLE* ,pos))

(defmacro |bit-mask-bar| (pos)
  ;; pos < 32
  `(AREF *LOGOPS-EFFICIENCY-HACK-BIT-MASK-BAR-TABLE* ,pos))

(defun logcar (i)
  (declare (type integer i))
  (if (oddp i) 1 0))

(defun logcdr (i)
  (declare (type integer i))
  (ash i -1))

(defun logcons (b i)
  (declare (type (integer 0 1) b) (type integer i))
  (logior b (ash i 1)))

(defmacro |logmask-bar| (size)
  `(ASH -1 ,size)))

(defmacro |logmask| (size)
  `(LOGNOT (|logmask-bar| ,size)))

(defun logmask (size)
  (declare (type (integer 0 *) size))
  (if (< size 32)
	  (|mask| size)
	(|logmask| size)))

(defmacro |loghead| (size i)
  (let ((mask (gensym)))
	`(LET ((,mask (IF (< ,size 32) (|mask| ,size) (|logmask| ,size))))
	   (IF (AND (>= ,i 0) (<= ,i ,mask))
	       ,i				;i already normalized.
	     (LOGAND ,i ,mask)))))

(defun loghead (size i)
  (declare (type (integer 0 *) size) (type integer i))
  #+monitor-logops (|size-monitor| |*loghead-monitor*| size i)
  (|loghead| size i))

(defmacro |logtail| (pos i)
  `(ASH ,i (- ,pos)))

(defun logtail (pos i)
  (declare (type (integer 0 *) pos) (type integer i))
  (|logtail| pos i))

(defmacro |logapp| (size i j)
  `(LOGIOR (LOGHEAD ,size ,i) (ASH ,j ,size)))

(defun logapp (size i j) 
  (declare (type (integer 0 *) size) (type integer i j))
  (|logapp| size i j))

(defparameter *logops-efficiency-hack-logrpl-bsp* '(0 . 0))

(defun logrpl (size i j)
  (declare (type (integer 0 *) size) (type integer i j))
  (setf (car *logops-efficiency-hack-logrpl-bsp*) size)
  (wrb i *logops-efficiency-hack-logrpl-bsp* j))

(defun logext (size i)
  (declare (type (integer 0 *) size) (type integer i))
  #+monitor-logops (|size-monitor| |*logext-monitor*| size i)
  (if (<= size 32)
	  (if (= (the fixnum size) 0)
	      0
	    (let ((pos (the fixnum (- (the fixnum size) 1))))
	      (if (<= 0 i)
		  (let ((mask (|mask| pos)))
		    (if (<= i mask)
			i
		      (if (logbitp pos i)
			  (logorc2 i mask)
			(logand i mask))))
		(let ((mask (|mask-bar| pos)))
		  (if (<= mask i)
		      i
		    (if (logbitp pos i)
			(logior i mask)
		      (logandc2 i mask)))))))
	(let ((pos (1- size)))
	  (if (<= 0 i)
	      (let ((mask (|logmask| pos)))
		(if (<= i mask)
		    i
		  (if (logbitp pos i)
		      (logorc2 i mask)
		    (logand i mask))))
	    (let ((mask (|logmask-bar| pos)))
	      (if (<= mask i)
		  i
		(if (logbitp pos i)
		    (logior i mask)
		  (logandc2 i mask))))))))
	      
;; In GCL, (BYTE size pos) = (CONS size pos) = (BSP size pos).
;;
;; Reading/writing single bits are an important use of RDB/WRB so we handle
;; them specially.  If the byte position is 0 we can also save a few
;; operations.

(defun rdb (bsp i)
  (declare (type cons bsp) (type integer i))
  #+monitor-logops (|bsp-monitor| |*rdb-monitor*| bsp i)
  (let ((size (car bsp))
	    (pos (cdr bsp)))
	(if (< size 32)
	    (if (= size 1)
		(if (logbitp pos i) 1 0)
	      (if (= pos 0)
		  (logand i (|mask| size))
		(logand (|logtail| pos i) (|mask| size))))
	  (if (= pos 0)
	      (logandc2 i (|logmask-bar| size))
	    (logandc2 (|logtail| pos i) (|logmask-bar| size))))))

(defun wrb (i bsp j)
  (declare (type cons bsp) (type integer i j))
  #+monitor-logops (|bsp-monitor| |*wrb-monitor*| bsp i)
  (let ((size (car bsp))
	    (pos (cdr bsp)))
	(if (< size 32)
	    (if (= size 1)
		(if (< pos 32)
		    (cond
		     ((= i 0) (logand j (|bit-mask-bar| pos)))
		     ((or (= i 1) (oddp i)) (logior j (|bit-mask| pos)))
		     (t (logand j (|bit-mask-bar| pos))))
		  (cond
		   ((= i 0) (logandc2 j (ash 1 pos)))
		   ((or (= i 1) (oddp i)) (logior j (ash 1 pos)))
		   (t (logandc2 j (ash 1 pos)))))
	      (if (= pos 0)
		  (logior (logand j (|mask-bar| size))
			  (|loghead| size i))
		(logior (logandc2 j (ash (|mask| size) pos))
			(ash (|loghead| size i) pos))))
	  (if (= pos 0)
	      (logior (logand j (|logmask-bar| size))
		      (|loghead| size i))
	    (logior (logandc2 j (ash (|logmask| size) pos))
		    (ash (|loghead| size i) pos))))))

(defun rdb-test (bsp i)
	(declare (type cons bsp) (type integer i))
	#+gcl
	(ldb-test bsp i)
	#-gcl
	(ldb-test (byte (car bsp) (cdr bsp)) i))

(defun rdb-field (bsp i)
	(declare (type cons bsp) (type integer i))
	#+gcl
	(mask-field bsp i)
	#-gcl
	(mask-field (byte (car bsp) (cdr bap)) i))

(defun wrb-field (i bsp j)
	(declare (type cons bsp) (type integer i j))
	#+gcl
	(deposit-field i bsp j)
	#-gcl
	(deposit-field i (byte (car bsp) (cdr bsp)) j))

;  MERGE-BYTE is optimized for merging bits.  This definition depends on
;  the strong guards from ACL2.

(defun merge-byte (i size pos j)
	(if (= i 0)
	    j
	  (+ j (if (= size 1)
		   (if (< pos 32)
		       (|bit-mask| pos)
		     (ash 1 pos))
		 (ash i pos)))))
 
;;  End Efficiency Hack Definitions
|#



