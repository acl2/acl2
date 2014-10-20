; basic-definitions.lisp  --  extensions to Common Lisp logical operations
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;; basic-definitions.lisp
;;;
;;; [Jared]: This book is a lighter-weight version of "logops-lemmas.lisp"
;;; which only defines the basic logical operations on words and bits, and
;;; omits functions like bsp, wrb, and rdb, the guard macros, and macros such
;;; as defword, defbytetype, etc.  All of these functions were originally part
;;; of logops-lemmas.lisp, with credit as follows:
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
(include-book "std/util/define" :dir :system)
(local (include-book "math-lemmas"))
(local (include-book "quotient-remainder-lemmas"))

(defxdoc logops
  :short "Definitions and lemmas about logical operations on integers."

  :long "<p>The books \"logops-definitions\" and \"logops-lemmas\" contain a
theory of the logical operations on numbers defined by CLTL (Section 12.7), and
a portable implementation of the CLTL byte manipulation functions (Section
12.8).  These books also extend the CLTL logical operations and byte
manipulation theory with a few new definitions, lemmas supporting those
definitions, and useful macros.</p>

<p>These books were developed as a basis for the formal specification and
verification of hardware, where integers are used to represent binary signals
and busses.  These books should be general enough, however, to be used as a
basis for reasoning about packed data structures, bit-encoded sets, and other
applications of logical operations on integers.</p>")

(defxdoc logops-definitions
  :short "A book a definitions of logical operations on numbers."

  :long "<p>This book, along with @(see logops-lemmas), includes a theory of
the Common Lisp logical operations on numbers, a portable implementation of the
Common Lisp byte operations, extensions to those theories, and some useful
macros.</p>

<p>This book contains only definitions, lemmas necessary to admit those
definitions, and selected type lemmas.  By \"type lemmas\" we mean any lemmas
about the logical operations that we have found necessary to verify the guards
of functions that use these operations.  We have separated these \"type
lemmas\" from the large body of other lemmas in @(see logops-lemmas) to allow a
user to use this book to define guard-verified functions without having to also
include the extensive theory in @('logops-lemmas').</p>

<p>The standard Common Lisp logical operations on numbers are defined on the
signed integers, and return signed integers as appropriate.  This allows a high
level, signed interpretation of hardware operations if that is appropriate for
the specification at hand.  We also provide unsigned versions of several of the
standard logical operations for use in specifications where fixed-length
unsigned integers are used to model hardware registers and busses.  This view
of hardware is used, for example, in Yuan Yu's Nqthm specification of the
Motorola MC68020.</p>")


; [Jared] some trivial rules that are useful for the MBE substitutions

(local (defthm ash-1-n
         (implies (natp n)
                  (equal (ash 1 n)
                         (expt 2 n)))))

(local (defthm logand-1
         (implies (integerp i)
                  (equal (logand i 1)
                         (mod i 2)))))

(local (defthm ash-minus-1
         (implies (integerp i)
                  (equal (ash i -1)
                         (floor i 2)))))

(local (defthm ash-plus-1
         (implies (integerp i)
                  (equal (ash i 1)
                         (* 2 i)))))

(local (defthm ash-minus-n
         (implies (and (integerp i)
                       (natp pos))
                  (equal (ash i (- pos))
                         (floor i (expt 2 pos))))))

(local (defthm ash-plus-n
         (implies (and (integerp i)
                       (natp pos))
                  (equal (ash i pos)
                         (* i (expt 2 pos))))))

(local (defthm logand-positive
         (implies (natp mask)
                  (<= 0 (logand i mask)))
         :rule-classes ((:linear))))

(encapsulate
  ()
  (local (defun my-induct (i size)
           (if (zp size)
               (list size i)
             (my-induct (ash i -1)
                        (- size 1)))))

  (defthmd mod-of-expt-2-is-logand
    (implies (and (integerp size)
                  (>= size 0)
                  (integerp i))
             (equal (mod i (expt 2 size))
                    (logand i (1- (ash 1 size)))))
    :hints(("Goal" :induct (my-induct i size)))))


;;;****************************************************************************
;;;
;;;    Definitions -- Round 1.
;;;
;;;  Type predicates and functions.
;;;
;;;  BITP b
;;;  BFIX b
;;;  LBFIX b
;;;  ZBP x
;;;
;;;****************************************************************************

(define bitp (b)
  :parents (logops-definitions)
  :short "Bit recognizer.  @('(bitp b)') recognizes 0 and 1."
  :long "<p>This is a predicate form of the @(see type-spec) declaration
@('(TYPE BIT b)').</p>"
  :returns bool
  :inline t
  :enabled t
  (or (eql b 0)
      (eql b 1)))

(define bfix (b)
  :parents (logops-definitions)
  :short "Bit fix.  @('(bfix b)') is a fixing function for @(see bitp)s.  It
 coerces any object to a bit (0 or 1) by coercing non-1 objects to 0."
  :long "<p>See also @(see lbfix).</p>"
  :inline t
  :returns bit
  :enabled t
  (if (eql b 1)
      1
    0))

(defsection lbfix
  :parents (logops-definitions)
  :short "Logical bit fix.  @('(lbfix b)') is logically identical to @('(bfix
b)') but executes as the identity.  It requires @('(bitp b)') as a guard, and
expands to just @('b')."
  :long "@(def lbfix)"

  (defmacro lbfix (x)
    `(mbe :logic (bfix ,x) :exec ,x)))

(define zbp
  :parents (logops-definitions)
  :short "Zero bit recognizer.  @('(zbp x)') tests for zero bits.  Any object
other than @('1') is considered to be a zero bit."
  ((x bitp))
  :returns bool
  :enabled t
  :inline t
  (mbe :logic (equal (bfix x) 0)
       :exec (/= (the (unsigned-byte 1) x) 1)))

(defsection bitp-basics
  :extension bitp

  (defthm bitp-bfix
    (bitp (bfix b)))

  (defthm bfix-bitp
    (implies (bitp b)
             (equal (bfix b) b))))



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

(define ifloor
  :parents (logops-definitions)
  :short "@('(ifloor i j)') is the same as @(see floor), except that it coerces
  its arguments to integers."
  ((i integerp)
   (j (and (integerp j)
           (not (= 0 j)))))
  :returns int
  :inline t
  :enabled t
  (mbe :logic (floor (ifix i) (ifix j))
       :exec (floor i j)))

(define imod
  :parents (logops-definitions)
  :short "@('(imod i j)') is the same as @(see mod), except that it coerces its
  arguments to integers."
  ((i integerp)
   (j (and (integerp j)
           (not (= 0 j)))))
  :returns int
  :inline t
  :enabled t
  (mbe :logic (mod (ifix i) (ifix j))
       :exec (mod i j)))

(define expt2
  :parents (logops-definitions)
  :short "@('(expt2 n)') is the same as @('(expt 2 n)'), except that it coerces
  its argument to a natural."
  ((n natp))
  :returns nat
  :enabled t
  :inline t
  (mbe :logic (expt 2 (nfix n))
       :exec (the unsigned-byte
                  (ash 1 (the unsigned-byte n)))))

(define logcar
  :parents (logops-definitions)
  :short "Least significant bit of a number."
  ((i integerp))
  :returns bit
  :long "<p>@('(LOGCAR i)') is the CAR of an integer conceptualized as a
bit-vector (where the least significant bit is at the head of the list).</p>

<p>In C notation, this computes @('i & 1').</p>"
  :enabled t
  :inline t
  (mbe :logic (imod i 2)
       :exec (the (unsigned-byte 1) (logand (the integer i) 1))))

(define logcdr
  :parents (logops-definitions)
  :short "All but the least significant bit of a number."
  ((i integerp))
  :returns int
  :long "<p>@('(logcdr i)') is the CDR of an integer conceptualized as a
bit-vector (where the least significant bit is at the head of the list).</p>

<p>In C notation, this computes @('i >> 1').</p>"
  :enabled t
  :inline t
  (mbe :logic (ifloor i 2)
       :exec (the integer (ash (the integer i) -1))))

(define logcons
  :parents (logops-definitions)
  :short "@('(logcons b i)') is the CONS operation for integers, conceptualized
as bit-vectors."
  ((b bitp     "LSB of the result.")
   (i integerp "All but the LSB of the result."))
  :returns int
  :long "<p>In C notation, this computes @('(i << 1) | b').</p>

<p>See also @(see logcar) and @(see logcdr).</p>"
  :inline t
  :enabled t
  (mbe :logic (let ((b (bfix b))
                    (i (ifix i)))
                (+ b (* 2 i)))
       :exec (the integer
                  (+ (the (unsigned-byte 1) b)
                     (the integer (ash i 1))))))

(define logbit
  :parents (logops-definitions logbitp)
  :short "@('(logbit pos i)') returns the bit of @('i') at bit-position @('pos')
as a @(see bitp), 0 or 1."
  ((pos natp)
   (i   integerp))
  :returns bit
  :long "<p>This is just like the Common Lisp function @('(logbitp pos i)'),
except that we return 1 or 0 (instead of t or nil).</p>

<p>In C notation, this is @('(i >> pos) & 1').</p>"
  :enabled t
  :inline t
  (if (logbitp pos i)
      1
    0))

(define logmask
  :parents (logops-definitions)
  :short "@('(logmask size)') creates a low-order, @('size')-bit mask."
  ((size natp))
  :returns nat
  :long "<p>In C notation, this is @('(1 << size) - 1').</p>"
  :enabled t
  :inline t
  (mbe :logic (- (expt2 size) 1)
       :exec (the unsigned-byte (1- (the unsigned-byte (ash 1 size))))))

(define logmaskp
  :parents (logops-definitions)
  :short "@('(logmaskp i)') recognizes positive masks."
  (i)
  :returns bool
  :enabled t
  (mbe :logic (and (integerp i)
                   (>= i 0) ;; silly, this is implied by the equality below
                   (equal i (- (expt2 (integer-length i)) 1)))
       :exec (and (integerp i)
                  (eql i (the unsigned-byte
                              (- (the unsigned-byte (ash 1 (integer-length i)))
                                 1))))))

(define bitmaskp
  :parents (logops-definitions)
  :short "@('(bitmaskp i)' recognizes positive masks.  It is similar to @(see
logmaskp) but respects @(see int-equiv)."
  ((i integerp))
  :returns bool
  :inline t
  (logmaskp (mbe :logic (ifix i)
                 :exec i)))

(define loghead
  :parents (logops-definitions)
  :short "@('(loghead size i)') returns the @('size') low-order bits of @('i')."
  ((size posp :type unsigned-byte)
   (i    integerp))
  :returns nat
  :long "<p>By convention we define @('(loghead 0 i)') as 0, but this
  definition is a bit arbitrary.</p>"
  :inline t
  :enabled t
  :split-types t
  (mbe :logic (imod i (expt2 size))
       ;; BOZO it'd be nicer to give this an :exec of (logand i (1- (ash 1
       ;; size))), but that'll require some additional lemmas...
       :exec
       (the unsigned-byte
            (logand i (the unsigned-byte
                           (1- (the unsigned-byte (ash 1 size))))))))

(defun-inline logtail (pos i)
  ":doc-section logops-definitions
  (LOGTAIL pos i) returns the high-order part of i starting at bit position
  pos.
  ~/~/~/"
  (declare (xargs :guard (and (integerp pos)
                              (>= pos 0)
                              (integerp i))))
  (mbe :logic (ifloor i (expt2 pos))
       :exec (ash i (- (the unsigned-byte pos)))))

(defun logapp (size i j)
  ":doc-section logops-definitions
  (LOGAPP size i j) is a binary append of i to j (where i effectively becomes
  the 'low' bits and j becomes the 'high' bits).
  ~/~/
  LOGAPP is a specification for merging integers.  Note that i is truncated to
  size bits before merging with j, and that j is also shifted to the left by
  size bits before the merge.~/"
  (declare (xargs :guard (and (integerp size)
                              (>= size 0)
                              (integerp i)
                              (integerp j))))
  (mbe :logic (let ((j (ifix j)))
                (+ (loghead size i) (* j (expt2 size))))
       ;; BOZO could do better than calling loghead with some work
       :exec (+ (loghead size i) (ash j size))))

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
                              (integerp j)))
           (inline logapp))
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
                              (integerp i))
                  :split-types t)
           (type unsigned-byte size)
           (type integer i))
  ;; BOZO could do better than this with MBE with some work, see centaur/bitops/sign-extend
  (let* ((size-1 (- size 1)))
    (declare (type unsigned-byte size-1))
    (logapp size-1 i
            (if (logbitp size-1 i)
                -1
              0))))

(defun logrev1 (size i j)
  ":doc-section logops-definitions
  Helper function for LOGREV.
  ~/~/~/"
  (declare (xargs :guard (and (integerp size)
                              (>= size 0)
                              (integerp i)
                              (integerp j))
                  :split-types t)
           (type unsigned-byte size)
           (type integer i j))
  (if (zp size)
      (mbe :logic (ifix j)
           :exec j)
    (logrev1 (the unsigned-byte (- size 1))
             (logcdr i)
             (logcons (logcar i) j))))

(defun-inline logrev (size i)
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
			      (integerp i))
                  :split-types t)
           (type unsigned-byte size)
           (type integer i))

  (let* ((i      (mbe :logic (ifix i) :exec i))
	 (val    (expt2 (the unsigned-byte (1- size))))
	 (maxval (the unsigned-byte (1- (the unsigned-byte val))))
	 (minval (- val)))
    (declare (type unsigned-byte val maxval)
             (type integer i minval))
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

(defthm ifloor-type
  (integerp (ifloor i j))
  :rule-classes :type-prescription
  :doc ":doc-section ifloor
  Type-prescription: (INTEGERP (IFLOOR I J)).
  ~/~/~/")

(defthm imod-type
  (integerp (imod i j))
  :rule-classes :type-prescription
  :doc ":doc-section imod
  Type-prescription: (INTEGERP (IMOD I J)).
  ~/~/~/")

(defthm expt2-type
  (natp (expt2 n))
  :rule-classes :type-prescription
  :doc ":doc-section expt2
  Type-prescription: (NATP (EXPT2 N)).
  ~/~/~/")

(defthm logcar-type
  (bitp (logcar i))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary (natp (logcar i)))
                 (:generalize :corollary
                              (or (equal (logcar i) 0)
                                  (equal (logcar i) 1))))
  :doc ":doc-section logcar
  Rewrite: (BITP (LOGCAR i)).
  ~/
  This rule is also stored as appropriate :TYPE-PRESCRIPTION and
  :GENERALIZE rules.~/~/")

(defthm logcdr-type
  (integerp (logcdr i))
  :rule-classes :type-prescription
  :doc ":doc-section logcdr
  Type-Prescription: (INTEGERP (LOGCDR I)).
  ~/~/~/")

(defthm logcons-type
  (integerp (logcons b i))
  :rule-classes :type-prescription
  :doc ":doc-section logcons
  Type-prescription: (INTEGERP (LOGCONS b i)).
  ~/~/~/")

(defthm logbit-type
  (bitp (logbit pos i))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary (natp (logbit pos i))))
  ;; BOZO want a generalize rule like in logcar?
  :doc ":doc-section logbit
  Rewrite: (BITP (LOGBIT pos i)).
  ~/
  This rule is also stored as an appropriate :TYPE-PRESCRIPTION.~/~/")

(defthm logmask-type
  (natp (logmask i))
  :rule-classes :type-prescription
  :doc ":doc-section logmask
  Type-Prescription: (NATP (LOGMASK i)).
  ~/~/~/")

(defthm loghead-type
  (natp (loghead size i))
  :rule-classes :type-prescription
  :doc ":doc-section loghead
  Type-prescription: (NATP (LOGHEAD size i)).
  ~/~/~/")

(defthm logtail-type
  (integerp (logtail pos i))
  :rule-classes :type-prescription
  :doc ":doc-section logcons
  Type-prescription: (INTEGERP (LOGTAIL POS I)).
  ~/~/~/")

(defthm logapp-type
  (integerp (logapp size i j))
  :rule-classes :type-prescription
  :doc ":doc-section logcons
  Type-prescription: (INTEGERP (LOGAPP SIZE I J)).
  ~/~/~/")

(defthm logrpl-type
  (integerp (logrpl size i j))
  :rule-classes :type-prescription
  :doc ":doc-section logcons
  Type-prescription: (INTEGERP (LOGRPL SIZE I J)).
  ~/~/~/")

(defthm logext-type
  (integerp (logext size i))
  :rule-classes :type-prescription
  :doc ":doc-section logext
  Type-Prescription: (INTEGERP (LOGEXT size i)).
  ~/~/~/")

(local (defthm logrev1-type
         (implies (>= j 0)
                  (natp (logrev1 size i j)))
         :rule-classes :type-prescription
         :hints(("Goal" :in-theory (disable imod ifloor)))))

(defthm logrev-type
  (natp (logrev size i))
  :rule-classes :type-prescription
  :doc ":doc-section logrev
  Type-prescription: (NATP (LOGREV size i)).
  ~/~/~/")

(defthm logsat-type
  (integerp (logsat size i))
  :rule-classes :type-prescription
  :doc ":doc-section logsat
  Type-Prescription: (INTEGERP (LOGSAT size i)).
  ~/~/~/")

(defthm logextu-type
  (natp (logextu final-size ext-size i))
  :rule-classes :type-prescription
  :doc ":doc-section logextu
  Type-prescription: (NATP (LOGEXTU final-size ext-size i)).
  ~/~/~/")

(defthm lognotu-type
  (natp (lognotu size i))
  :rule-classes :type-prescription
  :doc ":doc-section lognotu
  Type-prescription: (NATP (LOGNOTU size i)).
  ~/~/~/")

(defthm ashu-type
  (natp (ashu size i cnt))
  :rule-classes :type-prescription
  :doc ":doc-section ashu
  Type-prescription: (NATP (ASHU size i cnt)).
  ~/~/~/")

(defthm lshu-type
  (natp (lshu size i cnt))
  :rule-classes :type-prescription
  :doc ":doc-section lshu
  Type-prescription: (NATP (LSHU size i cnt)).
  ~/~/~/")



;;;****************************************************************************
;;;
;;;   Definitions -- Round 3.
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

(defun-inline b-not (i)
  ":doc-section logops-bit-functions
  B-NOT ~/~/~/"
  (declare (xargs :guard (bitp i)))
  (mbe :logic (if (zbp i) 1 0)
       :exec (the (unsigned-byte 1)
               (- 1 (the (unsigned-byte 1) i)))))

(defun-inline b-and (i j)
  ":doc-section logops-bit-functions
  B-AND ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (mbe :logic (if (zbp i) 0 (if (zbp j) 0 1))
       :exec (the (unsigned-byte 1)
               (logand (the (unsigned-byte 1) i)
                       (the (unsigned-byte 1) j)))))

(defun-inline b-ior (i j)
  ":doc-section logops-bit-functions
  B-IOR ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (mbe :logic (if (zbp i) (if (zbp j) 0 1) 1)
       :exec (the (unsigned-byte 1)
               (logior (the (unsigned-byte 1) i)
                       (the (unsigned-byte 1) j)))))

(defun-inline b-xor (i j)
  ":doc-section logops-bit-functions
  B-XOR ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (mbe :logic (if (zbp i) (if (zbp j) 0 1) (if (zbp j) 1 0))
       :exec (the (unsigned-byte 1)
               (logxor (the (unsigned-byte 1) i)
                       (the (unsigned-byte 1) j)))))

(defun-inline b-eqv (i j)
  ":doc-section logops-bit-functions
  B-EQV ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (mbe :logic (if (zbp i) (if (zbp j) 1 0) (if (zbp j) 0 1))
       ;; Goofy definition, Using logeqv or lognot of logxor would require
       ;; masking (they produce -1 for, e.g., (logeqv 0 0)).  So I'll just xor
       ;; with 1 to invert the bit.
       :exec (the (unsigned-byte 1)
               (logxor (the (unsigned-byte 1)
                         (logxor (the (unsigned-byte 1) i)
                                 (the (unsigned-byte 1) j)))
                       1))))

(defun-inline b-nand (i j)
  ":doc-section logops-bit-functions
  B-NAND ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (mbe :logic (if (zbp i) 1 (if (zbp j) 1 0))
       ;; Goofy :exec, similar to b-eqv for similar reasons
       :exec (the (unsigned-byte 1)
               (logxor (the (unsigned-byte 1)
                         (logand (the (unsigned-byte 1) i)
                                 (the (unsigned-byte 1) j)))
                       1))))

(defun-inline b-nor (i j)
  ":doc-section logops-bit-functions
  B-NOR ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (mbe :logic (if (zbp i) (if (zbp j) 1 0) 0)
       :exec (the (unsigned-byte 1)
               (logxor (the (unsigned-byte 1)
                         (logior (the (unsigned-byte 1) i)
                                 (the (unsigned-byte 1) j)))
                       1))))

(defun-inline b-andc1 (i j)
  ":doc-section logops-bit-functions
  B-ANDC1 ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (mbe :logic (if (zbp i) (if (zbp j) 0 1) 0)
       :exec (the (unsigned-byte 1)
               (logandc1 (the (unsigned-byte 1) i)
                         (the (unsigned-byte 1) j)))))

(defun-inline b-andc2 (i j)
  ":doc-section logops-bit-functions
  B-ANDC2 ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (mbe :logic (if (zbp i) 0 (if (zbp j) 1 0))
       :exec (the (unsigned-byte 1)
               (logandc2 (the (unsigned-byte 1) i)
                         (the (unsigned-byte 1) j)))))

(defun-inline b-orc1 (i j)
  ":doc-section logops-bit-functions
  B-ORC1 ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (mbe :logic (if (zbp i) 1 (if (zbp j) 0 1))
       :exec (the (unsigned-byte 1)
               (logior (the (unsigned-byte 1)
                         (logxor 1 (the (unsigned-byte 1) i)))
                       (the (unsigned-byte 1) j)))))

(defun-inline b-orc2 (i j)
  ":doc-section logops-bit-functions
  B-ORC2 ~/~/~/"
  (declare (xargs :guard (and (bitp i) (bitp j))))
  (mbe :logic (if (zbp i) (if (zbp j) 1 0) 1)
       :exec (the (unsigned-byte 1)
               (logior (the (unsigned-byte 1) i)
                       (the (unsigned-byte 1)
                         (logxor 1 (the (unsigned-byte 1) j)))))))

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
   (:type-prescription :corollary (natp (b-not i)))
   (:type-prescription :corollary (natp (b-and i j)))
   (:type-prescription :corollary (natp (b-ior i j)))
   (:type-prescription :corollary (natp (b-xor i j)))
   (:type-prescription :corollary (natp (b-eqv i j)))
   (:type-prescription :corollary (natp (b-nand i j)))
   (:type-prescription :corollary (natp (b-nor i j)))
   (:type-prescription :corollary (natp (b-andc1 i j)))
   (:type-prescription :corollary (natp (b-andc2 i j)))
   (:type-prescription :corollary (natp (b-orc1 i j)))
   (:type-prescription :corollary (natp (b-orc2 i j))))
  :doc ":doc-section logops-bit-functions
  Rewrite: All of the bit functions return BITP integers
  ~/
  We also prove an appropriate :TYPE-PRESCRIPTION for each.~/~/")


