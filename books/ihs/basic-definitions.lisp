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
;;;    Modified October 2014 by Jared Davis <jared@centtech.com>
;;;    Ported documentation to XDOC
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "std/basic/defs" :dir :system)
(local (include-book "math-lemmas"))
(local (include-book "quotient-remainder-lemmas"))

(defxdoc logops
  :parents (ihs)
  :short "Definitions and lemmas about logical operations on integers."

  :long "<p>The books @(see logops-definitions) and @(see logops-lemmas)
contain a theory of the logical operations on numbers defined by CLTL (Section
12.7), and a portable implementation of the CLTL byte manipulation
functions (Section 12.8).  These books also extend the CLTL logical operations
and byte manipulation theory with a few new definitions, lemmas supporting
those definitions, and useful macros.</p>

<p>These books were developed as a basis for the formal specification and
verification of hardware, where integers are used to represent binary signals
and busses.  These books should be general enough, however, to be used as a
basis for reasoning about packed data structures, bit-encoded sets, and other
applications of logical operations on integers.</p>")

(defxdoc logops-definitions
  :parents (ihs)
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

(local (xdoc::set-default-parents logops-definitions))

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

(local
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
     :hints(("Goal" :induct (my-induct i size))))))


(define zbp
  :parents (logops-definitions bitp)
  :short "Zero bit recognizer.  @('(zbp x)') tests for zero bits.  Any object
other than @('1') is considered to be a zero bit."
  ((x bitp))
  :returns bool
  :enabled t
  :inline t
  (mbe :logic (equal (bfix x) 0)
       :exec (/= (the (unsigned-byte 1) x) 1)))

(define ifloor
  :short "@('(ifloor i j)') is the same as @(see floor), except that it coerces
  its arguments to integers."
  ((i integerp)
   (j (and (integerp j)
           (not (= 0 j)))))
  :returns (int integerp
                :rule-classes :type-prescription
                :name ifloor-type)
  :inline t
  :enabled t
  (mbe :logic (floor (ifix i) (ifix j))
       :exec (floor i j)))

(define imod
  :short "@('(imod i j)') is the same as @(see mod), except that it coerces its
  arguments to integers."
  ((i integerp)
   (j (and (integerp j)
           (not (= 0 j)))))
  :returns (int integerp
                :rule-classes :type-prescription
                :name imod-type)
  :inline t
  :enabled t
  (mbe :logic (mod (ifix i) (ifix j))
       :exec (mod i j)))

(define expt2
  :short "@('(expt2 n)') is the same as @('(expt 2 n)'), except that it coerces
  its argument to a natural."
  ((n natp))
  :returns (nat natp
                :rule-classes :type-prescription
                :name expt2-type)
  :enabled t
  :inline t
  (mbe :logic (expt 2 (nfix n))
       :exec (the unsigned-byte
                  (ash 1 (the unsigned-byte n)))))

(define binary-minus-for-gl ((x acl2-numberp)
                             (y acl2-numberp))
  :parents (binary--)
  :short "Hack for implementing @(see binary--).  Don't use this."
  :long "<p>You should never need to use this, call @(see binary--) instead.</p>

<p>This is the logical definition for @(see binary--).  It has a custom GL
symbolic counterpart.  The only reason to make this a separate function,
instead of directly putting a symbolic counterpart on @('binary--') itself, is
to avoid infinite inlining problems when we define custom symbolic counterparts
for inlined functions on Lisps like SBCL.</p>"
  :enabled t
  (- x y))

(define binary--
  :parents (logops-definitions)
  :short "@('(binary-- x y)') is the same as @('(- x y)'), but may symbolically
simulate more efficiently in @(see gl)."
  ((x acl2-numberp)
   (y acl2-numberp))
  :enabled t
  :inline t
  :long "<p>This is an alias for @('(- x y)').  It should always be left
enabled and you should never prove any theorems about it.</p>

<p>In ACL2, @(see -) is a macro and @('(- x y)') expands to @('(+ x (unary--
y))').  This form is often not particularly good for symbolic simulation with
@(see gl): GL first has to negate @('y') and then carry out the addition.</p>

<p>In contrast, @('binary--') has a custom symbolic counterpart that avoids
this intermediate negation.  This may result in fewer BDD computations or AIG
nodes.  In the context of @(see hardware-verification), it may also help your
spec functions to better match the real implementation of subtraction circuits
in the hardware being analyzed.</p>"

  (mbe :logic (binary-minus-for-gl x y)
       :exec (- x y)))

(define logcar
  :short "Least significant bit of a number."
  ((i integerp))
  :returns (bit bitp
                ;; [Jared] 2016-04-08: Originally this rule had the following
                ;; rule-classes:
                ;;
                ;; :rule-classes ((:rewrite)
                ;;                (:type-prescription :corollary (natp (logcar i)))
                ;;                 (:generalize :corollary (or (equal (logcar i) 0)
                ;;                                             (equal (logcar i) 1)))))
                ;;
                ;; Now that bitp is a proper type-set, I think we don't need
                ;; the natp corollary and may as well get rid of the :rewrite
                ;; rule and just make it a type-prescription.
                ;;
                ;; I had hoped that we wouldn't need the generalize rule,
                ;; because when we do destructor elimination, ACL2 should be
                ;; smart enough to know that the new variable for the logcar is
                ;; a bit, right?  But this generalize rule is actually more
                ;; powerful than that, because it lets us case-split on whether
                ;; logcar is 0 or 1, and when I remove it, many theorems in the
                ;; logops-lemmas book fail because they are relying on this
                ;; case splitting to allow calls of functions like b-ior,
                ;; b-and, etc., to evaluate.
                ;;
                ;; Well, I don't think this is a very good way to do these
                ;; proofs, and it would be better to just explicitly enable the
                ;; bit functions instead of letting it case split when it does
                ;; destructor elimination.  But, this is such an old and
                ;; well-established book that, in this case, I think
                ;; maintaining backward compatibility is probably worth it.
                ;; So, I'll hold my nose and leave the generalize rule here.
                :rule-classes
                ((:type-prescription)
                 (:generalize :corollary (or (equal (logcar i) 0)
                                             (equal (logcar i) 1))))
                ;; Explicit name for backward compatibility
                :name logcar-type)

  :long "<p>@('(logcar i)') is the @(see car) of an integer conceptualized as a
bit-vector, where the least significant bit is at the head of the list.</p>

<p>In languages like C, this might be written as @('i & 1').</p>"
  :enabled t
  :inline t
  (mbe :logic (imod i 2)
       :exec (the (unsigned-byte 1) (logand (the integer i) 1))))

(define logcdr
  :short "All but the least significant bit of a number."
  ((i integerp))
  :returns (int integerp
                :rule-classes :type-prescription
                :name logcdr-type)
  :long "<p>@('(logcdr i)') is the @(see cdr) of an integer conceptualized as a
bit-vector, where the least significant bit is at the head of the list.</p>

<p>In languages like C, this might be written as @('i >> 1').</p>"
  :enabled t
  :inline t
  (mbe :logic (ifloor i 2)
       :exec (the integer (ash (the integer i) -1))))

(define logcons
  :short "@('(logcons b i)') is the @(see cons) operation for integers,
conceptualized as bit-vectors, where the least significant bit is at the head
of the list."
  ((b bitp     "LSB of the result.")
   (i integerp "All but the LSB of the result."))
  :returns (int integerp
                :rule-classes :type-prescription
                :name logcons-type)
  :long "<p>In languages like C, this might be written as @('(i << 1) + b').</p>

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
  :returns (bit bitp
                :rule-classes :type-prescription
                :name logbit-type ;; for backward compatibility with the old name
                )
  :long "<p>This is just like the Common Lisp function @('(logbitp pos i)'),
except that we return 1 or 0 (instead of t or nil).</p>

<p>In languages like C, this might be written as @('(i >> pos) & 1').</p>"
  :enabled t
  :inline t
  :no-function t ;; Sigh, switching to :abbreviation breaks various proofs
  (if (logbitp pos i)
      1
    0)
  ///
  ;; [Jared] 2016-04-08: as with logcar, switch to just a type-prescription
  ;; in the :returns, now that bitp is known to type-set.
  ;;
  ;; (defthm logbit-type
  ;;   (bitp (logbit pos i))
  ;;   :rule-classes ((:rewrite)
  ;;                  (:type-prescription :corollary (natp (logbit pos i))))
  ;; BOZO want a generalize rule like in logcar?
  ;; )
  )


(define logmask
  :short "@('(logmask size)') creates a low-order, @('size')-bit mask."
  ((size natp))
  :returns (nat natp
                :rule-classes :type-prescription
                :name logmask-type)
  :long "<p>In languages like C, this might be written as @('(1 << size) - 1').</p>"
  :enabled t
  :inline t
  (mbe :logic (- (expt2 size) 1)
       :exec (the unsigned-byte (1- (the unsigned-byte (ash 1 size))))))

(define logmaskp
  :short "@('(logmaskp i)') recognizes positive bit-masks, i.e., numbers of the
form @($2^n - 1$)."
  (i)
  :returns bool
  :enabled t
  :long "<p>Note that this function explicitly checks @('(integerp i)'), which
means it doesn't satisfy an @(see int-equiv) congruence.  See also @(see
bitmaskp), which fixes its argument and may execute slightly faster.</p>"
  (mbe :logic (and (integerp i)
                   (>= i 0) ;; silly, this is implied by the equality below
                   (equal i (- (expt2 (integer-length i)) 1)))
       :exec (and (integerp i)
                  (eql i (the unsigned-byte
                              (- (the unsigned-byte (ash 1 (integer-length i)))
                                 1))))))

(define bitmaskp
  :short "@('(bitmaskp i)') recognizes positive masks, i.e., numbers of the form
@($2^n - 1$).  It is like @(see logmaskp) but properly treats non-integers as 0."
  ((i integerp))
  :returns bool
  :inline t
  (mbe :logic (logmaskp (mbe :logic (ifix i)
                             :exec i))
       :exec (eql i (the unsigned-byte
                         (- (the unsigned-byte (ash 1 (integer-length i)))
                            1)))))

(define loghead
  :short "@('(loghead size i)') returns the @('size') low-order bits of @('i')."
  ((size (and (integerp size)
              (<= 0 size))
         :type unsigned-byte)
   (i    integerp))
  :returns (nat natp
                :rule-classes :type-prescription
                :name loghead-type)
  :long "<p>In languages like C, this might be written as @('i & ((1 << size) -
1)').</p>

<p>By convention we define @('(loghead 0 i)') as 0.  This definition is a
bit arbitrary but generally leads to nice lemmas.</p>"
  :inline t
  :enabled t
  :split-types t
  :guard-hints(("Goal" :in-theory (enable mod-of-expt-2-is-logand)))
  (mbe :logic (imod i (expt2 size))
       :exec
       (the unsigned-byte
            (logand i (the unsigned-byte
                           (1- (the unsigned-byte (ash 1 size))))))))

(define logtail
  :short "@('(logtail pos i)') returns the high-order part of @('i'), starting
  at bit position @('pos')."
  ((pos (and (integerp pos)
             (<= 0 pos))
        :type unsigned-byte)
   (i   integerp))
  :returns (int integerp
                :rule-classes :type-prescription
                :name logtail-type)
  :long "<p>In languages like C, this might be written as @('i >> pos').</p>"
  :split-types t
  :inline t
  :enabled t
  (declare (xargs :guard (and (integerp pos)
                              (>= pos 0)
                              (integerp i))))
  (mbe :logic (ifloor i (expt2 pos))
       :exec (ash i (- (the unsigned-byte pos)))))

(define logapp
  :short "@('(logapp size i j)') is a binary append of i to j, where i
  effectively becomes the 'low' bits and j becomes the 'high' bits."
  ((size (and (integerp size)
              (<= 0 size))
         :type unsigned-byte)
   (i    integerp)
   (j    integerp))
  :returns (int integerp
                :rule-classes :type-prescription
                :name logapp-type)
  :split-types t
  :long "<p>@('logapp') is a specification for merging integers.  Note that
@('i') is truncated to @('size') bits before merging with @('j'), and that @('j')
is shifted to the left by @('size') bits before the merge.</p>"
  :enabled t
  (mbe :logic (let ((j (ifix j)))
                (+ (loghead size i) (* j (expt2 size))))
       ;; BOZO could do better than calling loghead with some work
       ;; Could probably use logior instead of +.
       :exec (+ (loghead size i) (ash j size))))

(define logrpl
  :short "Logical replace.  @('(logrpl size i j)') replaces the @('size')
  low-order bits of @('j') with the @('size') low-order bits of @('i')."
  ((size (and (integerp size)
              (<= 0 size)))
   (i    integerp)
   (j    integerp))
  :returns (int integerp
                :rule-classes :type-prescription
                :name logrpl-type)
  :long "<p>@('logrpl') is a specification for the result of storing short
values into long words, i.e., the short value simply replaces the head of the
long word.</p>

<p>This function is equivalent to @('(WRB i (BSP size 0) j)').</p>"
  :enabled t
  (logapp size i (logtail size j)))

(define logext
  :short "@('(logext size i)') sign-extends @('i') to a @('size')-bit signed
integer."
  ((size (and (integerp size)
              (< 0 size))
         :type unsigned-byte)
   (i    integerp))
  :returns (int integerp
                :rule-classes :type-prescription
                :name logext-type)
  :split-types t
  :long "<p>@('logext') interprets the least significant @('size') bits of
@('i') as a signed, 2's complement integer.</p>

<p>Basic examples:</p>

@({
    (logext 4 7)  --> 7        Bottom four bits are 0111
                               Sign bit is 0
                               Sign extension creates {0000......0}111
                               2's complement interpretation: 7.

    (logext 3 7)  --> -1       Bottom 3 bits are 111
                               Sign bit is 1
                               Sign extension creates {1111.....1}111
                               2's complement interpretation: -1.

    (logext 4 8)  --> -8       Bottom 4 bits are 1000
                               Sign bit is 1
                               Sign extension creates {1111.....1}1000
                               2's complement interpretation: -8.
})

<p>This function returns a (possibly negative) integer.  For consistency with
@(see SIGNED-BYTE-P), @('size') must be strictly greater than 0.  In contrast,
the related function @(see logextu) carries out a sign-extension but only
returns the low @('size') bits, i.e., it always returns a natural number.</p>

<p>We specify @('logext') in terms of the @('size') of the result instead of as
a bit position because we normally specify integer subranges by the number of
significant (including sign) bits.</p>

<p>See also @(see bitops::bitops/fast-logext) for a logically identical
function that is optimized for better performance.</p>"
  :enabled t

  (let* ((size-1 (- size 1)))
    (declare (type unsigned-byte size-1))
    (logapp size-1 i
            (if (logbitp size-1 i)
                -1
              0))))

(define logrev1
  :parents (logrev)
  :short "Helper function for @(see logrev)."
  ((size (and (integerp size)
              (<= 0 size)))
   (i integerp)
   (j integerp))
  :returns (nat)
  :split-types t
  (declare (type unsigned-byte size)
           (type integer i j))
  :enabled t
  (if (zp size)
      (mbe :logic (ifix j)
           :exec j)
    (logrev1 (the unsigned-byte (- size 1))
             (logcdr i)
             (logcons (logcar i) j))))

(local (defthm logrev1-type
         (implies (>= j 0)
                  (natp (logrev1 size i j)))
         :rule-classes :type-prescription
         :hints(("Goal" :in-theory (disable imod ifloor)))))

(define logrev
  :short "Logical reverse.  @('(logrev size i)') bit-reverses the @('size')
  low-order bits of @('i'), discarding the high-order bits."
  ((size (and (integerp size)
              (<= 0 size)))
   (i    integerp))
  :returns (nat natp
                :rule-classes :type-prescription
                :name logrev-type)
  :long "<p>Normally we don't think of bit-reversing as a logical operation,
even though its hardware implementation is trivial: simply reverse the wires
leading from the source to the destination.</p>

<p>@('logrev') is included as a logical operation to support the specification
of DSPs, which may provide bit-reversing in their address generators to improve
the performance of the FFT.</p>

<p>@('logrev') entails a recursive definition of bit-reversing via the helper
function @(see logrev1).</p>

<p>See also @(see bitops::bitops/fast-logrev) for some optimized definitions of
@(see logrev).</p>"
  :inline t
  :enabled t
  (logrev1 size i 0))

(define logsat
  :short "Signed saturation.  @('(logsat size i)') coerces @('i') to a
  @('size')-bit signed integer by saturation."
  ((size (and (integerp size)
              (< 0 size))
         :type unsigned-byte)
   (i    integerp))
  :returns (int integerp
                :rule-classes :type-prescription
                :name logsat-type)

  :long "<p>If @('i') can be represented as a @('size')-bit signed integer,
then @('i') is returned unchanged.  Otherwise, @('(logsat size i)') returns
the @('size')-bit signed integer closest to @('i').  For positive i, this
will be @($2^{size-1} - 1$).  For negative @('i'), this will be
@($-(2^{size-1}$).</p>

<p>This function returns a (possibly negative) integer.  For consistency with
@(see signed-byte-p), size must be strictly greater than 0.  In contrast, the
related @(see bitops::bitops/saturate) functions always return @('size')-bit
natural numbers.</p>"

  :split-types t
  :enabled t
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

(define logextu
  :short "Logical sign extension, unsigned version.  @('(logextu final-size
 ext-size i)') \"sign-extends\" i with @('(logext ext-size i)'), then truncates
 the result to @('final-size') bits, creating an unsigned integer."
  ((final-size (and (integerp final-size)
                    (<= 0 final-size)))
   (ext-size   (and (integerp ext-size)
                    (< 0 ext-size)))
   (i          integerp))
  :returns (nat natp
                :rule-classes :type-prescription
                :name logextu-type)
  :enabled t
  :inline t
  (loghead final-size (logext ext-size i)))

(define lognotu
  :short "Logical negation, unsigned version.  @('(lognotu size i)') is an
 unsigned logical @('not').  It just truncates @('(lognot i)') to @('size')
 bits."
  ((size  (and (integerp size)
               (<= 0 size)))
   (i     integerp))
  :returns (nat natp
                :rule-classes :type-prescription
                :name lognotu-type)
  :enabled t
  :inline t
  (loghead size (lognot i)))

(define ashu
  :short "Arithmetic shift, unsigned version."
  ((size (and (integerp size)
              (< 0 size)))
   (i    integerp)
   (cnt  integerp))
  :returns (nat natp
                :rule-classes :type-prescription
                :name ashu-type)
  :long "<p>@('ashu') is a fixed-width version of @(see ash).  The integer
@('i') is first coerced to a @('size')-bit signed integer by sign-extension,
then shifted with @('ash'), and finally truncated back to a @('size')-bit
unsigned integer.</p>

<p>See also @(see lshu) for a logical (instead of arithmetic) shift.</p>"
  :enabled t
  (loghead size (ash (logext size i) cnt)))

(define lshu
  :short "Logical shift, unsigned version."
  ((size (and (integerp size)
              (<= 0 size)))
   (i   integerp)
   (cnt integerp))
  :returns (nat natp
                :rule-classes :type-prescription
                :name lshu-type)
  :long "<p>@('lshu') is a fixed-width logical shift.  It shifts @('i')
by @('cnt') bits by first coercing @('i') to an unsigned integer of @('size')
bits, performing the shift, and coercing the result to an @('size')-bit
unsigned integer.</p>

<p>For @('cnt >= 0'), @('(lshu size i cnt) = (ashu size i cnt)').</p>

<p>This is a model of a size-bit logical shift register.</p>"
  :enabled t
  (loghead size (ash (loghead size i) cnt)))

(define logite
  :short "Bitwise if-then-else among integers."
  ((test :type integer)
   (then :type integer)
   (else :type integer))
  :returns (logite integerp :rule-classes :type-prescription
                  :name logite-type)
  (logior (logand test then) (logand (lognot test) else)))


(defxdoc logops-bit-functions
  :parents (logops-definitions bitp)
  :short "Versions of the standard logical operations that operate on single bits."
  :long "<p>We provide versions of the non-trivial standard logical operations
that operate on single bits.</p>

<p>One reason that it is useful to introduce these operations separately from
the standard operations is the fact that @(see lognot) applied to a @(see bitp)
object never returns a @(see bitp).</p>

<p>All arguments to these functions must be @(see bitp), and we prove that
each returns a @(see bitp) integer, i.e., 0 or 1.  We define each function
explicitly in terms of 0 and 1 to simplify reasoning.</p>")

(local (xdoc::set-default-parents logops-bit-functions))

(define b-not ((i bitp))
  :returns (bit bitp :rule-classes :type-prescription)
  :short "Negation for @(see bitp)s."
  :inline t
  :enabled t
  (mbe :logic (if (zbp i) 1 0)
       :exec (the (unsigned-byte 1)
               (- 1 (the (unsigned-byte 1) i)))))

(define b-and ((i bitp) (j bitp))
  :returns (bit bitp :rule-classes :type-prescription)
  :short "Conjunction for @(see bitp)s."
  :inline t
  :enabled t
  (mbe :logic (if (zbp i) 0 (if (zbp j) 0 1))
       :exec (the (unsigned-byte 1)
               (logand (the (unsigned-byte 1) i)
                       (the (unsigned-byte 1) j)))))

(define b-ior ((i bitp) (j bitp))
  :returns (bit bitp :rule-classes :type-prescription)
  :short "Inclusive or for @(see bitp)s."
  :inline t
  :enabled t
  (mbe :logic (if (zbp i) (if (zbp j) 0 1) 1)
       :exec (the (unsigned-byte 1)
               (logior (the (unsigned-byte 1) i)
                       (the (unsigned-byte 1) j)))))

(define b-xor ((i bitp) (j bitp))
  :returns (bit bitp :rule-classes :type-prescription)
  :short "Exclusive or for @(see bitp)s."
  :enabled t
  :inline t
  (mbe :logic (if (zbp i) (if (zbp j) 0 1) (if (zbp j) 1 0))
       :exec (the (unsigned-byte 1)
               (logxor (the (unsigned-byte 1) i)
                       (the (unsigned-byte 1) j)))))

(define b-eqv ((i bitp) (j bitp))
  :returns (bit bitp :rule-classes :type-prescription)
  :short "Equivalence (a.k.a. if and only if, xnor) for @(see bitp)s."
  :enabled t
  :inline t
  (mbe :logic (if (zbp i) (if (zbp j) 1 0) (if (zbp j) 0 1))
       ;; Goofy definition, Using logeqv or lognot of logxor would require
       ;; masking (they produce -1 for, e.g., (logeqv 0 0)).  So I'll just xor
       ;; with 1 to invert the bit.
       :exec (the (unsigned-byte 1)
               (logxor (the (unsigned-byte 1)
                         (logxor (the (unsigned-byte 1) i)
                                 (the (unsigned-byte 1) j)))
                       1))))

(define b-nand ((i bitp) (j bitp))
  :returns (bit bitp :rule-classes :type-prescription)
  :short "Negated and for @(see bitp)s."
  :enabled t
  :inline t
  (mbe :logic (if (zbp i) 1 (if (zbp j) 1 0))
       ;; Goofy :exec, similar to b-eqv for similar reasons
       :exec (the (unsigned-byte 1)
               (logxor (the (unsigned-byte 1)
                         (logand (the (unsigned-byte 1) i)
                                 (the (unsigned-byte 1) j)))
                       1))))

(define b-nor ((i bitp) (j bitp))
  :returns (bit bitp :rule-classes :type-prescription)
  :short "Negated or for @(see bitp)s."
  :enabled t
  :inline t
  (mbe :logic (if (zbp i) (if (zbp j) 1 0) 0)
       :exec (the (unsigned-byte 1)
               (logxor (the (unsigned-byte 1)
                         (logior (the (unsigned-byte 1) i)
                                 (the (unsigned-byte 1) j)))
                       1))))

(define b-andc1 ((i bitp) (j bitp))
  :returns (bit bitp :rule-classes :type-prescription)
  :short "And of @(see bitp)s, complementing the first."
  :enabled t
  :inline t
  (mbe :logic (if (zbp i) (if (zbp j) 0 1) 0)
       :exec (the (unsigned-byte 1)
               (logandc1 (the (unsigned-byte 1) i)
                         (the (unsigned-byte 1) j)))))

(define b-andc2 ((i bitp) (j bitp))
  :returns (bit bitp :rule-classes :type-prescription)
  :short "And of @(see bitp)s, complementing the second."
  :enabled t
  :inline t
  (mbe :logic (if (zbp i) 0 (if (zbp j) 1 0))
       :exec (the (unsigned-byte 1)
               (logandc2 (the (unsigned-byte 1) i)
                         (the (unsigned-byte 1) j)))))

(define b-orc1 ((i bitp) (j bitp))
  :returns (bit bitp :rule-classes :type-prescription)
  :short "Inclusive or of @(see bitp)s, complementing the first."
  :enabled t
  :inline t
  (mbe :logic (if (zbp i) 1 (if (zbp j) 0 1))
       :exec (the (unsigned-byte 1)
               (logior (the (unsigned-byte 1)
                         (logxor 1 (the (unsigned-byte 1) i)))
                       (the (unsigned-byte 1) j)))))

(define b-orc2 ((i bitp) (j bitp))
  :returns (bit bitp :rule-classes :type-prescription)
  :short "Inclusive or of @(see bitp)s, complementing the second."
  :enabled t
  :inline t
  (mbe :logic (if (zbp i) (if (zbp j) 1 0) 1)
       :exec (the (unsigned-byte 1)
               (logior (the (unsigned-byte 1) i)
                       (the (unsigned-byte 1)
                         (logxor 1 (the (unsigned-byte 1) j)))))))

(define b-ite ((test bitp) (then bitp) (else bitp))
  :returns (bit bitp :rule-classes :type-prescription)
  :short "If-then-else for @(see bitp)s."
  :inline t
  :enabled t
  (if (zbp test) (bfix else) (bfix then)))

;; [Jared] this is subsumed by the bitp :returns specs above, now that
;; bitp is a type-set type.

;; (defsection bit-functions-type
;;   :short "Basic type rules for the @(see logops-bit-functions)."
;;
;;   (defthm bit-functions-type
;;     (and (bitp (b-not i))
;;          (bitp (b-and i j))
;;          (bitp (b-ior i j))
;;          (bitp (b-xor i j))
;;          (bitp (b-eqv i j))
;;          (bitp (b-nand i j))
;;          (bitp (b-nor i j))
;;          (bitp (b-andc1 i j))
;;          (bitp (b-andc2 i j))
;;          (bitp (b-orc1 i j))
;;          (bitp (b-orc2 i j))
;;          (bitp (b-ite test then else)))
;;     :rule-classes
;;     ((:rewrite)
;;      (:type-prescription :corollary (natp (b-not i)))
;;      (:type-prescription :corollary (natp (b-and i j)))
;;      (:type-prescription :corollary (natp (b-ior i j)))
;;      (:type-prescription :corollary (natp (b-xor i j)))
;;      (:type-prescription :corollary (natp (b-eqv i j)))
;;      (:type-prescription :corollary (natp (b-nand i j)))
;;      (:type-prescription :corollary (natp (b-nor i j)))
;;      (:type-prescription :corollary (natp (b-andc1 i j)))
;;      (:type-prescription :corollary (natp (b-andc2 i j)))
;;      (:type-prescription :corollary (natp (b-orc1 i j)))
;;      (:type-prescription :corollary (natp (b-orc2 i j)))
;;      (:type-prescription :corollary (natp (b-ite test then else))))))


(defmacro loglist* (&rest args)
  (xxxjoin 'logcons args))
