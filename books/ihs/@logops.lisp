; @logops.lisp  --  4-valued integer hardware model
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    @logops.lisp
;;;
;;;    Bishop Brock
;;;    Computational Logic, Inc.
;;;    1717 West 6th Street, Suite 290
;;;    Austin, Texas 78703
;;;    (512) 322-9951
;;;    brock@cli.com
;;;
;;;    Modified October 2014 by Jared Davis <jared@centtech.com>
;;;    Ported documentation to XDOC
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;****************************************************************************
;;;
;;;  Environment
;;;
;;;****************************************************************************

(in-package "ACL2")

#+program
(program)

;; ACL2 problems?

(include-book "ihs-definitions")
(include-book "ihs-lemmas")

;; [Jared] yikes, this does in-theory nil, right?  seriously do this non-locally?
(progn (minimal-ihs-theory))
(deflabel @logops)

(defxdoc @logops
  :parents (ihs)
  :short "A book of 4-valued counterparts for logical operations on integers."

  :long "<p>We can model `4-valued' integers using a pair of integers.  First
 think about a pair of bits.  We assign the values as 00 = `0', 01 = `1', 10 =
 `x', 11 = `z', where `x' is the `unknown' and `z' the `floating' value.  We
 call the low-order bit the `determinate' bit and the high-order bit the
 `indeterminate' bit.  We extend this notion to integers by using a pair of
 integers, where the first integer is the determinate integer, the second
 integer is the indeterminate integer, and each 4-valued bit f the integer is a
 slice through the two integers.  For example,</p>

@({
 (0 . 0)       =  ..00000000000
 (1 . 0)       =  ..00000000001
 (10 . 12)     =  ..0000000ZX10
 (0 . -1)      =  ..XXXXXXXXXXX
 (1023 . 1023) =  ..0ZZZZZZZZZZ
})

<p>All of the 4-valued counterparts of integer functions are uniformly
defined with the prefix character `@', e.g., @+, @LOGAND, etc..</p>")

(local (xdoc::set-default-parents @logops))

;  These will never appear in user code, so they're macros for efficiency.

(defmacro @cons (d i)
  "4-Valued CONS."
  (mlambda (d i)
    (cond
     ((zip i) d)
     (t (cons d i)))))

(defmacro @d (@)
  (mlambda (@)
    (cond
     ((integerp @) @)
     (t (ifix (car @))))))

(defmacro @i (@)
  (mlambda (@)
    (cond
     ((integerp @) 0)
     (t (ifix (cdr @))))))

;  The @@ forms are for when we have disestablished INTEGERP.

(defmacro @@d (@) (mlambda (@) (car @)))

(defmacro @@i (@) (mlambda (@) (cdr @)))

(define @integerp (@)
  :short "4-Valued INTEGERP."
  :enabled t
  (or (integerp @)
      (and (consp @)
	   (integerp (@@d @))
	   (integerp (@@i @))
	   (not (= (@@i @) 0)))))

(defthm @integerp-integerp
  (implies
   (integerp i)
   (@integerp i)))

(defthm @integerp-cons
  (equal (@integerp (cons d i))
	 (and (integerp d)
	      (integerp i)
	      (not (= i 0))))
  :hints (("Goal" :in-theory (enable @integerp))))

;;;  Constants

(defconst *@x* (@cons 0 -1))

(defconst *@x-bit* (@cons 0 1))

(defconst *@z* (@cons -1 -1))

(defconst *@z-bit* (@cons 1 1))

;;;  @BITP

(define @bitp (x)
  :short "4-valued BITP."
  :enabled t
  (cond
   ((integerp x) (bitp x))
   ((@integerp x) (and (bitp (@@d x)) (bitp (@@i x))))))

(defthm @bitp-integer
  (implies
   (integerp i)
   (equal (@bitp i)
	  (bitp i))))

(defthm @bitp-@integerp-forward
  (implies
   (@bitp i)
   (@integerp i))
  :rule-classes :forward-chaining
  :hints
  (("Goal"
    :in-theory (enable @bitp))))

;;;  @BFIX

(define @bfix (x)
  :short "4-valued BFIX."
  :enabled t
  (case x
    (0 0)
    (1 1)
    (t *@x-bit*)))

(defthm type-of-@bfix
  (and (@bitp (@bfix i))
       (@integerp (@bfix i))))

;;;  @+

(define @+ ((i @integerp)
            (j @integerp))
  :short "4-Valued +."
  :enabled t
  (cond
   ((and (integerp i) (integerp j)) (+ i j))
   (t *@x*)))

(defthm type-of-@+
  (@integerp (@+ i j)))

(defthm @+-integer
  (implies
   (and (integerp i)
	(integerp j))
   (equal (@+ i j)
	  (+ i j))))

(defmacro @1+ (i) (mlambda (i) (@+ 1 i)))

(defmacro @1- (i) (mlambda (i) (@+ -1 i)))

;;;  @unary--

(define @unary-- ((i @integerp))
  :short "4-Valued UNARY--."
  :enabled t
  (cond
   ((integerp i) (- i))
   (t *@x*)))

(defthm type-of-@unary--
  (@integerp (@unary-- i)))

(defthm @unary---integer
  (implies
   (integerp i)
   (equal (@unary-- i)
	  (- i))))

;  Modified from ACL2.

(defmacro @- (x &optional (y 'nil binary-casep))
  (if binary-casep
      (let ((y (if (and (consp y)
			(eq (car y) 'quote)
			(consp (cdr y))
			(@integerp (car (cdr y)))
			(eq (cdr (cdr y)) nil))
		   (car (cdr y))
		 y)))
	(if (@integerp y)
	    (cons '@+ (cons (@unary-- y) (cons x nil)))
	  (cons '@+ (cons x (cons (cons '@unary-- (cons y nil)) nil)))))
    (let ((x (if (and (consp x)
		      (eq (car x) 'quote)
		      (consp (cdr x))
		      (@integerp (car (cdr x)))
		      (eq (cdr (cdr x)) nil))
		 (car (cdr x))
	       x)))
      (if (@integerp x)
	  (@unary-- x)
	(cons '@unary-- (cons x nil))))))

(define @* ((i @integerp)
            (j @integerp))
  :short "4-Valued *."
  :enabled t
  (cond
   ((and (integerp i) (integerp j)) (* i j))
   (t *@x*)))

(defthm type-of-@*
  (@integerp (@* i j)))

(defthm @*-integer
  (implies
   (and (integerp i)
	(integerp j))
   (equal (@* i j)
	  (* i j))))

;;  @UNSIGNED-BYTE-P

(define @unsigned-byte-p (size i)
  :short "4-Valued UNSIGNED-BYTE-P."
  :enabled t
  (and (@integerp i)
       (unsigned-byte-p size (@d i))
       (unsigned-byte-p size (@i i))))

(defthm @unsigned-byte-p-integer
  (implies
   (integerp i)
   (equal (@unsigned-byte-p size i)
	  (unsigned-byte-p size i)))
  :hints
  (("Goal"
    :in-theory (enable unsigned-byte-p))))

(defthm @unsigned-byte-p-forward
  (implies
   (@unsigned-byte-p size i)
   (@integerp i))
  :rule-classes :forward-chaining)

(defthm @unsigned-byte-p-cons
  (equal (@unsigned-byte-p size (cons d i))
	 (and (unsigned-byte-p size d)
	      (unsigned-byte-p size i)
	      (not (= i 0))))
  :hints (("Goal" :in-theory (enable @unsigned-byte-p unsigned-byte-p))))

;;;  @SIGNED-BYTE-P

(define @signed-byte-p (size i)
  :short "4-Valued SIGNED-BYTE-P."
  :enabled t
  (and (integerp size)
       (< 0 size)
       (@integerp i)
       (signed-byte-p size (@d i))
       (signed-byte-p size (@i i))))

(defthm @signed-byte-p-integer
  (implies (integerp i)
           (equal (@signed-byte-p size i)
                  (signed-byte-p size i)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm @signed-byte-p-forward
  (implies (@signed-byte-p size i)
           (@integerp i))
  :rule-classes :forward-chaining)

(defthm @signed-byte-p-cons
  (equal (@signed-byte-p size (cons d i))
	 (and (signed-byte-p size d)
	      (signed-byte-p size i)
	      (not (= i 0))))
  :hints (("Goal" :in-theory (enable @signed-byte-p signed-byte-p))))

;;; @ASH

#||
;  Bug in GCL.

(defun ash! (i c)
  (declare (xargs :guard (and (integerp i)
			      (integerp c))))
  (floor (* i (expt 2 c)) 1))

(defthm ash!-works-NOT
  (implies
   (and (integerp i)
	(integerp c))
   (equal (ash! i c) (ash i c)))
  :hints
  (("Goal"
    :in-theory (enable ash))))

(in-theory (disable ash!))

(defun @ash (i count)
  (declare (xargs :guard (and (@integerp i)
			      (@integerp count))))
  (cond
   ((integerp count) (cond
		      ((integerp i) (ash! i count))
		      (t (@cons (ash! (@@d i) count) (ash! (@@i i) count)))))
   (t *@x*)))
||#

(define @ash ((i     @integerp)
              (count @integerp))
  :short "4-Valued ASH."
  :long "<p>Note the conservative definition.  We do not define @ASH when count
  is indeterminate.</p>"
  :enabled t
  (cond
   ((integerp count) (cond
		      ((integerp i) (ash i count))
		      (t (@cons (ash (@@d i) count) (ash (@@i i) count)))))
   (t *@x*))
  ///
  (defthm type-of-@ash (@integerp (@ash i count)))

  (defthm @ash-integer
    (implies (and (integerp i)
                  (integerp count))
             (equal (@ash i count)
                    (ash i count)))))

(define @integer-length ((i @integerp))
  :short "4-valued INTEGER-LENGTH."
  :long "<p>Note that when indeterminate, @INTEGER-LENGTH returns a `signed' X.
  Thus it may be necessary to coerce the result to an unsigned type.</p>"
  :enabled t
  (cond
   ((integerp i) (integer-length i))
   (t *@x*))
  ///
  (defthm type-of-@integer-length (@integerp (@integer-length i)))

  (defthm @integer-length-integer
    (implies (integerp i)
             (equal (@integer-length i)
                    (integer-length i)))))

(define @logcount ((i @integerp))
  :short "4-value LOGCOUNT."
  :long "When indeterminate @LOGCOUNT returns a signed X, thus it may need to be
  coerced to an unsigned value."
  :enabled t
  (cond ((integerp i) (logcount i))
        (t *@x*))
  ///
  (defthm type-of-@logount (@integerp (@logcount i)))

  (defthm @logcount-integer
    (implies (integerp i)
             (equal (@logcount i)
                    (logcount i)))))

(define @logcar ((i @integerp))
  :short "4-Valued LOGCAR."
  :enabled t
  :returns (bit @bitp :name @bitp-@logcar)
  (cond
   ((integerp i) (logcar i))
   (t (@cons (logcar (@@d i)) (logcar (@@i i)))))
  ///
  (defthm type-of-@logcar (@integerp (@logcar i)))

  (defthm @logcar-integer
    (implies (integerp i)
             (equal (@logcar i)
                    (logcar i)))))

(define @lognot ((i @integerp))
  :short "4-Valued LOGNOT."
  :long "@({

 ~~i = ?  ii di  ians/dans

  0   1   0  0    0 1
  1   0   0  1    0 0
  x   x   1  0    1 0
  z   x   1  1    1 0
})"
  :enabled t
  (cond ((integerp i) (lognot i))
        (t
         (let* ((di (@d i))
                (ii (@i i)))
           (@cons (lognor di ii) ii))))
  ///
  (defthm type-of-@lognot (@integerp (@lognot i)))

  (defthm @lognot-integer
    (implies (integerp i)
             (equal (@lognot i)
                    (lognot i)))))

(define @logand ((i @integerp)
                 (j @integerp))
  :short "4-Valued LOGAND."
  :long "@({
 i&j = ?  ii di ij dj  ians/dans

 0 0   0   0  0  0  0  	 0 0
 0 1   0   0  0  0  1  	 0 0
 0 x   0   0  0  1  0  	 0 0
 0 z   0   0  0  1  1  	 0 0
 1 0   0   0  1  0  0  	 0 0
 1 1   1   0  1  0  1  	 0 1
 1 x   x   0  1  1  0  	 1 0
 1 z   x   0  1  1  1  	 1 0
 x 0   0   1  0  0  0  	 0 0
 x 1   x   1  0  0  1  	 1 0
 x x   x   1  0  1  0  	 1 0
 x z   x   1  0  1  1  	 1 0
 z 0   0   1  1  0  0  	 0 0
 z 1   x   1  1  0  1  	 1 0
 z x   x   1  1  1  0  	 1 0
 z z   x   1  1  1  1  	 1 0
})"
  :enabled t
  (cond ((and (integerp i) (integerp j)) (logand i j))
        (t
         (let* ((di (@d i))
                (ii (@i i))
                (dj (@d j))
                (ij (@i j))
                (ians (logior (logand ii (logior ij dj)) (logand di ij)))
                (dans (logandc2 (logand di dj) ians)))
           (@cons dans ians))))
  ///
  (defthm type-of-@logand (@integerp (@logand i j)))

  (defthm @logand-integer
    (implies (and (integerp i)
                  (integerp j))
             (equal (@logand i j)
                    (logand i j)))))

(define @logior ((i @integerp)
                 (j @integerp))
  :short "4-Valued LOGIOR"
  :long "@({
 i|j = ?  ii di ij dj  ians/dans

 0 0   0   0  0  0  0  	 0 0
 0 1   1   0  0  0  1  	 0 1
 0 x   x   0  0  1  0  	 1 0
 0 z   x   0  0  1  1  	 1 0
 1 0   1   0  1  0  0  	 0 1
 1 1   1   0  1  0  1  	 0 1
 1 x   1   0  1  1  0  	 0 1
 1 z   1   0  1  1  1  	 0 1
 x 0   x   1  0  0  0  	 1 0
 x 1   1   1  0  0  1  	 0 1
 x x   x   1  0  1  0  	 1 0
 x z   x   1  0  1  1  	 1 0
 z 0   x   1  1  0  0  	 1 0
 z 1   1   1  1  0  1  	 0 1
 z x   x   1  1  1  0  	 1 0
 z z   x   1  1  1  1  	 1 0
})"
  :enabled t
  (cond
   ((and (integerp i) (integerp j)) (logior i j))
   (t
    (let* ((di (@d i))
	   (ii (@i i))
	   (dj (@d j))
	   (ij (@i j))
	   (ians (logior (logand ii (logorc2 ij dj)) (logandc1 di ij)))
	   (dans (logandc2 (logior di dj) ians)))
      (@cons dans ians))))
  ///
  (defthm type-of-@logior (@integerp (@logior i j)))

  (defthm @logior-integer
    (implies (and (integerp i)
                  (integerp j))
             (equal (@logior i j)
                    (logior i j)))))

(define @t-wire ((i @integerp)
                 (j @integerp))
  :short "Tristate resolution function."
  :long "@({
 i.j = ?  ii di ij dj  ians/dans

 0 0   0   0  0  0  0  	 0 0
 0 1   x   0  0  0  1  	 1 0
 0 x   x   0  0  1  0  	 1 0
 0 z   0   0  0  1  1  	 0 0
 1 0   x   0  1  0  0  	 1 0
 1 1   1   0  1  0  1  	 0 1
 1 x   x   0  1  1  0  	 1 0
 1 z   1   0  1  1  1  	 0 1
 x 0   x   1  0  0  0  	 1 0
 x 1   x   1  0  0  1  	 1 0
 x x   x   1  0  1  0  	 1 0
 x z   x   1  0  1  1  	 1 0
 z 0   0   1  1  0  0  	 0 0
 z 1   1   1  1  0  1  	 0 1
 z x   x   1  1  1  0  	 1 0
 z z   z   1  1  1  1  	 1 1
})"
  :enabled t
  (let* ((di (@d i))
	 (ii (@i i))
	 (dj (@d j))
	 (ij (@i j))
	 (ians (logior (logand ii (logorc1 di ij))
		       (logior (logandc2 ij dj)
			       (logandc1 ii (logandc1 ij (logxor di dj))))))
	 (dans (logand di dj)))
    (@cons dans ians))
  ///
  (defthm type-of-@t-wire (@integerp (@t-wire i j))))

;  Other @LOGOPS.  More efficient definitions are possible for those who
;  are inclined to do the work.

(define @logandc1 ((i @integerp)
                   (j @integerp))
  :short "4-Valued LOGANDC1."
  :enabled t
  (@logand (@lognot i) j))

(define @logandc2 ((i @integerp)
                   (j @integerp))
  :short "4-Valued LOGANDC2."
  :enabled t
  (@logand i (@lognot j)))

(define @lognand ((i @integerp)
                  (j @integerp))
  :short "4-Valued LOGNAND."
  :enabled t
  (@lognot (@logand i j)))

(define @lognor ((i @integerp)
                 (j @integerp))
  :short "4-Valued LOGNOR."
  :enabled t
  (@lognot (@logior i j)))

(define @logorc1 ((i @integerp)
                  (j @integerp))
  :short "4-Valued LOGORC1."
  :enabled t
  (@logior (@lognot i) j))

(define @logorc2 ((i @integerp)
                  (j @integerp))
  :short "4-Valued LOGORC2."
  :enabled t
  (@logior i (@lognot j)))

(define @logeqv ((i @integerp)
                 (j @integerp))
  :short "4-Valued LOGEQV."
  :enabled t
  (@logand (@logorc1 i j) (@logorc1 j i)))

(define @logxor ((i @integerp)
                 (j @integerp))
  :short "4-Valued LOGXOR."
  :enabled t
  (@lognot (@logeqv i j)))

(encapsulate ()

  (local (in-theory (e/d (@lognot @logand) (@integerp))))

  (defthm type-of-binary-@logops
    (and (@integerp (@logandc1 i j))
         (@integerp (@logandc2 i j))
         (@integerp (@logior i j))
         (@integerp (@lognand i j))
         (@integerp (@lognor i j))
         (@integerp (@logorc1 i j))
         (@integerp (@logorc1 i j))
         (@integerp (@logeqv i j))
         (@integerp (@logxor i j)))
    :hints(("Goal" :in-theory (disable zp zip ifix logior-=-0
                                       (:t @integerp)
                                       (:t binary-logior)
                                       (:t ifix)))))

  (defthm binary-@logops-integer
    (implies (and (integerp i)
                  (integerp j))
             (and (equal (@logandc1 i j) (logandc1 i j))
                  (equal (@logandc2 i j) (logandc2 i j))
                  (equal (@logior i j) (logior i j))
                  (equal (@lognand i j) (lognand i j))
                  (equal (@lognor i j) (lognor i j))
                  (equal (@logorc1 i j) (logorc1 i j))
                  (equal (@logorc1 i j) (logorc1 i j))
                  (equal (@logeqv i j) (logeqv i j))
                  (equal (@logxor i j) (logxor i j))))
    :hints
    (("Goal" :in-theory (enable logandc1 logandc2 logior lognand lognor
                                logorc1 logorc2 logeqv logxor)))))


;;;****************************************************************************
;;;
;;;  Logical operations on single @bits.
;;;
;;;  @B-NOT i
;;;  @B-AND i j
;;;  @B-IOR i j
;;;  @B-XOR i j
;;;  @B-EQV i j
;;;  @B-NAND i j
;;;  @B-NOR i j
;;;  @B-ANDC1 i j
;;;  @B-ANDC2 i j
;;;  @B-ORC1 i j
;;;  @B-ORC2 i j
;;;
;;;****************************************************************************

(defxdoc @logops-bit-functions
  :parents (@logops)
  :short "Versions of the standard logical operations that operate on single @bits.")

(local (xdoc::set-default-parents @logops-bit-functions))

(define @b-not ((i @bitp))
  :enabled t
  (case i (0 1) (1 0) (t *@x-bit*)))

(define @b-and ((i @bitp)
                (j @bitp))
  :enabled t
  (or (and (equal i 0) 0)
      (and (equal j 0) 0)
      (and (equal i 1) (equal j 1) 1)
      *@x-bit*))

(define @b-ior ((i @bitp)
                (j @bitp))
  :enabled t
  (or (and (equal i 1) 1)
      (and (equal j 1) 1)
      (and (equal i 0) (equal j 0) 0)
      *@x-bit*))

(define @b-xor ((i @bitp)
                (j @bitp))
  :enabled t
  (or (and (bitp i) (bitp j) (b-xor i j))
      *@x-bit*))

(define @b-eqv ((i @bitp)
                (j @bitp))
  :enabled t
  (or (and (bitp i) (bitp j) (b-eqv i j))
      *@x-bit*))

(define @b-nand ((i @bitp)
                 (j @bitp))
  :enabled t
  (or (and (equal i 0) 1)
      (and (equal j 0) 1)
      (and (equal i 1) (equal j 1) 0)
      *@x-bit*))

(define @b-nor ((i @bitp)
                (j @bitp))
  :enabled t
  (or (and (equal i 1) 0)
      (and (equal j 1) 0)
      (and (equal i 0) (equal j 0) 1)
      *@x-bit*))

(define @b-andc1 ((i @bitp)
                  (j @bitp))
  :enabled t
  (or (and (equal i 1) 0)
      (and (equal j 0) 0)
      (and (equal i 0) (equal j 1) 1)
      *@x-bit*))

(define @b-andc2 ((i @bitp)
                  (j @bitp))
  :enabled t
  (@b-andc1 j i))

(define @b-orc1 ((i @bitp)
                 (j @bitp))
  :enabled t
  (or (and (equal i 0) 1)
      (and (equal j 1) 1)
      (and (equal i 1) (equal j 0) 0)
      *@x-bit*))

(define @b-orc2 ((i @bitp)
                 (j @bitp))
  :enabled t
  (@b-orc1 j i))

(defrule type-of-@bit-functions
  :short "All of the @BIT functions return @(see @BITP) @(INTEGERP)S."
  (and (@bitp (@b-not i))
       (@integerp (@b-not i))
       (@bitp (@b-and i j))
       (@integerp (@b-and i j))
       (@bitp (@b-ior i j))
       (@integerp (@b-ior i j))
       (@bitp (@b-xor i j))
       (@integerp (@b-xor i j))
       (@bitp (@b-eqv i j))
       (@integerp (@b-eqv i j))
       (@bitp (@b-nand i j))
       (@integerp (@b-nand i j))
       (@bitp (@b-nor i j))
       (@integerp (@b-nor i j))
       (@bitp (@b-andc1 i j))
       (@integerp (@b-andc1 i j))
       (@bitp (@b-andc2 i j))
       (@integerp (@b-andc2 i j))
       (@bitp (@b-orc1 i j))
       (@integerp (@b-orc1 i j))
       (@bitp (@b-orc2 i j))
       (@integerp (@b-orc2 i j))))

(defrule @bit-functions-integer
  :short "Rewrite: Reduce all of the @BIT functions with integer args."
  (and (implies (bitp i)
                (equal (@b-not i)
                       (b-not i)))
       (implies (and (bitp i)
                     (bitp j))
                (and (equal (@b-and i j) (b-and i j))
                     (equal (@b-ior i j) (b-ior i j))
                     (equal (@b-xor i j) (b-xor i j))
                     (equal (@b-eqv i j) (b-eqv i j))
                     (equal (@b-nand i j) (b-nand i j))
                     (equal (@b-nor i j) (b-nor i j))
                     (equal (@b-andc1 i j) (b-andc1 i j))
                     (equal (@b-andc2 i j) (b-andc2 i j))
                     (equal (@b-orc1 i j) (b-orc1 i j))
                     (equal (@b-orc2 i j) (b-orc2 i j))))))


(local (xdoc::set-default-parents @logops))

(define @loghead ((size (and (integerp size)
                             (<= 0 size)))
                  (i @integerp))
  :short "4-Valued LOGHEAD."
  :enabled t
  (cond
   ((integerp i) (loghead size i))
   (t (@cons (loghead size (@@d i)) (loghead size (@@i i)))))
  ///
  (defthm type-of-@loghead (@integerp (@loghead i j)))

  (defthm @loghead-integer
    (implies (integerp i)
             (equal (@loghead size i)
                    (loghead size i)))))

(define @logtail ((size (and (integerp size)
                             (<= 0 size)))
                  (i @integerp))
  :short "4-Valued LOGTAIL."
  :enabled t
  (cond
   ((integerp i) (logtail size i))
   (t (@cons (logtail size (@@d i)) (logtail size (@@i i)))))
  ///
  (defthm type-of-@logtail (@integerp (@logtail i j)))

  (defthm @logtail-integer
    (implies (integerp i)
             (equal (@logtail size i)
                    (logtail size i)))))

(define @logext ((size (and (integerp size)
                            (< 0 size)))
                 (i @integerp))
  :short "4-Valued LOGEXT."
  :enabled t
  (cond
   ((integerp i) (logext size i))
   (t (@cons (logext size (@@d i)) (logext size (@@i i)))))
  ///
  (defthm type-of-@logext (@integerp (@logext i j)))
  (defthm @logext-integer
    (implies (integerp i)
             (equal (@logext size i)
                    (logext size i)))))


(define @logsat ((size (and (integerp size)
                            (< 0 size)))
                 (i @integerp))
  :short "4-Valued LOGSAT."
  :long "<p>Note the conservative definition.  We don't know what it means to
  saturate an indeterminate integer.  Also note that LOGSAT and @LOGSAT always
  return a `signed' object.</p>"
  :enabled t
  (cond ((integerp i) (logsat size i))
        (t *@x*))
  ///
  (defthm type-of-@logsat (@integerp (@logsat i j)))

  (defthm @logsat-integer
    (implies (integerp i)
             (equal (@logsat size i)
                    (logsat size i)))))

(define @logapp ((size (and (integerp size)
                            (<= 0 size)))
                 (i @integerp)
                 (j @integerp))
  :short "4-Valued LOGAPP."
  ;; not enabled (was previously disabled)
  (cond
   ((and (integerp i) (integerp j)) (logapp size i j))
   (t (@cons (logapp size (@d i) (@d j))
	     (logapp size (@i i) (@i j)))))
  ///
  (defthm type-of-@logapp (@integerp (@logapp size i j)))

  (defthm @logapp-integer
    (implies (and (integerp i)
                  (integerp j))
             (equal (@logapp size i j)
                    (logapp size i j)))))


(define @logbit ((pos (and (integerp pos)
                           (>= pos 0)))
                 (i @integerp))
  :short "4-Valued LOGBIT."
  :enabled t
  (cond
   ((integerp i) (logbit pos i))
   (t (@cons (logbit pos (@@d i)) (logbit pos (@@i i)))))
  ///
  (defthm type-of-@logbit (@integerp (@logbit pos i)))

  (defthm @logbit-integer
    (implies (integerp i)
             (equal (@logbit pos i)
                    (logbit pos i)))))


(define @logrev ((size (and (integerp size)
                            (<= 0 size)))
                 (i @integerp))
  :short "4-Valued LOGREV."
  (cond
   ((integerp i) (logrev size i))
   (t (@cons (logrev size (@@d i)) (logrev size (@@i i)))))
  ///
  (defthm type-of-@logrev (@integerp (@logrev i j)))

  (defthm @logrev-integer
    (implies (integerp i)
             (equal (@logrev size i)
                    (logrev size i)))))


(define @rdb ((bsp bspp)
              (i   @integerp))
  :short "4-valued RDB."
  :long "<p>NB: We consider this a specification construct, not a hardware
  device.  Thus, the byte specifier must be determinate.</p>"
  :enabled t
  (cond
   ((integerp i) (rdb bsp i))
   (t (@cons (rdb bsp (@@d i)) (rdb bsp (@@i i)))))
  ///
  (defthm type-of-@rdb (@integerp (@rdb bsp i)))

  (defthm @rdb-integer
    (implies (integerp i)
             (equal (@rdb bsp i)
                    (rdb bsp i)))))

(define @wrb ((i   @integerp)
              (bsp bspp)
              (j   @integerp))
  :short "4-valued WRB."
  :long "<p>NB: We consider this a specification construct, not a hardware
  device.  Thus, the byte specifier must be determinate.</p>"
  :enabled t
  (@cons (wrb (@d i) bsp (@d j)) (wrb (@i i) bsp (@i j)))
  ///
  (defthm type-of-@wrb (@integerp (@wrb i bsp j)))

  (defthm @wrb-integer
    (implies (and (integerp i)
                  (integerp j)
                  (bspp bsp))
             (equal (@wrb i bsp j)
                    (wrb i bsp j)))
    :hints (("Goal" :in-theory (enable wrb)))))


;;;****************************************************************************
;;;
;;;  Lemmas
;;;
;;;****************************************************************************

;;;  All @LOGOPS

(encapsulate ()

  (local
   (defthm @signed-byte-p-base-cases
     (and (implies (@signed-byte-p size i)
                   (@signed-byte-p size (@lognot i)))
          (implies (and (@signed-byte-p size i)
                        (@signed-byte-p size j))
                   (and (@signed-byte-p size (@logand i j))
                        (@signed-byte-p size (@logior i j)))))))

  (local (in-theory (disable @lognot @logand @logior @signed-byte-p)))

  (defrule @signed-byte-p-@logops
    :parents (@logops)
    :short "Rewrite: All @-logops are @SIGNED-BYTE-P when their arguments are."
    (and (implies (@signed-byte-p size i)
                  (@signed-byte-p size (@lognot i)))
         (implies (and (@signed-byte-p size i)
                       (@signed-byte-p size j))
                  (and (@signed-byte-p size (@logior i j))
                       (@signed-byte-p size (@logxor i j))
                       (@signed-byte-p size (@logand i j))
                       (@signed-byte-p size (@logeqv i j))
                       (@signed-byte-p size (@lognand i j))
                       (@signed-byte-p size (@lognor i j))
                       (@signed-byte-p size (@logandc1 i j))
                       (@signed-byte-p size (@logandc2 i j))
                       (@signed-byte-p size (@logorc1 i j))
                       (@signed-byte-p size (@logorc2 i j)))))))



(defsection @logand-thms
  :extension @logand

  (defthm @unsigned-byte-p-@logand
    (implies (and (or (@unsigned-byte-p size i)
                      (@unsigned-byte-p size j))
                  (@integerp i)
                  (@integerp j))
             (@unsigned-byte-p size (@logand i j)))
    :hints (("Goal" :in-theory (enable @unsigned-byte-p
                                       @logand
                                       @integerp logandc2
                                       unsigned-byte-p logand))))

  (defthm simplify-@logand
    (and (equal (@logand i 0) 0)
         (equal (@logand 0 i) 0))))


(defsection @logior-thms
  :extension @logior

  (defthm @unsigned-byte-p-@logior
    (implies (and (@unsigned-byte-p size i)
                  (@unsigned-byte-p size j))
             (@unsigned-byte-p size (@logior i j)))
    :hints (("Goal" :in-theory (enable @unsigned-byte-p @logior
                                       logandc1 logandc2 unsigned-byte-p)))))

;;;  @BIT Functions

(defrule simplify-@bit-functions
  :parents (@logops-bit-functions)
  :short "Simplification rules for all binary @B- functions including
  commutative rules, reductions with 1 explicit value, and reductions for
  identical agruments and complemented arguments."

  (and (equal (@b-and x y) (@b-and y x))
       (equal (@b-and 0 x) 0)
       (equal (@b-and 1 x) (@bfix x))
       (equal (@b-and x x) (@bfix x))

       (equal (@b-ior x y) (@b-ior y x))
       (equal (@b-ior 0 x) (@bfix x))
       (equal (@b-ior 1 x) 1)
       (equal (@b-ior x x) (@bfix x))

       (equal (@b-xor x y) (@b-xor y x))
       (equal (@b-xor 0 x) (@bfix x))
       (equal (@b-xor 1 x) (@b-not x))

       (equal (@b-eqv x y) (@b-eqv y x))
       (equal (@b-eqv 0 x) (@b-not x))
       (equal (@b-eqv 1 x) (@bfix x))

       (equal (@b-nand x y) (@b-nand y x))
       (equal (@b-nand 0 x) 1)
       (equal (@b-nand 1 x) (@b-not x))
       (equal (@b-nand x x) (@b-not x))

       (equal (@b-nor x y) (@b-nor y x))
       (equal (@b-nor 0 x) (@b-not x))
       (equal (@b-nor 1 x) 0)
       (equal (@b-nor x x) (@b-not x))

       (equal (@b-andc1 0 x) (@bfix x))
       (equal (@b-andc1 x 0) 0)
       (equal (@b-andc1 1 x) 0)
       (equal (@b-andc1 x 1) (@b-not x))

       (equal (@b-andc2 0 x) 0)
       (equal (@b-andc2 x 0) (@bfix x))
       (equal (@b-andc2 1 x) (@b-not x))
       (equal (@b-andc2 x 1) 0)

       (equal (@b-orc1 0 x) 1)
       (equal (@b-orc1 x 0) (@b-not x))
       (equal (@b-orc1 1 x) (@bfix x))
       (equal (@b-orc1 x 1) 1)

       (equal (@b-orc2 0 x) (@b-not x))
       (equal (@b-orc2 x 0) 1)
       (equal (@b-orc2 1 x) 1)
       (equal (@b-orc2 x 1) (@bfix x))))

(defsection @loghead-thms
  :extension @loghead

  (defthm @unsigned-byte-p-@loghead
    (implies (and (>= size1 size)
                  (>= size 0)
                  (integerp size)
                  (integerp size1))
             (@unsigned-byte-p size1 (@loghead size i))))

  (defthm @loghead-identity
    (implies (@unsigned-byte-p size i)
             (equal (@loghead size i)
                    i)))

  (defthm @bitp-@loghead-1
    (@bitp (@loghead 1 i))
    :hints (("Goal" :in-theory (enable @bitp @loghead)))))


(defsection @logext-thms
  :extension @logext

  (defthm @signed-byte-p-@logext
    (implies (and (>= size1 size)
                  (> size 0)
                  (integerp size1)
                  (integerp size))
             (@signed-byte-p size1 (@logext size i))))

  (defthm @logext-identity
    (implies (@signed-byte-p size i)
             (equal (@logext size i)
                    i))))


(defsection @logsat-thms
  :extension @logsat

  (defthm @signed-byte-p-@logsat
    (implies (and (>= size1 size)
                  (> size 0)
                  (integerp size1)
                  (integerp size))
             (@signed-byte-p size1 (@logsat size i)))))


(defsection @logbit-thms
  :extension @logbit

  (defthm @bitp-@logbit
    (@bitp (@logbit pos i))))


(defsection @rdb-thms
  :extension @rdb

  (defthm @unsigned-byte-p-@rdb
    (implies (and (>= size (bsp-size bsp))
                  (>= size 0)
                  (integerp size)
                  (bspp bsp))
             (@unsigned-byte-p size (@rdb bsp i)))
    :hints (("Goal" :in-theory (enable @unsigned-byte-p @rdb))))

  (defthm @bitp-@rdb-bsp-1
    (implies (and (@integerp i)
                  (equal (bsp-size bsp) 1))
             (@bitp (@rdb bsp i)))
    :hints (("Goal" :in-theory (enable @bitp @rdb rdb @integerp)))))


(defsection @wrb-thms
  :extension @wrb

  (defthm @unsigned-byte-p-@wrb
    (implies (and (@unsigned-byte-p n j)
                  (<= (+ (bsp-size bsp) (bsp-position bsp)) n)
                  (@integerp i)
                  (integerp n)
                  (bspp bsp))
             (@unsigned-byte-p n (@wrb i bsp j)))))


;;;****************************************************************************
;;;
;;;  Theories
;;;
;;;****************************************************************************

(defval *@functions*
  :short "List of all @(see @logops) functions."
  '(@integerp
    @bitp @bfix
    @+ @unary-- @*
    @unsigned-byte-p @signed-byte-p
    @ash @logcar @lognot @logand @t-wire
    @logandc1 @logandc2 @logior @lognand @lognor
    @logorc1 @logorc2 @logeqv @logxor
    @b-not @b-and @b-ior @b-xor @b-eqv @b-nand @b-nor
    @b-andc1 @b-andc2 @b-orc1 @b-orc2
    @rdb @wrb
    @loghead @logext @logsat @logbit @logrev))

(deftheory @functions *@functions*)

(in-theory (disable @functions))

(defsection @logops-theory
  :short "The \"minimal\" theory for the @(see @logops) book."
  :long "<p>This theory contains only those lemmas meant to be exported by the
  @('@logops') book.</p>"

  (deftheory @logops-theory
    (definition-free-theory
      (set-difference-theories (current-theory :here)
                               (current-theory '@logops)))))



;;;****************************************************************************
;;;
;;;  @DEFWORD
;;;
;;;  Use the DEFWORD code to define an @integer DEFWORD.
;;;
;;;****************************************************************************

(defsection @defword
  :short "A macro to define packed @integer data structures."
  :long "<p>@('@DEFWORD') is analogous to @(see DEFWORD), except that @DEFWORD
  uses @RDB and @WRB instead of RDB and WRB.</p>"

  (defmacro @defword (name struct &key conc-name set-conc-name keyword-updater doc)
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
            (defword-accessor-definitions '@RDB name conc-name struct))
           (updater-definitions
            (defword-updater-definitions '@WRB name set-conc-name struct))
           (field-names (strip-cars struct)))

        `(ENCAPSULATE () ;Only to make macroexpansion pretty.
                      (DEFLABEL ,name ,@(if doc `(:DOC ,doc) nil))
                      ,@accessor-definitions
                      ,@updater-definitions
                      ,(defword-keyword-updater
                         name keyword-updater set-conc-name field-names)))))))


;;;****************************************************************************
;;;
;;;  @DEFBYTETYPE
;;;
;;;  First, use DEFBYTETYPE to define the INTEGER version.  Then define
;;;  an analogous @INTEGER version.
;;;
;;;****************************************************************************

(defmacro @defbytetype (name size s/u &key saturating-coercion doc)
  (declare (xargs :guard (and (symbolp name)
                              ;; How to say that SIZE is a constant expression?
                              (or (eq s/u :SIGNED) (eq s/u :UNSIGNED))
                              (implies saturating-coercion
				       (and (symbolp saturating-coercion)
					    (eq s/u :SIGNED)))
                              (implies doc (stringp doc)))))

  `(PROGN

    (DEFBYTETYPE ,name ,size ,s/u
      :SATURATING-COERCION ,saturating-coercion :DOC ,doc)

    ,(let*
       ((integer-name name)
	(integer-predicate (pack-intern name name "-P"))
	(integer-saturating-coercion saturating-coercion)
	(name (pack-intern name "@" name))
	(saturating-coercion
	 (when$cl saturating-coercion
	   (pack-intern saturating-coercion "@" saturating-coercion)))
	(predicate (pack-intern name name "-P"))
	(predicate-lemma (pack-intern name predicate "-" name))
	(coercion-lemma (pack-intern name "REDUCE-" name))
	(forward-lemma (pack-intern predicate predicate "-FORWARD"))
	(type-lemma (pack-intern name "TYPE-OF-" name))
	(integer-lemma (pack-intern name name "-INTEGER"))
	(integer-predicate-lemma (pack-intern name predicate "-INTEGER"))
	(sat-lemma (pack-intern name predicate "-" saturating-coercion))
	(sat-type-lemma (pack-intern name "TYPE-OF-" saturating-coercion))
	(sat-integer-lemma (pack-intern name name "-SATURATING-INTEGER"))
	(x-constant (pack-intern name "*@X-" integer-name "*"))
	(theory (pack-intern name name "-THEORY")))

       `(ENCAPSULATE ()
	  (LOCAL (IN-THEORY (ENABLE ,integer-name ,integer-predicate
				    ,@(when$cl saturating-coercion
					(list integer-saturating-coercion)))))
	  (DEFUN ,predicate (X)
	    (DECLARE (XARGS :GUARD T))
	    ,(case s/u
	       (:SIGNED `(@SIGNED-BYTE-P ,size X))
	       (:UNSIGNED `(@UNSIGNED-BYTE-P ,size X))))
	  (DEFUN ,name (I)
	    ,@(when$cl doc (list doc))
	    (DECLARE (XARGS :GUARD (@INTEGERP I)))
	    ,(case s/u
	       (:SIGNED `(@LOGEXT ,size I))
	       (:UNSIGNED `(@LOGHEAD ,size I))))
	  (DEFCONST ,x-constant (,name *@X*))
	  (DEFTHM ,predicate-lemma
	    (,predicate (,name I)))
	  (DEFTHM ,coercion-lemma
	    (IMPLIES
	     (,predicate I)
	     (EQUAL (,name I) I)))
	  (DEFTHM ,forward-lemma
	    (IMPLIES
	     (,predicate X)
	     (@INTEGERP X))
	    :RULE-CLASSES :FORWARD-CHAINING)
	  (DEFTHM ,type-lemma
	    (@INTEGERP (,name X)))
	  (DEFTHM ,integer-lemma
	    (IMPLIES
	     (INTEGERP I)
	     (EQUAL (,name I) (,integer-name I))))
	  (DEFTHM ,integer-predicate-lemma
	    (IMPLIES
	     (INTEGERP I)
	     (EQUAL (,predicate I) (,integer-predicate I))))
	  ,@(when$cl saturating-coercion
	      (list
	       `(DEFUN ,saturating-coercion (I)
		  (DECLARE (XARGS :GUARD (@INTEGERP I)))
		  (@LOGSAT ,size I))
	       `(DEFTHM ,sat-lemma
		  (,predicate (,saturating-coercion I)))
	       `(DEFTHM ,sat-type-lemma
		  (@INTEGERP (,saturating-coercion X)))
	       `(DEFTHM ,sat-integer-lemma
		  (IMPLIES
		   (INTEGERP I)
		   (EQUAL (,saturating-coercion I)
			  (,integer-saturating-coercion I))))))
	  (IN-THEORY
	   (DISABLE ,predicate ,name
		    ,@(when$cl saturating-coercion
			(list saturating-coercion))))
	  (DEFTHEORY ,theory
	    (UNION-THEORIES
	     (DEFUN-TYPE/EXEC-THEORY
	       '(,predicate ,name ,@(when$cl saturating-coercion
				      (list saturating-coercion))))
	     '(,predicate-lemma ,coercion-lemma ,forward-lemma
				,type-lemma ,integer-lemma
				,@(when$cl saturating-coercion
				    (list sat-lemma sat-type-lemma
					  sat-integer-lemma)))))))))
