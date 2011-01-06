; @logops.lisp  --  4-valued integer hardware model
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
;;;    @logops.lisp
;;;
;;;    Bishop Brock
;;;    Computational Logic, Inc.
;;;    1717 West 6th Street, Suite 290
;;;    Austin, Texas 78703
;;;    (512) 322-9951
;;;    brock@cli.com
;;;
;;;  We can model `4-valued' integers using a pair of integers.  First think
;;;  about a pair of bits.  We assign the values as 00 = `0', 01 = `1', 10 =
;;;  `x', 11 = `z', where `x' is the `unknown' and `z' the `floating' value.
;;;  We call the low-order bit the `determinate' bit and the high-order bit
;;;  the `indeterminate' bit.  We extend this notion to integers by using a
;;;  pair of integers, where the first integer is the determinate integer,
;;;  the second integer is the indeterminate integer, and each 4-valued bit f
;;;  the integer is a slice through the two integers.  For example,
;;;
;;;  (0 . 0)       =  ..00000000000
;;;  (1 . 0)       =  ..00000000001
;;;  (10 . 12)     =  ..0000000ZX10
;;;  (0 . -1)      =  ..XXXXXXXXXXX  
;;;  (1023 . 1023) =  ..0ZZZZZZZZZZ
;;;
;;;  All of the 4-valued counterparts of integer functions are uniformly
;;;  defined with the prefix character `@', e.g., @+, @LOGAND, etc..
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
(progn (minimal-ihs-theory))

(deflabel @logops :doc 
  ":doc-section @logops
  A book of 4-valued counterparts for logical operations on integers.
  ~/~/~/")

;  These will never appear in user code, so they're macros for efficiency.

(defmacro @cons (d i)
  ":doc-section @cons
  4-Valued CONS.
  ~/~/~/"
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

(defun @integerp (@)
  ":doc-section @integerp
  4-Valued INTEGERP.
  ~/~/~/"
  (declare (xargs :guard t))
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
  :hints
  (("Goal"
    :in-theory (enable @integerp))))

;;;  Constants

(defconst *@x* (@cons 0 -1))

(defconst *@x-bit* (@cons 0 1))

(defconst *@z* (@cons -1 -1))

(defconst *@z-bit* (@cons 1 1))

;;;  @BITP

(defun @bitp (x)
  ":doc-section @logops
  4-valued BITP.
  ~/~/~/"
  (declare (xargs :guard t))
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

(defun @bfix (x)
  ":doc-section @logops
  4-valued BFIX.
  ~/~/~/"
  (declare (xargs :guard t))
  (case x
    (0 0)
    (1 1)
    (t *@x-bit*)))

(defthm type-of-@bfix
  (and (@bitp (@bfix i))
       (@integerp (@bfix i))))

;;;  @+

(defun @+ (i j)
  ":doc-section @+
  4-Valued +.
  ~/~/~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp j))))
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

(defun @unary-- (i)
  ":doc-section @unary--
  4-Valued UNARY--.
  ~/~/~/"
  (declare (xargs :guard (@integerp i)))
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

;;;  @*

(defun @* (i j)
  ":doc-section @*
  4-Valued *.
  ~/~/~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp j))))
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

(defun @unsigned-byte-p (size i)
  ":doc-section @unsigned-byte-p
  4-Valued UNSIGNED-BYTE-P.
  ~/~/~/"
  (declare (xargs :guard t))
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
  :hints
  (("Goal"
    :in-theory (enable @unsigned-byte-p unsigned-byte-p))))

;;;  @SIGNED-BYTE-P

(defun @signed-byte-p (size i)
  ":doc-section @signed-byte-p
  4-Valued SIGNED-BYTE-P.
  ~/~/~/"
  (declare (xargs :guard t))
  (and (integerp size)
       (< 0 size)
       (@integerp i)
       (signed-byte-p size (@d i))
       (signed-byte-p size (@i i))))

(defthm @signed-byte-p-integer
  (implies
   (integerp i)
   (equal (@signed-byte-p size i)
	  (signed-byte-p size i)))
  :hints
  (("Goal"
    :in-theory (enable signed-byte-p))))

(defthm @signed-byte-p-forward
  (implies
   (@signed-byte-p size i)
   (@integerp i))
  :rule-classes :forward-chaining)

(defthm @signed-byte-p-cons
  (equal (@signed-byte-p size (cons d i))
	 (and (signed-byte-p size d)
	      (signed-byte-p size i)
	      (not (= i 0))))
  :hints
  (("Goal"
    :in-theory (enable @signed-byte-p signed-byte-p))))

;;; @ASH

#|
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
  ":doc-section @ash
  4-Valued ASH.
  ~/~/
  Note the conservative definition.  We do not define @ASH when count is
  indeterminate. 
  ~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp count))))
  (cond
   ((integerp count) (cond
		      ((integerp i) (ash! i count))
		      (t (@cons (ash! (@@d i) count) (ash! (@@i i) count)))))
   (t *@x*)))
|#

(defun @ash (i count)
  ":doc-section @ash
  4-Valued ASH.
  ~/~/
  Note the conservative definition.  We do not define @ASH when count is
  indeterminate. 
  ~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp count))))
  (cond
   ((integerp count) (cond
		      ((integerp i) (ash i count))
		      (t (@cons (ash (@@d i) count) (ash (@@i i) count)))))
   (t *@x*)))

(defthm type-of-@ash (@integerp (@ash i count)))

(defthm @ash-integer
  (implies
   (and (integerp i)
	(integerp count))
   (equal (@ash i count)
	  (ash i count))))

;;;  @INTEGER-LENGTH

(defun @integer-length (i)
  ":doc-section @logops
  4-valued INTEGER-LENGTH.
  ~/~/
  Note that when indeterminate, @INTEGER-LENGTH returns a `signed' X.  Thus
  it may be necessary to coerce the result to an unsigned type.~/"
  (declare (xargs :guard (@integerp i)))
  (cond
   ((integerp i) (integer-length i))
   (t *@x*)))

(defthm type-of-@integer-length (@integerp (@integer-length i)))

(defthm @integer-length-integer
  (implies
   (integerp i)
   (equal (@integer-length i)
	  (integer-length i))))

;;;  @LOGCOUNT

(defun @logcount (i)
  ":doc-section @logops
  4-value LOGCOUNT.
  ~/~/
  When indeterminate @LOGCOUNT returns a signed X, thus it may need to be
  coerced to an unsigned value. ~/"
  (declare (xargs :guard (@integerp i)))
  (cond
   ((integerp i) (logcount i))
   (t *@x*)))

(defthm type-of-@logount (@integerp (@logcount i)))

(defthm @logcount-integer
  (implies
   (integerp i)
   (equal (@logcount i)
	  (logcount i))))

;;;  @LOGCAR

(defun @logcar (i)
  ":doc-section @logcar
  4-Valued LOGCAR.
  ~/~/~/"
  (declare (xargs :guard (@integerp i)))
  (cond
   ((integerp i) (logcar i))
   (t (@cons (logcar (@@d i)) (logcar (@@i i))))))

(defthm type-of-@logcar (@integerp (@logcar i)))

(defthm @logcar-integer
  (implies
   (integerp i)
   (equal (@logcar i)
	  (logcar i))))

;;;  @LOGNOT

(defun @lognot (i)
  ":doc-section @lognot
  4-Valued LOGNOT.
  ~/~/

 ~i = ?  ii di  ians/dans

  0   1   0  0    0 1
  1   0   0  1    0 0
  x   x   1  0    1 0
  z   x   1  1    1 0

 ~/"
  (declare (xargs :guard (@integerp i)))
  (cond
   ((integerp i) (lognot i))
   (t
    (let* ((di (@d i))
	   (ii (@i i)))
      (@cons (lognor di ii) ii)))))

(defthm type-of-@lognot (@integerp (@lognot i)))

(defthm @lognot-integer
  (implies
   (integerp i)
   (equal (@lognot i)
	  (lognot i))))

;;; @LOGAND

(defun @logand (i j)
  ":doc-section @logand
  4-Valued LOGAND.
  ~/~/

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

 ~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp j))))
  (cond
   ((and (integerp i) (integerp j)) (logand i j))
   (t
    (let* ((di (@d i))
	   (ii (@i i))
	   (dj (@d j))
	   (ij (@i j))
	   (ians (logior (logand ii (logior ij dj)) (logand di ij)))
	   (dans (logandc2 (logand di dj) ians)))
      (@cons dans ians)))))

(defthm type-of-@logand (@integerp (@logand i j)))

(defthm @logand-integer
  (implies
   (and (integerp i)
	(integerp j))
   (equal (@logand i j)
	  (logand i j))))

;;;  @LOGIOR

(defun @logior (i j)
  ":doc-section @logior
  4-Valued LOGIOR
  ~/~/

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

 ~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp j))))
  (cond
   ((and (integerp i) (integerp j)) (logior i j))
   (t
    (let* ((di (@d i))
	   (ii (@i i))
	   (dj (@d j))
	   (ij (@i j))
	   (ians (logior (logand ii (logorc2 ij dj)) (logandc1 di ij)))
	   (dans (logandc2 (logior di dj) ians)))
      (@cons dans ians)))))

(defthm type-of-@logior (@integerp (@logior i j)))

(defthm @logior-integer
  (implies
   (and (integerp i)
	(integerp j))
   (equal (@logior i j)
	  (logior i j))))

;;; @T-WIRE

(defun @t-wire (i j)
  ":doc-section @t-wire
  Tristate resolution function.
  ~/~/

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

 ~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp j))))
  (let* ((di (@d i))
	 (ii (@i i))
	 (dj (@d j))
	 (ij (@i j))
	 (ians (logior (logand ii (logorc1 di ij)) 
		       (logior (logandc2 ij dj) 
			       (logandc1 ii (logandc1 ij (logxor di dj))))))
	 (dans (logand di dj)))
    (@cons dans ians)))

(defthm type-of-@t-wire (@integerp (@t-wire i j)))

;  Other @LOGOPS.  More efficient definitions are possible for those who
;  are inclined to do the work.

(defun @logandc1 (i j)
  ":doc-section @logandc1
  4-Valued LOGANDC1.
  ~/~/~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp j))
		  :verify-guards nil))
  (@logand (@lognot i) j))

(defun @logandc2 (i j)
  ":doc-section @logandc2
  4-Valued LOGANDC2.
  ~/~/~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp j))
		  :verify-guards nil))
  (@logand i (@lognot j)))

(defun @lognand (i j)
  ":doc-section @lognand
  4-Valued LOGNAND.
  ~/~/~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp j))
		  :verify-guards nil))
  (@lognot (@logand i j)))

(defun @lognor (i j)
  ":doc-section @lognor
  4-Valued LOGNOR.
  ~/~/~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp j))
		  :verify-guards nil))
  (@lognot (@logior i j)))

(defun @logorc1 (i j)
  ":doc-section @logorc1
  4-Valued LOGORC1.
  ~/~/~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp j))
		  :verify-guards nil))
  (@logior (@lognot i) j))

(defun @logorc2 (i j)
  ":doc-section @logorc2
  4-Valued LOGORC2.
  ~/~/~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp j))
		  :verify-guards nil))
  (@logior i (@lognot j)))

(defun @logeqv (i j)
  ":doc-section @logeqv
  4-Valued LOGEQV.
  ~/~/~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp j))
		  :verify-guards nil))
  (@logand (@logorc1 i j) (@logorc1 j i)))

(defun @logxor (i j)
  ":doc-section @logxor
  4-Valued LOGXOR.
  ~/~/~/"
  (declare (xargs :guard (and (@integerp i)
			      (@integerp j))
		  :verify-guards nil))
  (@lognot (@logeqv i j)))

(encapsulate ()

  (local (in-theory (e/d (@lognot @logand) (@integerp))))

  (verify-guards @logandc1)
  (verify-guards @logandc2)
  (verify-guards @logior)
  (verify-guards @lognand)
  (verify-guards @lognor)
  (verify-guards @logorc1)
  (verify-guards @logorc2)
  (verify-guards @logeqv)
  (verify-guards @logxor)

  (defthm type-of-binary-@logops
    (and
     (@integerp (@logandc1 i j))
     (@integerp (@logandc2 i j))
     (@integerp (@logior i j))
     (@integerp (@lognand i j))
     (@integerp (@lognor i j))
     (@integerp (@logorc1 i j))
     (@integerp (@logorc1 i j))
     (@integerp (@logeqv i j))
     (@integerp (@logxor i j))))

  (defthm binary-@logops-integer
    (implies
     (and (integerp i)
	  (integerp j))
     (and
      (equal (@logandc1 i j)
	     (logandc1 i j))
      (equal (@logandc2 i j)
	     (logandc2 i j))
      (equal (@logior i j)
	     (logior i j))
      (equal (@lognand i j)
	     (lognand i j))
      (equal (@lognor i j)
	     (lognor i j))
      (equal (@logorc1 i j)
	     (logorc1 i j))
      (equal (@logorc1 i j)
	     (logorc1 i j))
      (equal (@logeqv i j)
	     (logeqv i j))
      (equal (@logxor i j)
	     (logxor i j))))
    :hints
    (("Goal"
      :in-theory (enable logandc1 logandc2 logior lognand lognor
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

(deflabel @logops-bit-functions
 :doc ":doc-section @logops
 Versions of the standard logical operations that operate on single @bits.
 ~/~/~/")

(defun @b-not (i)
  ":doc-section @logops-bit-functions
  @B-NOT ~/~/~/"
  (declare (xargs :guard (@bitp i)))
  (case i (0 1) (1 0) (t *@x-bit*)))

(defun @b-and (i j)
  ":doc-section @logops-bit-functions
  @B-AND ~/~/~/"
  (declare (xargs :guard (and (@bitp i) (@bitp j))))
  (or (and (equal i 0) 0)
      (and (equal j 0) 0)
      (and (equal i 1) (equal j 1) 1)
      *@x-bit*))

(defun @b-ior (i j)
  ":doc-section @logops-bit-functions
  @B-IOR ~/~/~/"
  (declare (xargs :guard (and (@bitp i) (@bitp j))))
  (or (and (equal i 1) 1)
      (and (equal j 1) 1)
      (and (equal i 0) (equal j 0) 0)
      *@x-bit*))

(defun @b-xor (i j)
  ":doc-section @logops-bit-functions
  @B-XOR ~/~/~/"
  (declare (xargs :guard (and (@bitp i) (@bitp j))))
  (or (and (bitp i) (bitp j) (b-xor i j))
      *@x-bit*))

(defun @b-eqv (i j)
  ":doc-section @logops-bit-functions
  @B-EQV ~/~/~/"
  (declare (xargs :guard (and (@bitp i) (@bitp j))))
  (or (and (bitp i) (bitp j) (b-eqv i j))
      *@x-bit*))

(defun @b-nand (i j)
  ":doc-section @logops-bit-functions
  @B-NAND ~/~/~/"
  (declare (xargs :guard (and (@bitp i) (@bitp j))))
  (or (and (equal i 0) 1)
      (and (equal j 0) 1)
      (and (equal i 1) (equal j 1) 0)
      *@x-bit*))

(defun @b-nor (i j)
  ":doc-section @logops-bit-functions
  @B-NOR ~/~/~/"
  (declare (xargs :guard (and (@bitp i) (@bitp j))))
  (or (and (equal i 1) 0)
      (and (equal j 1) 0)
      (and (equal i 0) (equal j 0) 1)
      *@x-bit*))

(defun @b-andc1 (i j)
  ":doc-section @logops-bit-functions
  @B-ANDC1 ~/~/~/"
  (declare (xargs :guard (and (@bitp i) (@bitp j))))
  (or (and (equal i 1) 0)
      (and (equal j 0) 0)
      (and (equal i 0) (equal j 1) 1)
      *@x-bit*))  

(defun @b-andc2 (i j)
  ":doc-section @logops-bit-functions
  @B-ANDC2 ~/~/~/"
  (declare (xargs :guard (and (@bitp i) (@bitp j))))
  (@b-andc1 j i))

(defun @b-orc1 (i j)
  ":doc-section @logops-bit-functions
  @B-ORC1 ~/~/~/"
  (declare (xargs :guard (and (@bitp i) (@bitp j))))
  (or (and (equal i 0) 1)
      (and (equal j 1) 1)
      (and (equal i 1) (equal j 0) 0)
      *@x-bit*))

(defun @b-orc2 (i j)
  ":doc-section @logops-bit-functions
  @B-ORC2 ~/~/~/"
  (declare (xargs :guard (and (@bitp i) (@bitp j))))
  (@b-orc1 j i))

(defthm type-of-@bit-functions
  (and
   (@bitp (@b-not i))
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
   (@integerp (@b-orc2 i j)))
  :doc ":doc-section @logops-bit-functions
  Rewrite: All of the @BIT functions return @BITP @INTEGERS.
  ~/~/~/")

(defthm @bit-functions-integer
  (and
   (implies
    (bitp i)
    (equal (@b-not i)
	   (b-not i)))
   (implies
    (and (bitp i)
	 (bitp j))
    (and
     (equal (@b-and i j)
	    (b-and i j))
     (equal (@b-ior i j)
	    (b-ior i j))
     (equal (@b-xor i j)
	    (b-xor i j))
     (equal (@b-eqv i j)
	    (b-eqv i j))
     (equal (@b-nand i j)
	    (b-nand i j))
     (equal (@b-nor i j)
	    (b-nor i j))
     (equal (@b-andc1 i j)
	    (b-andc1 i j))
     (equal (@b-andc2 i j)
	    (b-andc2 i j))
     (equal (@b-orc1 i j)
	    (b-orc1 i j))
     (equal (@b-orc2 i j)
	    (b-orc2 i j)))))
  :hints
  (("Goal"
    :in-theory (enable bitp)))
  :doc ":doc-section @logops-bit-functions
  Rewrite: Reduce all of the @BIT functions with integer args.
  ~/~/~/")


;;;  @LOGHEAD

(defun @loghead (size i)
  ":doc-section @loghead
  4-Valued LOGHEAD.
  ~/~/~/"
  (declare (xargs :guard (and (integerp size)
			      (<= 0 size)
			      (@integerp i))))
  (cond
   ((integerp i) (loghead size i))
   (t (@cons (loghead size (@@d i)) (loghead size (@@i i))))))

(defthm type-of-@loghead (@integerp (@loghead i j)))

(defthm @loghead-integer
  (implies
   (integerp i)
   (equal (@loghead size i)
	  (loghead size i))))

;;;  @LOGTAIL

(defun @logtail (size i)
  ":doc-section @logtail
  4-Valued LOGTAIL.
  ~/~/~/"
  (declare (xargs :guard (and (integerp size)
			      (<= 0 size)
			      (@integerp i))))
  (cond
   ((integerp i) (logtail size i))
   (t (@cons (logtail size (@@d i)) (logtail size (@@i i))))))

(defthm type-of-@logtail (@integerp (@logtail i j)))

(defthm @logtail-integer
  (implies
   (integerp i)
   (equal (@logtail size i)
	  (logtail size i))))

;;;  @LOGEXT

(defun @logext (size i)
  ":doc-section @logext
  4-Valued LOGEXT.
  ~/~/~/"
  (declare (xargs :guard (and (integerp size)
			      (< 0 size)
			      (@integerp i))))
  (cond
   ((integerp i) (logext size i))
   (t (@cons (logext size (@@d i)) (logext size (@@i i))))))

(defthm type-of-@logext (@integerp (@logext i j)))

(defthm @logext-integer
  (implies
   (integerp i)
   (equal (@logext size i)
	  (logext size i))))


;;;  @LOGSAT

(defun @logsat (size i)
  ":doc-section @logsat
  4-Valued LOGSAT.
  ~/~/
  Note the conservative definition.  We don't know what it means to saturate
  an indeterminate integer.  Also note that LOGSAT and @LOGSAT always
  return a `signed' object.
   ~/"
  (declare (xargs :guard (and (integerp size)
			      (< 0 size)
			      (@integerp i))))
  (cond
   ((integerp i) (logsat size i))
   (t *@x*)))

(defthm type-of-@logsat (@integerp (@logsat i j)))

(defthm @logsat-integer
  (implies
   (integerp i)
   (equal (@logsat size i)
	  (logsat size i))))

;;;  @LOGAPP

(defun @logapp (size i j)
  ":doc-section @logapp
  4-Valued LOGAPP.
  ~/~/~/"
  (declare (xargs :guard (and (integerp size)
			      (<= 0 size)
			      (@integerp i)
			      (@integerp j))))
  (cond
   ((and (integerp i) (integerp j)) (logapp size i j))
   (t (@cons (logapp size (@d i) (@d j))
	     (logapp size (@i i) (@i j))))))

(defthm type-of-@logapp (@integerp (@logapp size i j)))

(defthm @logapp-integer
  (implies
   (and (integerp i)
	(integerp j))
   (equal (@logapp size i j)
	  (logapp size i j))))

(in-theory (disable @logapp))

;;;  @LOGBIT

(defun @logbit (pos i)
  ":doc-section @logbit
  4-Valued LOGBIT.
  ~/~/~/"
  (declare (xargs :guard (and (integerp pos)
                              (>= pos 0)
                              (@integerp i))))
  (cond
   ((integerp i) (logbit pos i))
   (t (@cons (logbit pos (@@d i)) (logbit pos (@@i i))))))

(defthm type-of-@logbit (@integerp (@logbit pos i)))

(defthm @logbit-integer
  (implies
   (integerp i)
   (equal (@logbit pos i)
	  (logbit pos i))))

;;;  @LOGREV

(defun @logrev (size i)
  ":doc-section @logrev
  4-Valued LOGREV.
  ~/~/~/"
  (declare (xargs :guard (and (integerp size)
			      (<= 0 size)
			      (@integerp i))))
  (cond
   ((integerp i) (logrev size i))
   (t (@cons (logrev size (@@d i)) (logrev size (@@i i))))))

(defthm type-of-@logrev (@integerp (@logrev i j)))

(defthm @logrev-integer
  (implies
   (integerp i)
   (equal (@logrev size i)
	  (logrev size i))))


;;;  Byte functions.

;;;  RDB

(defun @rdb (bsp i)
  ":doc-section @rdb
  4-valued RDB.
  ~/~/
  NB: We consider this a specification construct, not a hardware device.
  Thus, the byte specifier must be determinate.~/"
  (declare (xargs :guard (and (bspp bsp)
			      (@integerp i))))
  (cond
   ((integerp i) (rdb bsp i))
   (t (@cons (rdb bsp (@@d i)) (rdb bsp (@@i i))))))
  
(defthm type-of-@rdb (@integerp (@rdb bsp i)))

(defthm @rdb-integer
  (implies
   (integerp i)
   (equal (@rdb bsp i)
	  (rdb bsp i))))

;;;  WRB

(defun @wrb (i bsp j)
  ":doc-section @wrb
  4-valued WRB.
  ~/~/
  NB: We consider this a specification construct, not a hardware device.
  Thus, the byte specifier must be determinate.~/"
  (declare (xargs :guard (and (@integerp i)
			      (bspp bsp)
			      (@integerp j))))
  (@cons (wrb (@d i) bsp (@d j)) (wrb (@i i) bsp (@i j))))
  
(defthm type-of-@wrb (@integerp (@wrb i bsp j)))

(defthm @wrb-integer
  (implies
   (and (integerp i)
	(integerp j)
	(bspp bsp))
   (equal (@wrb i bsp j)
	  (wrb i bsp j)))
  :hints
  (("Goal"
    :in-theory (enable wrb))))


;;;****************************************************************************
;;;
;;;  Lemmas
;;;
;;;****************************************************************************

;;;  All @LOGOPS

(encapsulate ()

  (local
   (defthm @signed-byte-p-base-cases
     (and
      (implies
       (@signed-byte-p size i)
       (@signed-byte-p size (@lognot i)))
      (implies
       (and (@signed-byte-p size i)
	    (@signed-byte-p size j))
       (and (@signed-byte-p size (@logand i j))
	    (@signed-byte-p size (@logior i j)))))))

  (local (in-theory (disable @lognot @logand @logior)))

  (defthm @signed-byte-p-@logops
    (and
     (implies
      (@signed-byte-p size i)
      (@signed-byte-p size (@lognot i)))
     (implies
      (and (@signed-byte-p size i)
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
	   (@signed-byte-p size (@logorc2 i j)))))
    :doc ":doc-section @logops
  REWRITE: All @-logops are @SIGNED-BYTE-P when their arguments are.
  ~/~/~/"))

;;;  @LOGCAR

(defthm @bitp-@logcar
  (@bitp (@logcar i))
  :doc ":doc-section @logcar
  Rewrite: (@BITP (@LOGCAR i)).
  ~/~/~/")

;;;  @LOGAND

(defthm @unsigned-byte-p-@logand
  (implies
   (and (or (@unsigned-byte-p size i)
	    (@unsigned-byte-p size j))
	(@integerp i)
	(@integerp j))
   (@unsigned-byte-p size (@logand i j)))
  :hints
  (("Goal"
    :in-theory (enable @unsigned-byte-p @logand @integerp logandc2)))
  :doc ":doc-section @logand
  Rewrite: (@UNSIGNED-BYTE-P size (@LOGAND i j)), when either
           (@UNSIGNED-BYTE-P size i) or (@UNSIGNED-BYTE-P size j).
  ~/~/~/")

(defthm simplify-@logand
  (and
   (equal (@logand i 0) 0)
   (equal (@logand 0 i) 0))
  :doc ":doc-section @logand
  Rewrite: (@LOGAND i 0) = 0, plus commutative form.
  ~/~/~/")

;;;  @LOGIOR

(defthm @unsigned-byte-p-@logior
  (implies
   (and (@unsigned-byte-p size i)
	(@unsigned-byte-p size j))
   (@unsigned-byte-p size (@logior i j)))
  :hints
  (("Goal"
    :in-theory (enable @unsigned-byte-p @logior logandc1 logandc2)))
  :doc ":doc-section @logand
  Rewrite: (@UNSIGNED-BYTE-P size (@LOGIOR i j)), when 
           (@UNSIGNED-BYTE-P size i) and (@UNSIGNED-BYTE-P size j).
  ~/~/~/")

;;;  @BIT Functions

(defthm simplify-@bit-functions
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
       (equal (@b-orc2 x 1) (@bfix x)))
  :hints
  (("Goal"
    :in-theory (enable bitp bfix)))
  :doc ":doc-section @logops
  Rewrite: Simplification rules for all binary @B- functions including
  commutative rules, reductions with 1 explicit value, and reductions for
  identical agruments and complemented arguments.
  ~/~/~/")

;;;  @LOGHEAD

(defthm @unsigned-byte-p-@loghead
  (implies
   (and (>= size1 size)
	(>= size 0)
	(integerp size)
	(integerp size1))
  (@unsigned-byte-p size1 (@loghead size i)))
  :doc ":doc-section @loghead
  Rewrite: (@UNSIGNED-BYTE-P size1 (@LOGHEAD size i)), when size1 >= size.
  ~/~/~/")

(defthm @loghead-identity
  (implies
   (@unsigned-byte-p size i)
   (equal (@loghead size i)
	  i))
  :doc ":doc-section @loghead
  Rewrite: (@LOGHEAD size i) = i, when (@UNSIGNED-BYTE-P size i).
  ~/~/~/")

(defthm @bitp-@loghead-1
  (@bitp (@loghead 1 i))
  :hints
  (("Goal"
    :in-theory (enable @bitp @loghead)))
  :doc ":doc-section @bitp
  Rewrite: (@BITP (@LOGHEAD 1 i))
  ~/~/~/")

;;;  @LOGEXT

(defthm @signed-byte-p-@logext
  (implies
   (and (>= size1 size)
	(> size 0)
        (integerp size1)
	(integerp size))
   (@signed-byte-p size1 (@logext size i)))
  :doc ":doc-section @logext
  Rewrite: (@SIGNED-BYTE-P size1 (@LOGEXT size i)), when size1 >= size.
  ~/~/~/")

(defthm @logext-identity
  (implies
   (@signed-byte-p size i)
   (equal (@logext size i)
	  i))
  :doc ":doc-section @logext
  :Rewrite (@LOGEXT size i) = i, when (@SIGNED-BYTE-P size i).
  ~/~/~/")

;;;  @LOGSAT

(defthm @signed-byte-p-@logsat
  (implies
   (and (>= size1 size)
	(> size 0)
        (integerp size1)
	(integerp size))
   (@signed-byte-p size1 (@logsat size i)))
  :doc ":doc-section @logsat
  Rewrite: (@SIGNED-BYTE-P size1 (@LOGSAT size i)), when size1 >= size.
  ~/~/~/")

;;;  @LOGBIT

(defthm @bitp-@logbit
  (@bitp (@logbit pos i))
  :doc ":doc-section @logbit
  Rewrite: (@BITP (@LOGBIT pos i)).
  ~/~/~/")

;;;  @RDB

(defthm @unsigned-byte-p-@rdb
  (implies
   (and (>= size (bsp-size bsp))
        (>= size 0)
        (integerp size)
	(bspp bsp))
   (@unsigned-byte-p size (@rdb bsp i)))
  :hints
  (("Goal"
    :in-theory (enable @unsigned-byte-p @rdb)))
  :doc ":doc-section @rdb
  Rewrite: (@UNSIGNED-BYTE-P size (@RDB bsp i)), when size >= (BSP-SIZE bsp).
  ~/~/~/")

(defthm @bitp-@rdb-bsp-1
  (implies
   (and (@integerp i)
	(equal (bsp-size bsp) 1))
   (@bitp (@rdb bsp i)))
  :hints
  (("Goal"
    :in-theory (enable @bitp @rdb rdb @integerp))))

;;;  @WRB

(defthm @unsigned-byte-p-@wrb
  (implies
   (and (@unsigned-byte-p n j)
	(<= (+ (bsp-size bsp) (bsp-position bsp)) n)
	(@integerp i)
	(integerp n)
	(bspp bsp))
   (@unsigned-byte-p n (@wrb i bsp j))))


;;;****************************************************************************
;;;
;;;  Theories
;;;
;;;****************************************************************************

(defconst *@functions*
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

(deftheory @logops-theory
  (definition-free-theory
    (set-difference-theories (current-theory :here)
			     (current-theory '@logops)))
  :doc ":doc-section @logops
  The `minimal' theory for the book \"@logops\".
  ~/~/

  This theory contains only those lemmas meant to be exported by this book.~/")


;;;****************************************************************************
;;;
;;;  @DEFWORD
;;;
;;;  Use the DEFWORD code to define an @integer DEFWORD.
;;;
;;;****************************************************************************

(defmacro @defword (name struct &key conc-name set-conc-name keyword-updater
			 doc) 
  ":doc-section @logops
  A macro to define packed @integer data structures.
  ~/~/
  @DEFWORD is analogous to DEFWORD, except that @DEFWORD uses @RDB and @WRB
  instead of RDB and WRB.~/"
  
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

      `(ENCAPSULATE ()                  ;Only to make macroexpansion pretty.
         (DEFLABEL ,name ,@(if doc `(:DOC ,doc) nil))
         ,@accessor-definitions
         ,@updater-definitions
         ,(defword-keyword-updater
	    name keyword-updater set-conc-name field-names))))))


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
	 (when$ saturating-coercion
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
				    ,@(when$ saturating-coercion
					(list integer-saturating-coercion)))))
	  (DEFUN ,predicate (X)
	    (DECLARE (XARGS :GUARD T))
	    ,(case s/u
	       (:SIGNED `(@SIGNED-BYTE-P ,size X))
	       (:UNSIGNED `(@UNSIGNED-BYTE-P ,size X))))
	  (DEFUN ,name (I)
	    ,@(when$ doc (list doc))
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
	  ,@(when$ saturating-coercion
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
		    ,@(when$ saturating-coercion
			(list saturating-coercion))))
	  (DEFTHEORY ,theory
	    (UNION-THEORIES
	     (DEFUN-TYPE/EXEC-THEORY
	       '(,predicate ,name ,@(when$ saturating-coercion
				      (list saturating-coercion))))
	     '(,predicate-lemma ,coercion-lemma ,forward-lemma
				,type-lemma ,integer-lemma
				,@(when$ saturating-coercion
				    (list sat-lemma sat-type-lemma
					  sat-integer-lemma)))))))))
