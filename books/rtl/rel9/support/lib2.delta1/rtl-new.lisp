; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

(set-enforce-redundancy t)

(local (include-book "rtl-new-proofs"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))
;(set-inhibit-warnings) ; restore theory warnings (optional)


;;This book contains definitions of the ACL2 functions that are used in the
;;formalization of RTL semantics.



;;Bit-vector access:

(defund fl (x)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bits_alt (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn_alt (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))))
  (mbe :logic (bits_alt x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))


;;CAT (concatenation):

(defund binary-cat_alt (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits_alt x (1- m) 0))
         (bits_alt y (1- n) 0))
    0))

(defun formal-+ (x y)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

;;X is a list of alternating data values and sizes.  CAT-SIZE returns the
;;formal sum of the sizes.  X must contain at least 1 data/size pair, but we do
;;not need to specify this in the guard, and leaving it out of that guard
;;simplifies the guard proof.

(defun cat-size (x)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard (and (true-listp x) (evenp (length x)))))
  (if (endp (cddr x))
      (cadr x)
    (formal-+ (cadr x)
	      (cat-size (cddr x)))))

(defmacro cat_alt (&rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(bits_alt ,(car x) ,(formal-+ -1 (cadr x)) 0))
        ((endp (cddddr x))
         `(binary-cat_alt ,@x))
        (t
         `(binary-cat_alt ,(car x)
                      ,(cadr x)
                      (cat_alt ,@(cddr x))
                      ,(cat-size (cddr x))))))

;Allows things like (in-theory (disable cat)) to refer to binary-cat_alt.
(add-macro-alias cat_alt binary-cat_alt)

(defund mulcat_alt (l n x)

; We introduce mbe not because we want particularly fast execution, but because
; the existing logic definition does not satisfy the guard of cat, which can't
; be changed because of the guard of bits_alt.

  (declare (xargs :guard (and (integerp l)
                              (< 0 l)
                              (acl2-numberp n)
                              (natp x))))
  (mbe :logic (if (and (integerp n) (> n 0))
                  (cat_alt (mulcat_alt l (1- n) x)
                       (* l (1- n))
                       x
                       l)
                0)
       :exec  (cond ((eql n 1)
                     (bits_alt x (1- l) 0))
                    ((and (integerp n) (> n 0))
                     (cat_alt (mulcat_alt l (1- n) x)
                          (* l (1- n))
                          x
                          l))
                    (t 0))))

;;LNOT (bitwise complement):

(defund lnot_alt (x n)
  (declare (xargs :guard (and (natp x)
                              (integerp n)
                              (< 0 n))))
  (if (natp n)
      (+ -1 (expt 2 n) (- (bits_alt x (1- n) 0)))
    0))

;LAND (bitwise and):

(defund binary-land_alt (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :measure (nfix n)))
  (mbe :logic
       (cond ((zp n)
              0)
             ((equal n 1)
              (if (and (equal (bitn_alt x 0) 1)
                       (equal (bitn_alt y 0) 1))
                  1
                0))
             (t (+ (* 2 (binary-land_alt (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                   (binary-land_alt (mod x 2) (mod y 2) 1))))
       :exec ; (land_alt0 x y n)
       (logand (bits_alt x (1- n) 0)
               (bits_alt y (1- n) 0))))



(defmacro land_alt (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(land_alt x y n) -- the base case
         `(binary-land_alt ,@x))
        (t
         `(binary-land_alt ,(car x)
                       (land_alt ,@(cdr x))
                       ,(car (last x))))))

;Allows things like (in-theory (disable land_alt)) to refer to binary-land_alt.
(add-macro-alias land_alt binary-land_alt)

;;LIOR_ALT (bitwise inclusive or):

(defund binary-lior_alt (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :measure (nfix n)))

  (mbe :logic
       (cond ((zp n)
              0)
             ((equal n 1)
              (if (or (equal (bitn_alt x 0) 1)
                      (equal (bitn_alt y 0) 1))
                  1
                0))
             (t (+ (* 2 (binary-lior_alt (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                   (binary-lior_alt (mod x 2) (mod y 2) 1))))
       :exec ; (lior_alt0 x y n)
       (logior (bits_alt x (1- n) 0)
               (bits_alt y (1- n) 0))))


(defmacro lior_alt (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(lior_alt x y n) -- the base case
         `(binary-lior_alt ,@x))
        (t
         `(binary-lior_alt ,(car x)
                       (lior_alt ,@(cdr x))
                       ,(car (last x))))))

;Allows things like (in-theory (disable lior_alt)) to refer to binary-lior_alt:
(add-macro-alias lior_alt binary-lior_alt)

;;LXOR_ALT (bitwise exclusive or):

(defund binary-lxor_alt (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :measure (nfix n)))
  (mbe :logic
       (cond ((zp n)
              0)
             ((equal n 1)
              (if (iff (equal (bitn_alt x 0) 1)
                       (equal (bitn_alt y 0) 1))
                  0
                1))
             (t (+ (* 2 (binary-lxor_alt (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                   (binary-lxor_alt (mod x 2) (mod y 2) 1))))
       :exec ; (lxor_alt0 x y n)
       (logxor (bits_alt x (1- n) 0)
               (bits_alt y (1- n) 0))))



(defmacro lxor_alt (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(lxor_alt x y n) -- the base case
         `(binary-lxor_alt ,@x))
        (t
         `(binary-lxor_alt ,(car x)
                       (lxor_alt ,@(cdr x))
                       ,(car (last x))))))

;Allows things like (in-theory (disable lxor_alt)) to refer to binary-lxor_alt.
(add-macro-alias lxor_alt binary-lxor_alt)


;;Bit-vector update:

; We have decided to allow setbits_alt to open up in terms of cat.  So, we leave it
; enabled.

(defun setbits_alt (x w i j y)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp i)
                              (integerp j)
                              (<= 0 j)
                              (<= j i)
                              (integerp w)
                              (< i w))))
  (mbe :logic (cat_alt (bits_alt x (1- w) (1+ i))
                   (+ -1 w (- i))
                   (cat_alt (bits_alt y (+ i (- j)) 0)
                        (+ 1 i (- j))
                        (bits_alt x (1- j) 0)
                        j)
                   (1+ i))
       :exec  (cond ((int= j 0)
                     (cond ((int= (1+ i) w)
                            (bits_alt y (+ i (- j)) 0))
                           (t
                            (cat_alt (bits_alt x (1- w) (1+ i))
                                 (+ -1 w (- i))
                                 (bits_alt y (+ i (- j)) 0)
                                 (1+ i)))))
                    ((int= (1+ i) w)
                     (cat_alt (bits_alt y (+ i (- j)) 0)
                          (+ 1 i (- j))
                          (bits_alt x (1- j) 0)
                          j))
                    (t
                     (cat_alt (bits_alt x (1- w) (1+ i))
                          (+ -1 w (- i))
                          (cat_alt (bits_alt y (+ i (- j)) 0)
                               (+ 1 i (- j))
                               (bits_alt x (1- j) 0)
                               j)
                          (1+ i))))))

(defun setbitn_alt (x w n y)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (<= 0 n)
                              (integerp w)
                              (< n w))))
  (setbits_alt x w n n y))


;;Equality comparison:

;Leaving this enabled caused a stack overflow in simple-loops when building one of our models.
;However, we have very few lemmas about log=, so you may want to enable this for your proofs.
(defund log= (x y)
  (declare (xargs :guard t))
  (if (equal x y) 1 0))

(defund log<> (x y)
  (declare (xargs :guard t))
  (if (equal x y) 0 1))


;;Unsigned inequalities:

(defund log< (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (< x y) 1 0))

(defund log<= (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (<= x y) 1 0))

(defund log> (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (> x y) 1 0))

(defund log>= (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (>= x y) 1 0))


;;Signed inequalities:

(defund comp2 (x n)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard (and (rationalp x) (integerp n))))
  (if (< x (expt 2 (1- n)))
      x
    (- (- (expt 2 n) x))))

(defund comp2< (x y n)
  (declare (xargs :guard (and (rationalp x) (rationalp y) (integerp n))))
  (log< (comp2 x n) (comp2 y n)))

(defund comp2<= (x y n)
  (declare (xargs :guard (and (rationalp x) (rationalp y) (integerp n))))
  (log<= (comp2 x n) (comp2 y n)))

(defund comp2> (x y n)
  (declare (xargs :guard (and (rationalp x) (rationalp y) (integerp n))))
  (log> (comp2 x n) (comp2 y n)))

(defund comp2>= (x y n)
  (declare (xargs :guard (and (rationalp x) (rationalp y) (integerp n))))
  (log>= (comp2 x n) (comp2 y n)))


;;Unary logical operations:

(defund logand1 (x n)
  (declare (xargs :guard (integerp n)))
  (log= x (1- (expt 2 n))))

(defund logior1 (x)
  (declare (xargs :guard t))
  (if (equal x 0) 0 1))

(defund logxor1 (src)
  (declare (xargs :guard (integerp src)))
  (if (oddp (logcount src)) 1 0))


;;Shifting operations:

(defund shft (x s l)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard (and (integerp s) (rationalp x))))
  (mod (fl (* (expt 2 s) x)) (expt 2 (nfix l))))

(defmacro lshft (x s l)
  `(shft ,x ,s ,l))

(defmacro rshft (x s l)
  `(shft ,x (- ,s) ,l))


;;Arithmetic operations

(defmacro mod+_alt (x y n)
  `(bits_alt (+ ,x ,y) (1- ,n) 0))

(defmacro mod*_alt (x y n)
  `(bits_alt (* ,x ,y) (1- ,n) 0))

#|
Note: We recently changed mod-.  This definition is a little weird, since it may rely on the value of (bits_alt x
i j) when x is negative.  However, bits_alt behaves properly in this case.  In fact, Eric proved this theorem
about the old defintion of mod-:

(thm
 (implies (and (bvecp x n)
	       (bvecp y n)
	       (natp n)
	       )
	  (equal (mod- x y n)
		 (bits_alt (- x y) (1- n) 0)))
	:hints (("Goal" :in-theory (enable  mod- comp2-inv bits_alt bvecp)))
)

We believe that mod- is only well-defined when x and y are bvecps of length n, so the change shouldn't affect
any behavior we care about.

Typically when we see (mod- x y n), we will know (<= y x); in such cases, the rule BITS_ALT-DROP-FROM-MINUS can
get rid of the bits_alt call.
|#

(defmacro mod-_alt (x y n)
  `(bits_alt (- ,x ,y) (1- ,n) 0))


#| Old definition of mod- :

;; the following function is not generated in the translate-rtl output. It is
;; only needed to define 'mod-
(defund comp2-inv (x n)
  (declare (xargs :guard (and (rationalp x)
                              (integerp n))))
  (if (< x 0)
      (+ x (expt 2 n))
    x))

(defund mod- (x y n)
  (declare (xargs :guard (and (rationalp x)
                              (rationalp y)
                              (integerp n))))
  (comp2-inv (- x y) n))
|#


;; NOTE -- the following definition of decode is "flawed". We still
;; need to add assumptions to "allow" this definition to be used.

(defund decode (x n)
  (declare (xargs :guard (rationalp n)))
  (if (and (natp x) (< x n))
      (ash 1 x)
    0))

(defund encode (x n)
    (declare (xargs :guard (and (acl2-numberp x)
                                (integerp n)
                                (<= 0 n))))
  (if (zp n)
      0
    (if (= x (ash 1 n))
        n
      (encode x (1- n)))))


;;Evaluation control operators

(defmacro bind (v x y)
  `(let ((,v ,x)) ,y))

(defun if1 (x y z)
  (declare (xargs :guard (integerp x)))
  (if (eql x 0) z y))

;BOZO Where in lib/ should these go?

(defthm if1-0
  (equal (if1 0 y z)
         z))

(defthm if1-non-0
  (implies (not (equal x 0))
           (equal (if1 x y z)
                  y)))

(defthm if1-x-x
  (equal (if1 tst x x)
         x))

(defun cond1-macro (clauses)
  ;; Based on cond-macro.
  (declare (xargs :guard (cond-clausesp clauses)))
  (if (consp clauses)
      (if (and (eq (car (car clauses)) t)
               (eq (cdr clauses) nil))
          (if (cdr (car clauses))
              (car (cdr (car clauses)))
            (car (car clauses)))
        (list 'if1 (car (car clauses))
              (if (cdr (car clauses))
                  (car (cdr (car clauses)))
                (car (car clauses)))
              (cond1-macro (cdr clauses))))
    0))

(defmacro cond1 (&rest clauses)
  (declare (xargs :guard (cond-clausesp clauses)))
  (cond1-macro clauses))


;;Natural number recognizer

(defund natp1 (x)
  (declare (xargs :guard t))
  (if (and (integerp x)
           (<= 0 x))
      1
    0))

;;Functions representing bit vectors of determined length but undetermined value:

(defund bvecp (x k)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defthm bvecp-if1
  (equal (bvecp (if1 x y z) n)
         (if1 x (bvecp y n) (bvecp z n))))

; The following are analogous to mk-bvarr etc. in rtlarr.lisp.

(defun mk-bvec (r k)
  (declare (xargs :guard (integerp k)))
  (if (bvecp r k) r 0))

(defthm mk-bvec-is-bvecp
  (bvecp (mk-bvec r k) k))

(defthm mk-bvec-identity
  (implies (bvecp r k)
           (equal (mk-bvec r k) r)))

(defmacro n! (i n)
  (declare (ignore n)
           (xargs :guard (and (natp i)
                              (natp n)
                              (bvecp i n))))
  i)

(encapsulate
 ((reset (key size) t))
 (local (defun reset (key size) (declare (ignore key size)) 0))
 (defthm bvecp-reset (bvecp (reset key size) size)
   :hints (("Goal" :in-theory (enable bvecp expt)))
   :rule-classes
   (:rewrite
    (:forward-chaining :trigger-terms ((reset key size)))
    (:type-prescription :corollary
                        (and (integerp (reset key size))
                             (>= (reset key size) 0))
                        :hints
                        (("Goal" :in-theory '(implies bvecp)))))))

(encapsulate
 ((unknown (key size n) t))
 (local (defun unknown (key size n) (declare (ignore key size n)) 0))
 (defthm bvecp-unknown (bvecp (unknown key size n) size)
   :hints (("Goal" :in-theory (enable bvecp expt)))
   :rule-classes
   (:rewrite
    (:forward-chaining :trigger-terms ((unknown key size n)))
    (:type-prescription :corollary
                        (and (integerp (unknown key size n))
                             (>= (unknown key size n) 0))
                        :hints
                        (("Goal" :in-theory '(implies bvecp)))))))


; Finally, we include bvecp (and, occasionally, related) lemmas for several
; functions that are disabled.  These are not included elsewhere, presumably
; because the functions will generally be enabled (hence blown away) by the
; user.

(defthm shft-bvecp
  (implies (and (<= n k)
		(case-split (integerp k)))
	   (bvecp (shft x s n) k)))

(defthm logand1-bvecp
  (bvecp (logand1 x y) 1))

(defthm logior1-bvecp
  (bvecp (logior1 x) 1))

(defthm logxor1-bvecp
  (bvecp (logxor1 x) 1))

(defthm log<-bvecp
  (bvecp (log< x y) 1))

(defthm log<-nonnegative-integer-type
  (and (integerp (log< x y))
       (<= 0 (log< x y)))
  :rule-classes (:type-prescription))

;;This rule is no better than log<-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log<)))

(defthm log<=-bvecp
  (bvecp (log<= x y) 1))

(defthm log<=-nonnegative-integer-type
  (and (integerp (log<= x y))
       (<= 0 (log<= x y)))
  :rule-classes (:type-prescription))

;;This rule is no better than log<=-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log<=)))

(defthm log>-bvecp
  (bvecp (log> x y) 1))

(defthm log>-nonnegative-integer-type
  (and (integerp (log> x y))
       (<= 0 (log> x y)))
  :rule-classes (:type-prescription))

;;This rule is no better than log>-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log>)))

(defthm log>=-bvecp
  (bvecp (log>= x y) 1))

(defthm log>=-nonnegative-integer-type
  (and (integerp (log>= x y))
       (<= 0 (log>= x y)))
  :rule-classes (:type-prescription))

;;This rule is no better than log>=-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log>=)))

(defthm log=-bvecp
  (bvecp (log= x y) 1))

(defthm log=-nonnegative-integer-type
  (and (integerp (log= x y))
       (<= 0 (log= x y)))
  :rule-classes (:type-prescription))

(defthm log=-commutative
       (equal (log= x y)
              (log= y x))
       :hints (("Goal" :in-theory (enable log=))))

;;This rule is no better than log=-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log=)))

(defthm log<>-bvecp
  (bvecp (log<> x y) 1))

(defthm log<>-nonnegative-integer-type
  (and (integerp (log<> x y))
       (<= 0 (log<> x y)))
  :rule-classes (:type-prescription))

(defthm log<>-commutative
  (equal (log<> x y)
	 (log<> y x)))

;;This rule is no better than log<>-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription log<>)))

;;The definitions of these functions are best disabled:

(in-theory (disable aref1))
(in-theory (disable aset1))
(in-theory (disable aref2))
(in-theory (disable aset2))
(in-theory (disable floor))
(in-theory (disable truncate))
(in-theory (disable mod))
(in-theory (disable rem))
(in-theory (disable expt))
(in-theory (disable ash))
(in-theory (disable acl2::binary-logand))
(in-theory (disable acl2::binary-logior))
(in-theory (disable acl2::binary-logxor))
(in-theory (disable acl2::binary-logeqv))
(in-theory (disable logorc1))
(in-theory (disable lognot))
(in-theory (disable mk-bvec))
(in-theory (disable if1))

