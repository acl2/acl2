; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   http://www.russinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

#|

The file deals with the RTL primitives, as well as natp, bvecp, unknown, unknown2, reset, and reset2.

Keep this file roughly in sync with Rob's version of rtl.lisp, currently:
/u/acl2/translator/linux27/lisp/model2-c/rtl.lisp

Most of the functions introduced are disabled.

!! add god type-prescription rules!

|#

(include-book "ground-zero")
(include-book "rtlarr") ;includes the defn of bvecp
(include-book "cat-def")

;;Definitions of the ACL2 functions that are used in the
;;formalization of the RTL semantics

;leave enabled
(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))


;; 1. bit-vector constants

(defmacro n! (i n)
  (declare (ignore n)
           (xargs :guard (and (natp i)
                              (natp n)
                              (bvecp i n))))
  i)

;; 2. equality comparison

(defund log= (x y)
  (declare (xargs :guard t))
  (if (equal x y) 1 0))

(defund log<> (x y)
  (declare (xargs :guard t))
  (if (equal x y) 0 1))


;; 3. unsigned inequalities

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


;; 4. signed inequalities

;; The following function is not generated by translate-rtl, it is only needed
;; for the definitions of comp2<, comp2<=, etc.
(defund comp2 (x n)
  (declare (xargs :guard (and (rationalp x) (integerp n))))
  (if (< x (expt 2 (1- n)))
      x
    (- (- (expt 2 n) x))))

(defund comp2< (x y n)
  (declare (xargs :guard (and (rationalp x) (rationalp y) (integerp n))
                  :guard-hints (("goal" :in-theory (enable COMP2)))))
  (log< (comp2 x n) (comp2 y n)))

(defund comp2<= (x y n)
  (declare (xargs :guard (and (rationalp x) (rationalp y) (integerp n))
                  :guard-hints (("goal" :in-theory (enable COMP2)))))
  (log<= (comp2 x n) (comp2 y n)))

(defund comp2> (x y n)
  (declare (xargs :guard (and (rationalp x) (rationalp y) (integerp n))
                  :guard-hints (("goal" :in-theory (enable COMP2)))))
  (log> (comp2 x n) (comp2 y n)))

(defund comp2>= (x y n)
  (declare (xargs :guard (and (rationalp x) (rationalp y) (integerp n))
                  :guard-hints (("goal" :in-theory (enable COMP2)))))
  (log>= (comp2 x n) (comp2 y n)))


;; 5. unary logical operations

(defund logand1 (x n)
  (declare (xargs :guard (integerp n)))
  (log= x (1- (expt 2 n))))

(defund logior1 (x)
  (declare (xargs :guard t))
  (if (equal x 0) 0 1))

(defund logxor1 (src)
  (declare (xargs :guard (integerp src)))
  (if (oddp (logcount src)) 1 0))


;; 6. bit-vector shifting operations

;; The following function will not be seen in the output from translate-rtl, it
;; is only provided here to define shft.
(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

#|
(defun shft (x s l)
  (mod (fl (* (expt 2 s) x)) (expt 2 l)))
|#

;; The following function will not be seen in the output from translate-rtl, it
;; is only provided here to define lshft and rshft.
(defund shft (x s l)
  (declare (xargs :guard (and (integerp s) (rationalp x))))
  (mod (fl (* (expt 2 s) x)) (expt 2 (nfix l))))

(defmacro lshft (x s l)
  `(shft ,x ,s ,l))

(defmacro rshft (x s l)
  `(shft ,x (- ,s) ,l))


;; 7. concatenation operations

;drop? and add cat?
(defund ocat (x y n)
  (declare (xargs :guard t))
  (+ (* (expt 2 (nfix n)) (nfix x)) (nfix y)))

#|
(defund omulcat (l n x)
  (declare (xargs :guard t))
  (if (and (integerp n) (> n 0))
      (ocat (omulcat l (1- n) x)
	   x
	   l)
    0))
|#

(defund mulcat (l n x)

; We introduce mbe not because we want particularly fast execution, but because
; the existing logic definition does not satisfy the guard of cat, which can't
; be changed because of the guard of bits.

  (declare (xargs :guard (and (integerp l)
                              (< 0 l)
                              (acl2-numberp n)
                              (natp x))
                  :verify-guards nil))
  (mbe :logic (if (and (integerp n) (> n 0))
                  (cat (mulcat l (1- n) x)
                       (* l (1- n))
                       x
                       l)
                0)
       :exec  (cond
               ((eql n 1)
                (bits x (1- l) 0))
               ((and (integerp n) (> n 0))
                (cat (mulcat l (1- n) x)
                     (* l (1- n))
                     x
                     l))
               (t 0))))


;; 8. bit-vector access and update

#| old versions:
(defun bits (x i j)
  (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))

(defun bits (x i j)
  (if (or (not (integerp i))
          (not (integerp j)))
      0
  (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j)))))

(defund bits (x i j)
  (declare (xargs :guard (rationalp x)))
  (if (or (not (integerp i))
          (not (integerp j)))
      0
    (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j)))))

(defun bitn (x n)
  (if (logbitp n x) 1 0))

(defund bitn (x n)
    (declare (xargs :guard (rationalp x)))
  (bits x n n))

|#

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))
                  :verify-guards nil))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

;setbits has a new parameter, w, indicating the size of the expression returned
;Note: when j is 0, there is not lower part of x, but we have cat-with-n-0 to handle this case.
(defund setbits (x w i j y)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp i)
                              (integerp j)
                              (<= 0 j)
                              (<= j i)
                              (integerp w)
                              (< i w))
                  :verify-guards nil))
  (mbe :logic (cat (bits x (1- w) (1+ i))
                   (+ -1 w (- i))
                   (cat (bits y (+ i (- j)) 0)
                        (+ 1 i (- j))
                        (bits x (1- j) 0)
                        j)
                   (1+ i))
       :exec  (cond ((int= j 0)
                     (cond ((int= (1+ i) w)
                            (bits y (+ i (- j)) 0))
                           (t
                            (cat (bits x (1- w) (1+ i))
                                 (+ -1 w (- i))
                                 (bits y (+ i (- j)) 0)
                                 (1+ i)))))
                    ((int= (1+ i) w)
                     (cat (bits y (+ i (- j)) 0)
                          (+ 1 i (- j))
                          (bits x (1- j) 0)
                          j))
                    (t
                     (cat (bits x (1- w) (1+ i))
                          (+ -1 w (- i))
                          (cat (bits y (+ i (- j)) 0)
                               (+ 1 i (- j))
                               (bits x (1- j) 0)
                               j)
                          (1+ i))))))

(defund setbitn (x w n y)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (<= 0 n)
                              (integerp w)
                              (< n w))
                  :verify-guards nil))
  (setbits x w n n y))


;; 9. bitwise operations

;; logand, logior, logxor are predefined ACL2 functions

#| old version
(defun lnot (x n)
  (1- (- (expt 2 n) x)))
|#

(defund lnot (x n)
  (declare (xargs :guard (and (natp x)
                              (integerp n)
                              (< 0 n))
                  :verify-guards nil))
  (if (natp n)
      (+ -1 (expt 2 n) (- (bits x (1- n) 0)))
    0))


;; 10. array access and update

;; aref1, aref2, aset1, aset2 are predefined ACL2 functions

;; actually, we now generate ag and as, which are defined in rtlarr.lisp
;; in the rtl library.




;; 11. arithmetic operations

(defmacro mod+ (x y n)
  `(bits (+ ,x ,y) (1- ,n) 0))

(defmacro mod* (x y n)
  `(bits (* ,x ,y) (1- ,n) 0))

#|
Note: We recently changed mod-.  This definition is a little weird, since it may rely on the value of (bits x
i j) when x is negative.  However, bits behaves properly in this case.  In fact, Eric proved this theorem
about the old defintion of mod-:

(thm
 (implies (and (bvecp x n)
	       (bvecp y n)
	       (natp n)
	       )
	  (equal (mod- x y n)
		 (bits (- x y) (1- n) 0)))
	:hints (("Goal" :in-theory (enable  mod- comp2-inv bits bvecp)))
)

We believe that mod- is only well-defined when x and y are bvecps of length n, so the change shouldn't affect
any behavior we care about.

Typically when we see (mod- x y n), we will know (<= y x); in such cases, the rule BITS-DROP-FROM-MINUS can
get rid of the bits call.
|#

(defmacro mod- (x y n)
  `(bits (- ,x ,y) (1- ,n) 0))


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


;; NOTE -- the following definition of decode is "flawed". We still need to add
;; assumptions to "allow" this definition to be used.

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

;; floor, rem are predefined ACL2 functions


;; 12. evaluation control operators

(defmacro bind (v x y)
  `(let ((,v ,x)) ,y))

(defun if1 (x y z)
  (declare (xargs :guard (integerp x)))
  (if (eql x 0) z y))

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

(defthm bvecp-if1
  (equal (bvecp (if1 x y z) n)
         (if1 x (bvecp y n) (bvecp z n))))

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


;; 13. extra operators

(defun natp1 (x)
  (declare (xargs :guard t))
  (if (and (integerp x)
           (<= 0 x))
      1
    0))


;land0


(defund binary-land0 (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :verify-guards nil))
  (logand (bits x (1- n) 0)
          (bits y (1- n) 0)))

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defmacro land0 (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(land0 x y n) -- the base case
         `(binary-land0 ,@x))
        (t
         `(binary-land0 ,(car x)
                       (land0 ,@(cdr x))
                       ,(car (last x))))))

;Allows things like (in-theory (disable land0)) to refer to binary-land0.
(add-macro-alias land0 binary-land0)

;;lior0

(defund all-ones (n)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (if (zp n)
      0 ;degenerate case
    (1- (expt 2 n))))


(defund binary-lior0 (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :verify-guards nil))
  (logior (bits x (1- n) 0)
          (bits y (1- n) 0)))

(defmacro lior0 (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(lior0 x y n) -- the base case
         `(binary-lior0 ,@x))
        (t
         `(binary-lior0 ,(car x)
                       (lior0 ,@(cdr x))
                       ,(car (last x))))))


;Allows things like (in-theory (disable lior0)) to refer to binary-lior0.
(add-macro-alias lior0 binary-lior0)

;;lxor0

(defund binary-lxor0 (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :verify-guards nil))
  (logxor (bits x (1- n) 0)
          (bits y (1- n) 0)))

(defmacro lxor0 (&rest x)
  (declare (xargs :guard (consp x)))
  (cond ((endp (cdddr x)) ;(lxor0 x y n) -- the base case
         `(binary-lxor0 ,@x))
        (t
         `(binary-lxor0 ,(car x)
                       (lxor0 ,@(cdr x))
                       ,(car (last x))))))

;Allows things like (in-theory (disable lxor0)) to refer to binary-lxor0.
(add-macro-alias lxor0 binary-lxor0)




;;4 functions that occur in the translated RTL, representing bit vectors of
;;determined length but undetermined value:

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

(encapsulate
 ((reset2 (key size) t))
 (local (defun reset2 (key size) (declare (ignore key size)) nil))

;do we need rule-classes on this thm?
 (defthm bv-arrp-reset2
   (bv-arrp (reset2 key size) size)
   :hints
   (("goal" :in-theory (enable bv-arrp)))
   ))

(encapsulate
 ((unknown2 (key size n) t))
 (local (defun unknown2 (key size n) (declare (ignore key size n)) nil))

;do we need rule-classes on this thm?
 (defthm bv-arrp-unknown2
   (bv-arrp (unknown2 key size n) size)
   :hints
   (("goal" :in-theory (enable bv-arrp)))
   ))




