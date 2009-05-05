; Goodstein function
; Contributed by John Cowles

(in-package "ACL2")

; This work was done before the introduction of the current ACL2 ordinal
; representation, so we include a book that defines the earlier
; representation:

(include-book "ordinals/e0-ordinal" :dir :system)

#||
Since Goodstein uses the COMPLETE base b representation in which
the exponents are also recursively represented in base b, it's
convenient to adopt notation similar to ACL2's notation for
ordinals less than epsilon 0. Recall that ACL2's ordinal notation
represents ordinals in base omega with the exponents recursively
also represented in base omega. (Here omega is the first infinite
ordinal.) This is more fully explained in the function Scalep
given below.

This connection with representations of ordinals and numbers
shows why Goodstein sequences must terminate. See below for an
informal argument.

||#

(defun pfix (x)
  (declare (xargs :guard t))
  (if (and (integerp x)
           (> x 0))
      x
    1))

(defun ilog-loop (nbr base pow L)

; This function implements the algorithm for computing (ilog nbr base), which
; is to start by calling (ilog-loop nbr base base 0), and then increment L as
; pow is multiplied by base until L exceeds nbr.

  (declare (xargs :guard (and (integerp nbr)
                              (> nbr 0)
                              (integerp base)
                              (> base 1)
                              (integerp pow)
                              (integerp L)
                              (>= L 0))
                  :measure (let ((nbr (pfix nbr))
                                 (L (nfix L)))
                             (if (>= L nbr)
                                 0
                               (- nbr L)))))
  (let ((nbr (pfix nbr))
        (L (nfix L)))
    (if (>= L nbr)
        L
      (if (> pow nbr)
          L
        (ilog-loop nbr base (* base pow) (+ L 1))))))

(defun ilog ( nbr base )

  "Return Log_base(nbr)."

  (declare (xargs :guard (and (integerp nbr)
                              (> nbr 0)
                              (integerp base)
                              (> base 1))))
  (ilog-loop nbr base base 0))

(defun Scalep ( x n )

  "A Scale of base n is just like an ACL2 representation
   of an ordinal less than epsilon 0 except that the base
   used to transform the representation into an actual
   ordinal is n instead of omega. Thus Scales of base n
   represent nonnegative integers. Therefore, a Scale of base
   n is either a nonnegative integer less than n or of the
   form '(x_1 ... x_j . k) where k is a nonnegative integer
   less than n, none of the x_i's are 0, each of the x_i's
   is a Scale of base n, and the x_i's are listed in
   non-increasing ordinal order."

  (declare (xargs :guard (and (integerp n)
                              (> n 1))))
  (if (consp x)
      (and (Scalep (car x) n)
           (not (equal (car x) 0))
           (Scalep (cdr x) n)
           (or (atom (cdr x))
               (not (e0-ord-< (car x) (cadr x)))))
    (and (integerp x)
         (>= x 0)
         (< x n))))

(defthm Scaleps-are-e0-ordinalps
  (implies (Scalep x n)
           (e0-ordinalp x))
  :rule-classes :forward-chaining)

(defun nbr-to-scale ( nbr base )

  "Convert nbr to a Scale with the given base."

  (declare (xargs :guard (and (integerp nbr)
                              (>= nbr 0)
                              (integerp base)
                              (> base 1))
                  :mode :program))
  (if (< nbr base)
      nbr
    (let ((ilog (ilog nbr base)))
      (cons (nbr-to-scale ilog base)
            (nbr-to-scale (- nbr (expt base ilog))
                          base)))))

(defun e0-ordinalp-to-nbr ( ord base )

  "Used to convert a Scale, with the given base, to a number."

  (declare (xargs :guard (and (integerp base)
                              (> base 1)
                              (e0-ordinalp ord))
                  :verify-guards nil))
  (if (consp ord)
      (+ (expt base (e0-ordinalp-to-nbr (car ord) base))
         (e0-ordinalp-to-nbr (cdr ord) base))
    ord))

(defun goodstein (x b)
  (declare (xargs :mode :program))
  (let* ((gn (nbr-to-scale x b))
         (y (e0-ordinalp-to-nbr gn (+ b 1))))
    (if (zp x)
        (list (list x b))
      (cons (list x b) (goodstein (- y 1) (+ b 1))))))

#||
Intuitively, the function goodstein terminates, because
           (nbr-to-scale x b) = (nbr-to-scale y (+ b 1))
                              > (nbr-to-scale (- y 1) (+ b 1)).
Here > is the "ordinal greater than".
||#
