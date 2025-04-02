; Cherry-pick the definitions of the BV functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book is intended to be a light-weight book that just brings in the
;; definitions of the BV operators, without all the theorems, so they can be
;; used in programming.

;; The definitions in this file should be kept in sync with the definitions in
;; the individual books about each function.

(include-book "slice-def")
(include-book "bvashr-def")
(include-book "getbit-def")
(include-book "bvsx-def")
(include-book "defs-bitwise")
(include-book "bvshr-def")
(include-book "bvshl-def")
(include-book "bvlt-def")
(include-book "bvplus-def")
(include-book "bvmult-def")
(include-book "defs-arith")
(include-book "leftrotate") ; todo: split out defs
(include-book "rightrotate") ; todo: split out defs
(include-book "logext-def")
;(include-book "ihs/basic-definitions" :dir :system) ;for logext
;(include-book "to-signed")
(include-book "bvcat2")

(local (include-book "sbvdiv")) ;; the verifies the guard of sbvdiv
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;divide and round toward 0
;fixme what should this do if y is 0?
(defun bvdiv (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y)
           (xargs :guard (not (equal 0 (bvchop n y)))))
  ;;drop the outer bvchop?
  (bvchop n (floor (bvchop n x) (bvchop n y))))

;fixme what should this do if y is 0?
(defund bvmod (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y)
           (xargs :guard (not (equal 0 (bvchop n y))))
           )
  (bvchop n (mod (bvchop n x) ;these two bvchops are new
                  (bvchop n y)
                  )))

;fixme make sure this is right
;this is like java's idiv
;takes and returns USBs
(defund sbvdiv (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y)
           (xargs :guard (not (equal 0 (bvchop n y)))))
  (bvchop n (truncate (logext n x) (logext n y))))

;fixme could call this sbvfloor
;this one rounds toward negative infinity
(defund sbvdivdown (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y)
           (xargs :guard (not (equal 0 (logext n y))) ;simplify!
                  ))
  (bvchop n (floor (logext n x) (logext n y))))

;fixme make sure this is what i want and that it matches what java does
(defund sbvrem (n x y)
  (declare (type integer x y)
           (type (integer 1 *) n)
           (xargs :guard (not (equal (bvchop n y) 0))))
  (bvchop n (rem (logext n x) (logext n y)))
;  (bvchop n (- x (* (truncate (logext n x) (logext n y)) y)))
  )

;; (defund sbvmod (n x y)
;;   (bvchop n (rem (logext n x) (logext n y))))

(defund sbvmoddown (n x y)
  (declare (type integer x y)
           (type (integer 1 *) n)
           (xargs :guard (not (EQUAL (LOGEXT N Y) 0))) ;rephrase in terms of bvchop?
           )
  (bvchop n (mod (logext n x) (logext n y))))

;x and y should be single bits
;guards?
;todo: make a book on this
(defun bitxnor (x y)
  (declare (type integer x y))
  (if (= (getbit 0 x) (getbit 0 y))
      1
    0))

;note that the test is a boolean, not a bit vector
(defund bvif (size test thenpart elsepart)
  (declare (xargs :guard (and (natp size)
                              (integerp thenpart)
                              (integerp elsepart))))
  (if test
      (bvchop size thenpart)
    (bvchop size elsepart)))

;floor of log (base 2) of x
(defund lg (x)
  (declare (xargs :guard (posp x)
                  :split-types t)
           (type integer x))
  (+ -1 (integer-length x)))

;just an alias for bvchop but only used for trimming (using bvchop caused loops if the rules weren't just right)
(defund trim (size i)
  (declare (type integer i)
           (type (integer 0 *) size))
  (bvchop size i))

; a totalized version of sbvdiv, where division by 0 yields 0
;logically this is equal to sbvdiv (see theorem sbvdiv-total-becomes-sbvdiv)
(defund sbvdiv-total (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (if (equal 0 (logext n y))
      (logext n 0)
    (sbvdiv n x y)))

;; TODO: Make books about the stuff below here?

;dups?

(defun xxxjoin2 (fn param args)
  (declare (xargs :guard (if (true-listp args) (cdr args) nil)
                  :mode :program))
  (if (cdr (cdr args))
      (cons fn
            (cons param
                  (cons (car args)
                        (cons (xxxjoin2 fn param (cdr args))
                              nil))))
    (cons fn (cons param args))))

;; A variant of BVAND that ANDs together n values, for n>=0.
(defmacro bvandn (size &rest args)
  (cond ((null args) `(+ -1 (expt 2 ,size)))  ; AND of no things is all ones
        ((null (cdr args)) `(bvchop ,size ,(car args)))
        (t (xxxjoin2 'bvand size args))))

;; A variant of BVOR that ORs together n values, for n>=0.
(defmacro bvorn (size &rest args)
  (cond ((null args) 0) ; OR of no things is 0
        ((null (cdr args)) `(bvchop ,size ,(car args)))
        (t (xxxjoin2 'bvor size args))))

;; A variant of BVXOR that XORs together n values, for n>=0.
(defmacro bvxorn (size &rest args)
  (cond ((null args) 0) ; XOR of no things is 0
        ((null (cdr args)) `(bvchop ,size ,(car args)))
        (t (xxxjoin2 'bvxor size args))))

;leaving these two enabled for now:

;increment by 1 (possibly 'rolling over' to 0)
(defun bvinc (size x)
  (bvplus size 1 x))

;decrement by 1 (possibly 'rolling under' to all 1's)
(defun bvdec (size x)
  (bvminus size x 1))
