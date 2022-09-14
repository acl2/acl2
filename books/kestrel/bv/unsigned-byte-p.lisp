; A lightweight book about the built-in function unsigned-byte-p.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; For unsigned-byte-p-forward and unsigned-byte-p-from-bounds,
; see the copyrights on the ihs and coi libraries.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))

(in-theory (disable unsigned-byte-p))

;; Note that unsigned-byte-p-forward-to-nonnegative-integerp is built into
;; ACL2, so we don't need to forward-chain to natp from unsigned-byte-p.

(defthm unsigned-byte-p-forward-to-<-of-expt
  (implies (unsigned-byte-p bits x)
           (< x (expt 2 bits)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;; I hope that bitp-compound-recognizer will then fire.
(defthm unsigned-byte-p-1-forward-to-bitp
  (implies (unsigned-byte-p 1 x)
           (bitp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;restrict to when size is not a quoted constant?
(defthm unsigned-byte-p-forward-to-natp-arg1
  (implies (unsigned-byte-p bits x)
           ;; This conjunction worked better than NATP:
           (and (integerp bits)
                (<= 0 bits)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm unsigned-byte-p-of-0-arg1
  (equal (unsigned-byte-p 0 x)
         (equal 0 x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-0-arg2
  (equal (unsigned-byte-p size 0)
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-1
  (equal (unsigned-byte-p n 1)
         (posp n))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm usb1-cases
  (implies (unsigned-byte-p 1 x)
           (or (equal 0 x)
               (equal 1 x)))
  :rule-classes nil)

(defthm unsigned-byte-p-from-bound
  (implies (and ;(syntaxp (quotep n))
                (< x free)
                (<= free (expt 2 n))
                (integerp x)
                (<= 0 x)
                (integerp n)
                (<= 0 n))
           (unsigned-byte-p n x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;rename?
(defthm ubp-longer-better
  (implies (and (unsigned-byte-p free x)
                (<= free n)
                (integerp n))
           (equal (unsigned-byte-p n x)
                  (<= 0 n)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p) nil))))

;should be cheap since FREE is a free var
(defthm integerp-from-unsigned-byte-p-size-param
  (implies (unsigned-byte-p size free) ;note that it's the size param
           (integerp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;should be cheap since FREE is a free var
(defthm acl2-numberp-from-unsigned-byte-p-size-param
  (implies (unsigned-byte-p size free)
           (acl2-numberp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-*
  (implies (and (unsigned-byte-p xsize x)
                (unsigned-byte-p ysize y))
           (unsigned-byte-p (+ xsize ysize) (* x y)))
  :hints (("Goal"

           :in-theory (e/d (unsigned-byte-p expt-of-+)
                           ()))))

(defthm unsigned-byte-p-of-*-gen
  (implies (and (unsigned-byte-p xsize x)
                (unsigned-byte-p ysize y)
                (<= (+ xsize ysize) size)
                (natp size))
           (unsigned-byte-p size (* x y)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-*)
           :in-theory (disable unsigned-byte-p-of-*
                               ubp-longer-better))))

(defthmd unsigned-byte-p-when-n-is-not-natp
  (implies (not (natp n))
           (not (unsigned-byte-p n x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;gen the 2?
(defthm unsigned-byte-p-of-times-2
  (implies (and (syntaxp (not (quotep x))) ;defeats ACL2's matching
                (natp x))
           (equal (unsigned-byte-p n (* 2 x))
                  (if (or (not (integerp n)) (< n 0))
                      nil
                    (if (equal 0 n)
                        (equal 0 x)
                      (unsigned-byte-p (+ -1 n) x)))))
  :hints (("Goal":in-theory (enable expt-of-+ unsigned-byte-p unsigned-byte-p-when-n-is-not-natp))))

(defthm size-non-negative-when-unsigned-byte-p-free
  (implies (unsigned-byte-p size free)
           (not (< size 0)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm usb-of-mask
  (implies (natp size)
           (unsigned-byte-p size (+ -1 (expt 2 size))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm usb-of-mask-gen
  (implies (and (<= size size2)
                (natp size)
                (integerp size2))
           (unsigned-byte-p size2 (+ -1 (expt 2 size))))
  :hints (("Goal" :in-theory (e/d (zip)
                                  (usb-of-mask size-non-negative-when-unsigned-byte-p-free))
           :use (:instance usb-of-mask))))

(defthm natp-when-unsigned-byte-p
  (implies (unsigned-byte-p free x)
           (natp x)))

(defthm booleanp-of-unsigned-byte-p
  (booleanp (unsigned-byte-p size x)))

(defthm unsigned-byte-p-of-*-of-expt
  (implies (and (<= m n)
                (integerp x)
                (natp m)
                (integerp n))
           (equal (unsigned-byte-p n (* (expt 2 m) x))
                  (unsigned-byte-p (- n m) x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p expt-of-+))))

(defthm unsigned-byte-p-of-*-of-expt-alt
  (implies (and (<= m n)
                (integerp x)
                (natp m)
                (integerp n))
           (equal (unsigned-byte-p n (* x (expt 2 m)))
                  (unsigned-byte-p (- n m) x)))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-*-of-expt)
           :in-theory (disable unsigned-byte-p-of-*-of-expt))))

;more like this?
(defthm acl2-numberp-when-unsigned-byte-p
  (implies (unsigned-byte-p free x) ;free var
           (acl2-numberp x)))

(defthm usb-0-1
  (implies (and (unsigned-byte-p 1 x)
                (not (equal 1 x)))
           (equal x 0))
  :rule-classes nil)

(defthmd unsigned-byte-p-of-+-strong
  (implies (and (syntaxp (quotep size)) ;drop?
                (integerp x)
                (integerp y))
           (equal (unsigned-byte-p size (+ x y))
                  (and (< (+ x y) (expt 2 size))
                       (<= 0 (+ x y))
                       (natp size))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-+-of-constant-strong
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)))
                (integerp x)
                (integerp k)
                )
           (equal (unsigned-byte-p n (+ k x))
                  (and (< x (- (expt 2 n) k))
                       (<= (- k) x)
                       (natp n))))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-+-strong (x k) (size n) (y x)))))

;rename
(defthm unsigned-byte-p-when-size-is-negative-limited
  (implies (< size 0)
           (not (unsigned-byte-p size x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm natp-when-unsigned-byte-p-size-arg
  (implies (unsigned-byte-p x free)
           (equal (natp x)
                  t))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-when-<=-cheap
  (implies (and (<= I free) ; i is bounded
                (syntaxp (quotep free))
                (syntaxp (quotep size))
                (< free (expt 2 size)) ;gets computed
                (natp i) ; i is a natural
                (natp size))
           (unsigned-byte-p size i))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;; The BV library doesn't use bitp, so we rewrite it using this rule to our
;; normal form:
(defthm bitp-becomes-unsigned-byte-p
  (equal (bitp x)
         (unsigned-byte-p 1 x)))

;;there is a version of this in books/coi/bags/eric-meta.lisp (but in the bag:: package)
(defthm unsigned-byte-p-from-bounds
  (implies (and (syntaxp (quotep bits))
                (< x (expt 2 bits))
                (integerp x)
                (<= 0 x)
                (integerp bits)
                (<= 0 bits))
           (unsigned-byte-p bits x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm usb-plus-from-bounds
  (implies (and (< x (- (expt 2 n) k))
                (natp x)
                (natp k)
                (natp n))
           (unsigned-byte-p n (+ k x)))
  :hints (("Goal" :use (:instance unsigned-byte-p-from-bounds
                                  (bits n)
                                  (x (+ k x)))
           :in-theory (enable ;unsigned-byte-p-from-bounds
                              ))))

;rename
(defthm unsigned-byte-p-false-when-not-longer
  (implies (and (not (unsigned-byte-p free x))
                (<= size free)
                (natp free))
           (not (unsigned-byte-p size x))))



(defthm unsigned-byte-p-of-if
  (equal (unsigned-byte-p size (if test x y))
         (if test
             (unsigned-byte-p size x)
           (unsigned-byte-p size y))))

;rename
(defthm bound-when-usb
  (implies (and (unsigned-byte-p n x)
                (<= (+ -1 (expt 2 n)) k)
                (integerp k))
           (not (< k x))))

(defthmd unsigned-byte-p-of-+-arg1-a
  (implies (and (unsigned-byte-p size1 x)
                (natp size2))
           (unsigned-byte-p (+ size1 size2) x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthmd unsigned-byte-p-of-+-arg1-b
  (implies (and (unsigned-byte-p size2 x)
                (natp size1))
           (unsigned-byte-p (+ size1 size2) x))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-of-+-of--1
  (implies (unsigned-byte-p bits x)
           (equal (unsigned-byte-p bits (+ -1 x))
                  (not (equal 0 x))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))
