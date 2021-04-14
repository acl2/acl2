; A recognizer for a power of 2
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "integer-length"))
(local (include-book "expt"))
(local (include-book "expt2"))
(local (include-book "times"))
(local (include-book "floor"))

;dup
;define in terms of lg?
(defund power-of-2p (x)
  (declare (xargs :guard t))
  (and (natp x) ;otherwise, this would count 1/2 but not 1/4
       (= x (expt 2 (+ -1 (integer-length x))))))

;; (defthm integerp-when-power-of-2p
;;   (implies (power-of-2p x)
;;            (integerp x))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (enable power-of-2p))))

(defthm power-of-2p-forward-to-natp
  (implies (power-of-2p x)
           (natp x))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable power-of-2p))))

;; (defthm natp-when-power-of-2p
;;   (implies (power-of-2p x)
;;            (natp x))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (enable power-of-2p))))

(defthm power-of-2p-of-expt-2
  (implies (integerp n)
           (equal (power-of-2p (expt 2 n))
                  (<= 0 n)))
  :hints
  (("Goal" :in-theory (e/d (power-of-2p expt)
                           ()))))


(defthm expt-2-of-+-of--1-and-integer-length-when-power-of-2p-cheap
  (implies (acl2::power-of-2p x)
           (equal (expt 2 (+ -1 (integer-length x)))
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable acl2::power-of-2p))))

(defthm integerp-of-power2-hack
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (integerp n))
           (equal (integerp (* k (/ (expt 2 n))))
                  (<= n (+ -1 (integer-length k)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (expt-of-+ power-of-2p) (integerp-of-expt-when-natp))
           :use (:instance integerp-of-expt-when-natp
                           (r 2)
                           (i (- (+ -1 (integer-length k)) n))))))

(defthm integerp-of-power2-hack-another-factor
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (<= n (+ -1 (integer-length k)))
                (Integerp y)
                (integerp n))
           (integerp (* k (/ (expt 2 n)) y)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (expt-of-+ power-of-2p) ( integerp-of-expt-when-natp))
           :use ((:instance integerp-of-* (x (* k (unary-/ (expt '2 n)))))
                 (:instance integerp-of-expt-when-natp
                            (r 2)
                            (i (- (+ -1 (integer-length k)) n)))))))

(defthm integerp-of-power2-hack-another-factor-alt
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (<= n (+ -1 (integer-length k)))
                (integerp y)
                (integerp n))
           (integerp (* k y (/ (expt 2 n)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (expt-of-+ power-of-2p) ( integerp-of-expt-when-natp))
           :use ((:instance integerp-of-* (x (* k (unary-/ (expt '2 n)))))
                 (:instance integerp-of-expt-when-natp
                            (r 2)
                            (i (- (+ -1 (integer-length k)) n)))))))

;make a cheap version?
(defthmd not-power-of-2p-when-oddp
  (implies (and (oddp n)
                (< 1 n))
           (not (power-of-2p n)))
  :hints (("Goal" :in-theory (enable power-of-2p))))

(defthm <-of-expt-2-and-one-less-than-integer-length
  (implies (posp n)
           (equal (< (expt 2 (+ -1 (integer-length n))) n)
                  (not (power-of-2p n))))
  :hints (("Goal" :in-theory (e/d (integer-length power-of-2p expt) (expt-hack floor)))))
