; A lightweight book about the built-in function natp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider disabling natp.

(defthm natp-of-+
  (implies (and (natp x)
                (natp y))
           (natp (+ x y))))

(defthm natp-of-+-of--1
  (implies (integerp x)
           (equal (natp (+ -1 x))
                  (< 0 x))))

;; This is nice because it preserves natp as the abstraction
(defthm natp-of-+-of-1
  (implies (natp x)
           (natp (+ 1 x)))
  :hints (("Goal" :in-theory (enable natp))))

(defthmd natp-of-+-of-1-alt
  (implies (integerp x)
           (equal (natp (+ 1 x))
                  (<= -1 x))))

;; Used in a few places, but kept disabled for speed.  Can loop with (:definition natp)?
(defthmd not-<-of-0-when-natp
  (implies (natp n)
           (not (< n 0))))

(defthm natp-of-+-when-negative-constant
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (< k 0))
           (equal (natp (+ k x))
                  (and (natp x) ; preserves the abstraction
                       (<= (- k) x))))
  :hints (("Goal" :in-theory (enable natp))))

(defthm natp-of-min
  (implies (and (natp x)
                (natp y))
           (natp (min x y))))

(defthm natp-of-max
  (implies (and (natp x)
                (natp y))
           (natp (max x y))))
