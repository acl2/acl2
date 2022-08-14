; A lightweight book about the built-in function bounded-integer-alistp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that bounded-integer-alistp is a bad name, because it allows a key of :header.

(defthm bounded-integer-alistp-of-append
  (implies (true-listp x)
           (equal (bounded-integer-alistp (append x y) n)
                  (and (bounded-integer-alistp x n)
                       (bounded-integer-alistp y n))))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp append))))

(defthm bounded-integer-alistp-of-revappend
  (implies (and (bounded-integer-alistp x n)
                (bounded-integer-alistp y n))
           (bounded-integer-alistp (revappend x y) n))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp revappend))))

(defthm integerp-of-car-of-assoc-equal-when-bounded-integer-alistp
  (implies (and (bounded-integer-alistp array n)
                (assoc-equal i array))
           (equal (integerp (car (assoc-equal i array)))
                  (not (eq :header (car (assoc-equal i array))))))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp assoc-equal))))

(defthm bound-of-car-of-assoc-equal-when-bounded-integer-alistp
  (implies (and (bounded-integer-alistp array n)
                (natp n)
                (assoc-equal i array))
           (equal (< (car (assoc-equal i array)) n)
                  (if (eq :header (car (assoc-equal i array)))
                      (not (equal n 0))
                    t)))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp assoc-equal))))

(defthmd not-assoc-equal-when-bounded-integer-alistp-out-of-bounds
  (implies (and (bounded-integer-alistp array bound)
                (<= bound index)
                (natp index))
           (equal (assoc-equal index array)
                  nil))
  :hints (("Goal" :in-theory (e/d (bounded-integer-alistp assoc-equal) ()))))

(defthm bound2-of-car-of-assoc-equal-when-bounded-integer-alistp
  (implies (and (bounded-integer-alistp array n)
                (assoc-equal i array))
           (not (< (car (assoc-equal i array)) 0)))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp assoc-equal))))

(defthm bounded-integer-alistp-of-cons
  (equal (bounded-integer-alistp (cons item array) n)
         (and (bounded-integer-alistp array n)
              (or (eq :header (car item))
                  (and (natp (car item))
                       (natp n)
                       (< (car item) n)))))
  :hints (("Goal" :in-theory (enable bounded-integer-alistp))))


(defthm bounded-integer-alistp-of-nil
  (equal (bounded-integer-alistp 'nil n)
         t)
  :hints (("Goal" :in-theory (enable bounded-integer-alistp))))

(defthmd assoc-equal-forward-when-bounded-integer-alistp
  (implies (and (assoc-equal i array)
                (bounded-integer-alistp array n)
                (not (equal :header i)))
           (and (natp i)
                (< i n)))
  :rule-classes :forward-chaining)
