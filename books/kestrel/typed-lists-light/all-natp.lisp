; A function to recognize lists of naturals
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/sequences/defforall" :dir :system) ;todo: drop

(defforall all-natp (lst) (natp lst) :declares ((type t lst)))

(defthmd natp-of-nth-when-all-natp
  (implies (and (all-natp lst)
                (< i (len lst))
                (natp i))
           (natp (nth i lst)))
  :hints (("Goal" :in-theory (enable len nth all-natp))))

(defthm all-natp-when-nat-listp-cheap
  (implies (nat-listp lst)
           (all-natp lst))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-natp nat-listp))))

(defthm all-natp-when-nat-listp
  (implies (nat-listp lst)
           (all-natp lst))
  :hints (("Goal" :in-theory (enable all-natp nat-listp))))

(defthm all-natp-of-set-difference-equal
  (implies (all-natp x)
           (all-natp (set-difference-equal x y))))

(defthm integerp-of-car-when-all-natp-cheap
  (implies (and (all-natp x)
                (consp x))
           (integerp (car x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(defthmd natp-of-nth-when-all-natp-type
  (implies (and (all-natp x)
                (< n (len x))
                (natp n))
           (natp (nth n x)))
  :rule-classes :type-prescription)

(defthmd not-<-of-nth-and-0-when-all-natp
  (implies (all-natp l)
           (not (< (nth n l) 0)))
  :hints (("Goal" :in-theory (enable all-natp nth))))
