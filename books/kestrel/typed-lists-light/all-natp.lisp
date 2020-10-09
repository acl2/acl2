; A function to recognize lists of naturals
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../sequences/defforall") ;todo: drop

(defforall all-natp (lst) (natp lst) :declares ((type t lst)))

;dup
(defthm natp-of-nth-from-all-natp
  (implies (and (all-natp lst)
                (< i (len lst))
                (natp i))
           (natp (nth i lst)))
  :hints (("Goal" :in-theory (e/d (len nth all-natp)
                                  (;list::len-of-cdr nth-of-cdr
                                   )))))

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
