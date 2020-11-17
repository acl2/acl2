; Mixed rules about numeric lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: compare to rational-lists.lisp

(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "kestrel/typed-lists-light/all-natp" :dir :system)
(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)

(defthmd rational-listp-when-all-natp
  (implies (all-natp items)
           (equal (rational-listp items)
                  (true-listp items)))
  :hints (("Goal" :in-theory (enable all-natp rational-listp))))

(defthm rational-listp-when-all-natp-cheap
  (implies (all-natp items)
           (equal (rational-listp items)
                  (true-listp items)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-natp rational-listp))))

(defthm all-natp-implies-all-integerp-cheap
  (implies (all-natp x)
           (all-integerp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-natp all-integerp))))

(defthm <-of-nth-of-0-and-0-when-all-natp-cheap
  (implies (all-natp indices)
           (equal (< (nth 0 indices) 0)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-natp))))

(defthm natp-of-maxelem-2
  (implies (and (nat-listp items)
                (consp items))
           (natp (maxelem items)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable all-natp maxelem))))

(defthm all-<-of-+-of-1-and-maxelem
  (implies (and (nat-listp nodenums)
                (consp nodenums))
           (all-< nodenums (+ 1 (maxelem nodenums)))))

(defthm maxelem-bound-maxint
  (implies (and (all-< nodenums 2147483646)
                (nat-listp nodenums)
                (consp nodenums))
           (<= (maxelem nodenums) 2147483645)))

(defthm maxelem-bound
  (implies (and (all-natp x)
                (consp x))
           (<= 0 (maxelem x)))
  :hints (("Goal" :in-theory (enable MAXELEM))))

(defthm integerp-of-maxelem2
  (implies (and (all-natp x) ;relax?
                (consp x))
           (integerp (maxelem x)))
  :hints (("Goal" :in-theory (enable MAXELEM))))
