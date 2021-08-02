; Mixed rules about lists of integers
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-integerp")
(include-book "all-natp")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;Disabled since it could be expensive
(defthmd all-integerp-when-all-natp
  (implies (all-natp x)
           (all-integerp x))
  :hints (("Goal" :in-theory (enable all-natp all-integerp))))

(defthm all-integerp-when-all-natp-cheap
  (implies (all-natp x)
           (all-integerp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-integerp-when-all-natp))))

;Disabled since it could be expensive
(defthmd integer-listp-when-all-natp
  (implies (all-natp x)
           (equal (integer-listp x)
                  (true-listp x)))
  :hints (("Goal" :in-theory (enable all-natp integer-listp))))

(defthm integer-listp-when-all-natp-cheap
  (implies (all-natp x)
           (equal (integer-listp x)
                  (true-listp x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable integer-listp-when-all-natp))))
