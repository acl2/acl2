; A lightweight book about the built-in-function doublet-listp
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "greater-than-or-equal-len"))

(in-theory (disable doublet-listp))

(defthm alistp-when-doublet-listp
  (implies (doublet-listp x)
           (alistp x))
  :hints (("Goal" :in-theory (enable doublet-listp))))

;; Justifies calling strip-cadrs on a doublet-list.
(defthm all->=-len-when-doublet-listp
  (implies (doublet-listp x)
           (acl2::all->=-len x 2))
  :hints (("Goal" :in-theory (enable doublet-listp))))

;; Then the built-in rule alistp-forward-to-true-listp should give us
;; true-listp as well.
(defthm doublet-listp-forward-to-alistp
  (implies (doublet-listp x)
           (alistp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable doublet-listp))))

(defthm doublet-listp-of-cdr
  (implies (doublet-listp x)
           (doublet-listp (cdr x)))
  :hints (("Goal" :in-theory (enable doublet-listp))))

(defthm len-of-car-when-doublet-listp-cheap
  (implies (doublet-listp x)
           (equal (len (car x))
                  (if (consp x) 2 0)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable doublet-listp))))
