; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "../bit-vectors/bitops-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "../bit-vectors/bitops"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline u32-fix (word)
  (declare (xargs :guard (unsigned-byte-p 32 word)
                  :split-types t)
           (type (unsigned-byte 32) word))
  (mbe :logic (if (unsigned-byte-p 32 word)
                  word
                0)
       :exec (the (unsigned-byte 32) word)))

(in-theory (disable (:t u32-fix)))

(defthm u32-fix-type-prescription
  (natp (u32-fix word))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable u32-fix))))

(defthm unsigned-byte-p-32-of-u32-fix
  (unsigned-byte-p 32 (u32-fix word))
  :hints (("Goal" :in-theory (enable u32-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm u32-fix-when-unsigned-byte-p-32
  (implies (unsigned-byte-p 32 x)
           (equal (u32-fix x)
                  x))
  :hints (("Goal" :in-theory (enable u32-fix))))

(defthmd u32-fix-when-not-unsigned-byte-p-32
  (implies (not (unsigned-byte-p 32 x))
           (equal (u32-fix x)
                  0))
  :hints (("Goal" :in-theory (enable u32-fix))))

(defthm u32-fix-when-not-unsigned-byte-p-32-cheap
  (implies (not (unsigned-byte-p 32 x))
           (equal (u32-fix x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by u32-fix-when-not-unsigned-byte-p-32)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline u32-equal (x y)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y))
                  :split-types t)
           (type (unsigned-byte 32) x y))
  (mbe :logic (equal (u32-fix x) (u32-fix y))
       :exec (= (the (unsigned-byte 32) x)
                (the (unsigned-byte 32) y))))

(defequiv u32-equal
  :hints (("Goal" :in-theory (enable u32-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t u32-equal)))

(defthm booleanp-of-u32-equal
  (booleanp (u32-equal x y))
  :hints (("Goal" :in-theory (enable u32-equal))))

(defthm u32-equal-type-prescription
  (booleanp (u32-equal x y))
  :rule-classes :type-prescription
  :hints (("Goal" :by booleanp-of-u32-equal)))

(defthm u32-fix-when-u32-equal-congruence
  (implies (u32-equal x y)
           (equal (u32-fix x)
                  (u32-fix y)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-equal))))

(defthm u32-fix-under-u32-equal
  (u32-equal (u32-fix word)
             word)
  :hints (("Goal" :in-theory (enable u32-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note that the u32 operations only used for performant execution and
;; type/equivalence reasoning. They are not the normal forms for actual
;; arithmetic reasoning; they should be unfolded and the bv operations used
;; instead.

(defund-inline u32-plus (x y)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y))
                  :split-types t)
           (type (unsigned-byte 32) x y))
  (mbe :logic (acl2::loghead 32 (+ (u32-fix x) (u32-fix y)))
       :exec (the (unsigned-byte 32)
               (logand (+ (the (unsigned-byte 32) x)
                          (the (unsigned-byte 32) y))
                       #.*u32-max*))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t u32-plus)))

(defthm u32-plus-type-prescription
  (natp (u32-plus x y))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable u32-plus))))

(defthm unsigned-byte-p-32-of-u32-plus
  (unsigned-byte-p 32 (u32-plus x y))
  :hints (("Goal" :in-theory (enable u32-plus))))

(defthm u32-plus-when-u32-equal-of-arg1-congruence
  (implies (u32-equal x0 x1)
           (equal (u32-plus x0 y)
                  (u32-plus x1 y)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-plus))))

(defthm u32-plus-when-u32-equal-of-arg2-congruence
  (implies (u32-equal y0 y1)
           (equal (u32-plus x y0)
                  (u32-plus x y1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-plus))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline u32-minus (x y)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y))
                  :split-types t)
           (type (unsigned-byte 32) x y))
  (mbe :logic (acl2::loghead 32 (- (u32-fix x) (u32-fix y)))
       :exec (the (unsigned-byte 32)
               (logand (- (the (unsigned-byte 32) x)
                          (the (unsigned-byte 32) y))
                       #.*u32-max*))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t u32-minus)))

(defthm u32-minus-type-prescription
  (natp (u32-minus x y))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable u32-minus))))

(defthm unsigned-byte-p-32-of-u32-minus
  (unsigned-byte-p 32 (u32-minus x y))
  :hints (("Goal" :in-theory (enable u32-minus))))

(defthm u32-minus-when-u32-equal-of-arg1-congruence
  (implies (u32-equal x0 x1)
           (equal (u32-minus x0 y)
                  (u32-minus x1 y)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-minus))))

(defthm u32-minus-when-u32-equal-of-arg2-congruence
  (implies (u32-equal y0 y1)
           (equal (u32-minus x y0)
                  (u32-minus x y1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-minus))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline u32-uminus (x)
  (declare (xargs :guard (unsigned-byte-p 32 x)
                  :split-types t)
           (type (unsigned-byte 32) x))
  (mbe :logic (acl2::loghead 32 (- (u32-fix x)))
       :exec (the (unsigned-byte 32)
               (logand (- x)
                       #.*u32-max*))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t u32-uminus)))

(defthm u32-uminus-type-prescription
  (natp (u32-uminus x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable u32-uminus))))

(defthm unsigned-byte-p-32-of-u32-uminus
  (unsigned-byte-p 32 (u32-uminus x))
  :hints (("Goal" :in-theory (enable u32-uminus))))

(defthm u32-uminus-when-u32-equal-congruence
  (implies (u32-equal x0 x1)
           (equal (u32-uminus x0)
                  (u32-uminus x1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-uminus))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline u32-and (x y)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y))
                  :split-types t)
           (type (unsigned-byte 32) x y))
  (mbe :logic (acl2::loghead 32 (logand (u32-fix x) (u32-fix y)))
       :exec (the (unsigned-byte 32)
               (logand (the (unsigned-byte 32) x)
                       (the (unsigned-byte 32) y)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t u32-and)))

(defthm u32-and-type-prescription
  (natp (u32-and x y))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable u32-and))))

(defthm unsigned-byte-p-32-of-u32-and
  (unsigned-byte-p 32 (u32-and x y))
  :hints (("Goal" :in-theory (enable u32-and))))

(defthm u32-and-when-u32-equal-of-arg1-congruence
  (implies (u32-equal x0 x1)
           (equal (u32-and x0 y)
                  (u32-and x1 y)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-and))))

(defthm u32-and-when-u32-equal-of-arg2-congruence
  (implies (u32-equal y0 y1)
           (equal (u32-and x y0)
                  (u32-and x y1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-and))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline u32-or (x y)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y))
                  :split-types t)
           (type (unsigned-byte 32) x y))
  (mbe :logic (acl2::loghead 32 (logior (u32-fix x) (u32-fix y)))
       :exec (the (unsigned-byte 32)
               (logior (the (unsigned-byte 32) x)
                       (the (unsigned-byte 32) y)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t u32-or)))

(defthm u32-or-type-prescription
  (natp (u32-or x y))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable u32-or))))

(defthm unsigned-byte-p-32-of-u32-or
  (unsigned-byte-p 32 (u32-or x y))
  :hints (("Goal" :in-theory (enable u32-or))))

(defthm u32-or-when-u32-equal-of-arg1-congruence
  (implies (u32-equal x0 x1)
           (equal (u32-or x0 y)
                  (u32-or x1 y)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-or))))

(defthm u32-or-when-u32-equal-of-arg2-congruence
  (implies (u32-equal y0 y1)
           (equal (u32-or x y0)
                  (u32-or x y1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-or))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline u32-xor (x y)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 32 y))
                  :split-types t)
           (type (unsigned-byte 32) x y))
  (mbe :logic (acl2::loghead 32 (logxor (u32-fix x) (u32-fix y)))
       :exec (the (unsigned-byte 32)
               (logxor (the (unsigned-byte 32) x)
                       (the (unsigned-byte 32) y)))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t u32-xor)))

(defthm u32-xor-type-prescription
  (natp (u32-xor x y))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable u32-xor))))

(defthm unsigned-byte-p-32-of-u32-xor
  (unsigned-byte-p 32 (u32-xor x y))
  :hints (("Goal" :in-theory (enable u32-xor))))

(defthm u32-xor-when-u32-equal-of-arg1-congruence
  (implies (u32-equal x0 x1)
           (equal (u32-xor x0 y)
                  (u32-xor x1 y)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-xor))))

(defthm u32-xor-when-u32-equal-of-arg2-congruence
  (implies (u32-equal y0 y1)
           (equal (u32-xor x y0)
                  (u32-xor x y1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-xor))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline u32-not (x)
  (declare (xargs :guard (unsigned-byte-p 32 x)
                  :split-types t)
           (type (unsigned-byte 32) x))
  (mbe :logic (acl2::loghead 32 (lognot (u32-fix x)))
       :exec (the (unsigned-byte 32)
               (logand (lognot (the (unsigned-byte 32)
                                 x))
                       #.*u32-max*))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t u32-not)))

(defthm u32-not-type-prescription
  (natp (u32-not x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable u32-not))))

(defthm unsigned-byte-p-32-of-u32-not
  (unsigned-byte-p 32 (u32-not x))
  :hints (("Goal" :in-theory (enable u32-not))))

(defthm u32-not-when-u32-equal-congruence
  (implies (u32-equal x0 x1)
           (equal (u32-not x0)
                  (u32-not x1)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-not))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund-inline u32-shl (x shift-amount)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 6 shift-amount))
                  :split-types t)
           (type (unsigned-byte 32) x)
           (type (unsigned-byte 7) shift-amount))
  (mbe :logic (acl2::lshu 32 (u32-fix x) shift-amount)
       :exec (the (unsigned-byte 32)
               (logand (ash (the (unsigned-byte 32) x)
                            (the (unsigned-byte 6) shift-amount))
                       #.*u32-max*))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t u32-shl)))

(defthm u32-shl-type-prescription
  (natp (u32-shl x shift-amount))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable u32-shl))))

(defthm unsigned-byte-p-32-of-u32-shl
  (unsigned-byte-p 32 (u32-shl x shift-amount))
  :hints (("Goal" :in-theory (enable u32-shl))))

(defthm u32-shl-when-u32-equal-congruence
  (implies (u32-equal x0 x1)
           (equal (u32-shl x0 shift-amount)
                  (u32-shl x1 shift-amount)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-shl))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note: since we are dealing with unsigned words, there is no difference
;; between arithmetic and logical shifts.
(defund-inline u32-shr (x shift-amount)
  (declare (xargs :guard (and (unsigned-byte-p 32 x)
                              (unsigned-byte-p 6 shift-amount))
                  :split-types t)
           (type (unsigned-byte 32) x)
           (type (unsigned-byte 7) shift-amount))
  (mbe :logic (acl2::lshu 32 (u32-fix x) (- shift-amount))
       :exec (the (unsigned-byte 32)
               (logand (ash (the (unsigned-byte 32) x)
                            (- (the (unsigned-byte 6) shift-amount)))
                       #.*u32-max*))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t u32-shr)))

(defthm u32-shr-type-prescription
  (natp (u32-shr x shift-amount))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable u32-shr))))

(defthm unsigned-byte-p-32-of-u32-shr
  (unsigned-byte-p 32 (u32-shr x shift-amount))
  :hints (("Goal" :in-theory (enable u32-shr))))

(defthm u32-shr-when-u32-equal-congruence
  (implies (u32-equal x0 x1)
           (equal (u32-shr x0 shift-amount)
                  (u32-shr x1 shift-amount)))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable u32-shr))))
