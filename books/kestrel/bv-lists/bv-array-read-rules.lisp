; Rules about bv-array-read
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-array-read")
(include-book "kestrel/bv/unsigned-byte-p-forced" :dir :system)
(include-book "kestrel/bv/bvmult" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)

(defthm unsigned-byte-p-forced-of-bv-array-read
  (implies (and (<= element-size n)
                (natp n)
                (natp element-size))
           (unsigned-byte-p-forced n (bv-array-read element-size len index data)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p-forced))))

;; turns the * into bvmult -- todo: use a more general scheme
(defthmd bv-array-read-of-*-arg3
  (implies (and (syntaxp (quotep len)) ; so we can evaluate the call to ceiling-of-lg
                (natp len)
                (integerp i1)
                (integerp i2))
           (equal (bv-array-read element-size len (* i1 i2) data)
                  (bv-array-read element-size len (bvmult (acl2::ceiling-of-lg len) i1 i2) data)))
  :hints (("Goal" :in-theory (enable bv-array-read bvmult))))


;; turns the + into bvplus
(defthmd bv-array-read-of-+-arg3
  (implies (and (syntaxp (quotep len)) ; so we can evaluate the call to ceiling-of-lg
                (natp len)
                (integerp i1)
                (integerp i2))
           (equal (bv-array-read element-size len (+ i1 i2) data)
                  (bv-array-read element-size len (bvplus (acl2::ceiling-of-lg len) i1 i2) data)))
  :hints (("Goal" :in-theory (enable bv-array-read bvplus))))
