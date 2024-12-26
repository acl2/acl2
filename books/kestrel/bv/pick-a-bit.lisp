; "Pick a bit" proofs showing equality from equality of an arbitrary bit
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

(include-book "getbit-def")
(local (include-book "getbit"))
(local (include-book "unsigned-byte-p"))
(local (include-book "bvcat")) ; for equal-of-bvchop-and-bvchop-when-smaller-bvchops-equal

;returns a bit where x and y differ (if any)
(defund differing-bit (n x y)
  (declare (xargs :measure (nfix (+ 1 n))))
  (if (not (natp n))
      -1
    (if (not (equal (getbit n x) (getbit n y)))
        n
      (differing-bit (+ -1 n) x y))))

(defthm differing-bit-bad-guy-lemma-helper
  (implies (and (equal (getbit (differing-bit m x y) x)
                       (getbit (differing-bit m x y) y))
                (< m n)
                (natp m)
                (natp n))
           (equal (slice m 0 x)
                  (slice m 0 y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable differing-bit slice-becomes-getbit bvchop-1-becomes-getbit))))

;; (defthm natp-of-differing-bit
;;   (natp (differing-bit n x y)))

(defthm <-of-differing-bit
  (implies (natp n)
           (not (< n (differing-bit n x y))))
  :hints (("Goal" :expand ((DIFFERING-BIT 0 X Y))
           :in-theory (enable differing-bit))))

(defthm <-of-differing-bit2
  (implies (and (natp n)
                (integerp k)
                (<= (+ 1 n) k))
           (< (differing-bit n x y) k))
  :hints (("Goal" :expand ((DIFFERING-BIT 0 X Y))
           :in-theory (enable differing-bit))))

;; Lets us prove that BVs values are equal if we can prove that they agree on an arbitrary bit:
(defthm differing-bit-bad-guy-lemma
  (implies (and (equal (getbit (differing-bit (+ -1 n) x y) x)
                       (getbit (differing-bit (+ -1 n) x y) y))
                (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (natp n))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :use (:instance differing-bit-bad-guy-lemma-helper (m (+ -1 n)))))
  )

(defthm <-of-differing-bit-and-0
  (implies (natp n)
           (equal (< (differing-bit n x y) 0)
                  (equal (bvchop (+ 1 n) x)
                         (bvchop (+ 1 n) y))))
  :hints (("Goal" :in-theory (enable differing-bit slice-becomes-getbit bvchop-1-becomes-getbit))))
