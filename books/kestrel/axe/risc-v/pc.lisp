; Normal forms for PC operations
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

;; TODO: Consider adding 32 to the names of the functions in this file (or
;; making separate packages for 32-bit and 64-bit RISC-V proofs).

(include-book "portcullis")
(include-book "risc-v-rules")
(include-book "kestrel/risc-v/specialized/states32" :dir :system)
(include-book "kestrel/bv/bvchop-def" :dir :system)

(local (in-theory (disable mod)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund pc (stat)
  (declare (xargs :guard (stat32ip stat)))
  (read32-pc stat))

(defthmd read32-pc-becomes-pc
  (equal (read32-pc stat)
         (pc stat))
  :hints (("Goal" :in-theory (enable pc))))

(theory-invariant (incompatible (:rewrite read32-pc-becomes-pc) (:definition pc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund set-pc (pc stat)
  (declare (xargs :guard (and (integerp pc) ; tighten?
                              (stat32ip stat))))
  (write32-pc pc stat))

(defthmd write32-pc-becomes-set-pc
  (equal (write32-pc pc stat)
         (set-pc pc stat))
  :hints (("Goal" :in-theory (enable set-pc))))

(theory-invariant (incompatible (:rewrite write32-pc-becomes-set-pc) (:definition set-pc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm pc-of-set-pc
  (equal (pc (set-pc pc stat))
         (mod (ifix pc) 4294967296))
  :hints (("Goal" :in-theory (enable pc set-pc))))

(defthm set-pc-of-set-pc
  (equal (set-pc pc1 (set-pc pc2 stat))
         (set-pc pc1 stat))
  :hints (("Goal" :in-theory (enable pc set-pc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm error32p-of-set-pc (equal (error32p (set-pc pc stat)) (error32p stat)) :hints (("Goal" :in-theory (enable set-pc))))
