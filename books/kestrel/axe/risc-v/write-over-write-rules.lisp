; Rules to normalize nests of writes
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

(include-book "portcullis")
(include-book "read-and-write")
(include-book "registers")
(include-book "pc")

(theory-invariant (incompatible (:rewrite write32-xreg-becomes-set-reg) (:definition set-reg))) ; todo: more

(defthm set-reg-of-set-pc
  (equal (set-reg reg val (set-pc pc stat))
         (set-pc pc (set-reg reg val stat)))
  :hints (("Goal" :in-theory (e/d (set-reg set-pc) (write32-xreg-becomes-set-reg)))))

(defthm write-byte-of-set-pc
  (equal (write-byte addr val (set-pc pc stat))
         (set-pc pc (write-byte addr val stat)))
  :hints (("Goal" :in-theory (e/d (write-byte set-pc) (write32-mem-ubyte8-becomes-write-byte)))))

(defthm write-of-set-pc
  (equal (write n addr val (set-pc pc stat))
         (set-pc pc (write n addr val stat)))
  :hints (("Goal" :in-theory (e/d (write) (write32-xreg-becomes-set-reg)))))

(defthm write-byte-of-set-reg
  (equal (write-byte addr val1 (set-reg reg val2 stat))
         (set-reg reg val2 (write-byte addr val1 stat)))
  :hints (("Goal" :in-theory (e/d (write-byte set-reg) (write32-xreg-becomes-set-reg write32-mem-ubyte8-becomes-write-byte)))))

(defthm write-of-set-reg
  (equal (write n addr val1 (set-reg reg val2 stat))
         (set-reg reg val2 (write n addr val1 stat)))
  :hints (("Goal" :in-theory (e/d (write) (write32-xreg-becomes-set-reg)))))
