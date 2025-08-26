; Rules about reading and writing state components
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

(defthm read-byte-of-set-reg (equal (read-byte addr (set-reg n val stat)) (read-byte addr stat)) :hints (("Goal" :in-theory (enable set-reg read-byte))))
(defthm read-of-set-reg (equal (read n addr (set-reg n2 val stat)) (read n addr stat)) :hints (("Goal" :in-theory (enable read))))

(defthm reg-of-write-byte (equal (reg n (write-byte addr val stat)) (reg n stat)) :hints (("Goal" :in-theory (enable reg write-byte))))
(defthm reg-of-write (equal (reg n (write n2 addr val stat)) (reg n stat)) :hints (("Goal" :in-theory (enable write))))
(defthm reg-of-set-pc (equal (reg n (set-pc pc stat)) (reg n stat)) :hints (("Goal" :in-theory (enable set-pc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-byte-of-set-pc
  (equal (read-byte addr (set-pc pc stat))
         (read-byte addr stat))
  :hints (("Goal" :in-theory (enable read-byte set-pc))))

(defthm read-of-set-pc
  (equal (read n addr (set-pc pc stat))
         (read n addr stat))
  :hints (("Goal" :in-theory (enable read))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm pc-of-set-reg (equal (pc (set-reg reg val stat)) (pc stat)) :hints (("Goal" :in-theory (enable pc set-reg))))

(defthm pc-of-write-byte (equal (pc (write-byte addr val stat)) (pc stat)) :hints (("Goal" :in-theory (enable pc write-byte))))

(defthm pc-of-write (equal (pc (write n addr val stat)) (pc stat)) :hints (("Goal" :in-theory (enable write))))
