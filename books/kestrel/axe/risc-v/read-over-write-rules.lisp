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

(defthm read-byte-of-set-reg (equal (read-byte addr (set-reg n val stat)) (read-byte addr stat)) :hints (("Goal" :in-theory (enable set-reg read-byte))))
(defthm read-of-set-reg (equal (read n addr (set-reg n2 val stat)) (read n addr stat)) :hints (("Goal" :in-theory (enable read))))

(defthm reg-of-write-byte (equal (reg n (write-byte addr val stat)) (reg n stat)) :hints (("Goal" :in-theory (enable reg write-byte))))
(defthm reg-of-write (equal (reg n (write n2 addr val stat)) (reg n stat)) :hints (("Goal" :in-theory (enable write))))
