;------------------------------------------
;
; Author:  Diana Toma
; TIMA-VDS, Grenoble, France
; March 2003
; ACL2 formalization of SHAs
; Logic functions (and theorems) needed for all four SHA
;------------------------------------------



(IN-PACKAGE "ACL2")

(include-book "bv-op-defthms")


;logic functions for SHAs

(defun Ch (x y z)
  (if (and  (bvp x)
          (bvp y)
          (bvp z))
       (bv-xor (bv-and x y) (bv-and (bv-not x) z))
       nil))

(defthm bvp-Ch
  (implies (and  (bvp x) (bvp y) (bvp z))
         (bvp (Ch x y z))))

(defthm wordp-Ch
  (implies (and  (wordp x w) (wordp y w) (wordp z w))
         (wordp (Ch x y z) w)))


(defun Parity (x y z)
  (if (and  (bvp x)
          (bvp y)
          (bvp z))
      (bv-xor  x y z)
       nil))

(defthm bvp-Parity
  (implies (and  (bvp x) (bvp y) (bvp z))
         (bvp (Parity x y z))))

(defthm wordp-Parity
  (implies (and  (wordp x w) (wordp y w) (wordp z w))
         (wordp (Parity x y z) w)))

(defun Maj (x y z)
  (if (and  (bvp x)
          (bvp y)
          (bvp z))
      (bv-xor  (bv-and x y) (bv-and x z) (bv-and y z))
       nil))

(defthm bvp-Maj
  (implies (and  (bvp x) (bvp y) (bvp z))
         (bvp (Maj x y z))))

(defthm wordp-Maj
  (implies (and  (wordp x w) (wordp y w) (wordp z w))
         (wordp (Maj x y z) w)))

(defun Ft (i x y z)
 (if (and (integerp i)
          (<= 0 i)
          (wordp x 32)
          (wordp y 32)
          (wordp z 32))
      (cond ((and (<= 0 i) (<= i 19))
            (Ch x y z))
            ((or (and (<= 20 i) (<= i 39)) (and (<= 60 i) (<= i 79)))
            (Parity x y z))
            ((and (<= 40 i) (<= i 59))
            (Maj x y z)))
      nil))

(defthm wordp-Ft
  (implies (and (integerp i) (<= 0 i)  (wordp x 32) (<= 0 i) (< i 80)
          (wordp y 32) (wordp z 32))
         (wordp (Ft i x y z) 32))
:hints (("goal" :in-theory (disable ch parity maj) )))

(defun sigma-0-256 (x)
     (if  (wordp x 32)
          (bv-xor  (rotr 2 x 32) (rotr 13 x 32) (rotr 22 x 32))
          nil))


(defthm wordp-sigma-0-256
(implies (wordp x 32)
   ( wordp  (sigma-0-256 x) 32))
:hints (("goal" :in-theory (disable binary-bv-xor rotr rotr->rotl  ))))

(defun sigma-1-256 (x)
     (if  (wordp x 32)
          (bv-xor (rotr 6 x 32) (rotr 11 x 32) (rotr 25 x 32))
          nil))

(defthm wordp-sigma-1-256
(implies (wordp x 32)
   ( wordp  (sigma-1-256 x) 32))
:hints (("goal" :in-theory (disable binary-bv-xor rotr rotr->rotl  ))))

(defun s-0-256 (x)
     (if  (wordp x 32)
          (bv-xor (rotr 7 x 32) (rotr 18 x 32) (shr 3 x 32))
          nil))

(defthm wordp-s-0-256
(implies (wordp x 32)
   ( wordp  (s-0-256 x) 32))
:hints (("goal" :in-theory (disable binary-bv-xor rotr rotr->rotl shr  ))))

(defun s-1-256 (x)
     (if  (wordp x 32)
          (bv-xor  (rotr 17 x 32) (rotr 19 x 32) (shr 10 x 32))
          nil))

(defthm wordp-s-1-256
(implies (wordp x 32)
   ( wordp  (s-1-256 x) 32))
:hints (("goal" :in-theory (disable binary-bv-xor rotr rotr->rotl shr  ))))

(defun sigma-0-512 (x)
     (if  (wordp x 64)
          (bv-xor  (rotr 28 x 64) (rotr 34 x 64) (rotr 39 x 64))
          nil))

(defthm wordp-sigma-0-512
(implies (wordp x 64)
   ( wordp  (sigma-0-512 x) 64))
:hints (("goal" :in-theory (disable binary-bv-xor rotr rotr->rotl  ))))

(defun sigma-1-512 (x)
     (if  (wordp x 64)
          (bv-xor  (rotr 14 x 64) (rotr 18 x 64) (rotr 41 x 64))
          nil))

(defthm wordp-sigma-1-512
(implies (wordp x 64)
   ( wordp  (sigma-1-512 x) 64))
:hints (("goal" :in-theory (disable binary-bv-xor rotr rotr->rotl  ))))

(defun s-0-512 (x)
     (if  (wordp x 64)
          (bv-xor  (rotr 1 x 64) (rotr 8 x 64) (shr 7 x 64))
          nil))

(defthm wordp-s-0-512
(implies (wordp x 64)
   ( wordp  (s-0-512 x) 64))
:hints (("goal" :in-theory (disable binary-bv-xor rotr rotr->rotl shr  ))))

(defun s-1-512 (x)
     (if  (wordp x 64)
          (bv-xor  (rotr 19 x 64) (rotr 61 x 64) (shr 6 x 64))
          nil))

(defthm wordp-s-1-512
(implies (wordp x 64)
   ( wordp  (s-1-512 x) 64))
:hints (("goal" :in-theory (disable binary-bv-xor rotr rotr->rotl shr  ))))
