; Supporting rules about bit-vectors
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: Push these back into libraries.

(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/bv/bvand" :dir :system)
(include-book "kestrel/bv/bvshr" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "kestrel/utilities/polarity" :dir :system) ; for want-to-strengthen
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ; for slice-too-high-is-0-new (todo: move it)
(local (include-book "kestrel/bv/rules10" :dir :system)) ; todo, for logand-of-bvchop-becomes-bvand etc
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor-and-expt" :dir :system))
;(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;; ;replace the other one!
;; (encapsulate ()
;;   (local (include-book "kestrel/arithmetic-light/expt" :dir :system))
;;   (defthm slice-of-times-of-expt-gen
;;     (implies (and            ;(<= j n) ;drop?
;;               (integerp x)   ;drop?
;;               (natp n)
;;               (natp j)
;;               (natp m))
;;              (equal (slice m n (* (expt 2 j) x))
;;                     (slice (- m j) (- n j) x)))
;;     :hints (("Goal" :in-theory (e/d (slice logtail nfix) ())))))

;move
;; ;avoids having to give a highsize
;; (defthm slice-of-logapp
;;   (implies (and (natp lowsize)
;;                 (natp low)
;;                 (natp high)
;;                 (integerp highval))
;;            (equal (slice high low (logapp lowsize lowval highval))
;;                   (slice high low (bvcat (+ 1 high (- lowsize)) highval lowsize lowval))))
;;   :otf-flg t
;;   :hints (("Goal" :use (:instance ACL2::BVCAT-RECOMBINE
;;                                   (acl2::lowsize lowsize)
;;                                   (acl2::lowval lowval)
;;                                   (acl2::highval highval)
;;                                   (acl2::highsize (+ 1 high (- lowsize)))))))


;;   :hints (("Goal" :in-theory (e/d (;bvcat logapp
;;                                          ;acl2::slice-of-sum-cases
;;                                          )
;;                                   ()))))

;move
(defthm slice-of-logapp-case-1
  (implies (and (natp high)
                (natp low)
                ;; (natp lowsize)
                (<= lowsize low) ; this case
                (unsigned-byte-p lowsize lowval)
                (integerp highval))
           (equal (acl2::slice high low (logapp lowsize lowval highval))
                  (acl2::slice (+ (- lowsize) high) (+ (- lowsize) low) highval)))
  :hints (("Goal" :in-theory (e/d (acl2::slice logapp) (acl2::logtail-of-plus
                                                  acl2::unsigned-byte-p-of-logapp-large-case))
           :use (:instance acl2::unsigned-byte-p-of-logapp-large-case
                           (size1 low)
                           (size lowsize)
                           (i lowval)
                           (j (acl2::BVCHOP (+ LOW (- LOWSIZE)) HIGHVAL))))))


(defthm plus-of-minus1-and-bvcat-of-0
  (implies (and (posp lowsize)
                (integerp highval)
                (natp HIGHSIZE))
           (equal (+ -1 (bvcat highsize highval lowsize 0))
                  (if (equal (bvchop highsize highval) 0)
                      -1
                    (bvcat highsize (+ -1 highval) lowsize (+ -1 (expt 2 lowsize))))))
  :hints (("Goal" :in-theory (e/d (bvcat bvplus acl2::bvchop-of-sum-cases)
                                  (
                                   ;acl2::equal-of-+-when-negative-constant
                                   )))))



(defthm +-of-minus1-and-bvcat-of-0
  (implies (natp size)
           (equal (+ -1 (BVCAT 1 1 size 0))
                  (+ -1 (expt 2 size))))
  :hints (("Goal" :in-theory (enable bvcat))))

(defthm bvshr-of-logand-becomes-bvshr-of-bvand
  (implies (and (natp amt)
                (< amt 32))
           (equal (acl2::bvshr 32 (logand x y) amt)
                  (acl2::bvshr 32 (bvand (+ 32 amt) x y) amt)))
  :hints (("Goal" :in-theory (e/d (acl2::bvshr bvand slice acl2::logtail-of-bvchop)
                                  (acl2::slice-of-logand
                                   ;acl2::logand-of-bvchop-becomes-bvand-alt
                                   ;acl2::logand-of-bvchop-becomes-bvand
                                   acl2::bvchop-of-logtail-becomes-slice
                                   acl2::anti-slice
                                   ACL2::BVAND-LOGTAIL-ARG2 ;looped
                                   ACL2::BVAND-LOGTAIL-ARG1 ;looped
                                   )))))

(defthm bvchop-of-+-of-*-of-256
  (implies (and (integerp x)
                (integerp y))
           (equal (acl2::bvchop 8 (+ x (* 256 y)))
                  (acl2::bvchop 8 x))))

(defthmd mod-becomes-bvchop-8
  (implies (integerp x)
           (equal (mod x 256)
                  (acl2::bvchop 8 x)))
  :hints (("Goal" :in-theory (enable acl2::bvchop ifix))))

;move
(defthm bvchop-upper-bound-strong
  (implies (natp n)
           (<= (acl2::bvchop n x) (+ -1 (expt 2 n))))
  :rule-classes (:rewrite)
  :hints (("Goal" :in-theory (enable acl2::bvchop))))

(defthm bvplus-of-*-of-256
  (implies (and (natp size)
                (<= 8 size)
                (unsigned-byte-p 8 byte)
                (integerp val))
           (equal (acl2::bvplus size byte (* 256 val))
                  (acl2::bvcat (- size 8) val 8 byte)))
  :hints (("Goal"
           :use (:instance bvchop-upper-bound-strong (n (+ -8 SIZE))
                           (x val))
           :in-theory (e/d (acl2::bvcat acl2::bvplus
                                        acl2::bvchop-of-sum-cases
                                        logtail
                                        ACL2::EXPT-OF-+)
                           (acl2::bvchop-upper-bound
                            bvchop-upper-bound-strong
                            ACL2::BVCHOP-BOUND-2)))))


(defthm fix-when-integerp
  (implies (integerp x)
           (equal (fix x)
                  x)))

(defthm open-ash-positive-constants
  (implies (and (syntaxp (quotep i))
                (syntaxp (quotep c))
                (natp c)
                (integerp i))
           (equal (ash i c)
                  (* i (expt 2 c))))
  :hints (("Goal" :in-theory (enable ash))))

;gen
(defthm strengthen-upper-bound-when-top-bit-0
  (implies (and (syntaxp (acl2::want-to-strengthen (< x 9223372036854775808)))
                (equal (acl2::getbit 63 x) 1)
                (integerp x))
           (equal (< x 9223372036854775808)
                  (<= x 0)))
  :hints (("Goal" :in-theory (e/d (acl2::getbit acl2::slice acl2::logtail)
                                  (acl2::slice-becomes-getbit
                                   acl2::bvchop-1-becomes-getbit
                                   acl2::bvchop-of-logtail-becomes-slice)))))

;; Since 0 and 1 are the only BVs less than 2
(defthmd <-of-bvchop-and-2
  (equal (< (ACL2::BVCHOP size x) 2)
         (or (equal (ACL2::BVCHOP size x) 0)
             (equal (ACL2::BVCHOP size x) 1))))

;;gen
(defthm bvplus-subst-smaller-term
  (implies (and (equal (bvchop 32 x) (bvchop 32 x2))
                (syntaxp (acl2::smaller-termp x2 x)))
           (equal (bvplus 32 x y)
                  (bvplus 32 x2 y))))

(defthm fix-of-ifix
  (equal (fix (ifix x))
         (ifix x)))

(defthm equal-of-bvchop-and-bvplus-same
  (implies (natp size)
           (equal (EQUAL (BVCHOP size K) (BVPLUS size n K))
                  (equal (bvchop size n) 0)))
  :hints (("Goal"
           :in-theory (e/d (bvplus acl2::bvchop-of-sum-cases bvuminus bvminus)
                           ( acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    acl2::slice-of-+ ;looped
                                                    ;; acl2::bvcat-of-+-high
   ;                                                    ACL2::NTH-OF-CDR
                                                    )) )))
