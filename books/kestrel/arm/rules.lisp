; Rules about the ARM model
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "pseudocode")
(include-book "instructions")
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(local (include-book "kestrel/bv/bvminus" :dir :system))
(local (include-book "kestrel/bv/bvand" :dir :system))
(local (include-book "kestrel/bv/bvxor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library rules:

(defthmd sbvlt-when-not-equal-weaken
  (implies (and (syntaxp (acl2::want-to-weaken (sbvlt 32 x y)))
                (not (equal x y))
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (sbvlt 32 x y)
                  (not (sbvlt 32 y x))))
  :hints (("Goal" :in-theory (enable acl2::sbvlt-rewrite))))

;gen
(defthm getbit-of-reg-too-high
  (implies (and (<= 32 bit)
                (integerp bit)
                (armp arm)
                (natp n)
                (< n 16))
           (equal (getbit bit (reg n arm))
                  0))
  :hints (("Goal" :in-theory (enable acl2::getbit-too-high))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;gen
(defthm <-of-maxint-31
  (implies (and (syntaxp (acl2::want-to-weaken (< x 2147483647)))
                (unsigned-byte-p 31 x))
           (equal (< x 2147483647)
                  (not (equal x 2147483647)))))

;gen
(defthm <-of-maxint-minus-one-31
  (implies (and (syntaxp (acl2::want-to-strengthen (< 2147483646 x)))
                (unsigned-byte-p 31 x))
           (equal (< 2147483646 x)
                  (equal x 2147483647))))

;dup
(local
 (defthm equal-of-+-of-bvchop-same-31-32-linear
   (implies (unsigned-byte-p 32 x)
            (equal x (+ (bvchop 31 x) (* (expt 2 31) (getbit 31 x)))))
   :rule-classes :linear
   :hints (("Goal" :use (:instance acl2::split-bv
                                   (x x)
                                   (n 32)
                                   (m 31))
                   :in-theory (enable bvcat acl2::logapp getbit)))))

(local (include-book "kestrel/bv/bvuminus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))

;dup
;todo: this is in rational-lists
(local
  (defthm acl2::<-of-+-of-1-strengthen
    (implies (and (syntaxp (acl2::want-to-strengthen (< acl2::x (+ 1 acl2::y))))
                  (integerp acl2::x)
                  (integerp acl2::y))
             (equal (< acl2::x (+ 1 acl2::y))
                    (<= acl2::x acl2::y)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm conditionpassed-of-set-reg
  (equal (conditionpassed cond (set-reg n val arm))
         (conditionpassed cond arm))
  :hints (("Goal" :in-theory (enable conditionpassed))))

(defthm conditionpassed-of-write
  (equal (conditionpassed cond (write n addr val arm))
         (conditionpassed cond arm))
  :hints (("Goal" :in-theory (enable conditionpassed))))

;; Here we recharacterize conditionpassed.  This scheme can result in fewer
;; branches during symbolic execution compared to just opening everything up
;; (consider the complex conditions like gt-condition).

(defund eq-condition (z) (declare (xargs :guard (bitp z))) (== z 1))
(defund ne-condition (z) (declare (xargs :guard (bitp z))) (not (== z 1))) ; or do (== z 0)

(defund cs-condition (c) (declare (xargs :guard (bitp c))) (== c 1))
(defund cc-condition (c) (declare (xargs :guard (bitp c))) (== c 0))

(defund mi-condition (n) (declare (xargs :guard (bitp n))) (== n 1))
(defund pl-condition (n) (declare (xargs :guard (bitp n))) (== n 0))

(defund vs-condition (v) (declare (xargs :guard (bitp v))) (== v 1))
(defund vc-condition (v) (declare (xargs :guard (bitp v))) (== v 0))

(defund hi-condition (c z) (declare (xargs :guard (and (bitp c) (bitp z)))) (and (== c 1) (== z 0)))
(defund ls-condition (c z) (declare (xargs :guard (and (bitp c) (bitp z)))) (not (and (== c 1) (== z 0))))

(defund ge-condition (n v) (declare (xargs :guard (and (bitp n) (bitp v)))) (== n v))
(defund lt-condition (n v) (declare (xargs :guard (and (bitp n) (bitp v)))) (not (== n v)))

(defund gt-condition (n v z) (declare (xargs :guard (and (bitp n) (bitp v) (bitp z)))) (and (== n v) (== z 0)))
(defund le-condition (n v z) (declare (xargs :guard (and (bitp n) (bitp v) (bitp z)))) (not (and (== n v) (== z 0))))

(defthm conditionpassed-of-0 (equal (conditionpassed 0 arm) (eq-condition (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed eq-condition))))
(defthm conditionpassed-of-1 (equal (conditionpassed 1 arm) (ne-condition (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed ne-condition))))

(defthm conditionpassed-of-2 (equal (conditionpassed 2 arm) (cs-condition (apsr.c arm))) :hints (("Goal" :in-theory (enable conditionpassed cs-condition))))
(defthm conditionpassed-of-3 (equal (conditionpassed 3 arm) (cc-condition (apsr.c arm))) :hints (("Goal" :in-theory (enable conditionpassed cc-condition))))

(defthm conditionpassed-of-4 (equal (conditionpassed 4 arm) (mi-condition (apsr.n arm))) :hints (("Goal" :in-theory (enable conditionpassed mi-condition))))
(defthm conditionpassed-of-5 (equal (conditionpassed 5 arm) (pl-condition (apsr.n arm))) :hints (("Goal" :in-theory (enable conditionpassed pl-condition))))

(defthm conditionpassed-of-6 (equal (conditionpassed 6 arm) (vs-condition (apsr.v arm))) :hints (("Goal" :in-theory (enable conditionpassed vs-condition))))
(defthm conditionpassed-of-7 (equal (conditionpassed 7 arm) (vc-condition (apsr.v arm))) :hints (("Goal" :in-theory (enable conditionpassed vc-condition))))

(defthm conditionpassed-of-8 (equal (conditionpassed 8 arm) (hi-condition (apsr.c arm) (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed hi-condition))))
(defthm conditionpassed-of-9 (equal (conditionpassed 9 arm) (ls-condition (apsr.c arm) (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed ls-condition))))

(defthm conditionpassed-of-10 (equal (conditionpassed 10 arm) (ge-condition (apsr.n arm) (apsr.v arm))) :hints (("Goal" :in-theory (enable conditionpassed ge-condition))))
(defthm conditionpassed-of-11 (equal (conditionpassed 11 arm) (lt-condition (apsr.n arm) (apsr.v arm))) :hints (("Goal" :in-theory (enable conditionpassed lt-condition))))

(defthm conditionpassed-of-12 (equal (conditionpassed 12 arm) (gt-condition (apsr.n arm) (apsr.v arm) (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed gt-condition))))
(defthm conditionpassed-of-13 (equal (conditionpassed 13 arm) (le-condition (apsr.n arm) (apsr.v arm) (apsr.z arm))) :hints (("Goal" :in-theory (enable conditionpassed le-condition))))

(defthm conditionpassed-of-14 (equal (conditionpassed 14 arm) t) :hints (("Goal" :in-theory (enable conditionpassed))))
(defthm conditionpassed-of-15 (equal (conditionpassed 15 arm) t) :hints (("Goal" :in-theory (enable conditionpassed))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Condition rules for CMP

(local
 (defthmd cmp-zero-elim
   (implies (and (unsigned-byte-p 32 x)
                 (unsigned-byte-p 32 y))
            (equal (cmp-zero x y)
                   (bool-to-bit (equal x y))))
   :hints (("Goal" :in-theory (enable cmp-zero acl2::bvnot-becomes-bvminus-of-bvuminus-and-1 acl2::bvminus-becomes-bvplus-of-bvuminus bool-to-bit)))))

(local
 (defthmd cmp-carry-elim
   (implies (and (unsigned-byte-p 32 x)
                 (unsigned-byte-p 32 y))
            (equal (cmp-carry x y)
                   (bool-to-bit (not (bvlt 32 x y)))))
   :hints (("Goal" :in-theory (enable cmp-carry mv-nth-1-of-addwithcarry
                                      bvnot bvplus bvlt lognot acl2::getbit-of-+)))))

;move
;; (local
;;   (defthm sbvlt-32-of-bvminus-1-and-bvminus-1
;;     (implies (and (not (equal x (expt 2 31)))
;;                   (not (equal y (expt 2 31)))
;;                   (unsigned-byte-p 32 x)
;;                 (unsigned-byte-p 32 y))
;;              (equal (sbvlt 32 (bvminus 32 x 1) (bvminus 32 y 1))
;;                     (sbvlt 32 x y)))
;;     :otf-flg t
;;     :hints (("Goal" :in-theory (enable acl2::sbvlt-rewrite bvlt bvplus acl2::bvchop-of-sum-cases)))))

;; todo: improve the rhs? e.g., using sbvlt-32-of-bvminus-1-and-bvminus-1
;; (local
;;  (defthmd cmp-overflow-elim
;;    (implies (and (unsigned-byte-p 32 x)
;;                  (unsigned-byte-p 32 y))
;;             (equal (cmp-overflow x y)
;;                    (bool-to-bit (or ;; see signed-addition-overflowsp:
;;                                  (and (sbvle 32 0 x)
;;                                       (sbvlt 32 (bvminus 32 (bvminus 32 2147483647 x) 1)
;;                                              (bvminus 32 (bvuminus 32 y) 1)))
;;                                  ;; see signed-addition-underflowsp:
;;                                  (and (sbvlt 32 x 0)
;;                                       (sbvlt 32 (bvminus 32 (bvuminus 32 y) 1)
;;                                              (bvminus 32 (bvminus 32 -2147483648 x) 1)))))))
;;    :hints (("Goal" :in-theory (e/d (cmp-overflow addwithcarry-overflow acl2::bvnot-becomes-bvminus-of-bvuminus-and-1)
;;                                    (acl2::bvminus-becomes-bvplus-of-bvuminus))))))

;; When x and y have the same sign, x <s y iff the sign bit of x - y is set
;; (no signed overflow is possible).
; unlocalize and move?
(local
 (defthmd getbit-of-bvminus-top-bit-when-same-sign-32 ; gen the 32!
   (implies (and (equal (getbit 31 x) (getbit 31 y))
                 (unsigned-byte-p 32 x)
                 (unsigned-byte-p 32 y))
            (equal (getbit 31 (bvminus 32 x y))
                   (bool-to-bit (sbvlt 32 x y))))
   :hints (("Goal" :use ((:instance acl2::split-bv (x y) (n 32) (m 31))
                         (:instance acl2::split-bv (x x) (n 32) (m 31)))
                   :in-theory (enable acl2::sbvlt-rewrite bvminus bvplus acl2::getbit-of-+
                                      bvlt acl2::bvchop-of-sum-cases)))))

;localize?
(defthm equal-of-cmp-sign-and-cmp-overflow-becomes-sbvle
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (equal (cmp-sign x y) (cmp-overflow x y))
                  (sbvle 32 y x)))
  :hints (("Goal"
           :use (:instance acl2::split-bv (x y) (n 32) (m 31))
           :in-theory (enable cmp-sign
                              cmp-overflow
                              addwithcarry-overflow
                              acl2::sbvlt-rewrite
                              bvminus
                              bvplus
                              acl2::getbit-of-+
                              bvlt
                              acl2::bvchop-of-sum-cases
                              bvnot
                              ;; bvcat
                              ;; logapp
                              lognot
                              bvuminus))))
;; V = N xor (x <s y).
;; Follows from the existing rule saying N = V iff y <=s x.
(defthmd cmp-overflow-elim-1
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cmp-overflow x y)
                  (acl2::bitxor (getbit 31 (bvminus 32 x y))
                                (acl2::bool-to-bit (sbvlt 32 x y)))))
  :hints (("Goal" :use (equal-of-cmp-sign-and-cmp-overflow-becomes-sbvle
                        (:instance unsigned-byte-p-of-cmp-overflow (size 1)))
                  :cases ((equal 0 (cmp-overflow x y)))
                  :in-theory (e/d (cmp-sign acl2::bool-to-bit)
                                  (equal-of-cmp-sign-and-cmp-overflow-becomes-sbvle
                                   unsigned-byte-p-of-cmp-overflow)))))

;; V = sign bit of (x xor y) and (x xor (x - y)).
(defthmd cmp-overflow-elim-2
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cmp-overflow x y)
                  (getbit 31 (bvand 32 (bvxor 32 x y) (bvxor 32 x (bvminus 32 x y))))))
  :hints (("Goal" :cases ((equal (getbit 31 x) (getbit 31 y)))
                  :in-theory (enable getbit-of-bvminus-top-bit-when-same-sign-32
                                     acl2::sbvlt-rewrite
                                     cmp-overflow-elim-1))))

;; The 14 rules for CMP:

(defthm eq-condition-of-cmp-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (eq-condition (cmp-zero x y))
                  (equal x y)))
  :hints (("Goal" :in-theory (enable eq-condition cmp-zero-elim))))

(defthm ne-condition-of-cmp-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (ne-condition (cmp-zero x y))
                  (not (equal x y))))
  :hints (("Goal" :in-theory (enable ne-condition cmp-zero-elim))))

(defthm cs-condition-of-cmp-carry
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cs-condition (cmp-carry x y))
                  (not (bvlt 32 x y))))
  :hints (("Goal" :in-theory (enable cs-condition cmp-carry-elim))))

(defthm cc-condition-of-cmp-carry
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cc-condition (cmp-carry x y))
                  (bvlt 32 x y)))
  :hints (("Goal" :in-theory (enable cc-condition cmp-carry-elim))))

(defthm mi-condition-of-cmp-sign
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (mi-condition (cmp-sign x y))
                  ;; todo: nicer form?:
                  (equal 1 (getbit 31 (bvminus 32 x y)))))
  :hints (("Goal" :in-theory (enable mi-condition cmp-sign))))

(defthm pl-condition-of-cmp-sign
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (pl-condition (cmp-sign x y))
                  ;; todo: nicer form?:
                  (equal 0 (getbit 31 (bvminus 32 x y)))))
  :hints (("Goal" :in-theory (enable pl-condition cmp-sign))))

;; todo: improve RHS?
;; todo: special case for same sign?
(defthm vs-condition-of-cmp-overflow
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (vs-condition (cmp-overflow x y))
                  (not (equal (getbit 31 (bvminus 32 x y))
                              (bool-to-bit (sbvlt 32 x y))))))
  :hints (("Goal" :in-theory (enable vs-condition cmp-overflow-elim-1))))

;; todo: improve RHS?
;; todo: special case for same sign?
(defthm vc-condition-of-cmp-overflow
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (vc-condition (cmp-overflow x y))
                  (equal (getbit 31 (bvminus 32 x y))
                         (bool-to-bit (sbvlt 32 x y)))))
  :hints (("Goal" :in-theory (enable vc-condition cmp-overflow-elim-1))))

(defthm hi-condition-of-cmp-carry-and-cmp-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (hi-condition (cmp-carry x y) (cmp-zero x y))
                  (not (bvle 32 x y))))
  :hints (("Goal" :in-theory (enable hi-condition cmp-zero-elim cmp-carry-elim))))

(defthm ls-condition-of-cmp-carry-and-cmp-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (ls-condition (cmp-carry x y) (cmp-zero x y))
                  (bvle 32 x y)))
  :hints (("Goal" :in-theory (enable ls-condition cmp-zero-elim cmp-carry-elim))))

(defthm le-condition-cmp-idiom
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (le-condition (cmp-sign x y) (cmp-overflow x y) (cmp-zero x y))
                  (sbvle 32 x y)))
  :hints (("Goal" :in-theory (enable le-condition cmp-zero-elim sbvlt-when-not-equal-weaken))))

(defthm gt-condition-cmp-idiom
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (gt-condition (cmp-sign x y) (cmp-overflow x y) (cmp-zero x y))
                  (sbvlt 32 y x)))
  :hints (("Goal" :in-theory (enable gt-condition cmp-zero-elim sbvlt-when-not-equal-weaken))))

(defthm ge-condition-cmp-idiom
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (ge-condition (cmp-sign x y) (cmp-overflow x y))
                  (sbvge 32 x y)))
  :hints (("Goal" :in-theory (enable ge-condition cmp-zero-elim sbvlt-when-not-equal-weaken))))

(defthm lt-condition-cmp-idiom
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (lt-condition (cmp-sign x y) (cmp-overflow x y))
                  (sbvlt 32 x y)))
  :hints (("Goal" :in-theory (enable lt-condition cmp-zero-elim sbvlt-when-not-equal-weaken))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Condition rules for CMN

(local
 (defthmd cmn-zero-elim
   (implies (and (unsigned-byte-p 32 x)
                 ;; (unsigned-byte-p 32 y)
                 )
            (equal (cmn-zero x y)
                   (bool-to-bit (equal x (bvuminus 32 y)))))
   :hints (("Goal" :in-theory (enable cmn-zero bvplus bvuminus acl2::bvchop-of-sum-cases bool-to-bit)))))

(local
 (defthmd cmn-carry-elim
   (implies (and (unsigned-byte-p 32 x)
                 (unsigned-byte-p 32 y))
            (equal (cmn-carry x y)
                   (bool-to-bit (bvle 33 (expt 2 32) (bvplus 33 x y)))))
   :hints (("Goal" :in-theory (enable cmn-carry
                                      mv-nth-1-of-addwithcarry
                                      bvnot bvplus bvlt lognot acl2::getbit-of-+)))))

(defthm bitp-of-cmn-carry-type
  (bitp (cmn-carry x y))
  :rule-classes :type-prescription)

(defthm eq-condition-of-cmn-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (eq-condition (cmn-zero x y))
                  (equal x (bvuminus 32 y))))
  :hints (("Goal" :in-theory (enable eq-condition
                                     cmn-zero-elim))))

(defthm ne-condition-of-cmn-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (ne-condition (cmn-zero x y))
                  (not (equal x (bvuminus 32 y)))))
  :hints (("Goal" :in-theory (enable ne-condition
                                     cmn-zero-elim))))

;; nice if y is constant
(defthm cs-condition-of-cmn-carry
  (implies (and (syntaxp (quotep y))
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cs-condition (cmn-carry x y))
                  (and (not (equal y 0))
                       (not (bvlt 32 x (bvuminus 32 y))))))
  :hints (("Goal" :in-theory (enable cs-condition cmn-carry-elim bvlt bvplus bvuminus acl2::bvchop-of-sum-cases))))

(defthm cs-condition-of-cmn-carry-alt
  (implies (and (syntaxp (not (quotep y))) ; for constant y, the other rule is better
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cs-condition (cmn-carry x y))
                  (bvlt 32 (bvplus 32 x y) x)))
  :hints (("Goal" :in-theory (enable cs-condition cmn-carry-elim bvlt bvplus bvuminus acl2::bvchop-of-sum-cases))))

;; nice if y is constant
(defthm cc-condition-of-cmn-carry
  (implies (and (syntaxp (quotep y))
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cc-condition (cmn-carry x y))
                  (or (equal y 0)
                      (bvlt 32 x (bvuminus 32 y)))))
  :hints (("Goal" :use cs-condition-of-cmn-carry
                  :in-theory (e/d (cs-condition cc-condition) (cs-condition-of-cmn-carry)))))

(defthm cc-condition-of-cmn-carry-alt
  (implies (and (syntaxp (not (quotep y))) ; for constant y, the other rule is better
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cc-condition (cmn-carry x y))
                  (not (bvlt 32 (bvplus 32 x y) x))))
  :hints (("Goal" :use cs-condition-of-cmn-carry
                  :in-theory (e/d (cs-condition cc-condition) (cs-condition-of-cmn-carry)))))

(defthm mi-condition-of-cmn-sign
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (mi-condition (cmn-sign x y))
                  (sbvlt 32 (bvplus 32 x y) 0)))
  :hints (("Goal" :in-theory (enable mi-condition cmn-sign acl2::sbvlt-rewrite))))

(defthm pl-condition-of-cmn-sign
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (pl-condition (cmn-sign x y))
                  (sbvle 32 0 (bvplus 32 x y))))
  :hints (("Goal" :use mi-condition-of-cmn-sign
                  :in-theory (e/d (mi-condition pl-condition) (mi-condition-of-cmn-sign)))))

;; The overflow flag says that the 32-bit sum differs from the true signed sum.
(local
 (defthmd cmn-overflow-elim-logext
   (implies (and (unsigned-byte-p 32 x)
                 (unsigned-byte-p 32 y))
            (equal (cmn-overflow x y)
                   (bool-to-bit (not (equal (logext 32 (bvplus 32 x y))
                                            (+ (logext 32 x) (logext 32 y)))))))
   :hints (("Goal" :use (:instance mv-nth-2-of-addwithcarry (n 32) (carry_in 0))
                   :in-theory (e/d (cmn-overflow addwithcarry sint uint bvplus bool-to-bit)
                                   (mv-nth-2-of-addwithcarry))))))

;move
(local
 (defthmd getbit-31-when-unsigned-byte-p-32
   (implies (unsigned-byte-p 32 v)
            (equal (getbit 31 v)
                   (if (< v 2147483648) 0 1)))
   :hints (("Goal" :use (:instance acl2::bvchop-top-bit-cases (size 32) (x v))
                   :in-theory (e/d (bvcat acl2::logapp) (acl2::bvchop-top-bit-cases))))))

;move
(local
 (defthmd logext-32-when-unsigned-byte-p-32
   (implies (unsigned-byte-p 32 v)
            (equal (logext 32 v)
                   (if (< v 2147483648) v (- v 4294967296))))
   :hints (("Goal" :use (:instance acl2::bvchop-top-bit-cases (size 32) (x v))
                   :in-theory (e/d (acl2::logext-cases bvcat acl2::logapp getbit-31-when-unsigned-byte-p-32)
                                   (acl2::bvchop-top-bit-cases))))))

;; AI: Keeps the sum's wrap-around explicit, so that later proofs need not open bvplus.
(local
 (defthmd logext-32-of-bvplus-32
   (implies (and (unsigned-byte-p 32 x)
                 (unsigned-byte-p 32 y))
            (equal (logext 32 (bvplus 32 x y))
                   (let ((s (if (< (+ x y) 4294967296) (+ x y) (- (+ x y) 4294967296))))
                     (if (< s 2147483648) s (- s 4294967296)))))
   :hints (("Goal" :use (:instance logext-32-when-unsigned-byte-p-32 (v (bvplus 32 x y)))
                   :in-theory (enable bvplus acl2::bvchop-of-sum-cases)))))

;; AI: Signed overflow of x + y, as a BV comparison: the 32-bit sum is less than x
;; exactly when y is negative, unless the addition overflowed.
(local
 (defthmd cmn-overflow-elim
   (implies (and (unsigned-byte-p 32 x)
                 (unsigned-byte-p 32 y))
            (equal (cmn-overflow x y)
                   (bool-to-bit (not (equal (sbvlt 32 (bvplus 32 x y) x)
                                            (sbvlt 32 y 0))))))
   :hints (("Goal" :cases ((< (+ x y) 4294967296))
                   :in-theory (enable cmn-overflow-elim-logext
                                      logext-32-of-bvplus-32
                                      logext-32-when-unsigned-byte-p-32
                                      sbvlt)))))

(defthm vs-condition-of-cmn-overflow
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (vs-condition (cmn-overflow x y))
                  (if (sbvlt 32 y 0)
                      (not (sbvlt 32 (bvplus 32 x y) x))
                    (sbvlt 32 (bvplus 32 x y) x))))
  :hints (("Goal" :in-theory (enable vs-condition cmn-overflow-elim))))

(defthm vc-condition-of-cmn-overflow
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (vc-condition (cmn-overflow x y))
                  (if (sbvlt 32 y 0)
                      (sbvlt 32 (bvplus 32 x y) x)
                    (not (sbvlt 32 (bvplus 32 x y) x)))))
  :hints (("Goal" :in-theory (enable vc-condition cmn-overflow-elim))))

(defthm hi-condition-of-cmn-carry-and-cmn-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (hi-condition (cmn-carry x y) (cmn-zero x y))
                  (and (not (equal y 0))
                       (not (bvle 32 x (bvuminus 32 y))))))
  :hints (("Goal" :in-theory (enable hi-condition cmn-carry-elim cmn-zero-elim bvlt bvplus bvuminus acl2::bvchop-of-sum-cases))))

(defthm ls-condition-of-cmn-carry-and-cmn-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (ls-condition (cmn-carry x y) (cmn-zero x y))
                  (or (equal y 0)
                      (bvle 32 x (bvuminus 32 y)))))
  :hints (("Goal" :in-theory (enable ls-condition cmn-carry-elim cmn-zero-elim bvlt bvplus bvuminus acl2::bvchop-of-sum-cases))))

;; N = V iff the true signed sum is non-negative.
(local
 (defthmd equal-of-cmn-sign-and-cmn-overflow-helper
   (implies (and (unsigned-byte-p 32 x)
                 (unsigned-byte-p 32 y))
            (equal (equal (cmn-sign x y) (cmn-overflow x y))
                   (<= 0 (+ (logext 32 x) (logext 32 y)))))
   :hints (("Goal" :cases ((< (+ x y) 4294967296))
                   :in-theory (enable cmn-sign cmn-overflow-elim-logext
                                      getbit-31-when-unsigned-byte-p-32
                                      logext-32-when-unsigned-byte-p-32
                                      bvplus acl2::bvchop-of-sum-cases)))))

;; Analogous to equal-of-cmp-sign-and-cmp-overflow-becomes-sbvle.
;; AI: The check for y = 2^31 is needed because
;; then -y does not exist: x + y >= 0 is false for every x, but
;; (sbvle 32 (bvuminus 32 y) x) is true for every x.
(defthm equal-of-cmn-sign-and-cmn-overflow-becomes-sbvle
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (equal (cmn-sign x y) (cmn-overflow x y))
                  (and (not (equal y 2147483648))
                       (sbvle 32 (bvuminus 32 y) x))))
  :hints (("Goal" :cases ((equal y 0) (< y 2147483648))
                  :in-theory (enable equal-of-cmn-sign-and-cmn-overflow-helper
                                     logext-32-when-unsigned-byte-p-32
                                     sbvlt bvuminus))))

(defthm ge-condition-cmn-idiom
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (ge-condition (cmn-sign x y) (cmn-overflow x y))
                  (and (not (equal y 2147483648))
                       (sbvge 32 x (bvuminus 32 y)))))
  :hints (("Goal" :in-theory (enable ge-condition))))

(defthm lt-condition-cmn-idiom
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (lt-condition (cmn-sign x y) (cmn-overflow x y))
                  (or (equal y 2147483648)
                      (sbvlt 32 x (bvuminus 32 y)))))
  :hints (("Goal" :in-theory (enable lt-condition))))

(defthm gt-condition-cmn-idiom
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (gt-condition (cmn-sign x y) (cmn-overflow x y) (cmn-zero x y))
                  (and (not (equal y 2147483648))
                       (sbvlt 32 (bvuminus 32 y) x))))
  :hints (("Goal" :in-theory (enable gt-condition cmn-zero-elim sbvlt-when-not-equal-weaken))))

(defthm le-condition-cmn-idiom
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (le-condition (cmn-sign x y) (cmn-overflow x y) (cmn-zero x y))
                  (or (equal y 2147483648)
                      (sbvle 32 x (bvuminus 32 y)))))
  :hints (("Goal" :in-theory (enable le-condition cmn-zero-elim sbvlt-when-not-equal-weaken))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Condition rules for SUB

;; (local
;;  (defthmd sub-carry-elim
;;    (implies (and (unsigned-byte-p 32 x)
;;                  (unsigned-byte-p 32 y))
;;             (equal (sub-carry x y)
;;                    (bool-to-bit (bvle 32 y x))))
;;    :hints (("Goal" :in-theory (enable sub-carry
;;                                       mv-nth-1-of-addwithcarry
;;                                       bvnot bvplus bvlt lognot acl2::getbit-of-+)))))

;; (defthm eq-condition-of-sub-zero
;;   (implies (and (unsigned-byte-p 32 x)
;;                 (unsigned-byte-p 32 y))
;;            (equal (eq-condition (sub-zero x y))
;;                   (equal x y)))
;;   :hints (("Goal" :in-theory (enable eq-condition
;;                                      sub-zero
;;                                      bvplus bvnot lognot acl2::bvchop-of-sum-cases))))

;; (defthm ne-condition-of-sub-zero
;;   (implies (and (unsigned-byte-p 32 x)
;;                 (unsigned-byte-p 32 y))
;;            (equal (ne-condition (sub-zero x y))
;;                   (not (equal x y))))
;;   :hints (("Goal" :in-theory (enable ne-condition
;;                                      sub-zero
;;                                      bvplus bvnot lognot acl2::bvchop-of-sum-cases))))

;; (defthm cs-condition-of-sub-carry
;;   (implies (and (unsigned-byte-p 32 x)
;;                 (unsigned-byte-p 32 y))
;;            (equal (cs-condition (sub-carry x y))
;;                   (bvle 32 y x)))
;;   :hints (("Goal" :in-theory (enable cs-condition sub-carry-elim))))

;; (defthm cc-condition-of-sub-carry
;;   (implies (and (unsigned-byte-p 32 x)
;;                 (unsigned-byte-p 32 y))
;;            (equal (cc-condition (sub-carry x y))
;;                   (not (bvle 32 y x))))
;;   :hints (("Goal" :in-theory (enable cs-condition sub-carry-elim))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::def-constant-opener eq-condition)
(acl2::def-constant-opener ne-condition)
(acl2::def-constant-opener cs-condition)
(acl2::def-constant-opener cc-condition)
(acl2::def-constant-opener mi-condition)
(acl2::def-constant-opener pl-condition)
(acl2::def-constant-opener vs-condition)
(acl2::def-constant-opener vc-condition)
(acl2::def-constant-opener hi-condition)
(acl2::def-constant-opener ls-condition)
(acl2::def-constant-opener ge-condition)
(acl2::def-constant-opener lt-condition)
(acl2::def-constant-opener gt-condition)
(acl2::def-constant-opener le-condition)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; restrict to constant k?
(defthm getbit-32-of-bvplus-helper
  (implies (and (< (expt 2 31) k) ; k is "negative"
                (unsigned-byte-p 32 k)
                ;(sbvle 32 0 x) ; todo: generalize?
                (unsigned-byte-p 32 x))
           (equal (getbit 32 (bvplus 33 k x))
                  (if (sbvle 32 0 x)
                      (bool-to-bit (sbvle 32 (- k) x))
                  1)))
  :hints (("Goal" :in-theory (enable acl2::sbvlt-rewrite bvplus acl2::getbit-of-+ bvlt))))

(local
 (defthmd bvplus-33-when-unsigned-byte-p-32
   (implies (unsigned-byte-p 32 (bvplus 33 x y))
            (equal (bvplus 33 x y)
                   (bvplus 32 x y)))))

;; todo: instead have bvchop-identity-axe know about bv-list-read-chunk-little
(defthm acl2::bvchop-32-of-bv-list-read-chunk-little
  (equal (bvchop '32 (bv-list-read-chunk-little '8 '4 i array))
         (bv-list-read-chunk-little '8 '4 i array)))

(local (include-book "kestrel/bv/rules" :dir :system))
(local (in-theory (enable acl2::bvplus-commutative-2-sizes-differ)))

;drop?
;todo: subgoal hints
;; often y and carry_in are constants.
;; todo: how do we know whether we want sbvlt or bvlt expressions in the RHS?
(defthm mv-nth-1-of-addwithcarry-special
  (implies (and (< (expt 2 31) (bvplus 33 carry_in y))
                (unsigned-byte-p 32 (bvplus 33 carry_in y))
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (bitp carry_in))
           (equal (mv-nth '1 (addwithcarry '32 x y carry_in))
                  (if (if (sbvle 32 0 x) ; todo: generalize?
                          (sbvle 32 (- (expt 2 32) (bvplus 32 y carry_in)) x)
                        t)
                      1 0)
;                  (getbit 32 (bvplus 33 carry_in (bvplus 33 x y)))
                  ))
  :hints (;("subgoal 2" :use (:instance bvplus-33-when-unsigned-byte-p-32 (x carry_in)))
          ("subgoal 2" :in-theory (enable bvplus-33-when-unsigned-byte-p-32))
          ("subgoal 1" :in-theory (enable bvplus-33-when-unsigned-byte-p-32))
          ("subgoal 3'" :in-theory (enable bvplus-33-when-unsigned-byte-p-32))
          ("Goal" :use ((:instance getbit-32-of-bvplus-helper (k (bvplus 33 carry_in y)))
                        ;(:instance bvplus-33-linear-when-unsigned-byte-p-32 (x carry_in))
                        )
                  :cases ((equal carry_in 0) (equal carry_in 1))
                  :in-theory (e/d (;bvplus-33-when-unsigned-byte-p-32
                                   )
                                  (getbit-32-of-bvplus-helper
                                   ;acl2::unsigned-byte-p-of-bvplus-tighten
                                   acl2::unsigned-byte-p-from-bounds
                                   acl2::unsigned-byte-p-from-bound
                                   ;; acl2::unsigned-byte-p-when-unsigned-byte-p-smaller
                                   acl2::unsigned-byte-p-of-+-of-minus ;drop?
                                   )))))

(defthm mv-nth-1-of-addwithcarry-combine-constants
  (implies (and (syntaxp (quotep k1))
                (not (equal k2 0))                 ; prevents loops
                (not (and ;(equal carry_in 1)
                          (equal k1 (+ -1 (expt 2 32))))) ;todo
                (bitp k2)
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 k1))
           (equal (mv-nth 1 (addwithcarry '32 x k1 k2))
                  (mv-nth 1 (addwithcarry '32 x (+ k1 k2) 0))))
  :hints (("Goal" :in-theory (enable addwithcarry uint))))

; (defstub foo (x y) t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; or we could make a version of acl2::getbit-identity-axe that "knows" about these function
(defthm getbit-0-of-cmp-carry
  (equal (getbit 0 (cmp-carry x y))
         (cmp-carry x y)))

(defthm getbit-0-of-cmp-zero
  (equal (getbit 0 (cmp-zero x y))
         (cmp-zero x y)))

(defthm getbit-0-of-cmp-sign
  (equal (getbit 0 (cmp-sign x y))
         (cmp-sign x y)))

(defthm getbit-0-of-cmp-overflow
  (equal (getbit 0 (cmp-overflow x y))
         (cmp-overflow x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; todo: more like this
;; (defthm lt-condition-of-sub-sign-and-sub-overflow
;;   (implies (and (unsigned-byte-p 32 x)
;;                 (unsigned-byte-p 32 y))
;;            (equal (lt-condition (sub-sign x y) (sub-overflow x y))
;;                   (sbvlt 32 x y)))
;;   :hints (("Goal" :in-theory (enable lt-condition sub-sign sub-overflow addwithcarry uint sint
;;                                      acl2::bvchop-of-sum-cases
;;                                      sbvlt
;;                                      bvlt
;;                                      bvnot
;;                                      bvplus
;;                                      lognot
;;                                      acl2::logext-cases
;;                                      acl2::getbit-of-+))))
