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

(defthmd cmn-zero-elim
  (implies (and (unsigned-byte-p 32 x)
                ;; (unsigned-byte-p 32 y)
                )
           (equal (cmn-zero x y)
                  (bool-to-bit (equal x (bvuminus 32 y)))))
  :hints (("Goal" :in-theory (enable cmn-zero bvplus bvuminus acl2::bvchop-of-sum-cases bool-to-bit))))

(defthmd cmp-zero-elim
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cmp-zero x y)
                  (bool-to-bit (equal x y))))
  :hints (("Goal" :in-theory (enable cmp-zero acl2::bvnot-becomes-bvminus-of-bvuminus-and-1 bool-to-bit))))

(defthmd cmn-carry-elim
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cmn-carry x y)
                  (bool-to-bit (bvle 33 (expt 2 32) (bvplus 33 x y)))))
  :hints (("Goal" :in-theory (enable cmn-carry
                                     mv-nth-1-of-addwithcarry
                                     bvnot bvplus bvlt lognot acl2::getbit-of-+))))

(defthmd cmp-carry-elim
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cmp-carry x y)
                  (bool-to-bit (not (bvlt 32 x y)))))
  :hints (("Goal" :in-theory (enable cmp-carry mv-nth-1-of-addwithcarry
                                     bvnot bvplus bvlt lognot acl2::getbit-of-+))))

(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
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
(defthmd cmp-overflow-elim
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (cmp-overflow x y)
                  (bool-to-bit (or ;; see signed-addition-overflowsp:
                                 (and (sbvle 32 0 x)
                                      (sbvlt 32 (bvminus 32 (bvminus 32 2147483647 x) 1)
                                             (bvminus 32 (bvuminus 32 y) 1)))
                                 ;; see signed-addition-underflowsp:
                                 (and (sbvlt 32 x 0)
                                      (sbvlt 32 (bvminus 32 (bvuminus 32 y) 1)
                                             (bvminus 32 (bvminus 32 -2147483648 x) 1)))))))
  :hints (("Goal" :in-theory (e/d (cmp-overflow addwithcarry-overflow acl2::bvnot-becomes-bvminus-of-bvuminus-and-1)
                                  (acl2::bvminus-becomes-bvplus-of-bvuminus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm eq-condition-of-cmp-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (eq-condition (cmp-zero x y))
                  (equal x y)))
  :hints (("Goal" :in-theory (enable eq-condition
                                     cmp-zero-elim))))

(defthm ne-condition-of-cmp-zero
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (ne-condition (cmp-zero x y))
                  (not (equal x y))))
  :hints (("Goal" :in-theory (enable ne-condition
                                     cmp-zero-elim))))

;; todo: need more of these!
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
   (implies (and (unsigned-byte-p 32 x)
                 (integerp y))
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

(defthm equal-of-cmp-sign-and-cmp-overflow-becomes-sbvle
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (equal (cmp-sign x y) (cmp-overflow x y))
                  (sbvle 32 y x)))
  :hints (("Goal"
           :use (:instance acl2::split-bv (x y) (n 32) (m 31))
           :in-theory (e/d (cmp-sign
                            cmp-overflow
                            addwithcarry-overflow
                            acl2::sbvlt-rewrite
                            bvminus
                            bvplus
                            acl2::getbit-of-+
                            bvlt
                            acl2::bvchop-of-sum-cases
                            bvnot
                            ;bvcat
                            ;logapp
                            lognot
                            bvuminus)
                           ()))))

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
(local (include-book "kestrel/axe/rules3" :dir :system)) ; todo: reduce, for acl2::bvplus-commutative-2-sizes-differ

;drop?
;todo: subgoal hints
;; often y and carry_in are constants.
;; todo: how do we know whether we want sbvlt or bvlt expressions in the RHS?
(defthm mv-nth-1-of-addwithcarry-special
  (implies (and (< (expt 2 31) (bvplus 33 carry_in y))
                (unsigned-byte-p 32 (bvplus 33 carry_in y))
                (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y)
                (unsigned-byte-p 32 (bvplus 33 carry_in y))
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
