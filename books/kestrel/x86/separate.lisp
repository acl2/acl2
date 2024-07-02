; Mixed x86 supporting material
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA") ;todo: use X package?

(include-book "projects/x86isa/proofs/utilities/disjoint" :dir :system)
(include-book "projects/x86isa/machine/application-level-memory" :dir :system) ; for canonical-address-p
(include-book "kestrel/bv/bvchop" :dir :system)

;; todo: drop these irrelevant params from separate
(defthm separate-normalize-r-w-x-1
  (implies (not (eq r-w-x-1 :r)) ;not using syntaxp since axe could not handle that
           (equal (separate r-w-x-1 n-1 addr-1 r-w-x-2 n-2 addr-2)
                  (separate :r n-1 addr-1 r-w-x-2 n-2 addr-2)))
  :hints (("Goal" :in-theory (enable separate))))

;; todo: drop these irrelevant params from separate
(defthm separate-normalize-r-w-x-2
  (implies (not (eq r-w-x-2 :r)) ;not using syntaxp since axe could not handle that
           (equal (separate r-w-x-1 n-1 addr-1 r-w-x-2 n-2 addr-2)
                  (separate r-w-x-1 n-1 addr-1 :r n-2 addr-2)))
  :hints (("Goal" :in-theory (enable separate))))

;(in-theory (enable x86-fetch-decode-execute)) ;needed for code proofs (no, use the opener?)

(defthm not-separate-self
  (implies (and (posp n)
                (posp n2))
           (not (separate rwx n addr rwx2 n2 addr)))
  :hints (("Goal" :in-theory (enable separate))))

;gen the 1 here:

(defthm separate-of-plus
  (implies (and (separate :r n text-offset ;n is a free var
                          :r n2+ x)
                (< k n)
                (<= n2 n2+)
                (natp n2+)
                (natp k)
                (natp n))
           (separate :r 1 (+ k text-offset)
                     :r n2 x))
  :hints (("Goal" :in-theory (enable separate))))

;reorders the hyp...
(defthm separate-of-plus-alt
  (implies (and (separate :r n2+ x
                          :r n text-offset ;n is a free var
                          )
                (<= n2 n2+)
                (natp n2+)
                (< k n)
                (natp k)
                (natp n))
           (separate :r 1 (+ k text-offset)
                     :r n2 x))
  :hints (("Goal" :in-theory (enable separate))))


(defthm separate-below-and-above
  (implies (and (<= k1 0)
                (<= k2 (- k1))
                (integerp k1)
                (integerp k2)
                )
           (separate rwx1 k2 (+ k1 x) ;this stuff is below x
                     rwx2 j x)) ;this stuff is above x
  :hints (("Goal" :in-theory (enable separate))))

(defthm separate-below-and-above-alt
  (implies (and (<= k1 0)
                (<= k2 (- k1))
                (integerp k1)
                (integerp k2)
                )
           (separate rwx2 j x
                     rwx1 k2 (+ k1 x)))
  :hints (("Goal" :in-theory (enable separate))))

(defthm separate-below-and-above-offset
  (implies (and (integerp k)
                (integerp k2)
                (<= (+ k n) k2))
           (separate :r n2 (+ k2 x)
                     :r n (+ k x)))
  :hints (("Goal" :in-theory (enable separate))))

(defthm separate-below-and-above-offset-alt
  (implies (and (integerp k)
                (integerp k2)
                (<= (+ k n) k2))
           (separate :r n (+ k x)
                     :r n2 (+ k2 x)))
  :hints (("Goal" :in-theory (enable separate))))

(defthm separate-same-lemma-1
  (implies (and (<= num off2)
                (integerp num)
                (integerp off2))
           (separate :r num x
                     :r num2 (+ off2 x)))
  :hints (("Goal" :in-theory (enable separate))))

(defthm separate-same-lemma-1-alt
  (implies (and (<= num off2)
                (integerp num)
                (integerp off2))
           (separate :r num2 (+ off2 x)
                     :r num x))
  :hints (("Goal" :in-theory (enable separate))))

;gen?
(defthm separate-lemma-1
  (implies (and (separate :r n text-offset
                          :r big (+ bigneg x))
                (natp n)
                (natp off)
                (<= (+ num off) n)
                (equal big (- bigneg))
                (<= small (- smallneg))
                (<= bigneg smallneg)
                (<= 0 small)
                (<= 0 big)
                (integerp smallneg)
                (integerp bigneg)
                (integerp small)
                (integerp big)
                (integerp text-offset))
           (separate :r num (+ off text-offset)
                     :r small (+ smallneg x)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-lemma-1-alt
  (implies (and (separate :r n text-offset
                          :r big (+ bigneg x))
                (natp n)
                (natp off)
                (<= (+ num off) n)
                (equal big (- bigneg))
                (<= small (- smallneg))
                (<= bigneg smallneg)
                (<= 0 small)
                (<= 0 big)
                (integerp smallneg)
                (integerp bigneg)
                (integerp small)
                (integerp big)
                (integerp text-offset))
           (separate :r small (+ smallneg x)
                     :r num (+ off text-offset)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

;no offset
(defthm separate-lemma-1b
  (implies (and (separate :r n text-offset
                          :r big (+ bigneg x))
                (natp n)
                (<= num n)
                (equal big (- bigneg))
                (<= small (- smallneg))
                (<= bigneg smallneg)
                (<= 0 small)
                (<= 0 big)
                (integerp smallneg)
                (integerp bigneg)
                (integerp small)
                (integerp big)
                (integerp text-offset))
           (separate :r num text-offset
                     :r small (+ smallneg x)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-lemma-1b-alt
  (implies (and (separate :r n text-offset
                          :r big (+ bigneg x))
                (natp n)
                (<= num n)
                (equal big (- bigneg))
                (<= small (- smallneg))
                (<= bigneg smallneg)
                (<= 0 small)
                (<= 0 big)
                (integerp smallneg)
                (integerp bigneg)
                (integerp small)
                (integerp big)
                (integerp text-offset))
           (separate :r small (+ smallneg x)
                     :r num text-offset))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))




(defthm separate-of-if-arg3
  (equal (separate rwx1 n1 (if test addr1a addr1b) rwx2 n2 addr2)
         (if test
             (separate rwx1 n1 addr1a rwx2 n2 addr2)
           (separate rwx1 n1 addr1b rwx2 n2 addr2))))

(defthm separate-of-if-arg6
  (equal (separate rwx1 n1 addr1 rwx2 n2 (if test addr2a addr2b))
         (if test
             (separate rwx1 n1 addr1 rwx2 n2 addr2a)
           (separate rwx1 n1 addr1 rwx2 n2 addr2b))))

(defthm separate-lemma-2b
  (implies (and (separate :r n text-offset
                          :r big x)
                (natp n)
                (natp off)
                (<= (+ num off) n)
                (integerp text-offset)
                (natp big)
                (natp off2)
                (<= (+ off2 num2) big)
                (natp num2)
                )
           (separate :r num (+ off text-offset)
                     :r num2 (+ off2 x)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-lemma-2b-alt
  (implies (and (separate :r n text-offset
                          :r big x)
                (natp n)
                (natp off)
                (<= (+ num off) n)
                (integerp text-offset)
                (natp big)
                (natp off2)
                (<= (+ off2 num2) big)
                (natp num2)
                )
           (separate :r num2 (+ off2 x)
                     :r num (+ off text-offset)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))


(defthm separate-lemma-3
  (implies (and (separate :r n text-offset
                          :r big x)
                (natp n)
                (<= num n)
                (integerp text-offset)
                (natp big)
                (natp off2)
                (<= (+ off2 num2) big)
                (natp num2)
                )
           (separate :r num text-offset
                     :r num2 (+ off2 x)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-lemma-3-alt
  (implies (and (separate :r n text-offset
                          :r big x)
                (natp n)
                (<= num n)
                (integerp text-offset)
                (natp big)
                (natp off2)
                (<= (+ off2 num2) big)
                (natp num2)
                )
           (separate :r num2 (+ off2 x)
                     :r num text-offset))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))



;; In this series of lemmas, the assumption about separate contains no offsets:
;; todo: these subsume some things above

(defthm separate-from-separate-lemma-1
  (implies (and (separate rwx3 num3 base1
                          rwx4 num4 base2)
                (<= (+ num1 off1) num3)
                (<= (+ num2 off2) num4)
                (natp num1)
                (natp num2)
                (natp off1)
                (natp off2)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 (+ off1 base1)
                     rwx2 num2 (+ off2 base2)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-from-separate-lemma-1-alt
  (implies (and (separate rwx4 num4 base2
                          rwx3 num3 base1)
                (<= (+ num1 off1) num3)
                (<= (+ num2 off2) num4)
                (natp num1)
                (natp num2)
                (natp off1)
                (natp off2)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 (+ off1 base1)
                     rwx2 num2 (+ off2 base2)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

;off1=0
(defthm separate-from-separate-lemma-1b
  (implies (and (separate rwx3 num3 base1
                          rwx4 num4 base2)
                (<= num1 num3)
                (<= (+ num2 off2) num4)
                (natp num1)
                (natp num2)
                (natp off2)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 base1
                     rwx2 num2 (+ off2 base2)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-from-separate-lemma-1b-alt
  (implies (and (separate rwx4 num4 base2
                          rwx3 num3 base1)
                (<= num1 num3)
                (<= (+ num2 off2) num4)
                (natp num1)
                (natp num2)
                (natp off2)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 base1
                     rwx2 num2 (+ off2 base2)))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

;off2=0
(defthm separate-from-separate-lemma-1c
  (implies (and (separate rwx3 num3 base1
                          rwx4 num4 base2)
                (<= (+ num1 off1) num3)
                (<= num2 num4)
                (natp num1)
                (natp num2)
                (natp off1)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 (+ off1 base1)
                     rwx2 num2 base2))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-from-separate-lemma-1c-alt
  (implies (and (separate rwx4 num4 base2
                          rwx3 num3 base1)
                (<= (+ num1 off1) num3)
                (<= num2 num4)
                (natp num1)
                (natp num2)
                (natp off1)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 (+ off1 base1)
                     rwx2 num2 base2))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

;both off1 and odff2 are 0
(defthm separate-from-separate-lemma-1d
  (implies (and (separate rwx3 num3 base1
                          rwx4 num4 base2)
                (<= num1 num3)
                (<= num2 num4)
                (natp num1)
                (natp num2)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 base1
                     rwx2 num2 base2))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

(defthm separate-from-separate-lemma-1d-alt
  (implies (and (separate rwx4 num4 base2
                          rwx3 num3 base1)
                (<= num1 num3)
                (<= num2 num4)
                (natp num1)
                (natp num2)
                (integerp num3)
                (integerp num4)
                (integerp base1)
                (integerp base2))
           (separate rwx1 num1 base1
                     rwx2 num2 base2))
  :hints (("Goal" :in-theory (e/d (separate)
                                  (;x86isa::RGFI-IS-I64P
                                   )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Quite powerful
;; For when the range starting at ad1 is within the range starting at ad3.
;; Often the Ns will be constant.
(defthm separate-when-separate
  (implies (and (separate rwx n3 ad3 rwx n4 ad4)
                (<= ad3 ad1)
                (<= (- ad1 ad3) (- n3 n1))
                (<= ad4 ad2)
                (<= (- ad2 ad4) (- n4 n2)))
           (separate rwx n1 ad1 rwx n2 ad2))
  :hints (("Goal" :in-theory (enable separate))))

;; Quite powerful
;; For when the range starting at ad1 is within the range starting at ad4.
;; Often the Ns will be constant.
(defthm separate-when-separate-alt
  (implies (and (separate rwx n3 ad3 rwx n4 ad4)
                (<= ad4 ad1)
                (<= (- ad1 ad4) (- n4 n1))
                (<= ad3 ad2)
                (<= (- ad2 ad3) (- n3 n2)))
           (separate rwx n1 ad1 rwx n2 ad2))
  :hints (("Goal" :in-theory (enable separate))))

;; ;drop?!
;; ;todo: compare to X86ISA::SEPARATE-SMALLER-REGIONS
;; (defthm separate-when-separate-2
;;   (implies (and (separate :r n3 addr3 :r n4 addr4) ; free vars
;;                 (<= addr3 addr1)
;;                 (<= n1 (+ n3 (- addr3 addr1)))
;;                 (<= addr4 addr2)
;;                 (<= n2 (+ n4 (- addr4 addr2))))
;;            (separate :r n1 addr1 :r n2 addr2)))

;; May be expensive, but needed if separate-of-1-and-1 fires.
;; TODO: Could add a syntaxp to restrict this to equalities of things that might be addresses.
(defthm not-equal-when-separate
  (implies (and (separate rwx n3 ad3 rwx n4 ad4)
                (<= ad3 ad1)
                (< (- ad1 ad3) n3)
                (<= ad4 ad2)
                (< (- ad2 ad4) n4))
           (not (equal ad1 ad2)))
  :hints (("Goal" :in-theory (enable separate))))

;; May be expensive, but needed if separate-of-1-and-1 fires.
;; TODO: Could add a syntaxp to restrict this to equalities of things that might be addresses.
(defthm not-equal-when-separate-alt
  (implies (and (separate rwx n3 ad3 rwx n4 ad4)
                (<= ad4 ad1)
                (< (- ad1 ad4) n4)
                (<= ad3 ad2)
                (< (- ad2 ad3) n3))
           (not (equal ad1 ad2)))
  :hints (("Goal" :in-theory (enable separate))))

;;If we use this, we probably also need not-equal-when-separate and not-equal-when-separate-alt.
(defthm separate-of-1-and-1
  (implies (and (integerp ad1)
                (integerp ad2))
           (equal (separate :r 1 ad1 :r 1 ad2)
                  (not (equal ad1 ad2))))
  :hints (("Goal" :in-theory (enable separate))))

;; for showing that rsp is not a constant (e.g., the address of an instruction)
(defthm not-equal-constant-when-separate-of-constants
  (implies (and (syntaxp (quotep k))
                ;; n and base typically indicate where the program is:
                (separate rwx1 n base rwx2 stack-size (binary-+ neg-stack-size rsp)) ; stack-size is commonly 800
                (syntaxp (and (quotep base)
                              (quotep n)
                              (quotep neg-stack-size)
                              (quotep stack-size)))
                (< base k) ; strict, since the separate claim doesn't actually cover rsp itself
                (< k (+ n base))
                (equal neg-stack-size (- stack-size))
                (posp stack-size))
           (not (equal k rsp)))
  :hints (("Goal" :in-theory (enable separate))))

;; for showing that rsp is not a constant (e.g., the address of an instruction)
(defthm not-equal-constant-when-separate-of-constants-alt
  (implies (and (syntaxp (quotep k))
                ;; n and base typically indicate where the program is:
                (separate rwx1 n base rwx2 stack-size (binary-+ neg-stack-size rsp)) ; stack-size is commonly 800
                (syntaxp (and (quotep base)
                              (quotep n)
                              (quotep neg-stack-size)
                              (quotep stack-size)))
                (< base k) ; strict, since the separate claim doesn't actually cover rsp itself
                (< k (+ n base))
                (equal neg-stack-size (- stack-size))
                (posp stack-size))
           (not (equal rsp k)))
  :hints (("Goal" :by not-equal-constant-when-separate-of-constants)))

;; not quite true?
(defthm not-equal-constant-and-bvchop-48-when-separate-of-constants
  (implies (and (syntaxp (quotep k))
                ;; n and base typically indicate where the program is:
                (separate rwx1 n base rwx2 stack-size (binary-+ neg-stack-size rsp)) ; stack-size is commonly 800
                (syntaxp (and (quotep base)
                              (quotep n)
                              (quotep neg-stack-size)
                              (quotep stack-size)))
                (< base k) ; strict, since the separate claim doesn't actually cover rsp itself
                (< k (+ n base))
                (equal neg-stack-size (- stack-size))
                (posp stack-size)
                (canonical-address-p rsp)
                (canonical-address-p (+ (- stack-size) rsp))
                (natp base) (integerp n)
                (equal 0 base) ; !!
                (< k stack-size)
                )
           (not (equal k (acl2::bvchop 48 rsp))))
  :hints (("Goal" :in-theory (enable separate canonical-address-p acl2::bvchop-when-signed-byte-p signed-byte-p))))

(defthm not-equal-constant-and-bvchop-48-when-separate-of-constants-alt
  (implies (and (syntaxp (quotep k))
                ;; n and base typically indicate where the program is:
                (separate rwx1 n base rwx2 stack-size (binary-+ neg-stack-size rsp)) ; stack-size is commonly 800
                (syntaxp (and (quotep base)
                              (quotep n)
                              (quotep neg-stack-size)
                              (quotep stack-size)))
                (< base k) ; strict, since the separate claim doesn't actually cover rsp itself
                (< k (+ n base))
                (equal neg-stack-size (- stack-size))
                (posp stack-size)
                (canonical-address-p rsp)
                (canonical-address-p (+ (- stack-size) rsp))
                (natp base) (integerp n)
                (equal 0 base) ; !!
                (< k stack-size)
                )
           (not (equal (acl2::bvchop 48 rsp) k)))
  :hints (("Goal" :use not-equal-constant-and-bvchop-48-when-separate-of-constants
           :in-theory (disable not-equal-constant-and-bvchop-48-when-separate-of-constants))))
