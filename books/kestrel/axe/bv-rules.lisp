; Bit-vector rules
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/rules6" :dir :system)
(local (include-book "kestrel/library-wrappers/arithmetic-top-with-meta" :dir :system))

(local (in-theory (disable expt)))

;yuck?
(defthm bvcat-bvxor-neighbors-hack3
  (implies (and (equal low2 (+ 1 high))
                (equal j (+ high 1 (- low)))
                (equal k (+ high2 1 (- low2)))
                (<= low high)
                (<= low2 high2)
                (natp high)
                (natp low)
                (natp high2)
                (natp low2)
                )
           (equal (bvcat k
                         (BVXOR k (slice high2 low2 y) (slice high2 low2 x)) j
                         (BVXOR j (slice high low y) (slice high low x)))
                  (bvxor (+ 1 high2 (- low))
                         (slice high2 low y)
                         (slice high2 low x))))
  :hints (("Goal" :use ()
           :in-theory (e/d (;bvxor
                            )
                           ( ;BVXOR-TRIM-ARG1 ;BVXOR-CANCEL BVXOR-CANCEL-alt BVXOR-CANCEL-cross-2
                            ))) ;why the disables?
          ))


;yuck..
(defthmd bvcat-bvxor-neighbors-hack4
  (implies (and (equal n (+ 1 high))
                (equal j (+ high 1 (- low)))
                (natp high)
                (natp n)
                (natp low)
                (<= low high)
                )
           (equal (bvcat
                   1
                   (BVXOR 1 (getbit n y) (getbit n x)) j
                   (BVXOR j (slice high low y) (slice high low x)))
                  (bvxor (+ 1 n (- low))
                         (slice n low y)
                         (slice n low x))))
  :hints (("Goal" :use ((:instance bvcat-bvxor-neighbors-hack3 (high2 n) (low2 n) (k 1)))
           :in-theory (disable bvcat-bvxor-neighbors-hack3))))

;; Used in CLAIM!
(DEFTHMd BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P-non-const
  (IMPLIES (AND ;(SYNTAXP (CONSTANT-SYNTAXP SIZE))
                (< 0 SIZE)
                (UNSIGNED-BYTE-P (1- SIZE) I))
           (SIGNED-BYTE-P SIZE I))
  :HINTS
  (("Goal" :IN-THEORY (E/d (SIGNED-BYTE-P UNSIGNED-BYTE-P) (;HACK-6
                                                            )))))

;fixme pretty special purpose
(defthm bvif-hack
  (equal (bvif 8 test1
               (bvif 8 test2 a b)
               (bvif 8 test2 b a))
         (bvif 8 (xor test1 test2)
               b
               a))
  :hints (("Goal" :in-theory (e/d (xor bvif myif) (;bvchop-bvchop
                                                   )))))

(defthm bvif-hack-gen
  (implies (and (integerp size)
                (< 0 size))
           (equal (bvif size test1
                         (bvif size test2 a b)
                         (bvif size test2 b a))
                  (bvif size (xor test1 test2)
                         b
                         a)))
  :hints (("Goal" :in-theory (e/d (xor bvif myif) (;bvchop-bvchop
                                                   )))))

(defthm bvif-of-logext-1
  (implies (and (<= size size2)
                (natp size)
                (integerp size2) ;new
                (< 0 size))
           (equal (bvif size test (logext size2 x) y)
                  (bvif size test x y)))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (e/d (bvif BVCHOP-WHEN-I-IS-NOT-AN-INTEGER) (;BVCHOP-BVCHOP
                                                                   )))))

(defthm bvif-of-logext-2
  (implies (and (<= size size2)
                (integerp size2)
                (natp size)
                (< 0 size))
           (equal (bvif size test y (logext size2 x))
                  (bvif size test y x)))
  :hints (("Goal" :in-theory (e/d (bvif BVCHOP-WHEN-I-IS-NOT-AN-INTEGER) (;BVCHOP-BVCHOP
                                                                          )))))

(defthm myif-equal-bit-0-expt-2-n
  (implies (and (unsigned-byte-p 1 bit)
                (natp n))
           (equal (myif (equal bit 0) 0 (expt 2 n))
                  (bvcat 1 bit n 0)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm myif-equal-bit-0-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (+ -1 (integer-length k))))
                (< 0 (integer-length k))
                (unsigned-byte-p 1 bit))
           (equal (myif (equal bit 0) 0 k)
                  (bvcat 1 bit (+ -1 (integer-length k)) 0)))
  :hints (("Goal" :use (:instance myif-equal-bit-0-expt-2-n (n (+ -1 (integer-length k)) )))))

;BOZO can this loop?
(defthm bvchop-32-times-subst
  (implies (and (equal (bvchop 32 x) (bvchop 32 free)) ;binds the variable FREE
                (syntaxp (smaller-termp free x))
                (integerp x)
                (integerp z)
                (integerp free)
                )
           (EQUAL (BVCHOP 32 (* z x))
                  (BVCHOP 32 (* z free))))
  :hints (("Goal" :use ((:instance bvchop-n-times-drop (n 32) (x x) (y z))
                        (:instance bvchop-n-times-drop (n 32) (x free) (y z)))
           :in-theory (disable bvchop-n-times-drop))))

(defthmd apply-logext-32-to-both-sides
  (implies (and (equal x y)
                (equal a (logext 32 x))
                (equal b (logext 32 y)))
           (equal (equal a b)
                  t)))

(defthmd apply-logext-32-to-both-sides-alt
  (implies (and (equal y x)
                (equal b (logext 32 x))
                (equal a (logext 32 y)))
           (equal (equal a b)
                  t)))

;yikes, don't we want to go the other way?
(defthm bvchop-of-sbp-equal-constant
  (implies (and (syntaxp (quotep k))
                (signed-byte-p 32 x) ;backchain limit?
                )
           (equal (equal k (bvchop 32 x))
                  (and (unsigned-byte-p 32 k)
                       (equal (logext 32 k) x))))
  :hints (("Goal" :in-theory (enable apply-logext-32-to-both-sides-alt apply-logext-32-to-both-sides))))

;for example, we prefer
;(EQUAL '0 (BVCAT '1 x '7 '0))
;to:
;(EQUAL '0 (LOGEXT '8 (BVCAT '1 x '7 '0)))
;is this one okay?
(defthm add-bvchops-to-equality-of-sbps-5
  (implies (and (syntaxp (and (quotep y)
                              (consp x)
                              (member-equal (car x) *trimmable-operators*)))
                (integerp newsize)
                (< 0 newsize))
           (equal (equal (logext newsize x) y)
                  (if (integerp x) ;remove the other case?
                      (and (signed-byte-p newsize y)
                           (equal (bvchop newsize x)
                                  (bvchop newsize y)))
                    (equal 0 y))))
  :hints (("Goal"
           :cases ((integerp x))
           :use (:instance add-bvchops-to-equality-of-sbps-4))))

(defthm logext-equal-logext-rewrite
  (implies (and (integerp x)
                (integerp size)
                (< 0 size))
           (equal (EQUAL (LOGEXT size x) (LOGEXT size y))
                  (equal (bvchop size x) (bvchop size y))))
  :hints (("Goal" :in-theory (enable ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-4))))

(DEFTHM GETBIT-0-OF-TIMES-constant
  (IMPLIES (AND (syntaxp (and (quotep x)
                              (not (unsigned-byte-p 1 (unquote x)))))
                (INTEGERP X)
                (INTEGERP Y))
           (EQUAL (GETBIT 0 (* X Y))
                  (GETBIT 0 (* (GETBIT 0 X) Y))))
  :HINTS
  (("Goal" :use (:instance bvchop-n-times-drop (n 1))
    :IN-THEORY
    (E/D (GETBIT)
         (BVCHOP-1-BECOMES-GETBIT SLICE-BECOMES-GETBIT bvchop-n-times-drop)))))

;bozo more
(defthm bvchop-times-logext-32
  (implies (and (integerp x)
                (integerp y))
           (equal (BVCHOP 32 (* x (LOGEXT 32 y)))
                  (BVCHOP 32 (* x y))))
  :hints (("Goal" :in-theory (disable bvchop-n-times-drop)
           :use ((:instance bvchop-n-times-drop (n 32) (x (logext 32 y)) (y x))
                 (:instance bvchop-n-times-drop (n 32) (x y) (y x))))))

;sort of strength reduction
;gen
;can loop?
(defthmd floor-by-4
  (implies (integerp x)
           (equal (floor x 4)
                  (logtail 2 x)))
  :hints (("Goal" :in-theory (enable logtail))))
(theory-invariant (incompatible (:rewrite FLOOR-BY-4) (:DEFINITION LOGTAIL)))

(theory-invariant (incompatible (:rewrite logapp-0) (:rewrite times-4-becomes-logapp)))

(defthm logext-of-plus-of-logext
  (implies (and (<= smallsize bigsize)
                (integerp smallsize)
                (integerp bigsize)
                (< 0 smallsize)
                (force (integerp x))
                (force (integerp y)))
           (equal (LOGEXT smallsize (+ x (LOGEXT bigsize y)))
                  (LOGEXT smallsize (+ x y))))
  :hints (("Goal" :in-theory (e/d (ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-4) (;BVPLUS-RECOLLAPSE
                                                                       )))))

(defthm logext-of-plus-of-logext-alt
  (implies (and (<= smallsize bigsize)
                (integerp smallsize)
                (integerp bigsize)
                (< 0 smallsize)
                (force (integerp x))
                (force (integerp y)))
           (equal (LOGEXT smallsize (+ (LOGEXT bigsize y) x))
                  (LOGEXT smallsize (+ x y))))
  :hints (("Goal" :in-theory (e/d (ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-4) (logext)))))



;slow?
(defthm slice-of-plus-of-logext-gen
  (implies (and (< high size)
                (natp high)
                (integerp size)
                (<= low high)
                (natp low)
                (force (integerp x))
                (force (integerp y)))
           (equal (SLICE high low (+ x (LOGEXT size y)))
                  (SLICE high low (+ x y))
                  ))
  :hints (("Goal" :in-theory (e/d (SLICE bvchop-of-logtail)
                                  (anti-slice LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE LOGTAIL-OF-LOGEXT)))))

;todo: (theory-invariant (incompatible (:rewrite LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE) (:rewrite slice)))

(defthm slice-of-plus-of-logext-gen-alt
  (implies (and (< high size)
                (natp high)
                (integerp size)
                (<= low high)
                (natp low)
                (force (integerp x))
                (force (integerp y)))
           (equal (slice high low (+ (logext size y) x))
                  (slice high low (+ x y))
                  ))
  :hints (("Goal" :in-theory (e/d (slice) (anti-slice LOGEXT-OF-LOGTAIL-BECOMES-LOGEXT-OF-SLICE LOGEXT-of-logtail)))))

;instead, inner sum should go to bvplus...
(defthm bvxor-of-sum-logext
  (implies (and (<= size size2)
                (natp size)
                (natp size2)
                (integerp y)
                (integerp z))
           (equal (bvxor size x (+ (logext size2 y) z))
                  (bvxor size x (+ y z))))
  :hints (("Goal" :in-theory (e/d (bvxor) (logxor-bvchop-bvchop)))))

;instead, inner sum should go to bvplus...
;BOZO handle this stuff better?
(defthm bvxor-of-sum-logext-alt
  (implies (and (<= size size2)
                (natp size)
                (natp size2)
                (integerp y)
                (integerp z))
           (equal (bvxor size x (+ z (logext size2 y)))
                  (bvxor size x (+ y z))))
  :hints (("Goal" :in-theory (e/d (bvxor) (logxor-bvchop-bvchop)))))

;trying this and the above...
(in-theory (disable bvxor-of-slice-tighten-1 bvxor-of-slice-tighten-2 bvxor-of-slice-tighten-alt bvxor-of-slice-tighten))

;drop?
;bozo gen (or match usb claims in rhs?)
(defthmd bvplus-bound
  (< (bvplus 2 x y) 4)
  :hints (("Goal" :in-theory (e/d (bvplus) (;anti-bvplus
                                            )))))

(defthm logext-of-bv-plus-equal-plus-rewrite
  (implies (and (integerp x) ;hyps are new
                (integerp y))
           (equal (EQUAL (LOGEXT 32 (BVPLUS 32 x y))
                         (+ x y))
                  (signed-byte-p 32 (+ x y))))
  :hints (("Goal" :in-theory (e/d (BVPLUS) (;anti-bvplus
                                            logext-of-plus)))))

;move?
(defthmd usb-of-bvplus-from-bounds
  (implies (and (< x (- (expt 2 n) k)) ;use bvlt?
                (natp x)
                (natp k)
                (natp n))
           (unsigned-byte-p n (bvplus m k x)))
  :hints (("Goal" :in-theory (e/d (bvplus ;usb-plus-from-bounds
                                   ) (
                                            )))))

; rules needed to prove the lemmas that result from my tool (mostly size junk)

(theory-invariant (incompatible (:rewrite LOGAPP-0) (:rewrite LOGAPP-RECOLLECT-FROM-SHIFT)))

(theory-invariant (incompatible (:rewrite rewrite-unsigned-byte-p-when-term-size-is-larger) (:rewrite logtail-equal-0)))

;; essentialy, we are subtracting 1, chopping, and then adding 1 back
(defthm +-of-1-and-bvchop-of-ones-and-x
  (implies (integerp x)
           (equal (+ 1 (bvchop 31 (+ 2147483647 x)))
                  (if (equal 0 (bvchop 31 x))
                      2147483648
                    (bvchop 31 x))))
  :hints (("Goal" :in-theory (enable bvchop-of-sum-cases))))

(defthm logext-when-low-bits-known
  (implies (and (equal (bvchop 31 x) free)
                (syntaxp (quotep free)))
           (equal (logext 32 x)
                  (if (equal 0 (getbit 31 x))
                      free
                    (+ (- (expt 2 31))
                       free))))
  :hints (("Goal" :in-theory (enable logext))))

(defthm logext-negative-linear-cheap
  (implies (equal (getbit 31 x) 1)
           (< (logext 32 x) 0))
  :rule-classes ((:linear :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable logext))))
