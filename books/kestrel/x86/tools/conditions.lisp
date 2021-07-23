; An approach to dealing with conditional jumps
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "projects/x86isa/machine/instructions/conditional" :dir :system)
(include-book "flags") ;for get-flag
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(include-book "kestrel/bv/defs" :dir :system) ;for bvplus, etc.
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/rules10" :dir :system))
(local (include-book "kestrel/bv/arith" :dir :system)) ;todo, maybe for ACL2::FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT?
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;todo

;;
;; A scheme for reducing case-splits introduced by conditional jump instructions
;;

;; These represent the behavior of jcc/cmovcc/setcc-spec in specific cases.

(defund jo-condition (of)
  (equal 1 of))

(defund jno-condition (of)
  (equal 0 of))

(defund jb-condition (cf)
  (equal 1 cf))

(defund jnb-condition (cf)
  (equal 0 cf))

(defund jz-condition (zf)
  (equal 1 zf))

(defund jnz-condition (zf)
  (equal 0 zf))

(defund jbe-condition (cf zf)
  (or (equal 1 cf)
      (equal 1 zf)))

(defund jnbe-condition (cf zf)
  (and (equal 0 cf)
       (equal 0 zf)))

(defund js-condition (sf)
  (equal 1 sf))

(defund jns-condition (sf)
  (equal 0 sf))

(defund jp-condition (pf)
  (equal 1 pf))

(defund jnp-condition (pf)
  (equal 0 pf))

(defund jl-condition (sf of)
  (not (equal sf of)))

(defund jnl-condition (sf of)
  (equal sf of))

(defund jle-condition (zf sf of)
  (or (equal 1 zf)
      (not (equal sf of))))

(defund jnle-condition (zf sf of)
  (and (equal 0 zf)
       (equal sf of)))

;; Instead of opening up x86isa::jcc/cmovcc/setcc-spec, which has 16 cases,
;; some of which involve AND and OR, we use the rules below.  Then we further
;; rewrite the condition functions (in many cases) to nice bv tests like sbvlt.

;; The accesses of the individual flags in these rules should allow any
;; irrelevant writes to be dropped, so we don't have to prove read-over-write
;; rules for the condition functions.

(defthm jcc/cmovcc/setcc-spec-rewrite-jo
  (implies (and (equal (bvchop 4 opcode) 0)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jo-condition (x::get-flag :of x86))))
  :hints (("Goal" :in-theory (e/d (jo-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;N01P-FLGI-EXCEPT-IOPL
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jno
  (implies (and (equal (bvchop 4 opcode) 1)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jno-condition (x::get-flag :of x86))))
  :hints (("Goal" :in-theory (e/d (jno-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;n01p-flgi-except-iopl
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jb
  (implies (and (equal (bvchop 4 opcode) 2)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jb-condition (x::get-flag :cf x86))))
  :hints (("Goal" :in-theory (e/d (jb-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;N01P-FLGI-EXCEPT-IOPL
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jnb
  (implies (and (equal (bvchop 4 opcode) 3)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jnb-condition (x::get-flag :cf x86))))
  :hints (("Goal" :in-theory (e/d (jnb-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;n01p-flgi-except-iopl
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jz
  (implies (and (equal (bvchop 4 opcode) 4)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jz-condition (x::get-flag :zf x86))))
  :hints (("Goal" :in-theory (e/d (jz-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;N01P-FLGI-EXCEPT-IOPL
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jnz
  (implies (and (equal (bvchop 4 opcode) 5)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jnz-condition (x::get-flag :zf x86))))
  :hints (("Goal" :in-theory (e/d (jnz-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;n01p-flgi-except-iopl
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jbe
  (implies (and (equal (bvchop 4 opcode) 6)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jbe-condition (x::get-flag :cf x86)
                                 (x::get-flag :zf x86))))
  :hints (("Goal" :in-theory (e/d (jbe-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;N01P-FLGI-EXCEPT-IOPL
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jnbe
  (implies (and (equal (bvchop 4 opcode) 7)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jnbe-condition (x::get-flag :cf x86)
                                 (x::get-flag :zf x86))))
  :hints (("Goal" :in-theory (e/d (jnbe-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;N01P-FLGI-EXCEPT-IOPL
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-js
  (implies (and (equal (bvchop 4 opcode) 8)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (js-condition (x::get-flag :sf x86))))
  :hints (("Goal" :in-theory (e/d (js-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;N01P-FLGI-EXCEPT-IOPL
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jns
  (implies (and (equal (bvchop 4 opcode) 9)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jns-condition (x::get-flag :sf x86))))
  :hints (("Goal" :in-theory (e/d (jns-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;n01p-flgi-except-iopl
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jp
  (implies (and (equal (bvchop 4 opcode) 10)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jp-condition (x::get-flag :pf x86))))
  :hints (("Goal" :in-theory (e/d (jp-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;N01P-FLGI-EXCEPT-IOPL
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jnp
  (implies (and (equal (bvchop 4 opcode) 11)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jnp-condition (x::get-flag :pf x86))))
  :hints (("Goal" :in-theory (e/d (jnp-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;n01p-flgi-except-iopl
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jl
  (implies (and (equal (bvchop 4 opcode) 12)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jl-condition (x::get-flag :sf x86)
                                (x::get-flag :of x86))))
  :hints (("Goal" :in-theory (e/d (jl-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;N01P-FLGI-EXCEPT-IOPL
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jnl
  (implies (and (equal (bvchop 4 opcode) 13)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jnl-condition (x::get-flag :sf x86)
                                 (x::get-flag :of x86))))
  :hints (("Goal" :in-theory (e/d (jnl-condition
                                   x::get-flag
                                   x86isa::jcc/cmovcc/setcc-spec
                                   bvchop)
                                  (;N01P-FLGI-EXCEPT-IOPL
                                   )))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jle
  (implies (equal (bvchop 4 opcode) 14)
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jle-condition (x::get-flag :zf x86)
                                 (x::get-flag :sf x86)
                                 (x::get-flag :of x86))))
  :hints (("Goal" :in-theory (enable jle-condition
                                     x::get-flag
                                     x86isa::jcc/cmovcc/setcc-spec
                                     bvchop))))

(defthm jcc/cmovcc/setcc-spec-rewrite-jnle
  (implies (and (equal (bvchop 4 opcode) 15)
                (integerp opcode))
           (equal (x86isa::jcc/cmovcc/setcc-spec opcode x86)
                  (jnle-condition (x::get-flag :zf x86)
                                 (x::get-flag :sf x86)
                                 (x::get-flag :of x86))))
  :hints (("Goal" :in-theory (enable jnle-condition
                                     x::get-flag
                                     x86isa::jcc/cmovcc/setcc-spec
                                     bvchop))))

;;;
;;; Rules to replace the condition functions with nice expressions
;;;

;; This puts in a nicer expression for this test. In particular, sbvlt clearly
;; only uses the low 32-bits of x.  I think this can help with termination.
;; TODO: What other cases can arise here?
(defthm jle-condition-rewrite-1
  (implies (unsigned-byte-p 32 x)
           (equal (jle-condition (if (equal 0 x) 1 0)
                                 (acl2::getbit 31 x)
                                 0)
                  (not (acl2::sbvlt 32 0 x))))
  :hints (("Goal" :in-theory (enable jle-condition acl2::sbvlt-rewrite))))

;rename
(defthm jnle-condition-rewrite
  (implies (unsigned-byte-p 32 x)
           (equal (jnle-condition (if (equal 0 x) 1 0)
                                 (acl2::getbit 31 x)
                                 0)
                  (acl2::sbvlt 32 0 x)))
  :hints (("Goal" :in-theory (enable jnle-condition acl2::sbvlt-rewrite))))

(defthmd signed-byte-p-with-top-bit-0
  (implies (and (signed-byte-p 64 x)
                (equal (acl2::getbit 63 x) 0))
           (<= 0 x)))

(defthmd signed-byte-p-with-top-bit-0-bound
  (implies (and (<= -9223372036854775808 x)
                (integerp x)
                (equal (acl2::getbit 63 x) 0))
           (<= 0 x))
  :hints (("Goal" :in-theory (e/d (acl2::getbit acl2::slice logtail bvchop)
                                  (acl2::slice-becomes-getbit
                                   acl2::bvchop-1-becomes-getbit
                                   acl2::bvchop-of-logtail-becomes-slice)))))


(defthmd signed-byte-p-with-top-bit-1-bound
  (implies (and (<= x 9223372036854775807)
                (integerp x)
                (equal (acl2::getbit 63 x) 1))
           (< x 0))
  :hints (("Goal" :in-theory (e/d (acl2::getbit acl2::slice logtail)
                                  (acl2::slice-becomes-getbit
                                   acl2::bvchop-1-becomes-getbit
                                   acl2::bvchop-of-logtail-becomes-slice)))))

(defthm logext-of-expt-of-one-less
  (implies (posp size)
           (equal (logext size (expt 2 (+ -1 size)))
                  (- (expt 2 (+ -1 size)))))
  :hints (("Goal" :in-theory (enable logext))))

;move
(defthm *-of-expt-and-expt-of-minus
  (implies (and (integerp size)
                (integerp n))
           (equal (* (expt 2 size) (expt 2 (+ n (- size))))
                  (expt 2 n)))
  :hints (("Goal" :in-theory (enable ACL2::expt-of-+))))

;move and gen
;use the min exponent
(defthm mod-of-mod-expt-expt
  (implies (and (natp size)
                (integerp x))
           (equal (MOD (MOD X (EXPT 2 SIZE))
                       (EXPT 2 (+ -1 SIZE)))
                  (MOD X
                       (EXPT 2 (+ -1 SIZE)))))
  :hints (("Goal" :in-theory (enable acl2::mod-of-mod-when-mult
                                     ))))

;gen to split off any number of bits
(defthm acl2::split-signed-bv-top
  (implies (and (signed-byte-p size x)
                (posp size))
           (equal x
                  (+ (* (- (expt 2 (+ -1 size))) (acl2::getbit (+ -1 size) x))
                     (bvchop (+ -1 size) x))))
  :hints (("Goal" :cases ((equal 0 (acl2::getbit (+ -1 size) x)))
           :in-theory (e/d (acl2::bvcat logapp
                                  acl2::getbit
                                  ;slice logtail bvchop
                                  SIGNED-BYTE-P
                                  bvchop
                                  ACL2::ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-4)
                           (;ACL2::PLUS-BVCAT-WITH-0
                            ;ACL2::PLUS-BVCAT-WITH-0-ALT
                            acl2::slice-becomes-getbit
                            acl2::bvchop-1-becomes-getbit
                            acl2::bvchop-of-logtail-becomes-slice
                            ACL2::MOD-OF-EXPT-OF-2
                            ACL2::MOD-EXPT-SPLIT))
           :use ((:instance acl2::split-bv
                           (y (bvchop size x))
                           (n size)
                           (m (+ -1 size)))
                 (:instance ACL2::LOGEXT-OF-PLUS
                            (size size)
                            (x (expt 2 (+ -1 size)))
                            (y (BVCHOP (+ -1 size) X))))))
  :rule-classes nil)

;where should this go?
;it depends on bvplus
(defthm jnl-condition-rewrite-1
  (implies (and (signed-byte-p 64 x)
                (signed-byte-p 64 y))
           (equal (jnl-condition (x86isa::sf-spec64$inline (acl2::bvplus '64 x (acl2::bvuminus '64 y)))
                                 (x86isa::of-spec64$inline (binary-+ x (unary-- y))))
                  (acl2::sbvle 64 y x)))
  :otf-flg t
  :hints (("Goal"
           :use ((:instance acl2::split-signed-bv-top
                            (x x)
                            (size 64))
                 (:instance acl2::split-signed-bv-top
                            (x y)
                            (size 64)))
           :cases ((and (equal 0 (acl2::getbit 63 Y))
                        (equal 0 (acl2::getbit 63 x)))
                   (and (equal 0 (acl2::getbit 63 Y))
                        (equal 1 (acl2::getbit 63 x)))
                   (and (equal 1 (acl2::getbit 63 Y))
                        (equal 0 (acl2::getbit 63 x)))
                   (and (equal 1 (acl2::getbit 63 Y))
                        (equal 1 (acl2::getbit 63 x))))

           :in-theory (e/d ( ;signed-byte-p-with-top-bit-0
                            signed-byte-p-with-top-bit-0-bound
                            signed-byte-p-with-top-bit-1-bound
                            jnl-condition
                            x86isa::of-spec64$inline
                            x86isa::sf-spec64$inline
                            acl2::bvplus
                            ;; acl2::bvchop-of-sum-cases
                            signed-byte-p
                            acl2::bvuminus
                            acl2::bvminus
                            acl2::getbit-of-plus
                            ;; acl2::equal-of-bitxor-and-1
                            ;; acl2::bvcat
                            ;; logapp
                            ;; logext
                            acl2::sbvlt
                            acl2::bvlt
                            )
                           ( ;acl2::bvplus-recollapse
                            acl2::bvminus-becomes-bvplus-of-bvuminus
;acl2::plus-bvcat-with-0 ;looped
;acl2::plus-bvcat-with-0-alt ;looped
                            acl2::slice-of-+)))))

(defthmd jnl-condition-rewrite-1-32-helper
  (implies (and (signed-byte-p 32 x)
                (signed-byte-p 32 y))
           (equal (jnl-condition (x86isa::sf-spec32$inline (acl2::bvplus 32 x (acl2::bvuminus 32 y)))
                                 (x86isa::of-spec32$inline (binary-+ (logext 32 x) (unary-- (logext 32 y)))))
                  (acl2::sbvle 32 y x)))
  :otf-flg t
  :hints (("Goal"
           :use ((:instance acl2::split-signed-bv-top
                            (x x)
                            (size 32))
                 (:instance acl2::split-signed-bv-top
                            (x y)
                            (size 32)))
           :cases ((and (equal 0 (acl2::getbit 31 Y))
                        (equal 0 (acl2::getbit 31 x)))
                   (and (equal 0 (acl2::getbit 31 Y))
                        (equal 1 (acl2::getbit 31 x)))
                   (and (equal 1 (acl2::getbit 31 Y))
                        (equal 0 (acl2::getbit 31 x)))
                   (and (equal 1 (acl2::getbit 31 Y))
                        (equal 1 (acl2::getbit 31 x))))
           :in-theory (e/d ( ;signed-byte-p-with-top-bit-0
                            signed-byte-p-with-top-bit-0-bound
                            signed-byte-p-with-top-bit-1-bound
                            jnl-condition
                            x86isa::of-spec32$inline
                            x86isa::sf-spec32$inline
                            acl2::bvplus
                            ;; acl2::bvchop-of-sum-cases
                            signed-byte-p
                            acl2::bvuminus
                            acl2::bvminus
                            acl2::getbit-of-plus
                            ;; acl2::equal-of-bitxor-and-1
                            ;; acl2::bvcat
                            ;; logapp
                            ;; logext
                            acl2::sbvlt
                            acl2::bvlt
                            )
                           ( ;acl2::bvplus-recollapse
                            acl2::bvminus-becomes-bvplus-of-bvuminus
                            ;;acl2::plus-bvcat-with-0 ;looped
                            ;;acl2::plus-bvcat-with-0-alt ;looped
                            acl2::slice-of-+)))))

(defthm jnl-condition-rewrite-1-32
  (implies (and (unsigned-byte-p 32 x)
                (unsigned-byte-p 32 y))
           (equal (jnl-condition (x86isa::sf-spec32$inline (acl2::bvplus 32 x (acl2::bvuminus 32 y)))
                                 (x86isa::of-spec32$inline (binary-+ (logext 32 x) (unary-- (logext 32 y)))))
                  (acl2::sbvle 32 y x)))
  :hints (("Goal" :use (:instance jnl-condition-rewrite-1-32-helper
                                  (x (logext 32 x))
                                  (y (logext 32 y))))))

;move
(defthm sbvlt-of-+-of--4294967296
  (implies (integerp k2)
           (equal (sbvlt 32 x (+ -4294967296 k2))
                  (sbvlt 32 x k2)))
  :hints (("Goal" :in-theory (enable sbvlt acl2::logext-cases
                                     acl2::getbit-of-plus))))

(defthm bvuminus-of--
 (equal (bvuminus 32 (- k2))
        (bvchop 32 k2))
 :hints (("Goal" :in-theory (e/d (bvuminus bvminus) (ACL2::BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS)))))

;k2 is, for example, -10, and k1 is 4294967286
(defthm jnl-condition-rewrite-1-32-constant-version
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (< k2 0) ;gen?
                (integerp k2)
                (signed-byte-p 32 (- k2))
                (equal k1 (+ (expt 2 32) k2))
                (unsigned-byte-p 32 x))
           (equal (jnl-condition (x86isa::sf-spec32$inline (acl2::bvplus 32 k1 x))
                                 (x86isa::of-spec32$inline (binary-+ k2 (logext 32 x))))
                  (acl2::sbvle 32 (- k2) x)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d ( ;bvuminus
                                   ACL2::BVPLUS-OF-PLUS-ARG3
                                   ) (jnl-condition-rewrite-1-32
                                      ;;ACL2::BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
                                   ))
           :use (:instance jnl-condition-rewrite-1-32
                           (x x)
                           (y (- k2))))))

(acl2::def-constant-opener jo-condition)
(acl2::def-constant-opener jno-condition)
(acl2::def-constant-opener jb-condition)
(acl2::def-constant-opener jnb-condition)
(acl2::def-constant-opener jz-condition)
(acl2::def-constant-opener jnz-condition)
(acl2::def-constant-opener jbe-condition)
(acl2::def-constant-opener jnbe-condition)
(acl2::def-constant-opener js-condition)
(acl2::def-constant-opener jns-condition)
(acl2::def-constant-opener jp-condition)
(acl2::def-constant-opener jnp-condition)
(acl2::def-constant-opener jl-condition)
(acl2::def-constant-opener jnl-condition)
(acl2::def-constant-opener jle-condition)
(acl2::def-constant-opener jnle-condition)

(local (include-book "kestrel/bv/rules3" :dir :system))

(defthm jnle-condition-rewrite-2
  (equal (jnle-condition
          (if (equal 0
                     (acl2::bvplus 32
                             x
                             (acl2::bvuminus 32
                                       (logext 32 y))))
              1 0)
          (acl2::getbit 31
                  (acl2::bvplus 32
                          x
                          (acl2::bvuminus 32
                                    (logext 32 y))))
          (bool->bit
           (not (signed-byte-p 32
                               (+ (logext 32 x)
                                  (- (logext 32 y)))))))
         (acl2::sbvlt 32 y x))
  :otf-flg t
  :hints (("Goal"
           :use (:instance acl2::split-bv
                           (y (bvchop 32 x))
                           (n 32)
                           (m 31))
           :in-theory (e/d (jnle-condition acl2::bvplus
                                                   acl2::bvchop-of-sum-cases
                                                   signed-byte-p
                                                   acl2::bvuminus
                                                   acl2::bvminus
                                                   acl2::sbvlt
                                                   acl2::getbit-of-plus
                                                   acl2::equal-of-bitxor-and-1
                                                   acl2::bvcat
                                                   logapp
                                                   logext)
                           (acl2::bvplus-recollapse acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    acl2::plus-bvcat-with-0 ;looped
                                                    acl2::plus-bvcat-with-0-alt ;looped
                                                    )))))

;same as above but with 2 irrelevant logext calls removed
(defthm jnle-condition-rewrite-2-alt
  (equal (jnle-condition
          (if (equal 0
                     (acl2::bvplus 32
                             x
                             (acl2::bvuminus 32
                                       y)))
              1 0)
          (acl2::getbit 31
                  (acl2::bvplus 32
                          x
                          (acl2::bvuminus 32
                                    y)))
          (bool->bit
           (not (signed-byte-p 32
                               (+ (logext 32 x)
                                  (- (logext 32 y)))))))
         (acl2::sbvlt 32 y x))
  :otf-flg t
  :hints (("Goal"
           :use (:instance acl2::split-bv
                           (y (bvchop 32 x))
                           (n 32)
                           (m 31))
           :in-theory (e/d (jnle-condition acl2::bvplus
                                                   acl2::bvchop-of-sum-cases
                                                   signed-byte-p
                                                   acl2::bvuminus
                                                   acl2::bvminus
                                                   acl2::sbvlt
                                                   acl2::getbit-of-plus
                                                   acl2::equal-of-bitxor-and-1
                                                   acl2::bvcat
                                                   logapp
                                                   logext)
                           (acl2::bvplus-recollapse acl2::bvminus-becomes-bvplus-of-bvuminus
                                                    acl2::plus-bvcat-with-0 ;looped
                                                    acl2::plus-bvcat-with-0-alt ;looped
                                                    )))))

(defthm jle-condition-rewrite-2
  (implies (unsigned-byte-p 32 x)
           (equal
            (jle-condition (zf-spec x)
                           (sf-spec32 x)
                           0)
            (acl2::sbvle 32 x 0)))
  :hints (("Goal" :in-theory (enable jle-condition
                                     acl2::sbvlt
                                     x86isa::zf-spec
                                     sf-spec32))))

(defthm jle-condition-rewrite-3
  (implies (unsigned-byte-p 32 x)
           (equal
            (jle-condition (zf-spec x)
                           (sf-spec32 x)
                           (of-spec32 (logext 32 x)))
            (acl2::sbvle 32 x 0)))
  :hints (("Goal" :in-theory (enable jle-condition
                                     acl2::sbvlt
                                     x86isa::zf-spec
                                     sf-spec32
                                     of-spec32))))

(defthm jnle-condition-rewrite-3
  (implies (and (signed-byte-p 64 x)
                (signed-byte-p 64 y))
           (equal (jnle-condition (zf-spec (acl2::bvplus 64 x (acl2::bvuminus 64 y)))
                                  (x86isa::sf-spec64 (acl2::bvplus 64 x (acl2::bvuminus 64 y)))
                                  (x86isa::of-spec64 (+ x (- y))))
                  (acl2::sbvlt 64 y x)))
  :otf-flg t
  :HINTS
  (("Goal"
    :USE ((:INSTANCE acl2::split-signed-bv-top
                     (size 64))
          (:INSTANCE acl2::split-signed-bv-top
                     (x y)
                     (size 64)))
    :IN-THEORY
    (E/D
     (acl2::bvlt
      JNLE-CONDITION
      X86ISA::OF-SPEC64
      X86ISA::SF-SPEC64
      BVPLUS ACL2::BVCHOP-OF-SUM-CASES
      SIGNED-BYTE-P BVUMINUS
      BVMINUS SBVLT ACL2::GETBIT-OF-PLUS
      ACL2::EQUAL-OF-BITXOR-AND-1
      BVCAT LOGAPP LOGEXT)
     (ACL2::GETBIT-OF-* ;looped
;ACL2::REWRITE-<-WHEN-SIZES-DONT-MATCH2 ;looped
      ACL2::REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1 ;looped
      ACL2::BVPLUS-RECOLLAPSE
      ACL2::BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
      ACL2::PLUS-BVCAT-WITH-0
      ACL2::PLUS-BVCAT-WITH-0-ALT)))))

(defthm jnle-condition-rewrite-3-32
  (equal (jnle-condition (zf-spec (acl2::bvplus 32 x (acl2::bvuminus 32 y)))
                         (x86isa::sf-spec32 (acl2::bvplus 32 x (acl2::bvuminus 32 y)))
                         (x86isa::of-spec32 (+ (logext 32 x) (- (logext 32 y)))))
         (acl2::sbvlt 32 y x))
  :otf-flg t
  :HINTS
  (("Goal"
    :USE ()
    :IN-THEORY
    (E/D
     (acl2::bvlt
      JNLE-CONDITION
      X86ISA::OF-SPEC32
      X86ISA::SF-SPEC32
      X86ISA::ZF-SPEC
      BVPLUS ACL2::BVCHOP-OF-SUM-CASES
      SIGNED-BYTE-P BVUMINUS
      BVMINUS SBVLT ACL2::GETBIT-OF-PLUS
      ACL2::EQUAL-OF-BITXOR-AND-1
      BVCAT LOGAPP LOGEXT)
     (ACL2::GETBIT-OF-* ;looped
;ACL2::REWRITE-<-WHEN-SIZES-DONT-MATCH2 ;looped
      ACL2::REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1 ;looped
      ACL2::BVPLUS-RECOLLAPSE
      ACL2::BVMINUS-BECOMES-BVPLUS-OF-BVUMINUS
      ACL2::PLUS-BVCAT-WITH-0
      ACL2::PLUS-BVCAT-WITH-0-ALT
      ;ACL2::EQUAL-OF-BVCHOPS-WHEN-EQUAL-OF-GETBITS ;looped
      )))))

(defthm jnz-condition-rule-1
  (equal (jnz-condition (if test 1 0))
         (not test)))

(defthm jnz-condition-rule-2
  (equal (jnz-condition (zf-spec$inline (bvplus 32 x y)))
         (not (equal (bvuminus 32 x) (bvchop 32 y))))
  :hints (("Goal" :in-theory (e/d (bvuminus bvminus bvplus acl2::bvchop-of-sum-cases)
                                  (acl2::bvminus-becomes-bvplus-of-bvuminus)))))

;odd rule
;todo gen
(defthm jnbe-condition-rewrite-1
 (equal (jnbe-condition (bool->bit$inline (< (bvplus 8 24 x) 1))
                                (zf-spec$inline (bvplus 8 23 x)))
        (and (not (equal (bvchop 8 -24)
                         (bvchop 8 x)))
             (not (equal (bvchop 8 -23)
                         (bvchop 8 x)))))
 :hints (("Goal" :in-theory (e/d (jnbe-condition
                                  bvlt bvplus acl2::bvchop-of-sum-cases)
                                 (acl2::bvplus-recollapse)))))
