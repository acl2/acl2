; Centaur Bitops Library
; Copyright (C) 2010-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

#!ACL2
(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

(defconst *bitops-exports*
  '(
    ;; rulesets
    ihsext-basic-thms
    ihsext-advanced-thms
    ihsext-bad-type-thms
    ihsext-redefs
    ihsext-recursive-redefs
    ihsext-inductions
    ihsext-bounds-thms
    ihsext-arithmetic
    bitops-congruences
    bitops-congruences-incompatible
    logbitp-case-splits
    logbitp-case-splits+
    ihs-ext-disabled-rules

    ;; basic arith equiv stuff we want to import
    lnfix lifix lbfix lposfix pos-fix
    int-equiv nat-equiv bit-equiv pos-equiv
    bit->bool bool->bit
    negp zbp
    arith-equiv-forwarding

    ;; basic bit definitions from ihs we want to import
    logbitp logbit logior logand lognot logxor logite
    logcons logcar logcdr loghead logtail
    logext logapp logrev logrev1 logcount
    logmask logmaskp bitmaskp
    b-eqv b-nand b-nor b-andc1 b-andc2 b-orc1 b-orc2
    b-not b-and b-ior b-xor b-ite bfix bitp
    binary-logand binary-logior binary-logxor binary--
    maybe-bitp maybe-bit-fix

    ;; induction schemes to import
    logcdr-induction-1
    logcdr-induction-2
    logcdr-induction-3
    sub1-logcdr-induction-1
    sub1-logcdr-induction-2
    sub1-logcdr-induction-2-w/carry
    sub1-logcdr-induction-3

    ;; recursive redefinitions we want to export
    integer-length** ash**
    logbitp** loghead** logtail**
    lognot** logand** logior** logxor**
    unsigned-byte-p** signed-byte-p**
    logsquash** logapp** logmask** logcount** logrev**
    bitmaskp** logext**

    ;; new definitions we want to export
    nth-slice2 nth-slice4 nth-slice8 nth-slice16
    nth-slice32 nth-slice64 nth-slice128 nth-slice256 nth-slice512 nth-slice nth-slice$
    negate-slice8 negate-slice16
    negate-slice32 negate-slice64
    abs-diff
    setbit clearbit copybit notbit
    bitscan-fwd bitscan-rev
    install-bit install-bit**
    part-select
    part-install
    fast-rotate-left rotate-left rotate-left-1 rotate-left** rotate-left**-tr
    fast-rotate-right rotate-right rotate-right-1 rotate-right** rotate-right**-tr
    fast-logext fast-logext-fn
    fast-logrev-u8 fast-logrev-u16 fast-logrev-u32 fast-logrev-u64
    signed-saturate signed-saturate-fn
    unsigned-saturate unsigned-saturate-fn
    merge-2-bits  merge-4-bits merge-8-bits merge-16-bits
    merge-2-u2s   merge-4-u2s   merge-8-u2s
    merge-2-u4s   merge-4-u4s
    merge-2-u8s   merge-4-u8s   merge-8-u8s  merge-16-u8s  merge-32-u8s
    merge-2-u16s  merge-4-u16s  merge-8-u16s merge-16-u16s
    merge-2-u32s  merge-4-u32s  merge-8-u32s merge-16-u32s
    merge-2-u64s  merge-4-u64s  merge-8-u64s
    merge-2-u128s merge-4-u128s
    merge-2-u256s
    parity fast-parity
    logrepeat fast-logrepeat fast-logrepeat!

    ;; selected theorems, hints, etc
    right-shift-to-logtail
    equal-by-logbitp
    logbitp-hyp
    logbitp-lhs
    logbitp-rhs
    equal-by-logbitp-hint
    equal-by-logbitp-hammer
    equal-by-logbitp-witnessing
    unequal-by-logbitp-witnessing
    logbitp-reasoning
    logbitp-mismatch
    logbitp-mismatch-correct

    ;; these seem to get instantiated a lot, so we'll import/export them
    unsigned-byte-p-of-logand-1
    unsigned-byte-p-of-logand-2
    unsigned-byte-p-of-logior
    unsigned-byte-p-of-loghead
    unsigned-byte-p-of-logtail
    unsigned-byte-p-of-ash
    unsigned-byte-p-of-logxor
    unsigned-byte-p-of-logsquash
    unsigned-byte-p-of-logapp
    unsigned-byte-p-of-logrev

    ))

(defpkg "BITOPS"
  (union-eq *standard-acl2-imports*
            std::*std-exports*
            *bitops-exports*
            '(;; consider adding to *acl2-exports*
              value
              unquote
              hist
              pspv
              ctx

              ;; basic stuff
              assert!
              b*
              fun
              why
              with-redef
              defxdoc
              defsection
              def-ruleset
              def-ruleset!
              add-to-ruleset
              enable*
              disable*
              e/d*
              pseudo-term-list-listp
              non-parallel-book
              do-not
              def-gl-thm

              witness-cp
              defexample
              definstantiate
              witness-cp-witness-rules
              witness-cp-instance-rules

              introduce-var

              add-context-rule

              defwitness
              add-wizard-advice

              ;; the symbol *bitops-exports* itself, so you can write
              ;; acl2::*bitops-exports* or bitops::*bitops-exports*
              *bitops-exports*

              ;; selected theorems to import from ihs
              logcar-logcdr-elim
              loghead-identity
              logtail-identity
              loghead-upper-bound
              logand-upper-bound
              logbitp-logtail
              unsigned-byte-p-logior
              unsigned-byte-p-logand
              signed-byte-p-logops

              ;; documentation
              bitops

              ;; variable names to share with the acl2 package
              ;; (and ihs in particular)
              a b c d e f g h i j k l m n o p q r s t u v w x y z
              pos size size1

              )))

(assign acl2::verbose-theory-warning nil)

#!bitops
(defconst *sparseint-exports*
  '(sparseint
    sparseint-p
    sparseint-fix
    sparseint-equiv
    int-to-sparseint
    sparseint-val
    sparseint-concatenate
    sparseint-rightshift
    sparseint-ash
    sparseint-bit
    sparseint-bitnot
    sparseint-bitand
    sparseint-bitor
    sparseint-bitxor
    sparseint-biteqv
    sparseint-bitandc1
    sparseint-bitandc2
    sparseint-bitnand
    sparseint-bitorc1
    sparseint-bitorc2
    sparseint-bitnor
    sparseint-test-bitand
    sparseint-test-bitor
    sparseint-test-bitxor
    sparseint-test-biteqv
    sparseint-test-bitandc1
    sparseint-test-bitandc2
    sparseint-test-bitnand
    sparseint-test-bitorc1
    sparseint-test-bitorc2
    sparseint-test-bitnor
    sparseint-equal
    sparseint-length
    sparseint-plus
    sparseint-unary-minus
    sparseint-binary-minus
    sparseint-compare
    sparseint-<
    sparseint-binary-bitop
    sparseint-trailing-0-count
    sparseint-trailing-0-count-from
    sparseint-trailing-1-count
    sparseint-trailing-1-count-from
    sparseint-bitcount
    sparseint-bitcount-from))
