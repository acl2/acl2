; MULTIPLIER RULES

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "fnc-defs")

(include-book "svl-spec")

(include-book "meta-fnc-eval-correct")

(include-book "equal-meta")

(include-book "mult-rules")

;(include-book "s-of-c-meta")

(include-book "centaur/svl/top" :dir :system)

(update-rp-clause-proc svl-mult-rules)

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(encapsulate
  nil
  
  (local
   (use-arithmetic-5 t))

  (defthmd bits-is-bit-of-nosyntaxp
    (implies (and (integerp num)
                  (natp start))
             (equal (svl::bits num start 1)
                    (bit-of num start)))
    :hints (("Goal"
             :in-theory (e/d (bitp
                              oddp
                              evenp
                              bit-of
                              SV::4VEC-PART-SELECT
                              svl::bits
                              SV::4VEC->LOWER
                              SV::2VEC
                              SV::4VEC-RSH
                              SV::4VEC->UPPER
                              SV::4VEC-ZERO-EXT
                              
                              SV::4VEC
                              ;SV::4VEC-CONCAT
                              SV::4VEC-SHIFT-CORE
;LOGHEAD
                              logbitp
                              ifix
                              mod
                              expt
                              ash
                              logbit
                              loghead
                              )
                             (SVL::BITP-BITS-SIZE=1
                              ;;loghead
                              (:REWRITE SV::4VEC-EQUAL)
                              
                              (:DEFINITION ACL2::EXPT2$INLINE)
                              ;(:DEFINITION ACL2::IMOD$INLINE)
                              
                              (:REWRITE ACL2::REMOVE-WEAK-INEQUALITIES)
                              SVL::CONVERT-4VEC-CONCAT-TO-4VEC-CONCAT$
                              SVL::4VEC-ZERO-EXT-IS-BITS
                              SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
                              SVL::4VEC-CONCAT$-OF-SIZE=1-TERM2=0
                            
                              SVL::4VEC-PART-SELECT-IS-BITS)))))

  (def-rp-rule bits-is-bit-of
    (implies (and (integerp num)
                  (natp start)
                  (syntaxp (atom (ex-from-rp num))))
             (equal (svl::bits num start 1)
                    (bit-of num start)))
    :hints (("Goal"
             :in-theory (e/d (bits-is-bit-of-nosyntaxp) ()))))

  (defthmd bits-is-bit-of-reverse
    (implies (and (integerp num)
                  (natp start))
             (equal (bit-of num start)
                    (svl::bits num start 1)))))


(def-rp-rule bits-of-bit-of
  (equal (svl::bits (bit-of x pos) 0 1)
         (bit-of x pos))
  :otf-flg t
  :hints (("Goal"
           :do-not '(preprocess)
           :cases ((bitp (bit-of x pos)))
           :in-theory (e/d (bitp)
                           (BITP-OF-BIT-OF
                            (:TYPE-PRESCRIPTION BIT-OF))))
          ("Subgoal 2"
           :in-theory (e/d () ()))))

(def-rp-rule 4vec-bitxor-is-binary-xor-when-bitp
  (implies (and (bitp x)
                (bitp y))
           (equal (sv::4vec-bitxor x y)
                  (binary-xor x y)))
  :hints (("goal"
           :in-theory (e/d (bitp) ()))))


(def-rp-rule 4vec-bitxor-is-binary-xor-when-integerp
  (implies t
           (equal (sv::4vec-bitxor (bit-of x start1) (bit-of y start2))
                  (binary-xor (bit-of x start1) (bit-of y start2))))
  :hints (("Goal"
           :do-not '(preprocess)
           :in-theory (e/d ()
                           (SVL::4VEC-PART-SELECT-IS-BITS)))))

(def-rp-rule 4vec-bitand-is-binary-and-when-bitp
  (implies (and (bitp x)
                (bitp y))
           (equal (sv::4vec-bitand x y)
                  (rp::and$ x y)))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(def-rp-rule 4vec-bitand-is-binary-and-when-integerp
  (implies t
           (equal (sv::4vec-bitand (bit-of x start1) (bit-of y start2))
                  (rp::and$ (bit-of x start1) (bit-of y start2))))
  :hints (("Goal"
           :do-not '(preprocess)
           :in-theory (e/d ()
                           (SVL::4VEC-PART-SELECT-IS-BITS)))))

(encapsulate
  nil

  (local
   (use-arithmetic-5 t))

  (def-rp-rule 4vec-bitand$-is-binary-and-when-bitp
    (implies (and (bitp x)
                  (bitp y)
                  (posp size))
             (equal (svl::4vec-bitand$ size x y)
                    (rp::and$ x y)))
    :otf-flg t
    :hints (("Goal"
             :do-not '(preprocess)
             :in-theory (e/d (bitp
                              ifix
                              SVL::4VEC-BITAND$
                              SV::4VEC-PART-SELECT
                              SVL::BITS
                              SV::4VEC-CONCAT
                              logapp
                              loghead
                              SV::4VEC->UPPER
                              sv::4vec->lower)
                             (SVL::4VEC-PART-SELECT-IS-BITS
                              SVL::CONVERT-4VEC-CONCAT-TO-4VEC-CONCAT$
                              SVL::4VEC-ZERO-EXT-IS-BITS)))))

  (def-rp-rule 4vec-bitor$-is-binary-and-when-bitp
    (implies (and (bitp x)
                  (bitp y)
                  (posp size))
             (equal (svl::4vec-bitor$ size x y)
                    (rp::or$ x y)))
    :otf-flg t
    :hints (("Goal"
             :do-not '(preprocess)
             :in-theory (e/d (bitp
                              ifix
                              SVL::4VEC-BITor$
                              SV::4VEC-PART-SELECT
                              SVL::BITS
                              SV::4VEC-CONCAT
                              logapp
                              loghead
                              SV::4VEC->UPPER
                              sv::4vec->lower)
                             (SVL::4VEC-PART-SELECT-IS-BITS
                              SVL::4VEC-ZERO-EXT-IS-BITS
                              SVL::CONVERT-4VEC-CONCAT-TO-4VEC-CONCAT$)))))

  (def-rp-rule 4vec-bitxor$-is-binary-and-when-bitp
    (implies (and (bitp x)
                  (bitp y)
                  (posp size))
             (equal (svl::4vec-bitxor$ size x y)
                    (binary-xor x y)))
    :otf-flg t
    :hints (("Goal"
             :do-not '(preprocess)
             :in-theory (e/d (bitp
                              ifix
                              SVL::4VEC-BITxor$
                              SV::4VEC-PART-SELECT
                              SVL::BITS
                              SV::4VEC-CONCAT
                              logapp
                              loghead
                              SV::4VEC->UPPER
                              sv::4vec->lower)
                             (SVL::4VEC-PART-SELECT-IS-BITS
                              SVL::4VEC-ZERO-EXT-IS-BITS
                              SVL::CONVERT-4VEC-CONCAT-TO-4VEC-CONCAT$))))))

(def-rp-rule 4vec-bitor-is-binary-and-when-bitp
  (implies (and (bitp x)
                (bitp y))
           (equal (sv::4vec-bitor x y)
                  (rp::or$ x y)))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))


(def-rp-rule 4vec-bitor-is-binary-or-when-integerp
  (implies t
           (equal (sv::4vec-bitor (bit-of x start1) (bit-of y start2))
                  (rp::or$ (bit-of x start1) (bit-of y start2))))
  :hints (("Goal"
           :do-not '(preprocess)
           :in-theory (e/d ()
                           (SVL::4VEC-PART-SELECT-IS-BITS)))))

(def-rp-rule 4vec-?*-to-binary-?*
  (implies (and (bitp test)
                (bitp x)
                (bitp y))
           (equal (svl::4vec-?* test x y)
                  (binary-? test x y)))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(def-rp-rule 4vec-?-to-binary-?*
  (implies (and (bitp test)
                (bitp x)
                (bitp y))
           (equal (svl::4vec-? test x y)
                  (binary-? test x y)))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(def-rp-rule convert-4vec-bitnot$-binary-not
    (implies (bitp x)
             (equal (svl::4vec-bitnot$ 1 x)
                    (binary-not x)))
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

(def-rp-rule 4vec-fix=-of-binary-fns
  (and (equal (svl::4vec-fix (binary-not s))
              (binary-not s))
       (equal (svl::4vec-fix (or$ x y))
              (or$ x y))
       (equal (svl::4vec-fix (and$ x y))
              (and$ x y))
       (equal (svl::4vec-fix (binary-xor x y))
              (binary-xor x y))))

(encapsulate
  nil
  
  (local
   (use-arithmetic-5 t))

  (def-rp-rule bits-of-binary-fns
    (implies (not (zp start))
             (and (equal (svl::bits (or$ x y) start 1 )
                         0)
                  (equal (svl::bits (and$ x y) start 1 )
                         0)
                  (equal (svl::bits (not$ x) start 1 )
                         0)
                  (equal (svl::bits (binary-xor x y) start 1 )
                         0)
                  (equal (svl::bits (binary-? x y z) start 1 )
                         0)
                  (equal (svl::bits (bit-of x y) start 1 )
                         0)))
    :hints (("goal"
             :do-not '(preprocess)
             :in-theory (e/d (or$
                              svl::bits
                              svl::4vec-part-select
                              sv::4vec->lower
                              sv::4vec->upper
                              svl::4vec-zero-ext
                              svl::4vec-rsh
                              loghead
                              not$
                              mod floor
                              svl::4vec-shift-core)
                             (svl::4vec-part-select-is-bits
                              SVL::4VEC-ZERO-EXT-IS-BITS
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-concat$-of-size=1-term2=0
                              svl::4vec-zero-ext-is-4vec-concat)))))

  (def-rp-rule bits-of-binary-fns-start=0
    (implies t
             (and (equal (svl::bits (or$ x y) 0 1 )
                         (or$ x y))
                  (equal (svl::bits (and$ x y) 0 1 )
                         (and$ x y))
                  (equal (svl::bits (not$ x) 0 1 )
                         (not$ x))
                  (equal (svl::bits (binary-xor x y) 0 1 )
                         (binary-xor x y))
                  (equal (svl::bits (binary-? x y z) 0 1 )
                         (binary-? x y z))
                  (equal (svl::bits (bit-of x y) 0 1 )
                         (bit-of x y))))
    :hints (("goal"
             :do-not '(preprocess)
             :in-theory (e/d (or$
                              svl::bits
                              svl::4vec-part-select
                              sv::4vec->lower
                              sv::4vec->upper
                              svl::4vec-zero-ext
                              svl::4vec-rsh
                              loghead
                              not$
                              mod floor
                              svl::4vec-shift-core)
                             (svl::4vec-part-select-is-bits
                              BITS-IS-BIT-OF
                              SVL::4VEC-ZERO-EXT-IS-BITS
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-concat$-of-size=1-term2=0
                              svl::4vec-zero-ext-is-4vec-concat))))))


(encapsulate
  nil
  
  (local
   (use-arithmetic-5 t))

  (local
   (defthm lemma1
     (implies (and (not (zp start))
                   (bitp x))
              (equal (bit-of x start)
                     0))
     :hints (("Goal"
              :in-theory (e/d (bitp bit-of) ())))))

  (local
   (defthm lemma2
     (implies (and (bitp x))
              (equal (bit-of x 0)
                     x))
     :hints (("Goal"
              :in-theory (e/d (bitp bit-of) ())))))
  
  (def-rp-rule$ t t
    bit-of-binary-fns
    (implies (not (zp start))
             (and (equal (bit-of (or$ x y) start )
                         0)
                  (equal (bit-of (and$ x y) start)
                         0)
                  (equal (bit-of (not$ x) start)
                         0)
                  (equal (bit-of (binary-xor x y) start )
                         0)
                  (equal (bit-of (binary-? x y z) start )
                         0)))
    :hints (("goal"
             :do-not '(preprocess)
             :in-theory (e/d (bitp)
                             (svl::4vec-part-select-is-bits
                              SVL::4VEC-ZERO-EXT-IS-BITS
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-concat$-of-size=1-term2=0
                              svl::4vec-zero-ext-is-4vec-concat)))))

  (def-rp-rule$ t t
    bit-of-binary-fns-start=0
    (implies t
             (and (equal (bit-of (or$ x y) 0 )
                         (or$ x y))
                  (equal (bit-of (and$ x y) 0)
                         (and$ x y))
                  (equal (bit-of (not$ x) 0)
                         (not$ x))
                  (equal (bit-of (binary-xor x y) 0)
                         (binary-xor x y))
                  (equal (bit-of (binary-? x y z) 0)
                         (binary-? x y z))))
    :hints (("goal"
             :do-not '(preprocess)
             :in-theory (e/d ()
                             (svl::4vec-part-select-is-bits
                              SVL::4VEC-ZERO-EXT-IS-BITS
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-concat$-of-size=1-term2=0
                              svl::4vec-zero-ext-is-4vec-concat))))))




(def-rp-rule bits-of-4vec-==-binary-fncs
  (and (equal (SVL::BITS (SV::4VEC-== (BINARY-OR x y) 1) '0 '1)
              (BINARY-OR x y))
       (equal (SVL::BITS (SV::4VEC-== (BINARY-and x y) 1) '0 '1)
              (BINARY-and x y)))
  :hints (("Goal"
           :in-theory (e/d (bitp and$ or$) ()))))

(def-rp-rule$ t t
  bit-of-4vec-bitnot-main
  (implies (bitp x)
           (equal (BIT-OF (SV::4VEC-BITNOT x) 0)
                  (svl::4vec-bitnot$ 1 x)))
  :hints (("Goal"
           :in-theory (e/d (bitp) (bitp-of-bit-of
                                   (:TYPE-PRESCRIPTION BIT-OF))))))

(def-rp-rule$ t t
  bit-of-4vec-bitnot
  (equal (BIT-OF (SV::4VEC-BITNOT (bit-of x start)) 0)
         (svl::4vec-bitnot$ 1 (bit-of x start)))
  :hints (("Goal"
           :use ((:instance bitp-of-bit-of
                            (num x)
                            (pos start)))
           :in-theory (e/d (bitp) (bitp-of-bit-of
                                   (:TYPE-PRESCRIPTION BIT-OF))))))

(def-rp-rule 4vec-fix-of-bit-of
  (equal (svl::4vec-fix (bit-of x pos))
         (bit-of x pos))
  :hints (("Goal"
           :in-theory (e/d (bit-of
                            bitp)
                           (bit-fix)))))



(def-rp-rule
  integerp-of-bit-of
  (b* ((res (bit-of num pos))) (integerp res))
  :rule-classes :rewrite)

;; (def-rp-rule 4vec-concat$-of-and$-commutes
;;   (implies (syntaxp (pp-and$-order x y))
;;            (equal (svl::4vec-concat$ size
;;                                 (and$ y x)
;;                                 rest)
;;                   (svl::4vec-concat$ size
;;                                 (and$ x y)
;;                                 rest)))
;;   :hints (("Goal"
;;            :in-theory (e/d (and$) ()))))

(def-rp-rule 3vec-fix-of-binary-fncs
  (and (equal (SV::3VEC-FIX (binary-and a b))
              (binary-and a b))
       (equal (SV::3VEC-FIX (binary-or a b))
              (binary-or a b))
       (equal (SV::3VEC-FIX (binary-xor a b))
              (binary-xor a b))
       (equal (SV::3VEC-FIX (binary-? a b c))
              (binary-? a b c))
       (equal (SV::3VEC-FIX (binary-not a))
              (binary-not a)))
  :hints (("Goal"
           :in-theory (e/d (binary-?
                            binary-and
                            binary-not
                            binary-or
                            binary-xor) ()))))

(def-rp-rule 3vec-fix-of-bit-of
  (implies t 
           (equal (sv::3vec-fix (bit-of x index))
                  (bit-of x index))))

#|(def-rp-rule bits-of-adder-and
  (equal (svl::bits (adder-and a b) 0 1)
         (adder-and a b))
  :hints (("Goal"
           :in-theory (e/d (adder-and) ()))))||#




(skip-proofs
 (def-rp-rule bits-0-1-of-s
   (equal (svl::bits (s pp c/d) 0 1)
          (s pp c/d))))

(skip-proofs
 (def-rp-rule bits-1-1-of-s
   (implies (and (not (zp start))
                 (natp size))
            (equal (svl::bits (s pp c/d) start size)
                   0))))


(def-rp-rule equal-of-concat$-with-hyp
  (implies (equal x1 x2)
           (equal (equal (svl::4vec-concat$ 1 x1 rest1)
                         (svl::4vec-concat$ 1 x2 rest2))
                  (equal (sv::4vec-fix rest1)
                         (sv::4vec-fix rest2))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))
