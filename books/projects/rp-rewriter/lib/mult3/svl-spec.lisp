; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2022 Intel Corporation

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

(include-book "centaur/svl/top" :dir :system)

(include-book "spec")

(include-book "fnc-defs")

(local
 (include-book "lemmas"))

(local
 (in-theory (enable bit-fix)))

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/ihs-extensions" :dir :system)
  use-ihs-extensions
  :disabled t))

(defun bits-to-bit-of (x)
  x)

(local
 (in-theory (disable oddp evenp
                     ash ifix and$ acl2::b-and
                     floor mod logbitp svl::bits
                     logbit
                     (:TYPE-PRESCRIPTION BINARY-AND)
                     (:TYPE-PRESCRIPTION SV::4VEC-RSH))))

(local
 (defthm integerp-4vec-list
   (implies (and (integerp a)
                 (integerp b))
            (integerp (svl::4vec-list a b)))
   :hints (("goal"
            :do-not '(preprocess)
            :in-theory (e/d (svl::4vec-concat$
                             sv::4vec-concat
                             sv::4vec->lower
                             sv::4vec
                             sv::4vec->upper)
                            (svl::convert-4vec-concat-to-4vec-concat$
                             #|svl::4vec-concat$-enter-bits||#))))))

(encapsulate
  nil

  (local
   (use-arithmetic-5 t))

  (defthmd bits-is-bit-of-nosyntaxp
    (implies (and (integerp num)
                  (natp start))
             (equal (svl::bits num start 1)
                    (bit-of num start)))
    :hints (("goal"
             :in-theory (e/d (bitp
                              oddp
                              evenp
                              bit-of
                              sv::4vec-part-select
                              svl::bits
                              sv::4vec->lower
                              sv::2vec
                              sv::4vec-rsh
                              sv::4vec->upper
                              sv::4vec-zero-ext

                              sv::4vec
;sv::4vec-concat
                              sv::4vec-shift-core
;loghead
                              logbitp
                              ifix
                              mod
                              expt
                              ash
                              logbit
                              loghead
                              )
                             (svl::bitp-bits-size=1
                              ;;loghead
                              (:rewrite sv::4vec-equal)

                              (:definition acl2::expt2$inline)
;(:definition acl2::imod$inline)

                              (:rewrite acl2::remove-weak-inequalities)
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-zero-ext-is-bits
                              svl::4vec-zero-ext-is-4vec-concat
                              svl::4vec-concat$-of-term2=0

                              SVL::4VEC-PART-SELECT-IS-BITS)))))

  (defthm bits-is-bit-of
    (implies (and (syntaxp (atom (ex-from-rp num)))
                  (integerp num)
                  (natp start))
             (equal (svl::bits num start 1)
                    (bit-of num start)))
    :hints (("Goal"
             :in-theory (e/d (bits-is-bit-of-nosyntaxp) ()))))

  (defthmd bits-is-bit-of-reverse
    (implies (and (integerp num)
                  (natp start))
             (equal (bit-of num start)
                    (svl::bits num start 1)))))

;; multiplier-spec:
(progn

  (local
   (define svl-sum-col-bybit-aux ((mult integerp)
                                  (mcand integerp)
                                  (col-index natp))
     "Same as sum-col-bybit but shift-amount is set to 0 and col-index < out-size"
     :returns
     (res integerp
          :hyp (and (integerp mult) (integerp mcand)))
     :verify-guards nil
     (cond ((zp col-index)
            (and$ (svl::bits mult 0 1 )
                  (svl::bits mcand 0 1 )))
           (t
            (sum (and$ (svl::bits mult 0 1)
                       (svl::bits mcand col-index 1 ))
                 (svl-sum-col-bybit-aux (svl::4vec-rsh 1 mult)
                                        mcand
                                        (1- col-index)))))))

  (define svl-sum-col-bybit ((mult integerp)
                             (start integerp)
                             (mcand integerp)
                             (col-index natp))
    "Same as sum-col-bybit but shift-amount is set to 0 and col-index < out-size"
    :returns
    (res integerp
         :hyp (and (integerp mult) (integerp mcand)))
    :verify-guards nil
    (cond ((zp col-index)
           (and$ (svl::bits mult start 1)
                 (svl::bits mcand 0 1)))
          (t
           (sum (and$ (svl::bits mult start 1  )
                      (svl::bits mcand col-index 1 ))
                (svl-sum-col-bybit mult
                                   (1+ start)
                                   mcand
                                   (1- col-index))))))

  (define svl-sum-pps-bycol-bybit ((mult integerp)
                                   (mcand integerp)
                                   (carry-in integerp)
                                   (out-size natp)
                                   (col-index natp))
    :returns (res integerp :hyp (and (and (integerp mult)
                                          (integerp mcand)
                                          (integerp carry-in)
                                          (natp col-index))))
    :measure (nfix (- out-size col-index))
    :guard (<= col-index out-size)
    :verify-guards nil
    :prepwork ((local
                (in-theory (e/d () (+-IS-SUM)))))
    (if (zp (- out-size col-index))
        0
      (b* ((col-sum (svl-sum-col-bybit mult 0 mcand col-index)))
        (svl::4vec-concat$ 1
                           (s-spec (list col-sum carry-in))
                           (svl-sum-pps-bycol-bybit mult mcand
                                                    (c-spec (list col-sum carry-in))
                                                    out-size
                                                    (1+ col-index))))))

  (define svl-mult-final-spec ((mult integerp)
                               (mcand integerp)
                               (out-size natp))
    :verify-guards nil
    (svl-sum-pps-bycol-bybit mult mcand 0 out-size 0)
    ///
    (add-rp-rule svl-mult-final-spec)))

(local
 (defthm svl-sum-col-bybit-is-svl-sum-col-bybit2
   (implies (and (integerp mult)
                 (integerp mcand)
;(natp col-index)
                 (natp start))
            (equal (svl-sum-col-bybit mult
                                      start
                                      mcand
                                      col-index)
                   (svl-sum-col-bybit-aux (sv::4vec-rsh start mult)
                                          mcand
                                          col-index)))
   :hints (("Goal"
            :in-theory (e/d (svl-sum-col-bybit-aux
                             bits-is-bit-of-reverse
                             SVL::BITS-OF-RSH-NO-SYNTAXP
                             svl-sum-col-bybit)
                            (bits-is-bit-of))))))

(local
 (encapsulate
   nil
   (local
    (use-arithmetic-5 t))

   (defthm b-and-is-and$
     (and (equal (acl2::b-and x y)
                 (and$ x y)))
     :hints (("Goal"
              :in-theory (e/d (acl2::b-and
                               and$) ()))))
   (defthm logbit-is-bits
     (implies (and (natp index)
                   (integerp term))
              (equal (logbit index term)
                     (svl::bits term index 1 )))
     :hints (("Goal"
              :do-not '(preprocess)
              :in-theory (e/d (and$ acl2::b-and
                                    svl::bits
                                    SV::4VEC-PART-SELECT
                                    SVL::4VEC-CONCAT$
                                    SV::4VEC->UPPER
                                    sv::4VEC->LOWER
                                    SV::4VEC-CONCAT
                                    SV::4VEC-RSH
                                    SV::4VEC-SHIFT-CORE
                                    ash
                                    logbitp
                                    oddp
                                    evenp
                                    floor
                                    mod
                                    ifix
                                    logbit)
                              (SVL::4VEC-PART-SELECT-IS-BITS
                               SVL::4VEC-ZERO-EXT-IS-BITS
                               SVL::4VEC-CONCAT$-OF-TERM2=0
                               SVL::CONVERT-4VEC-CONCAT-TO-4VEC-CONCAT$)))))

   (defthm ash-minus1-is-4vec-rsh
     (implies (integerp term)
              (equal (ash term -1)
                     (sv::4vec-rsh 1 term)))
     :hints (("Goal"
              :in-theory (e/d (ash
                               ifix
                               SV::4VEC-P
                               SV::4VEC->UPPER
                               sv::4vec->lower
                               SV::4VEC-SHIFT-CORE
                               sv::4vec-rsh) ()))))

   (defthm logapp-is-4vec-concat$
     (implies (and (integerp a)
                   (integerp b)
                   (natp size))
              (equal (logapp size a b)
                     (svl::4vec-concat$ size a b)))
     :hints (("Goal"
              :do-not '(preprocess)
              :in-theory (e/d (svl::4vec-concat$
                               SV::4VEC->UPPER
                               sv::4vec->lower
                               SV::4VEC-CONCAT
                               SV::4VEC-P
                               ifix
                               )
                              (logapp
                               SVL::CONVERT-4VEC-CONCAT-TO-4VEC-CONCAT$)))))

   (defthm integerp-4vec-rsh
     (implies (integerp mult)
              (INTEGERP (Sv::4vec-rsh 1 MULT)))
     :hints (("Goal"
              :use ((:instance  ash-minus1-is-4vec-rsh
                                (term mult)))
              :in-theory (e/d () (ash-minus1-is-4vec-rsh)))))

   (define m2 (x)
     (mod (ifix x) 2))

   (define f2 (x)
     (floor (ifix x) 2))

   (defthm +-is-SUM
     (implies (and (integerp a)
                   (integerp b))
              (equal (+ a b)
                     (sum a b)))
     :hints (("Goal"
              :in-theory (e/d (sum) ()))))

   (defthm mod2-is-m2
     (implies (integerp x)
              (equal (mod x 2)
                     (m2 x)))
     :hints (("Goal"
              :in-theory (e/d (m2) (mod)))))

   (defthm floor2-if-f2
     (implies (integerp x)
              (equal (floor x 2)
                     (f2 x)))
     :hints (("Goal"
              :in-theory (e/d (f2) (floor)))))

   #|(defthm c-is-f2
   (equal (c hash-code a b c)
   (f2 (sum (sum-list a) (sum-list b) c)))
   :hints (("Goal"
   :in-theory (e/d (c f2 sum sum-list)
   (+-is-SUM
   floor2-if-f2
   mod2-is-m2)))))||#

   #|(defthm s-is-m2
   (equal (s hash-code b c)
   (m2 (sum (sum-list b) c)))
   :hints (("Goal"
   :in-theory (e/d (s m2 sum sum-list)
   (+-is-SUM
   floor2-if-f2
   mod2-is-m2)))))||#

   (defthm sum-list-is-sum
     (equal (sum-list (cons a b))
            (sum a (sum-list b)))
     :hints (("Goal"
              :expand (sum-list (cons a b))
              :in-theory (e/d (sum-list sum
                                        )
                              (SUM-OF-IFIX
                               +-is-SUM)))))

   (defthm s-spec-is-m2
     (equal (s-spec lst)
            (m2 (sum-list lst)))
     :hints (("Goal"
              :in-theory (e/d (s-spec) ()))))

   (defthm c-spec-is-m2
     (equal (c-spec lst)
            (f2 (sum-list lst)))
     :hints (("Goal"
              :in-theory (e/d (c-spec) ()))))

   (defthm s-c-spec-is-list-m2-f2
     (equal (s-c-spec sum)
            (list (m2 (sum-list sum))
                  (f2 (sum-list sum))))
     :hints (("Goal"
              :in-theory (e/d (s-c-spec) ()))))

   (defthm c-s-spec-is-list-m2-f2
     (equal (c-s-spec sum)
            (list (f2 (sum-list sum))
                  (m2 (sum-list sum))))
     :hints (("Goal"
              :in-theory (e/d (c-s-spec) ()))))

   (defthm S-OF-C-TRIG-def
     (equal (S-OF-C-TRIG x)
            x)
     :hints (("Goal"
              :in-theory (e/d (s-of-c-trig) ()))))

   (defthm loghead-is-logapp
     (implies (and (integerp term)
                   (natp size))
              (equal (loghead size term)
                     (logapp size term 0)))
     :hints (("Goal"
              :in-theory (e/d () ()))))

   (defthm integerp-4vec-concat$
     (implies (and (integerp a)
                   (integerp b)
                   (natp size))
              (integerp (svl::4vec-concat$ size a b)))
     :hints (("Goal"
              :use ((:instance logapp-is-4vec-concat$))
              :in-theory (e/d ()
                              (logapp-is-4vec-concat$)))))))

(encapsulate
  nil
  (local
   (defthm svl-sum-col-bybit-aux-is-sum-col-bybit-simple
     (implies (and (integerp mult)
                   (integerp mcand))
              (equal (svl-sum-col-bybit-aux mult mcand col-index)
                     (sum-col-bybit-simple mult mcand col-index)))
     :hints (("Goal"
              :in-theory (e/d (svl-sum-col-bybit-aux
                               sum-col-bybit-simple
                               svl::natp-implies-integerp
                               svl::bitp-implies-natp
                               )
                              (logbitp ash
                                       ifix))))))

  (local
   (defthm svl-sum-col-bybit-is-sum-col-bybit-simple
     (implies (and (integerp mult)
                   (integerp mcand))
              (equal (svl-sum-col-bybit mult 0 mcand col-index)
                     (sum-col-bybit-simple mult mcand col-index)))
     :hints (("Goal"
              :in-theory (e/d ()
                              (logbitp ash
                                       ifix))))))

  (local
   (defthm sum-pps-bycol-bybit-is-svl-sum-pps-bycol-bybit
     (implies (and (integerp mult)
                   (integerp mcand)
                   (integerp carry-in))
              (equal (svl-sum-pps-bycol-bybit mult mcand carry-in out-size col-index)
                     (sum-pps-bycol-bybit-simple mult mcand carry-in out-size col-index)))
     :hints (("Goal"
              :in-theory (e/d (sum-pps-bycol-bybit-simple
                               svl-sum-pps-bycol-bybit)
                              (logbitp ash
                                       SVL::4VEC-CONCAT$-OF-TERM2=0
                                       ifix))))))

  (def-rp-rule :disabled-for-acl2 t
    mult-final-spec-is-svl-mult-final-spec
    (implies (and (integerp mult)
                  (integerp mcand))
             (equal (mult-final-spec mult mcand out-size)
                    (svl-mult-final-spec mult mcand out-size)))
    :hints (("Goal"
             :in-theory (e/d (mult-final-spec
                              svl-mult-final-spec) ())))))

(def-rp-rule loghead-of-*-is-svl-mult-final-spec-1 ;;for unsigned multiplication
  (implies (and (integerp mult)
                (integerp mcand)
                (natp mult-size)
                (natp mcand-size)
                (natp out-size)
                #|(syntaxp (or (rp::pp-and$-order mult mcand)
                (not (cw "WARNING! Proof will be faster if var name ~p0 ~
                came before var name ~p1 as determined by rp::pp-and$-order ~%" mult mcand))))||#)
           (equal (loghead out-size
                           (* (loghead mult-size mult)
                              (loghead mcand-size mcand)))
                  (svl-mult-final-spec
                   (svl::4vec-concat$ mult-size mult 0)
                   (svl::4vec-concat$ mcand-size mcand 0)
                   out-size)))
  :hints (("Goal"
           :use ((:instance loghead-of-*-is-mult-final-spec
                            (mult (SVL::4VEC-CONCAT$ MULT-SIZE MULT 0))
                            (mcand (SVL::4VEC-CONCAT$ MCAND-SIZE MCAND 0))))
           :in-theory (e/d (mult-final-spec-is-svl-mult-final-spec)
                           (nfix loghead
                                 loghead-of-*-is-mult-final-spec)))))

(def-rp-rule loghead-of-*-is-svl-mult-final-spec-2 ;;for signed multiplication.
  (implies (and (integerp mult)
                (integerp mcand)
                (natp mult-size)
                (natp mcand-size)
                (bitp mult-msb)
                (bitp mcand-msb)
                (natp out-size)
                #|(syntaxp (or (rp::pp-and$-order mult mcand)
                (not (cw "WARNING! Proof will be faster if var name ~p0 ~
                came before var name ~p1 as determined by rp::pp-and$-order ~%" mult mcand))))||#)
           (equal (loghead out-size
                           (* (logapp mult-size mult (- mult-msb))
                              (logapp mcand-size mcand (- mcand-msb))))
                  (svl-mult-final-spec
                   (svl::4vec-concat$ mult-size mult (- mult-msb))
                   (svl::4vec-concat$ mcand-size mcand (- mcand-msb))
                   out-size)))
  :hints (("Goal"
           :use ((:instance loghead-of-*-is-mult-final-spec
                            (mult (svl::4vec-concat$ mult-size mult (- mult-msb)))
                            (mcand (svl::4vec-concat$ mcand-size mcand (- mcand-msb)))))
           :in-theory (e/d (mult-final-spec-is-svl-mult-final-spec)
                           (nfix loghead
                                 logapp
                                 loghead-of-*-is-mult-final-spec)))))

(def-rp-rule bits-*-IS-MULT-FINAL-SPEC ;;for unsigned multiplication
  (implies (and (integerp mult)
                (integerp mcand)
                (natp out-size)
                #|(syntaxp (or (rp::pp-and$-order mult mcand)
                (not (cw "WARNING! Proof will be faster if var name ~p0 ~
                came before var name ~p1 as determined by rp::pp-and$-order ~%" mult mcand))))||#)
           (equal (svl::bits (* mult mcand) 0 out-size)
                  (svl-mult-final-spec mult mcand out-size)))
  :hints (("Goal"
           :use ((:instance loghead-of-*-is-mult-final-spec))
           :in-theory (e/d (mult-final-spec-is-svl-mult-final-spec
                            svl::bits
                            SV::4VEC-PART-SELECT
                            SV::4VEC->UPPER
                            SV::4VEC->LOWER
                            SVL::4VEC-CONCAT$)
                           (nfix loghead
                                 loghead-of-*-is-mult-final-spec)))))

(def-rp-rule integerp-of-*
  (implies (and (integerp x)
                (integerp y))
           (integerp (* x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Openers:

(progn
  (def-rp-rule svl-sum-col-bybit-opener-col-index>0
    (implies (not (zp col-index))
             (equal (svl-sum-col-bybit mult start mcand col-index)
                    (sum (and$
                          (bits-to-bit-of (svl::bits mult start 1))
                          (bits-to-bit-of (svl::bits mcand col-index 1)))
                         (svl-sum-col-bybit mult
                                            (1+ start)
                                            mcand (1- col-index)))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (svl-sum-col-bybit and$) ()))))

  #|(defthm svl-sum-col-bybit-opener-col-index>0-reverse
  (implies (not (zp col-index))
  (equal (svl-sum-col-bybit mult mcand col-index)
  (pp-sum (and$ (svl::bits 0 1 mult)
  (svl::bits col-index 1 mcand))
  (svl-sum-col-bybit (sv::4vec-rsh 1 mult)
  mcand (1- col-index)))))
  :hints (("Goal"
  :in-theory (e/d (svl-sum-col-bybit merge-pp-sum
  pp-sum) ()))))||#

  #|(defthm svl-sum-col-bybit-opener-mult=0
  (equal (svl-sum-col-bybit mult start mcand col-index)
  0)
  :hints (("Goal"
  :in-theory (e/d (svl-sum-col-bybit
  and$) ()))))||#

  (def-rp-rule svl-sum-col-bybit-opener-col-index=0
    (equal (svl-sum-col-bybit mult start mcand 0)
           (and$ (bits-to-bit-of (svl::bits mult start 1))
                 (bits-to-bit-of (svl::bits mcand 0 1))))
    :hints (("goal"
             :in-theory (e/d (svl-sum-col-bybit) ())))))

(progn
  (def-rp-rule svl-sum-pps-bycol-bybit-opener-zp
    (implies (zp (- out-size col-index))
             (equal (svl-sum-pps-bycol-bybit mult mcand carry-in
                                             out-size col-index)
                    0))
    :hints (("Goal"
             :in-theory (e/d (svl-sum-pps-bycol-bybit) ()))))

  (def-rp-rule svl-sum-pps-bycol-bybit-opener
    (implies (not (zp (- out-size col-index)))
             (equal (svl-sum-pps-bycol-bybit mult mcand carry-in
                                             out-size col-index)
                    (b* (((list s c)
                          (s-c-spec
                           (list (sort-sum (svl-sum-col-bybit mult 0 mcand col-index))
                                 carry-in))))
                      (svl::4vec-concat$
                       1
                       s
                       (svl-sum-pps-bycol-bybit mult mcand c
                                                out-size (1+ col-index))))))
    :hints (("goal"
             :in-theory (e/d (svl-sum-pps-bycol-bybit
                              sort-sum) ())))))

(in-theory (enable svl-mult-final-spec))

(define 4vec-adder ((x integerp)
                    (y integerp)
                    (carry-in integerp)
                    (size natp))
  :verify-guards nil
  (if (zp size)
      0
    (let ((sum (list (svl::bits x 0 1)
                     (svl::bits y 0 1)
                     carry-in)))
      (svl::4vec-concat$ 1
                         (s-spec sum)
                         (4vec-adder (svl::4vec-rsh 1 x)
                                     (svl::4vec-rsh 1 y)
                                     (c-spec sum)
                                     (1- size)))))
  ///
  (def-rp-rule 2vec-adder-is-4vec-adder ;; for backwards compatibility
    (implies (and (integerp x)
                  (integerp y)
                  (integerp carry-in)
                  (natp size))
             (equal (2vec-adder x y carry-in size)
                    (4vec-adder x y carry-in size)))
    :hints (("Goal"
             :in-theory (e/d (2vec-adder
                              BIT-CONCAT)
                             ())))))

(encapsulate
  nil

  (local
   (progn
     (defthm 4vec-rsh-by-1-is-f2
       (implies (integerp x)
                (equal (sv::4vec-rsh 1 x)
                       (f2 x)))
       :hints (("goal"
                :use ((:instance acl2::floor-cancel-*-const
                                 (acl2::lhs (* x 1/2))
                                 (acl2::rhs 1)
                                 (acl2::c 2))
                      (:instance acl2::|(* y (* x z))|
                                 (acl2::y 2)
                                 (acl2::x x)
                                 (acl2::z 1/2)))

                :in-theory (e/d (f2
                                 ash
                                 ifix
                                 sv::4vec-shift-core
                                 sv::4vec->upper
                                 sv::4vec->lower
                                 acl2::|arith (* x 1)|
                                 acl2::|(* y (* x z))|
                                 acl2::|arith (* y (* x z))|
                                 sv::4vec-rsh)
                                (floor2-if-f2
                                 ash-minus1-is-4vec-rsh)))))

     (defthm bits-0-1-is-m2
       (implies (integerp x)
                (equal (svl::bits x 0 1)
                       (m2 x)))
       :hints (("goal"
                :do-not '(preprocess)
                :in-theory (e/d (m2 svl::bits
                                    sv::4vec-part-select
                                    ifix
                                    sv::4vec->upper
                                    logapp
                                    mod
                                    loghead
                                    sv::4vec-concat
                                    sv::4vec-zero-ext
                                    sv::4vec->lower)
                                (svl::4vec-part-select-is-bits

                                 loghead-is-logapp
                                 svl::4vec-zero-ext-is-4vec-concat
                                 mod2-is-m2
                                 logapp-is-4vec-concat$
                                 svl::4vec-zero-ext-is-bits
                                 svl::4vec-concat$-of-term2=0
                                 svl::convert-4vec-concat-to-4vec-concat$)))))))

  (def-rp-rule 4vec-plus++-is-4vec-adder
    (implies (and (integerp x)
                  (integerp y)
                  (integerp carry-in)
                  #|(syntaxp (or (and (not (equal y '0))
                  (not (equal y ''0)))
                  (and (or (equal y '0)
                  (equal y ''0))
                  (or (equal x '0)
                  (equal x ''0)))))|#
                  (natp size))
             (equal (svl::4vec-plus++ x y carry-in size)
                    (4vec-adder x y carry-in size)))
    :hints (("goal"
             :induct (4vec-adder x y carry-in size)
             :in-theory (e/d (svl::4vec-plus++
                              4vec-adder
                              ifix)
                             ()))))

  (def-rp-rule 4vec-adder-opener-0
    (equal (4vec-adder x y carry-in 0)
           0)
    :hints (("goal"
             :in-theory (e/d (4vec-adder) ()))))

  (def-rp-rule 4vec-adder-opener-size>0
    (implies (not (zp size))
             (equal (4vec-adder x y carry-in size)
                    (b* (((list s c) (s-c-spec (list (bits-to-bit-of (svl::bits x 0 1))
                                                     (bits-to-bit-of (svl::bits y 0 1))
                                                     carry-in))))
                      (svl::4vec-concat$ 1 (s-of-c-trig s)
                                         (4vec-adder (sv::4vec-rsh 1 x)
                                                     (sv::4vec-rsh 1 y)
                                                     c
                                                     (1- size))))))
    :hints (("goal"
             :in-theory (e/d (4vec-adder
                              s-c-spec) ())))))

(defmacro svl::sign-ext (num size)
  `(logapp ,size ,num (- (svl::bits ,num (1- ,size) 1))))

(defmacro rp::sign-ext (num size)
  `(logapp ,size ,num (- (svl::bits ,num (1- ,size) 1))))

(def-rw-opener-error
  bits-to-bit-of-opener-error
  (bits-to-bit-of x))

(def-rp-rule
  bits-to-bit-of-opener
  (equal (bits-to-bit-of x)
         x))

;; this should never be used because of (:rewrite bits-is-bit-of)?
(def-rp-rule bits-to-bit-of-with-wrapper
  (implies (and (syntaxp (atom (ex-from-rp num)))
                (integerp num)
                (natp start))
           (equal (bits-to-bit-of (svl::bits num start 1))
                  (bit-of num start))))

(encapsulate
  nil

  (local
   (use-ihs-extensions t))

  (def-rp-rule bits-of-plus
    (implies (and (natp start)
                  (natp size)
                  (integerp x)
                  (integerp y))
             (equal (svl::bits (+ x y) start size)
                    (svl::bits (loghead (+ start size) (+ x y))
                               start size)))
    :hints (("Goal"
             :cases ((equal start 0))
             :in-theory (e/d (svl::bits
                              natp
                              ;;SVL::ASH-TO-4VEC-RSH
                              SV::4VEC-PART-SELECT
                              SV::4VEC-CONCAT
                              SVL::4VEC-CONCAT$
                              SV::4VEC->LOWER
                              SV::4VEC->upper
                              SV::4VEC-ZERO-EXT
                              SV::4VEC-RSH
                              SV::4VEC-SHIFT-CORE)
                             (loghead
                              LOGHEAD-OF-+-IS-2VEC-ADDER-WITHOUT-CARRY
                              SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
                              LOGAPP-IS-4VEC-CONCAT$
                              LOGHEAD-IS-LOGAPP
                              +-is-SUM
                              mod2-is-m2
                              floor2-if-f2)))))

  (def-rp-rule bits-of-mult
    (implies (and (natp start)
                  (natp size)
                  (integerp x)
                  (integerp y))
             (equal (svl::bits (* x y) start size)
                    (svl::bits (loghead (+ start size) (* x y))
                               start size)))
    :hints (("Goal"
             :cases ((equal start 0))
             :in-theory (e/d (svl::bits
                              natp
                              ;;SVL::ASH-TO-4VEC-RSH
                              SV::4VEC-PART-SELECT
                              SV::4VEC-CONCAT
                              SVL::4VEC-CONCAT$
                              SV::4VEC->LOWER
                              SV::4VEC->upper
                              SV::4VEC-ZERO-EXT
                              SV::4VEC-RSH
                              SV::4VEC-SHIFT-CORE)
                             (loghead
                              LOGHEAD-OF-*-IS-MULT-FINAL-SPEC
                              LOGHEAD-OF-+-IS-2VEC-ADDER-WITHOUT-CARRY
                              SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
                              LOGAPP-IS-4VEC-CONCAT$
                              LOGHEAD-IS-LOGAPP
                              +-is-SUM
                              mod2-is-m2
                              floor2-if-f2))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(Local
 (defthm *-of-bits-lemma-for-*-of-bits
   (not (< x x))))

(progn
  (defun unsigned-byte-p-recursive (size x)
    (and (natp size)
         (if (zp size)
             (equal x 0)
           (and (integerp x)
                (unsigned-byte-p-recursive  (1- size)
                                            (acl2::logcdr x))))))

  (defthmd unsigned-byte-p-redef-to-recursive
    (implies t
             (equal (unsigned-byte-p size x)
                    (unsigned-byte-p-recursive size x)))
    :hints (("Goal"
             :expand ((UNSIGNED-BYTE-P SIZE X)
                      (UNSIGNED-BYTE-P 0 X))
             :induct (unsigned-byte-p-recursive size x)
             :do-not-induct t
             :in-theory (e/d ()
                             (unsigned-byte-p)))))

  (defthm unsigned-byte-p-recursive-implies-integerp
    (implies (unsigned-byte-p-recursive size x)
             (and (natp size)
                  (integerp x)))
    :rule-classes :forward-chaining)

  (defthm unsigned-byte-p-redef-to-recursive-of-minus-1
    (not (UNSIGNED-BYTE-P-RECURSIVE size -1))))

(encapsulate
  nil
  (local
   (use-arithmetic-5 t))

  (progn
    (defun *-recursive (x y)
      (declare (xargs
                :hints (("Goal"
                         :in-theory (e/d () (+-IS-SUM))))))
      (if (or (not (integerp x))
              (equal x 0))
          0
        (if (equal x -1)
            (- y)
          (+ (if (acl2::logbitp 0 x) y 0)
             (* 2 (*-recursive (acl2::logcdr x) y))))))
    (local
     (defthmd *-to-recursive-redef-lemma
       (implies (and (integerp x)
                     (syntaxp (equal x 'x)))
                (equal (* x y)
                       (if (LOGBITP 0 X)
                           (* (1+ (* 2 (acl2::logcdr x))) y)
                         (* (* 2 (acl2::logcdr x)) y))))
       :hints (("Goal"
                :in-theory (e/d (
                                 oddp evenp LOGBITP)
                                (+-IS-SUM))))))

    (defthmd *-to-recursive-redef
      (implies (and (integerp x)
                    (integerp y))
               (equal (* x y)
                      (*-recursive x y)))
      :hints (("Goal"
               :in-theory (e/d (*-to-recursive-redef-lemma)
                               (ACL2::LOGCDR$INLINE
                                +-IS-SUM)))))


    (defthm integerp-of-*-recursive
      (implies (and (integerp x)
                    (integerp y))
               (integerp (*-recursive x y))))))

(encapsulate
  nil
  (local
   (use-arithmetic-5 t))

  (progn
    (defun *-recursive2 (x y)
      (declare (xargs
                :hints (("Goal"
                         :in-theory (e/d () (+-IS-SUM))))))
      (if (zp x)
          0
        (+ y (*-recursive2 (1- x) y))))
    
    

    (defthmd *-to-recursive2-redef
      (implies (and (natp x)
                    (natp y))
               (equal (* x y)
                      (*-recursive2 x y)))
      :hints (("Goal"
               :in-theory (e/d ()
                               (ACL2::LOGCDR$INLINE
                                +-IS-SUM)))))


    (defthm integerp-of-*-recursive2
      (implies (and (integerp x)
                    (integerp y))
               (integerp (*-recursive2 x y))))))




(encapsulate
  nil
  (local
   (use-arithmetic-5 t))

  (local
   (defthm +-boundry-lemma1
     (implies (and (natp x)
                   (natp y)
                   (< x u1)
                   (< y u2))
              (< (+ x y) (+ u1 u2)))))

  (local
   (use-arithmetic-5 nil))

  (local
   (in-theory (disable +-IS-SUM)))

  (local
   (defun dec-dec-induct (n m)
     (if (or (zp n) (zp m))
         nil (dec-dec-induct (- n 1) (- m 1))))) 
  
  (Local
   (defthm *-boundry-lemma1
     (implies (and (natp x)
                   (natp y)
                   (natp u1)
                   (natp u2)
                   (< x u1)
                   (< y u2))
              (< (* x y) (* u1 u2)))
     :hints (("Goal"
              :induct (dec-dec-induct x u1)
              :do-not-induct t
              :in-theory (e/d (*-to-recursive2-redef
                               *-RECURSIVE)
                              (+-IS-SUM
                               ACL2::LOGCDR))))))

  (local
   (use-arithmetic-5 t))

  (local
   (defthm split-expt-2-lemma
     (Implies (and (natp size1)
                   (natp size2))
              (equal (EXPT 2 (+ SIZE1 SIZE2))
                     (* (expt 2 size1)
                        (expt 2 size2))))))

  (local
   (defthm LOGCDR-of-*recursive-*
     (Implies (integerp x)
              (equal (ACL2::LOGCDR (*-RECURSIVE 2 x))
                     x))
     :hints (("Goal"
              :expand ((*-RECURSIVE 2 X)
                       (*-RECURSIVE 1 X))
              :in-theory (e/d () (FLOOR2-IF-F2))))))

  (defthm unsigned-byte-p-of-*
    (implies (and (unsigned-byte-p size1 x)
                  (unsigned-byte-p size2 y))
             (unsigned-byte-p (+ size1 size2)
                              (* x y)))
    :hints (("Goal"
             #| :induct (and (unsigned-byte-p-recursive (+ size1 size2)
             (* x y)) ;
             (unsigned-byte-p-recursive siz21 ;
             x) ;
             (unsigned-byte-p-recursive size2 ;
             y)) ;
             :do-not-induct t ;
             :expand ((UNSIGNED-BYTE-P-RECURSIVE (+ SIZE1 SIZE2) ;
             (* X Y)) ;
             (UNSIGNED-BYTE-P-RECURSIVE ;
             (+ SIZE1 SIZE2) ;
             (*-RECURSIVE 2 (*-RECURSIVE (ACL2::LOGCDR X) Y))) ;
             (UNSIGNED-BYTE-P-RECURSIVE ;
             (+ SIZE1 SIZE2) ;
             (+ Y ;
             (*-RECURSIVE 2 (*-RECURSIVE (ACL2::LOGCDR X) Y)))))|#
             :in-theory (e/d (;;unsigned-byte-p-redef-to-recursive
                              ;;*-to-recursive-redef
                              )
                             (+-is-SUM
                              ACL2::NORMALIZE-FACTORS-GATHER-EXPONENTS
                              FLOOR2-IF-F2
                              ACL2::LOGCDR$INLINE))))))

(encapsulate
  nil
  (Local
   (use-arithmetic-5 t))
  (local
   (defthm bits-when-unsiged-byte-p
     (implies (and (natp size)
                   (unsigned-byte-p size x))
              (equal (svl::bits x 0 size)
                     x))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (svl::bits
                               SV::4VEC->UPPER
                               SV::4VEC->LOWER
                               SV::4VEC-CONCAT
                               SVL::4VEC-CONCAT$
                               SV::4VEC-PART-SELECT)
                              (LOGAPP-IS-4VEC-CONCAT$
                               LOGHEAD-IS-LOGAPP))))))

  (def-rp-rule unsigned-byte-p-of-bits
    (implies (and ;;(natp size1)
              (natp size2)
              ;;(<= size2 size1)
              (integerp x)
              (natp start))
             (unsigned-byte-p size2 (svl::bits x start size2)))
    :hints (("Goal"
             :in-theory (e/d (SVL::BITS
                              SV::4VEC->UPPER
                              SV::4VEC->lower
                              SV::4VEC-RSH
                              SV::4VEC-CONCAT
                              SV::4VEC-SHIFT-CORE
                              SV::4VEC-PART-SELECT
                              SV::4VEC)
                             (+-is-SUM)))))

  (def-rp-rule *-of-bits
    (implies (and (natp start1)
                  (natp start2)
                  (natp size1)
                  (natp size2)
                  (integerp x)
                  (integerp y))
             (equal (* (svl::bits x start1 size1)
                       (svl::bits y start2 size2))
                    (svl-mult-final-spec (svl::bits x start1 size1)
                                         (svl::bits y start2 size2)
                                         (+ size1 size2))))
    :hints (("Goal"
             :use ((:instance bits-*-IS-MULT-FINAL-SPEC
                              (mult (svl::bits x start1 size1))
                              (mcand (svl::bits y start2 size2))
                              (out-size (+ size1 size2))))
             :in-theory (e/d () (bits-*-IS-MULT-FINAL-SPEC
                                 svl-mult-final-spec
                                 +-is-SUM)))))

  (defthm *-of-known-sized-vecs
    (implies (and (unsigned-byte-p size1 x)
                  (unsigned-byte-p size2 y))
             (equal (* x y)
                    (svl-mult-final-spec x y
                                         (+ size1 size2))))
    :hints (("Goal"
             :use ((:instance bits-*-IS-MULT-FINAL-SPEC
                              (mult x)
                              (mcand y)
                              (out-size (+ size1 size2))))
             :in-theory (e/d () (bits-*-IS-MULT-FINAL-SPEC
                                 svl-mult-final-spec
                                 +-is-SUM))))))
