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

(include-book "centaur/svl/top" :dir :system)

(include-book "spec")

(include-book "meta/pp-order-fncs")

(local
 (in-theory (disable m2 merge-pp-sum merge-sum f2 sum)))

(local
 (include-book "greedy-lemmas"))

(local
 (in-theory (enable bit-fix)))

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

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
            (merge-pp-sum (and$ (svl::bits mult 0 1)
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
           (merge-pp-sum (and$ (svl::bits mult start 1  )
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
    (if (zp (- out-size col-index))
        0
      (b* ((col-sum (svl-sum-col-bybit mult 0 mcand col-index))
           (col-sum (merge-sum col-sum carry-in)))
        (svl::4vec-concat$ 1 (m2 col-sum)
                           (svl-sum-pps-bycol-bybit mult mcand
                                                    (f2 col-sum)
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
                               SVL::4VEC-CONCAT$-OF-SIZE=1-TERM2=0
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

   (defthm +-is-sum
     (implies (and (integerp a)
                   (integerp b))
              (equal (+ a b)
                     (sum a b)))
     :hints (("Goal"
              :in-theory (e/d (sum type-fix) ()))))

   (defthm mod2-if-m2
     (implies (integerp x)
              (equal (mod x 2)
                     (m2 x)))
     :hints (("Goal"
              :in-theory (e/d (m2 type-fix) (mod)))))

   (defthm floor2-if-f2
     (implies (integerp x)
              (equal (floor x 2)
                     (f2 x)))
     :hints (("Goal"
              :in-theory (e/d (f2 type-fix) (floor)))))

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
                               svl::bitp-implies-natp)
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
                                       SVL::4VEC-CONCAT$-OF-SIZE=1-TERM2=0
                                       ifix))))))

  (def-rp-rule$ t nil
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
                (syntaxp (or (rp::pp-and$-order mult mcand)
                             (not (cw "WARNING! Proof will be faster if var name ~p0 ~
  came before var name ~p1 as determined by rp::pp-and$-order ~%" mult mcand)))))
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
                (syntaxp (or (rp::pp-and$-order mult mcand)
                             (not (cw "WARNING! Proof will be faster if var name ~p0 ~
  came before var name ~p1 as determined by rp::pp-and$-order ~%" mult mcand)))))
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
                (syntaxp (or (rp::pp-and$-order mult mcand)
                             (not (cw "WARNING! Proof will be faster if var name ~p0 ~
  came before var name ~p1 as determined by rp::pp-and$-order ~%" mult mcand)))))
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
                    (merge-pp-sum (and$
                                   (svl::bits mult start 1)
                                   (svl::bits mcand col-index 1))
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
           (and$ (svl::bits mult start 1)
                 (svl::bits mcand 0 1)))
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

  (defthm-lambda svl-sum-pps-bycol-bybit-opener
    (implies (not (zp (- out-size col-index)))
             (equal (svl-sum-pps-bycol-bybit mult mcand carry-in
                                             out-size col-index)
                    (b* ((col-sum (merge-sum (svl-sum-col-bybit mult 0 mcand col-index) carry-in)))
                      (svl::4vec-concat$
                       1 (m2-new col-sum)
                       (svl-sum-pps-bycol-bybit mult mcand (f2-new col-sum)
                                                out-size (1+ col-index))))))
    :hints (("goal"
             :in-theory (e/d (svl-sum-pps-bycol-bybit) ())))))

(in-theory (enable svl-mult-final-spec))

(in-theory (disable DEFAULT-*-1
                    DEFAULT-*-2
                    logapp
                    bitp
                    loghead
                    type-fix
                    commutativity-of-*))

(define 4vec-adder ((x integerp)
                    (y integerp)
                    (carry-in integerp)
                    (size natp))
  :verify-guards nil
  (if (zp size)
      0
    (let ((sum (merge-sum (svl::bits x 0 1)
                          (svl::bits y 0 1)
                          carry-in)))
      (svl::4vec-concat$ 1
                         (m2-new sum)
                         (4vec-adder (svl::4vec-rsh 1 x)
                                     (svl::4vec-rsh 1 y)
                                     (f2-new sum)
                                     (1- size))))))

(encapsulate
  nil

  (local
   (progn
     (defthm 4vec-rsh-by-1-is-f2
       (implies (integerp x)
                (equal (sv::4vec-rsh 1 x)
                       (f2-new x)))
       :hints (("Goal"
                :use ((:instance ACL2::FLOOR-CANCEL-*-CONST
                                 (acl2::lhs (* x 1/2))
                                 (acl2::rhs 1)
                                 (acl2::c 2))
                      (:instance ACL2::|(* y (* x z))|
                                 (acl2::y 2)
                                 (acl2::x x)
                                 (acl2::z 1/2)))

                :in-theory (e/d (f2 type-fix
                                    ash
                                    ifix
                                    SV::4VEC-SHIFT-CORE
                                    SV::4VEC->UPPER
                                    SV::4VEC->LOWER
                                    acl2::|arith (* x 1)|
                                    acl2::|(* y (* x z))|
                                    acl2::|arith (* y (* x z))|
                                    sv::4vec-rsh)
                                (floor2-if-f2
                                 ASH-MINUS1-IS-4VEC-RSH)))))

     (defthm bits-0-1-is-m2
       (implies (integerp x)
                (equal (svl::bits x 0 1)
                       (m2-new x)))
       :hints (("Goal"
                :do-not '(preprocess)
                :in-theory (e/d (m2 svl::bits type-fix
                                    SV::4VEC-PART-SELECT
                                    ifix
                                    SV::4VEC->UPPER
                                    logapp
                                    mod
                                    loghead
                                    SV::4VEC-CONCAT
                                    SV::4VEC-ZERO-EXT
                                    SV::4VEC->LOWER)
                                (SVL::4VEC-PART-SELECT-IS-BITS
                                 MOD2-IF-M2
                                 LOGHEAD-IS-LOGAPP
                                 SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
                                 LOGAPP-IS-4VEC-CONCAT$
                                 SVL::4VEC-ZERO-EXT-IS-BITS
                                 SVL::4VEC-CONCAT$-OF-SIZE=1-TERM2=0
                                 SVL::CONVERT-4VEC-CONCAT-TO-4VEC-CONCAT$)))))))

  (def-rp-rule 4vec-plus++-is-4vec-adder
    (implies (and (integerp x)
                  (integerp y)
                  (integerp carry-in)
                  (natp size))
             (equal (svl::4vec-plus++ x y carry-in size)
                    (4vec-adder x y carry-in size)))
    :hints (("Goal"
             :induct (4VEC-ADDER X Y CARRY-IN SIZE)
             :in-theory (e/d (svl::4vec-plus++
                              4vec-adder
                              ifix)
                             ()))))

  (def-rp-rule 4vec-adder-opener-0
    (equal (4vec-adder x y carry-in 0)
           0)
    :hints (("Goal"
             :in-theory (e/d (4vec-adder) ()))))

  (defthm-lambda 4vec-adder-opener-size>0
    (implies (not (zp size))
             (equal (4vec-adder x y carry-in size)
                    (LET ((SUM (MERGE-SUM (SVL::BITS x 0 1)
                                          (SVL::BITS y 0 1)
                                          CARRY-IN)))
                         (SVL::4VEC-CONCAT$ 1 (M2-NEW SUM)
                                            (4VEC-ADDER (SV::4VEC-RSH 1 X)
                                                        (SV::4VEC-RSH 1 Y)
                                                        (F2-NEW SUM)
                                                        (1- SIZE))))))
    :hints (("Goal"
             :in-theory (e/d (4vec-adder) ())))))

(defmacro svl::sign-ext (num size)
  `(logapp ,size ,num (- (svl::bits ,num (1- ,size) 1))))

(defmacro rp::sign-ext (num size)
  `(logapp ,size ,num (- (svl::bits ,num (1- ,size) 1))))
