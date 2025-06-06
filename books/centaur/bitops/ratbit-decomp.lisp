;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Author: Sol Swords <sol.swords@arm.com>

(in-package "ACL2")
(include-book "ratbits")
(include-book "centaur/bitops/trailing-0-count" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "centaur/misc/multiply-out" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable unsigned-byte-p)))

(local (in-theory (disable acl2::<-*-/-right-commuted
                           acl2::<-*-/-left-commuted
                           acl2::<-unary-/-positive-right
                           acl2::<-*-/-right
                           acl2::<-*-/-left
                           (tau-system))))

(local (in-theory (disable multiply-out-<
                           acl2::/r-when-abs-numerator=1
                           acl2::floor-=-x/y)))
(local (in-theory (disable ACL2::MOD-X-Y-=-X+Y-FOR-RATIONALS
                           floor-bounded-by-/
                           mod-x-y-=-x-for-rationals
                           floor-=-x/y)))


(defsection repeating-bits-measure
  ;; The measure function for repeating-bits-aux is a bit awkward to define.
  ;; The argument is that all the possible input values are positive numbers
  ;; less than div, so we can go through at most div-1 iterations before we
  ;; come to a value we've seen before. In fact, this value that we come to has
  ;; to be the value we started with, because the step function (num*2 mod div)
  ;; is injective in num when div is odd -- whatever value we first collide
  ;; with, we would have collided with its preimage first unless it was the
  ;; starting value.

  ;; We bootstrap the measure for this iteration by first using a function
  ;; repeating-bits-collect that tracks all seen values, stopping if we hit a
  ;; value we've already seen.  The measure for this function is the number of
  ;; values (naturals less than div) we haven't seen. Then, the measure for
  ;; repeating-bits-aux presupposes that the num input is a member of the list
  ;; of values collected by repeating-bits-collect, that measure being the
  ;; length of the tail starting with that value. 
  (local (include-book "std/lists/sets" :dir :system))



  (define list-nats-under ((n natp))
    (if (zp n)
        nil
      (cons (1- n) (list-nats-under (1- n))))
    ///
    (defthm len-of-list-nats-under
      (equal (len (list-nats-under n)) (nfix n)))

    (defthm member-of-list-nats-under
      (iff (member-equal k (list-nats-under n))
           (and (natp k) (< k (nfix n)))))

    (defthm no-duplicates-of-list-nats-under
      (no-duplicatesp-equal (list-nats-under n))))


  (local
   (encapsulate nil

     (local
      (defun ind (y x)
        (if (atom y)
            x
          (ind (cdr y) (remove-equal (car y) x)))))

     (defthm subsetp-remove
       (implies (subsetp-equal x y)
                (subsetp-equal (remove-equal (car y) x) (cdr y))))

     (defthm len-remove-equal-when-no-dups
       (implies (no-duplicatesp-equal x)
                (equal (len (remove-equal k x))
                       (if (member-equal k x)
                           (- (len x) 1)
                         (len x)))))

     (defthm len-remove-equal-bound-when-member
       (implies (member-equal k x)
                (<= (len (remove-equal k x)) (- (len x) 1)))
       :rule-classes :linear)

     (defthm len-remove-equal-bound
       (<= (len (remove-equal k x)) (len x))
       :rule-classes :linear)

     (defthm no-dups-of-remove
       (implies (no-duplicatesp-equal x)
                (no-duplicatesp-equal (remove-equal k x))))

     (defthm set-difference-equal-of-remove
       (implies (not (member-equal k y))
                (equal (set-difference-equal y (remove-equal k x))
                       (set-difference-equal y x))))

     (defthm intersection-equal-of-remove
       (implies (not (member-equal k y))
                (equal (intersection-equal y (remove-equal k x))
                       (intersection-equal y x))))

     (defthm len-set-diff-when-subset
       (implies (and (subsetp-equal x y)
                     (no-duplicatesp-equal y)
                     (no-duplicatesp-equal x))
                (equal (len (set-difference-equal y x))
                       (- (len y) (len x))))
       :hints (("goal" :induct (ind y x))))

     (defthm len-intersection-when-no-dups
       (implies (no-duplicatesp-equal y)
                (<= (len (intersection-equal y x))
                    (len x)))
       :hints (("goal" :induct (ind y x)))
       :rule-classes :linear)

     (defthm no-dups-of-remove-dups
       (no-duplicatesp-equal (remove-duplicates-equal x)))))
             


  (define repeating-bits-meas-fix-seen (seen div)
    :verify-guards nil
    (intersection-equal (remove-duplicates-equal seen)
                        (list-nats-under div))
    ///
    (defthm repeating-bits-meas-fix-seen-bound
      (<= (len (repeating-bits-meas-fix-seen seen div)) (nfix div))
      :rule-classes :linear)

    (defthm len-of-repeating-bits-meas-fix-seen-of-cons
      (implies (and (natp num)
                    (< num (nfix div))
                    (not (member-equal num seen)))
               (equal (len (repeating-bits-meas-fix-seen (cons num seen) div))
                      (+ 1 (len (repeating-bits-meas-fix-seen seen div)))))))


  (define repeating-bits-collect (num div seen)
    :measure (- (nfix div) (len (repeating-bits-meas-fix-seen seen div)))
    :verify-guards nil
    (if (and (natp num)
             (natp div)
             (< num div)
             (not (member-equal num seen)))
        (cons num
              (repeating-bits-collect
               (if (< (* 2 num) div)
                   (* 2 num)
                 (- (* 2 num) div))
               div (cons num seen)))
      nil)
    ///
    (defthm repeating-bits-collect-member-equal-*2
      (implies (and (member-equal k (repeating-bits-collect num div seen))
                    (< (* 2 k) div)
                    (not (member-equal (* 2 k) seen)))
               (member-equal (* 2 k) (repeating-bits-collect num div seen)))
      :hints (("goal" :induct t)
              (and stable-under-simplificationp
                   '(:expand ((repeating-bits-collect (* 2 k) div (cons k seen)))))))

    (defthm repeating-bits-collect-member-equal-*2minus
      (implies (and (member-equal k (repeating-bits-collect num div seen))
                    (<= div (* 2 k))
                    (not (member-equal (+ (- div) (* 2 k)) seen)))
               (member-equal (+ (- div) (* 2 k)) (repeating-bits-collect num div seen)))
      :hints (("goal" :induct t)
              (and stable-under-simplificationp
                   '(:expand ((repeating-bits-collect (+ (- div) (* 2 k)) div (cons k seen)))))))

    (local (defthmd integerp-of-half-sides-of-ineq
             (implies (equal x y)
                      (integerp (* 1/2 (- x y))))))
  
    (local (defthm tmp
             (implies (and (integerp x)
                           (integerp y)
                           (integerp z)
                           (not (integerp (* 1/2 z))))
                      (not (equal (+ (- z) (* 2 x)) (* 2 y))))
             :hints (("goal" :use ((:instance integerp-of-half-sides-of-ineq
                                    (x (+ (- z) (* 2 x))) (y (* 2 y))))))
                    
             :otf-flg t))

    (local (defthm member-repeating-bits-implies
             (implies (member-equal k (repeating-bits-collect num div seen))
                      (and (natp k)
                           (natp div)
                           (< k div)))
             :rule-classes :forward-chaining))
  
    (defthm repeating-bits-collect-len-member-equal-*2
      (implies (and (member-equal k (repeating-bits-collect num div seen))
                    ;; (natp k)
                    ;; (< k div)
                    (< (* 2 k) div)
                    (not (integerp (/ div 2)))
                    (not (equal k 0))
                    (not (equal num (* 2 k))))
               (equal (len (member-equal (* 2 k) (repeating-bits-collect num div seen)))
                      (+ -1 (len (member-equal k (repeating-bits-collect num div seen))))))
      :hints (("goal" :induct t
               :expand ((repeating-bits-collect num div seen)))
              (and stable-under-simplificationp
                   '(:expand ((repeating-bits-collect (* 2 k) div (cons k seen)))))))

    (defthm repeating-bits-collect-len-member-equal-*2minus
      (implies (and (member-equal k (repeating-bits-collect num div seen))
                    ;; (natp k)
                    ;; (< k div)
                    (<= div (* 2 k))
                    (not (integerp (/ div 2)))
                    (not (equal k 0))
                    (not (equal num (+ (- div) (* 2 k)))))
               (equal (len (member-equal (+ (- div) (* 2 k)) (repeating-bits-collect num div seen)))
                      (+ -1 (len (member-equal k (repeating-bits-collect num div seen))))))
      :hints (("goal" :induct t
               :expand ((repeating-bits-collect num div seen)))
              (and stable-under-simplificationp
                   '(:expand ((repeating-bits-collect (+ (- div) (* 2 k)) div (cons k seen))))))))

  (define repeating-bits-measure (num div first)
    :verify-guards nil
    (len (member-equal num (repeating-bits-collect first div nil)))
    ///
    (defthm repeating-bits-measure-correct-*2
      (implies (and (member-equal num (repeating-bits-collect first div nil))
                    (not (equal (* 2 num) first))
                    (natp div)
                    (not (integerp (/ div 2)))
                    (natp first)
                    (not (equal num 0))
                    (< (* 2 num) div))
               (equal (repeating-bits-measure (* 2 num) div first)
                      (1- (repeating-bits-measure num div first)))))

    (defthm repeating-bits-measure-correct-*2minus
      (implies (and (member-equal num (repeating-bits-collect first div nil))
                    (not (equal (+ (- div) (* 2 num)) first))
                    (natp div)
                    (not (integerp (/ div 2)))
                    (natp first)
                    (not (equal num 0))
                    (<= div (* 2 num)))
               (equal (repeating-bits-measure (+ (- div) (* 2 num)) div first)
                      (1- (repeating-bits-measure num div first)))))))




(define repeating-bits-aux ((num natp)
                            (div natp)
                            (first natp))
  :guard (and (< 0 num)
              (< num div)
              (< first div)
              (not (integerp (* 1/2 div)))
              (member-equal num (ec-call (repeating-bits-collect first div nil))))
  :verify-guards nil
  :returns (mv (val natp :rule-classes :type-prescription)
               (nbits posp :rule-classes :type-prescription
                      :hints (("goal" :induct t :do-not-induct t)
                              '(:cases ((posp num))))))
  :measure (repeating-bits-measure num div (nfix first))
  (b* ((num (lnfix num))
       (div (lnfix div))
       (first (lnfix first))
       (less (< (* 2 num) div))
       (next (if less (* 2 num) (- (* 2 num) div)))
       ((unless (and (mbt (and (member-equal num (repeating-bits-collect first div nil))
                               (posp num)
                               (< num div)
                               (not (integerp (* 1/2 div)))))
                     (not (eql next first))))
        (mv (if less 0 1) 1))
       ((mv restval restbits)
        (repeating-bits-aux next div first)))
    (mv (logapp restbits restval (if less 0 1))
        (+ 1 restbits)))
  ///
  (verify-guards repeating-bits-aux)

  (defret repeating-bits-aux-size
    (unsigned-byte-p nbits val))

  (std::defretd repeating-bits-aux-correct
    (implies (and (integerp num)
                  (< 0 num)
                  (integerp div)
                  (< num div)
                  (not (integerp (* 1/2 div)))
                  (natp first)
                  (< first div)
                  (< 0 first)
                  (member-equal num (repeating-bits-collect first div nil)))
             (equal val
                    (- (* (expt 2 nbits) (/ num div)) (/ first div))))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable logapp))))))


(define repeating-bits ((num natp) (div natp))
  :guard (and (< num div)
              (not (integerp (* 1/2 div))))
  :guard-hints (("goal" :Expand ((repeating-bits-collect num div nil)
                                 (:free (next) (repeating-bits-collect next div (list num))))))
  :returns (mv (val natp :rule-classes :type-prescription)
               (nbits posp :rule-classes :type-prescription))
  (b* ((num (lnfix num))
       (div (lnfix div))
       ((when (eql num 0)) (mv 0 1))
       (less (< (* 2 num) div))
       (next (if less (* 2 num) (- (* 2 num) div)))
       ((mv restval restbits)
        (repeating-bits-aux next div num)))
    (mv (logapp restbits restval (if less 0 1))
        (+ 1 restbits)))
  ///
  (defret <fn>-size
    (unsigned-byte-p nbits val))
 
  (local (defthm member-of-repeating-bits-collect
           (implies (and (natp next)
                         (natp div)
                         (< next div)
                         (not (member-equal next seen)))
                    (member-equal next (repeating-bits-collect next div seen)))
           :hints(("Goal" :expand ((repeating-bits-collect next div seen))))))

  (local (defthm <-when-<=-times-two-when-odd
           (implies (and (not (integerp (* 1/2 div)))
                         (integerp num)
                         (<= div (* 2 num)))
                    (< div (* 2 num)))))
  
  (std::defretd <fn>-correct
    (implies (and (integerp num)
                  (<= 0 num)
                  (integerp div)
                  (< num div)
                  (not (integerp (* 1/2 div))))
             (equal val
                    (* (1- (expt 2 nbits)) (/ num div))))
    :hints(("Goal" :in-theory (enable logapp))
           (and stable-under-simplificationp
                '(:in-theory (enable repeating-bits-aux-correct)
                  :Expand ((repeating-bits-collect num div nil))))))

  (local (defthmd less-of-mult-by-less-than-1
           (implies (and (rationalp x)
                         (< 0 x)
                         (rationalp y)
                         (< y 1))
                    (< (* x y) x))))
  
  (defret <fn>-val-upper-bound
    (implies (and (integerp num)
                  (<= 0 num)
                  (integerp div)
                  (< num div)
                  (not (integerp (* 1/2 div))))
             (<= val (- (expt 2 nbits) 2)))
    :hints (("goal" :use ((:instance <fn>-correct)
                          (:instance less-of-mult-by-less-than-1
                           (x (- (expt 2 (mv-nth 1 (repeating-bits num div))) 1))
                           (y (/ num div))))
             :in-theory (e/d (multiply-out-<)
                             (<fn>-correct
                              multiply-out-equal
                              <fn>))))
    :rule-classes :linear))


(define repbits-fix ((rep integerp)
                     (repbits posp))
  :returns (new-rep natp :rule-classes :type-prescription)
  (let* ((repbits (lposfix repbits))
         (head (loghead repbits rep)))
    (if (eql head (logmask repbits))
        0
      head))
  ///
  (defret repbits-fix-fixes
    (implies (and (natp rep)
                  (< rep (1- (expt 2 (pos-fix repbits)))))
             (equal new-rep rep))
    :hints(("Goal" :in-theory (enable unsigned-byte-p))))

  (defret repbits-fix-bound
    (< new-rep (1- (expt 2 (pos-fix repbits))))
    :hints (("goal" :use ((:instance unsigned-byte-p-of-loghead
                           (i rep) (size (pos-fix repbits))
                           (size1 (pos-fix repbits))))
             :in-theory (e/d (unsigned-byte-p)
                             (unsigned-byte-p-of-loghead))))
    :rule-classes :linear))
  

(fty::defprod rbdecomp
  ((exp integerp :rule-classes :type-prescription)
   (seq integerp :rule-classes :type-prescription)
   (rep integerp
        :reqfix (repbits-fix rep repbits))
   (repbits posp :rule-classes :type-prescription))
  :require (and (<= 0 rep)
                (< rep (1- (expt 2 repbits))))
  :layout :list
  ///
  (defthm rbdecomp->rep-type
    (natp (rbdecomp->rep x))
    :rule-classes :type-prescription)

  (defthm rbdecomp-require-linear
    (< (rbdecomp->rep x) (1- (expt 2 (rbdecomp->repbits x))))
    :rule-classes :linear)

  (defthm unsigned-byte-p-of-rbdecomp->rep
    (unsigned-byte-p (rbdecomp->repbits x) (rbdecomp->rep x))
    :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

(define rbdecomp-eval ((x rbdecomp-p))
  :returns (eval rationalp :rule-classes :type-prescription)
  (b* (((rbdecomp x)))
    (* (expt 2 x.exp)
       (+ x.seq (/ x.rep (1- (expt 2 x.repbits)))))))


(define rational-bit-decomp ((x rationalp))
  :returns (decomp rbdecomp-p)
  :prepwork ((local (defthm logtail-trailing-0-count-when-posp
                      (implies (posp x)
                               (posp (logtail (bitops::trailing-0-count x) x)))
                      :hints(("Goal" :in-theory (e/d* (bitops::trailing-0-count
                                                       bitops::ihsext-recursive-redefs))
                              :induct t))
                      :rule-classes :type-prescription))
             (local (defthm logcar-logtail-trailing-0-count
                      (implies (posp x)
                               (equal (logcar (logtail (bitops::trailing-0-count x) x)) 1))
                      :hints(("Goal" :in-theory (e/d* (bitops::trailing-0-count
                                                       bitops::ihsext-recursive-redefs))
                              :induct t))))
             (local (defthm odd-logtail-trailing-0-count
                      (implies (posp x)
                               (not (integerp (* 1/2 (logtail (bitops::trailing-0-count x) x)))))
                      :hints (("goal" :use logcar-logtail-trailing-0-count
                               :in-theory (e/d (logcar) (logcar-logtail-trailing-0-count
                                                         bitops::logcar-of-logtail))))))
             (local (defthmd ash-logtail-trailing-0-count
                      (equal (ash (logtail (bitops::trailing-0-count x) x)
                                  (bitops::trailing-0-count x))
                             (ifix x))
                      :hints(("Goal" :in-theory (e/d* (bitops::trailing-0-count
                                                       bitops::ihsext-recursive-redefs))
                              :induct t))))
             (local (defthmd logtail-trailing-0-count-arith
                      (equal (logtail (bitops::trailing-0-count x) x)
                             (* (expt 2 (- (bitops::trailing-0-count x))) (ifix x)))
                      :hints (("goal" :use ash-logtail-trailing-0-count
                               :in-theory (e/d (bitops::ash-is-expt-*-x)))))))
                      
  (b* ((num-exp (bitops::trailing-0-count (numerator x)))
       (den-exp (bitops::trailing-0-count (denominator x)))
       (exp (+ num-exp (- den-exp)))
       (num0 (ash (numerator x) (- num-exp)))
       (den0 (ash (denominator x) (- den-exp)))
       (seq (floor num0 den0))
       (num1 (mod num0 den0))
       ((mv rep repbits) (repeating-bits num1 den0)))
    (rbdecomp exp seq rep repbits))
  ///
  ;; (defret rational-bit-decomp-rep-width
  ;;   (unsigned-byte-p repbits rep))

  (local (in-theory (disable (force)
                             multiply-out-equal)))

  (local (defthm distributivity-2
           (equal (* (+ x y) z)
                  (+ (* x z) (* y z)))))

  (local (defthm x*denom
           (implies (rationalp x)
                    (equal (* x (denominator x)) (numerator x)))))
  
  (local (defthm x*denom*z
           (implies (rationalp x)
                    (equal (* x (denominator x) z)
                           (* (numerator x) z)))
           :hints (("goal" :use ((:instance (:theorem (implies (equal x y) (equal (* x z) (* y z))))
                                  (x (* x (denominator x))) (y (numerator x))))))))
  
  (defret rational-bit-decomp-correct
    (equal (rbdecomp-eval decomp)
           (rfix x))
    :hints(("goal" :in-theory (enable rbdecomp-eval))
           (and stable-under-simplificationp
                '(:in-theory (enable repeating-bits-correct)))
           (and stable-under-simplificationp
                '(:in-theory (enable logtail-trailing-0-count-arith)))
           (and stable-under-simplificationp
                '(:in-theory (enable mod)))
           (and stable-under-simplificationp
                '(:in-theory (e/d (multiply-out-equal)
                                  (distributivity-2))))
           )))




(local (defthm ratio-with-expt-minus-1-equals-repeated-ratio
         (implies (and (integerp k)
                       (< 0 k)
                       (integerp x)
                       ;; (< x (+ -1 (expt 2 k)))
                       )
                  (equal (* x (/ (expt 2 k)) (/ (+ -1 (expt 2 k))))
                         (- (/ x (+ -1 (expt 2 k))) (/ x (expt 2 k)))))
         :hints (("goal" :in-theory (enable multiply-out-equal)))))




(encapsulate nil
  (local (include-book "centaur/misc/collect-like-terms" :dir :system))
  (local (defthm ratbitp-in-terms-of-rational-bit-decomp1
           (equal (ratbitp n x)
                  (equal 1 (mod (floor (rbdecomp-eval
                                        (rational-bit-decomp x))
                                       (expt 2 n))
                                2)))
           :hints (("goal" ;; :use rational-bit-decomp-correct
                    :in-theory (enable ratbitp)))))

  (local (defthmd factor-out-expt
           (implies (bind-free
                     (b* ((q '(EXPT '2 (RBDECOMP->EXP$INLINE (RATIONAL-BIT-DECOMP X))))
                          ((mv a-fact ?a-unfact) (factor-out-from-sum q a))
                          ((mv b-fact ?b-unfact) (factor-out-from-sum q b)))
                       (and (not (equal a-fact ''0))
                            (not (equal b-fact ''0))
                            `((q . ,q))))
                     (q))
                    (equal (+ a b)
                           (factor-out-trigger q a b)))
           :hints(("Goal" :in-theory (e/d (factor-out-trigger)
                                          (factor-out-meta))))))

  (local (defthm floor-expt
           (implies (and (rationalp x)
                         (integerp m)
                         (integerp n))
                    (equal (floor (* (expt 2 m) x)
                                  (expt 2 n))
                           (floor x (expt 2 (- n m)))))
           :hints (("goal" :use ((:instance floor-cancel-*-2
                                  (x (expt 2 m)) (y x)
                                  (z (expt 2 (- n m)))))
                    :in-theory (disable floor-cancel-*-2)))))

  (local (defthm floor-expt-2
           (implies (and (rationalp x)
                         (rationalp y)
                         (integerp m)
                         (integerp n))
                    (equal (floor (* y (expt 2 m) x)
                                  (expt 2 n))
                           (floor (* y x) (expt 2 (- n m)))))
           :hints (("goal" :use ((:instance floor-expt (x (* y x))))
                    :in-theory (disable floor-expt)))))

  (local (defun mod-floor-expt-minus1-prod-ind (n k)
           (declare (xargs :measure (nfix (- n))))
           (if (<= (nfix (- n)) (pos-fix k))
               0
             (+ 1 (mod-floor-expt-minus1-prod-ind (+ n (pos-fix k)) k)))))

  (local (in-theory (disable  mod-=-0)))

  (local (in-theory (disable multiply-out-equal)))

  (local (defthm mod-floor-when-floor-equal
           (implies (and (equal (floor x y) (+ A b))
                         (integerp (* 1/2 a))
                         (integerp a)
                         (rationalp b))
                    (equal (mod (floor x y) 2)
                           (mod b 2)))))

  (local (defthmd mod-n-k-when-just-below
           (implies (and (integerp n)
                         (< n 0)
                         (integerp k)
                         (<= (- n) k))
                    (equal (mod n k)
                           (+ n k)))
           :hints(("Goal" :in-theory (enable mod)))))

  (local
   (defun collect-powers-of-2 (x)
     (case-match x
       (('binary-* a b) (append (collect-powers-of-2 a)
                                (collect-powers-of-2 b)))
       (('expt ''2 n) (list n))
       (('unary-/ ('expt ''2 n)) (list `(unary-- ,n)))
       (('quote r) (list (let ((m (ratmsb r)))
                           (and (equal (expt 2 m) r)
                                (kwote m)))))
       (& nil))))

  (local
   (defun collect-other-must-be-integers (x)
     (case-match x
       (('binary-* a b) (append (collect-other-must-be-integers a)
                                (collect-other-must-be-integers b)))
       (('expt ''2 &) nil)
       (('unary-/ ('expt ''2 &)) nil)
       (('quote r) (let ((m (ratmsb r)))
                     (and (not (equal (expt 2 m) r))
                          (list (kwote r)))))
       (& (list x)))))
  
  (local
   (defun powers-of-2-bind-free (x)
     (let ((explst (collect-powers-of-2 x))
           (intlst (collect-other-must-be-integers x)))
       (if (atom explst)
           nil
         `((exp . ,(if (atom (cdr explst)) (car explst) (xxxjoin 'binary-+ explst)))
           (other . ,(if (atom intlst)
                         ''1
                       (if (atom (cdr intlst))
                           (car intlst)
                         (xxxjoin 'binary-* intlst)))))))))

  (local (defun expt+ (n x)
           (expt n x)))
  (local (defthm expt+-of-plus
           (implies (and (integerp x) (integerp y)
                         (integerp n)
                         (not (equal 0 n)))
                    (equal (expt+ n (+ x y))
                           (* (expt+ n x) (expt+ n y))))))

  (local (defthm integerp-of-product-of-powers-of-2
           (implies (and (bind-free (powers-of-2-bind-free `(binary-* ,x ,y)) (exp other))
                         (integerp exp)
                         (equal (* other (expt+ 2 exp)) (* x y))
                         (integerp other)
                         (<= 0 exp))
                    (integerp (* x y)))))
                    
  (local
   (defthm integerp-neg
     (implies (integerp x)
              (integerp (- x)))))
      
  (local (defthm base-case-lemma
           (IMPLIES (AND (<= (- N) K)
                         (INTEGERP N)
                         (< N 0)
                         (INTEGERP K)
                         (< 0 K)
                         (NATP X)
                         (< X (+ -1 (EXPT 2 K))))
                    (EQUAL (FLOOR (* X (/ (+ -1 (EXPT 2 K))))
                                  (EXPT 2 N))
                           (FLOOR x (* (EXPT 2 K) (EXPT 2 N)))))
           :hints (("goal" :use ((:instance (:theorem (implies (equal x y)
                                                               (equal (floor x z) (floor y z))))
                                  (x (* x (/ (+ -1 (expt 2 k)))))
                                  (y (+ (/ x (expt 2 k)) (* x (/ (+ -1 (expt 2 k))) (/ (expt 2 k)))))
                                  (z (expt 2 n)))
                                 (:instance floor-x+i*k-i*j
                                  (x (* x (/ (+ -1 (expt 2 k))) (/ (expt 2 k))))
                                  (i (/ (expt 2 k))) (k x)
                                  (j (expt 2 (+ n k)))))
                    :in-theory (disable ;; ratio-with-expt-minus-1-equals-repeated-ratio-inv
                                        ratio-with-expt-minus-1-equals-repeated-ratio
                                        floor-x+i*k-i*j))
                   (and stable-under-simplificationp
                        '(:in-theory (enable multiply-out-equal
                                             multiply-out-<)))
                   )))


  (Local (defthm inductive-case-lemma
           (implies (and (integerp n)
                         (integerp k)
                         (< 0 k)
                         (< k (- n))
                         (integerp x))
                    (equal (floor (* x (/ (+ -1 (expt 2 k))))
                                  (* (expt 2 k) (expt 2 n)))
                           (+ (- (* x (/ (expt 2 k)) (/ (expt 2 n))))
                              (floor (* x (/ (+ -1 (expt 2 k))))
                                     (expt 2 n)))))
           :hints ((and stable-under-simplificationp
                        '(:use ((:instance floor-cancel-*-2
                                 (x (expt 2 (- k)))
                                 (y (* x (/ (+ -1 (expt 2 k)))))
                                 (z (* (expt 2 k) (expt 2 n)))))))
                   ;; (and stable-under-simplificationp
                   ;;      '(:in-theory (enable floor-divide-out)))
                   )))
           
                                          
  
  (local
   (defthm mod-floor-expt-minus1-prod
     (implies (and (integerp n)
                   (< n 0)
                   (integerp k)
                   (< 0 k)
                   (natp x)
                   (< x (1- (expt 2 k))))
              (equal (mod (floor (* x (/ (+ -1 (expt 2 k))))
                                 (expt 2 n))
                          2)
                     (mod (floor x (expt 2 (mod n k))) 2)))
     :hints (("goal" :induct (mod-floor-expt-minus1-prod-ind n k)
              :in-theory (enable mod-n-k-when-just-below))
             ;; (and stable-under-simplificationp
             ;;      '(:in-theory (enable exponents-add-unrestricted)))
             )))

  (local
   (defthm mod-floor-expt-minus1-prod-gen
     (implies (and (integerp n)
                   (integerp m)
                   (< n m)
                   (integerp k)
                   (< 0 k)
                   (natp x)
                   (< x (1- (expt 2 k))))
              (equal (mod (floor (* x (/ (+ -1 (expt 2 k))))
                                 (* (expt 2 n) (/ (expt 2 m))))
                          2)
                     (mod (floor x (expt 2 (mod (- n m) k))) 2)))
     :hints (("goal" :use ((:instance mod-floor-expt-minus1-prod
                            (n (- n m))))
              :in-theory (disable mod-floor-expt-minus1-prod)
              ;; :in-theory (enable floor-divide-out)
              )
             ;; (and stable-under-simplificationp
             ;;      '(:in-theory (enable exponents-add-unrestricted)))
             )))

  (local (defthmd ratio-<-1
           (implies (and (natp x)
                         (integerp y)
                         (< x y))
                    (< (* x (/ y)) 1))
           :hints (("goal" :in-theory (enable multiply-out-<)))))
  
  (local
   (defthm mod-floor-expt-seq-split
     (implies (and (integerp n)
                   (<= 0 n)
                   (integerp seq)
                   (integerp k)
                   (<= 0 k)
                   (natp x)
                   (< x (1- (expt 2 k))))
              (equal (mod (floor (+ seq (* x (/ (+ -1 (expt 2 k)))))
                                 (expt 2 n))
                          2)
                     (mod (floor seq (expt 2 n)) 2)))
     :hints (("goal" :use ((:instance floor-x+i*k-i*j
                            (x (* x (/ (+ -1 (expt 2 k)))))
                            (i 1)
                            (k seq)
                            (j (expt 2 n))))
              :in-theory (e/d (ratio-<-1)
                              (floor-x+i*k-i*j))))))

  (local
   (defthm mod-floor-expt-seq-split-gen
     (implies (and (integerp n)
                   (integerp m)
                   (<= 0 (- n m))
                   (integerp seq)
                   (integerp k)
                   (<= 0 k)
                   (natp x)
                   (< x (1- (expt 2 k))))
              (equal (mod (floor (+ seq (* x (/ (+ -1 (expt 2 k)))))
                                 (* (expt 2 n) (/ (expt 2 m))))
                          2)
                     (mod (floor seq (expt 2 (- n m))) 2)))
     :hints (("goal" :use ((:instance mod-floor-expt-seq-split
                            (n (- n m))))
              :in-theory (disable mod-floor-expt-seq-split)))))
                          

  
  (local (in-theory (disable mod-=-0)))

  (defthm ratbitp-in-terms-of-rational-bit-decomp
    (implies (and (rationalp x)
                  (natp n))
             (equal (ratbitp n x)
                    (b* (((rbdecomp d)
                          (rational-bit-decomp x))
                         (n0 (- n d.exp))
                         ((when (<= 0 n0))
                          (logbitp n0 d.seq)))
                      (logbitp (mod n0 d.repbits) d.rep))))
    :hints(("Goal" :in-theory (e/d (logbitp oddp evenp
                                            rbdecomp-eval)
                                   (rational-bit-decomp-correct)))
           (and stable-under-simplificationp
                '(:in-theory (e/d (factor-out-expt)
                                  (rational-bit-decomp-correct
                                   distributivity
                                   multiply-out-equal))))
           (and stable-under-simplificationp
                '(:in-theory (e/d (mod-=-0)
                                  (rational-bit-decomp-correct
                                   distributivity
                                   multiply-out-equal))))
           )))


(define rbdecomp-negate ((x rbdecomp-p))
  :returns (neg rbdecomp-p)
  :prepwork ((local (defthmd logmask-inv
                      (implies (natp n)
                               (equal (+ -1 (expt 2 n))
                                      (logmask n)))
                      :hints(("Goal" :in-theory (enable logmask)))))
             (local (defthm loghead-lognot-when-nonzero
                      (implies (and (unsigned-byte-p n x)
                                    (not (equal x 0)))
                               (not (equal (loghead n (lognot x))
                                           (1- (expt 2 n)))))
                      :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                                         bitops::ihsext-recursive-redefs
                                                         bitops::expt-2-is-ash
                                                         bitops::equal-logcons-strong
                                                         logmask-inv)
                                                      (logmask))))))
             (local (defthm loghead-lognot-less
                      (implies (and (not (equal (loghead n x)
                                                (1- (expt 2 n))))
                                    (natp n))
                               (< (loghead n x) (1- (expt 2 n))))
                      :hints (("goal" :use ((:instance unsigned-byte-p-of-loghead
                                             (i x) (size  n)
                                             (size1 n)))
                               :in-theory (e/d (unsigned-byte-p)
                                               (unsigned-byte-p-of-loghead))))
                      :rule-classes :linear)))
  (b* (((rbdecomp x)))
    (if (eql 0 x.rep)
        (change-rbdecomp x :seq (- x.seq))
      (change-rbdecomp x
                       :seq (lognot x.seq)
                       :rep (loghead x.repbits (lognot x.rep)))))
  ///

  (local (defthm logcdr-of-minus
           (implies (integerp x)
                    (equal (logcdr (- x))
                           (1- (- (b-not (logcar x))
                                  (logcdr x)))))
           :hints(("Goal" :in-theory (enable bitops::minus-to-lognot)))))
  
  (local (defthm loghead-lognot-arith
           (equal (loghead n (lognot x))
                  (- (logmask n) (loghead n x)))
           :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs
                                            bitops::equal-logcons-strong
                                            logmask-inv)
                                           (logmask))))))
  
  (defret eval-of-<fn>
    (equal (rbdecomp-eval neg)
           (- (rbdecomp-eval x)))
    :hints(("Goal" :in-theory (enable rbdecomp-eval))
           (and stable-under-simplificationp
                '(:in-theory (enable lognot))))))




(local (defthmd mod-n-k-when-just-below
         (implies (and (integerp n)
                       (< n 0)
                       (integerp k)
                       (<= (- n) k))
                  (equal (mod n k)
                         (+ n k)))
         :hints(("Goal" :in-theory (enable mod)))))

(define repeat-bits-aux ((nbits natp)
                         (rep integerp)
                         (repbits posp)
                         (acc natp))
  :returns (repeat natp :rule-classes :type-prescription)
  (b* ((nbits (lnfix nbits))
       (repbits (lposfix repbits))
       (acc (lnfix acc))
       ((when (<= nbits repbits))
        (logapp nbits (logtail (- repbits nbits) rep) acc)))
    (repeat-bits-aux (- nbits repbits) rep repbits
                     (logapp repbits rep acc)))
  ///
  (defret repeat-bits-aux-of-0
    :pre-bind ((rep 0) (acc 0))
    (equal repeat 0))

  (defret logbitp-of-<fn>
    (equal (logbitp n repeat)
           (if (< (nfix n) (nfix nbits))
               (logbitp (mod (- (nfix n) (nfix nbits)) (pos-fix repbits)) rep)
             (logbitp (- (nfix n) (nfix nbits)) (nfix acc))))
    :hints(("Goal" :in-theory (enable mod-n-k-when-just-below)))))

(define repeat-bits ((nbits natp)
                     (rep integerp)
                     (repbits posp))
  :returns (repeat natp :rule-classes :type-prescription)
  (mbe :logic (repeat-bits-aux nbits rep repbits 0)
       :exec (if (eql rep 0)
                 0
               (repeat-bits-aux nbits rep repbits 0)))
  ///
  (defret logbitp-of-<fn>
    (equal (logbitp n repeat)
           (and (< (nfix n) (nfix nbits))
                (logbitp (mod (- (nfix n) (nfix nbits)) (pos-fix repbits)) rep)))))

;; ;; Work in progress
;; (define repeat-and-bits ((arep integerp)
;;                          (brep integerp)
;;                          (arepbits posp)
;;                          (brepbits posp)
;;                          (aindex natp)
;;                          (bindex natp))
;;   :guard (and (< aindex arepbits)
;;               (< bindex brepbits))
;;   :returns (mv (andrep natp :rule-classes :type-prescription)
;;                (andrepbits posp :rule-classes :type-prescription))
;;   (b* ((arepbits (lposfix arepbits))
;;        (brepbits (lposfix brepbits))
;;        (aindex (lnfix aindex))
;;        (bindex (lnfix bindex))
;;        (arep (lifix arep))
;;        (brep (lifix brep))
;;   (cond ((eql arep 0) (if (eql brep 0)
;;                           (mv 0 1)
;;                         (logapp (- brepbits bindex) (logtail bindex brep)
;;                                 (loghead bindex brep))))
;;         ((eql brep 0) (logapp (- arepbits aindex) (logtail aindex arep)
;;                               (loghead aindex arep)))
;;         (t 

;; (define rbdecomp-and ((x rbdecomp-p) (y rbdecomp-p))
;;   :returns (and rbdecomp-p)
;;   (b* (((rbdecomp x))
;;        ((rbdecomp y))
;;        ((mv (rbdecomp a) (rbdecomp b))
;;         (if (< x.exp y.exp)
;;             (mv x y)
;;           (mv y x)))
;;        (seq (logapp (- b.exp a.exp)
;;                     (logand a.seq (repeat-bits (- b.exp a.exp) b.rep b.repbits))
;;                     (logand (logtail (- b.exp a.exp) a.seq) b.seq)))
;;        ((mv rep repbits)
;;         (repeat-and-bits a.rep b.rep a.repbits b.repbits
;;                          0 ;; a index
;;                          (mod (- b.exp a.exp) b.repbits)))
;;        ((when (eql rep 0))
;;         (rbdecomp a.exp seq 0 1)))
;;     (rbdecomp a.exp seq rep repbits)))
                    
                    
  
