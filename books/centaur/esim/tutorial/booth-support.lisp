; Centaur Hardware Verification Tutorial for ESIM/VL2014
; Copyright (C) 2008-2015 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>
;                  Jared Davis <jared@centtech.com>


(in-package "ACL2")

(local (include-book "centaur/bitops/ihs-extensions" :dir :System))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/util/bstar" :dir :system)

; NOTE ---- ESIM is still available but it is no longer being actively
; maintained.  The successor of ESIM is SVEX.  If you don't already have
; projects based on ESIM, you should probably skip this tutorial and learn
; about SVEX instead.



(defun booth-enc-one (a b)
  (+ (if (logbitp 0 a) b        0)
     (if (logbitp 1 a) b        0)
     (if (logbitp 2 a) (* -2 b) 0)))

(local
 (progn
   (defund booth-enc-coeff (a)
     (+ (logcar a)
        (logext 2 (logcdr a))))

   (defthm booth-enc-one-redef
     (equal (booth-enc-one a b)
            (* (booth-enc-coeff a)
               b))
     :hints(("Goal" :expand ((:free (n a) (logext n a))
                             (:free (n a) (logbitp n a)))
             :in-theory (enable booth-enc-coeff))))




   (defthmd booth-enc-one-impl
     (implies (integerp b)
              (equal (booth-enc-one a b)
                     (b* ((bsign (if (logbitp 2 a) (- b) b))
                          (shft (iff (logbitp 0 a) (logbitp 1 a)))
                          (zro (and shft (iff (logbitp 1 a) (logbitp 2 a))))
                          (res1 (if zro 0 bsign)))
                       (if shft (* 2 res1) res1))))
     :hints(("Goal" :in-theory (disable booth-enc-one-redef))))


   (local (in-theory (disable booth-enc-one)))

   (defun booth-sum (n a b)
     (if (zp n)
         0
       (+ (booth-enc-one a b)
          (* 4 (booth-sum (1- n) (logtail 2 a) b)))))


   (local
    (progn
      (encapsulate nil
        (local (defthm floor-1
                 (implies (integerp x)
                          (equal (floor x 1) x))
                 :hints(("Goal" :in-theory (enable floor)))))
        (local (defthm logcar-of-ash-2
                 (equal (logcar (ash n 2)) 0)
                 :hints(("Goal" :in-theory (enable ash**)))))
        (defthm logcar-of-*-4
          (implies (integerp n)
                   (equal (logcar (* 4 n)) 0))
          :hints (("goal" :use logcar-of-ash-2
                   :in-theory (enable ash))))

        (local (defthm logcdr-of-ash-2
                 (equal (logcdr (ash n 2)) (ash n 1))
                 :hints(("Goal" :in-theory (enable ash**)))))
        (defthm logcdr-of-*-4
          (implies (integerp n)
                   (equal (logcdr (* 4 n))
                          (* 2 n)))
          :hints (("goal" :use logcdr-of-ash-2
                   :in-theory (enable ash)))))

      (defthm logcar-of-logext
        (equal (logcar (logext n a))
               (logcar a))
        :hints(("Goal" :in-theory (enable* ihsext-inductions
                                           ihsext-recursive-redefs))))

      (defthm sum-negative-prods
        (implies (syntaxp (and (quotep a) (quotep b)))
                 (equal (+ (- (* a n)) (* b n) c)
                        (+ (* (- b a) n) c))))))

   (local (in-theory (disable logext-identity
                              logtail-identity)))

   (defthm booth-sum-is-multiply
     (implies (integerp b)
              (equal (booth-sum n a b)
                     (let ((m (logext (+ 1 (* 2 (nfix n))) a)))
                       (* (+ (logcdr m) (logcar m)) b))))
     :hints(("Goal" :in-theory (e/d* (logcons booth-enc-coeff)
                                     ((:d booth-sum)))
             :induct (booth-sum n a b)
             :expand ((booth-sum n a b)
                      (:free (a) (logext 1 a))
                      (:free (a) (logext 2 a))
                      (:free (a) (logext (* 2 n) a))
                      (:free (a) (logext (+ 1 (* 2 n)) a))
                      (:free (a) (logbitp 0 a))
                      (:free (a) (logbitp 1 a))
                      (:free (a) (logbitp 2 a))
                      (:free (a) (logtail 0 a))
                      (:free (a) (logtail 1 a))
                      (:free (a) (logtail 2 a))))
            (and stable-under-simplificationp
                 `(:use ((:instance logcar-logcdr-elim
                          (i (logext (+ -1 (* 2 n)) (logcdr (logcdr a))))))))))



   (defund booth-sum-impl1 (n i a b)
     (if (zp n)
         0
       (+ (ash (booth-enc-one (ash a (- 1 (* 2 i))) b) (* 2 i))
          (booth-sum-impl1 (1- n) (+ 1 i) a b))))

   (local (defthm integerp-expt-when-not-negp
            (implies (and (not (negp i))
                          (integerp b))
                     (integerp (expt b i)))
            :hints(("Goal" :in-theory (enable expt)))
            :rule-classes :type-prescription))

   (local (defthm floor-1-when-integer
            (implies (integerp i)
                     (equal (floor i 1) i))
            :hints(("Goal" :in-theory (enable floor)))))

   (local (defthmd left-shift-to-expt
            (implies (not (negp shift))
                     (equal (ash i shift)
                            (* (ifix i) (expt 2 shift))))
            :hints(("Goal" :in-theory (enable ash)))))

   (defthm booth-enc-one-integerp
     (implies (integerp b)
              (integerp (booth-enc-one a b)))
     :hints(("Goal" :in-theory (enable booth-enc-one)))
     :rule-classes :type-prescription)

   (defthm booth-sum-integerp
     (implies (integerp b)
              (integerp (booth-sum n a b)))
     :hints(("Goal" :in-theory (enable booth-sum)))
     :rule-classes :type-prescription)

   (defthm booth-sum-impl1-is-booth-sum
     (implies (and (natp i)
                   (integerp b))
              (equal (booth-sum-impl1 n i a b)
                     (ash (booth-sum n (ash a (- 1 (* 2 i))) b) (* 2 i))))
     :hints(("Goal" :in-theory (e/d (booth-sum booth-sum-impl1 logcons)
                                    (booth-enc-one-redef
                                     booth-sum-is-multiply))
             :induct (booth-sum-impl1 n i a b)
             :expand ((:free (a) (booth-sum n a b))))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (left-shift-to-expt)
                                   (booth-enc-one-redef
                                    booth-sum-is-multiply))))))



   (defthm logext-of-loghead-when-signed-byte-p
     (implies (signed-byte-p n x)
              (equal (logext n (loghead n x))
                     x))
     :hints(("Goal" :in-theory (e/d* (ihsext-recursive-redefs
                                      ihsext-inductions)
                                     (signed-byte-p)))))

   (defthm booth-enc-coeff-lower-bound
     (<= -2 (booth-enc-coeff a))
     :hints(("Goal" :in-theory (enable booth-enc-coeff logcons)
             :expand ((:free (a) (logext 2 a))
                      (:free (a) (logext 1 a))
                      (:free (a) (logext 0 a)))))
     :rule-classes :linear)

   (defthm booth-enc-coeff-upper-bound
     (<= (booth-enc-coeff a) 2)
     :hints(("Goal" :in-theory (enable booth-enc-coeff logcons)
             :expand ((:free (a) (logext 2 a))
                      (:free (a) (logext 1 a))
                      (:free (a) (logext 0 a)))))
     :rule-classes :linear)



   (local (defthmd minus-of-*
            (implies (syntaxp (quotep a))
                     (equal (- (* a b))
                            (* (- a) b)))))

   (defthm signed-byte-p-of-booth-enc-one
     (implies (signed-byte-p (+ -2 n) b)
              (signed-byte-p n (booth-enc-one a b)))
     :hints(("Goal" :in-theory (e/d (booth-enc-one-redef)
                                    (booth-enc-one
                                     exponents-add))
             :expand ((expt 2 (+ -1 n))
                      (expt 2 (+ -2 n)))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:cases ((equal (booth-enc-coeff a) -2)
                           (equal (booth-enc-coeff a) -1)
                           (equal (booth-enc-coeff a) 0)
                           (equal (booth-enc-coeff a) 1)
                           (equal (booth-enc-coeff a) 2))))))

   ))

(defund boothmul-pp-spec (sz i a b)
  (loghead (+ 2 sz) (booth-enc-one (ash a (- 1 (* 2 i)))
                                   (logext sz b))))

(defund booth-sum-impl (n i a b sz)
  (if (zp n)
      0
    (+ (ash (logext (+ 2 sz) (boothmul-pp-spec sz i a b)) (* 2 i))
       (booth-sum-impl (1- n) (+ 1 i) a b sz))))

(local
 (defthm booth-sum-impl-is-booth-sum-impl1
   (implies (posp sz)
            (equal (booth-sum-impl n i a b sz)
                   (booth-sum-impl1 n i a (logext sz b))))
   :hints(("Goal" :in-theory (e/d* (booth-sum-impl
                                    boothmul-pp-spec
                                    booth-sum-impl1)
                                   (booth-sum-impl1-is-booth-sum
                                    booth-enc-one-redef
                                    booth-enc-one
                                    signed-byte-p))))))

(defthm booth-sum-impl-is-multiply
  (implies (and (integerp b)
                (posp sz)
                (posp n))
           (equal (booth-sum-impl n 0 a b sz)
                  (* (logext sz b) (logext (* 2 n) a))))
  :hints (("goal" :expand ((LOGEXT (+ 1 (* 2 N)) (ASH A 1))))))
