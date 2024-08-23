; Copyright (C) 2024 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
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
                           acl2::<-*-/-left)))

(define lrfix ((x rationalp))
  :inline t
  :enabled t
  (mbe :logic (rfix x) :exec x))

(local (defthm rfix-when-rationalp
           (implies (rationalp x)
                    (equal (rfix x) x))))


(defxdoc ratbits
  :parents (acl2::bit-vectors)
  :short "Library for reasoning about rational numbers as bidirectional sequences of bits.")

(local (xdoc::set-default-parents (ratbits)))

(local (defthm floor-divide-out
         (implies (and (not (equal (rfix y) 0))
                       (syntaxp (not (equal y ''1)))
                       (rationalp x))
                  (equal (floor x y)
                         (floor (/ x y) 1)))
         :hints(("Goal" :in-theory (enable rfix)))))

(local (defthm mod-divide-out
         (implies (and (not (equal (rfix y) 0))
                       (syntaxp (not (equal y ''1)))
                        (rationalp x))
                  (equal (mod x y)
                         (* y (mod (/ x y) 1))))
         :hints(("Goal" :in-theory (enable mod rfix)))))

(local (in-theory (disable ACL2::MOD-X-Y-=-X+Y-FOR-RATIONALS)))


(local (in-theory (disable multiply-out-<
                           floor-divide-out
                           mod-divide-out
                           acl2::/r-when-abs-numerator=1
                           acl2::floor-=-x/y)))

(local
 (encapsulate nil

            
   ;; (local (defthm floor-of-mod-offset
   ;;          (implies (and (rationalp x)
   ;;                        (natp n)
   ;;                        (integerp i)
   ;;                        (integerp j))
   ;;                   (equal (floor (mod x (expt 2 (+ i n))) (expt 2 i))
   ;;                          (mod (floor x (expt 2 i)) (expt 2 n))))
   ;;          :hints (("goal" :induct (expt 2 n)
   ;;                   :in-theory (enable expt)))))
                     

   (defthmd floor-plus-multiple
     (implies (and (integerp i)
                   (rationalp x)
                   (rationalp y)
                   (not (equal y 0)))
              (equal (floor (+ x (* i y)) y)
                     (+ i (floor x y)))))
   
   (local (in-theory (disable ACL2::CANCEL-FLOOR-+-BASIC
                              ACL2::MOD-X-I*J-OF-POSITIVES)))

   (local (defthm integerp-lemma
            (implies (and (<= (ifix m) (ifix n))
                          (integerp y))
                     (integerp (- (* (/ (expt 2 m))
                                     (expt 2 n)
                                     y))))
            :hints (("Goal" :use ((:instance (:theorem (implies (and (natp n) (integerp y)) (integerp (* (expt 2 n) y))))
                                   (n (- (ifix n) (ifix m)))))))))

   (local (defthm floor-of-floor-expt-lemma
            (implies (and (rationalp x)
                          (natp m))
                     (equal (floor (floor x (expt 2 n)) (expt 2 m))
                            (floor x (expt 2 (+ (ifix n) (ifix m))))))))
   
   (defthm floor-of-floor-expt
     (implies (and (rationalp x)
                   (not (negp m)))
              (equal (floor (floor x (expt 2 n)) (expt 2 m))
                     (floor x (expt 2 (+ (ifix n) (ifix m))))))
     :hints (("goal" :use ((:instance floor-of-floor-expt-lemma
                            (m (ifix m))))
              :in-theory (disable floor-of-floor-expt-lemma))))

   (defthm floor-of-floor-expt-gen
     (implies (and (rationalp x)
                   (bind-free
                    (case-match e1
                      (('expt ''2 n) `((n . ,n)))
                      (('quote c) (and (integerp c)
                                       (equal c (expt 2 (1- (integer-length c))))
                                       `((n . ',(1- (integer-length c))))))
                      (& nil))
                    (n))
                   (equal e1 (expt 2 n))
                   (bind-free
                    (case-match e2
                      (('expt ''2 m) `((m . ,m)))
                      (('quote c) (and (integerp c)
                                       (equal c (expt 2 (1- (integer-length c))))
                                       `((m . ',(1- (integer-length c))))))
                      (& nil))
                    (m))
                   (equal e2 (expt 2 m))
                   (not (negp m)))
              (equal (floor (floor x e1) e2)
                     (floor x (expt 2 (+ (ifix n) (ifix m)))))))

   (local (defthm floor-of-floor-expt-crock
            (implies (and (rationalp x)
                          (<= (ifix m) (ifix r)))
                     (equal (floor (floor x (expt 2 n)) (* (/ (expt 2 m)) (expt 2 r)))
                            (floor x (expt 2 (+ (ifix n) (ifix r) (- (ifix m)))))))
            :hints (("goal" :use ((:instance floor-of-floor-expt
                                   (m (- (ifix r) (ifix m)))))
                     :in-theory (disable floor-of-floor-expt
                                         acl2::floor-floor-integer)))))
            
   (local (defthm integerp-/-expt
            (implies (zp n)
                     (integerp (/ (expt 2 n))))
            :hints (("goal" :use ((:instance (:theorem (implies (natp n) (integerp (expt 2 n))))
                                   (n (- (ifix n)))))
                     :in-theory (disable acl2::expt-type-prescription-integerp)))
            :rule-classes :type-prescription))

   (defthmd floor-of-mod
     (implies (rationalp x)
              (equal (floor (mod x (expt 2 n)) (expt 2 m))
                     (if (<= (ifix n) (ifix m))
                         0
                       (mod (floor x (expt 2 m)) (expt 2 (- (ifix n) (ifix m)))))))
     :hints ((and stable-under-simplificationp
                  (member-equal '(not (< (ifix m) (ifix n))) clause)
                  '(:use ((:instance floor-plus-multiple
                           (x x) (y (expt 2 m)) (i (- (* (expt 2 (- (ifix n) (ifix m))) (floor x (expt 2 n)))))))
                    :in-theory (enable mod)
                    :do-not '(generalize fertilize eliminate-destructors)))
             (and stable-under-simplificationp
                  (member-equal '(< (ifix m) (ifix n)) clause)
                  '(:use ((:instance acl2::expt-is-increasing-for-base>1
                           (r 2) (i (ifix n)) (j (ifix m))))
                    :in-theory (enable* acl2::arith-equiv-forwarding))))
     :otf-flg t)

   (defthm floor-of-mod-gen
     (implies (and (rationalp x)
                   (bind-free
                    (case-match e1
                      (('expt ''2 n) `((n . ,n)))
                      (('quote c) (and (integerp c)
                                       (equal c (expt 2 (1- (integer-length c))))
                                       `((n . ',(1- (integer-length c))))))
                      (& nil))
                    (n))
                   (equal e1 (expt 2 n))
                   (bind-free
                    (case-match e2
                      (('expt ''2 m) `((m . ,m)))
                      (('quote c) (and (integerp c)
                                       (equal c (expt 2 (1- (integer-length c))))
                                       `((m . ',(1- (integer-length c))))))
                      (& nil))
                    (m))
                   (equal e2 (expt 2 m)))
              (equal (floor (mod x e1) e2)
                     (if (<= (ifix n) (ifix m))
                         0
                       (mod (floor x e2) (expt 2 (- (ifix n) (ifix m)))))))
     :hints(("Goal" :in-theory (enable floor-of-mod))))
                   

   (defthmd mod-of-floor
     (implies (Rationalp x)
              (equal (mod (floor x (expt 2 m)) (expt 2 n))
                     (if (<= (ifix n) 0)
                         0
                       (floor (mod x (expt 2 (+ (ifix n) (ifix m)))) (expt 2 m)))))
     :hints(("Goal" :use ((:instance floor-of-mod
                           (m m) (n (+ (ifix n) (ifix m)))))
             :in-theory (disable floor-of-mod))))

   (defthmd mod-of-floor-gen
     (implies (and (rationalp x)
                   (bind-free
                    (case-match e1
                      (('expt ''2 n) `((n . ,n)))
                      (('quote c) (and (integerp c)
                                       (equal c (expt 2 (1- (integer-length c))))
                                       `((n . ',(1- (integer-length c)))))))
                    (n))
                   (equal e1 (expt 2 n))
                   (bind-free
                    (case-match e2
                      (('expt ''2 m) `((m . ,m)))
                      (('quote c) (and (integerp c)
                                       (equal c (expt 2 (1- (integer-length c))))
                                       `((m . ',(1- (integer-length c)))))))
                    (m))
                   (equal e2 (expt 2 m)))
              (equal (mod (floor x e2) e1)
                     (if (<= (ifix n) 0)
                         0
                       (floor (mod x (expt 2 (+ (ifix n) (ifix m)))) (expt 2 m)))))
     :hints(("Goal" :in-theory (enable mod-of-floor))))))




(define ratbitp ((i integerp) (x rationalp))
  :returns (bitp booleanp)
  :short "Get the given bit index (integer i) of the given rational x.  Like @(see logbitp), extended to rationals."
  (equal 1 (mod (floor (lrfix x) (expt 2 i)) 2))
  ///
  
  
  (local (in-theory (disable ACL2::MOD-X-I*J-OF-POSITIVES
                             acl2::floor-bounded-by-/
                             ACL2::MOD-X-Y-=-X-FOR-RATIONALS)))
  
  (defthmd ratbitp-rec
    (equal (ratbitp i x)
           (cond ((zip i)
                  (equal 1 (mod (floor (rfix x) 1) 2)))
                 ((< 0 i) (ratbitp (1- i) (/ (rfix x) 2)))
                 (t       (ratbitp (1+ i) (* (rfix x) 2)))))
    :hints (("goal" :expand ((expt 2 i))
             :in-theory (e/d (floor-divide-out)
                             (expt
                              acl2::floor-bounded-by-/
                              multiply-out-<
                              acl2::0-<-*
                              acl2::<-*-0
                              acl2::mod-bounded-by-modulus))))
    :rule-classes ((:definition :install-body nil
                    :controller-alist ((ratbitp t nil)))))

  (defun ratbitp-ind (i x)
    (Declare (Xargs :measure (abs (ifix i))))
    (cond ((zip i)
           x)
          ((< 0 i) (ratbitp-ind (1- i) (/ (rfix x) 2)))
          (t       (ratbitp-ind (1+ i) (* (rfix x) 2)))))
    
  (defthmd ratbitp-induct
    t
    :rule-classes ((:induction :pattern (ratbitp i x)
                    :scheme (ratbitp-ind i x))))

  (defthm ratbitp-of-0
    (not (ratbitp i 0)))

  (local (defthm integerp-half-/-expt-when-negative
           (implies (negp i)
                    (integerp (* 1/2 (/ (expt 2 i)))))
           :hints (("Goal" :use ((:instance (:theorem (implies (natp x) (integerp (expt 2 x))))
                                  (x (1- (- i)))))
                    :in-theory (e/d (acl2::exponents-add-unrestricted)
                                    (acl2::expt-type-prescription-integerp))))))
  
  (defthm ratbitp-of-mod-1
    (implies (Rationalp x)
             (equal (ratbitp i (mod x 1))
                    (and (< (ifix i) 0)
                         (ratbitp i x)))))

  (local (defthm <0-ifix-plus-1
           (equal (< 0 (+ 1 (ifix i)))
                  (not (negp i)))))
  
  (defthm ratbitp-of-floor-1
    (implies (Rationalp x)
             (equal (ratbitp i (floor x 1))
                    (and (<= 0 (ifix i))
                         (ratbitp i x))))
    :hints(("Goal" :in-theory (e/d (mod-of-floor-gen)
                                   (floor-of-mod-gen))))))
                      

(define ratshift ((x rationalp) (i integerp))
  :returns (shift rationalp :rule-classes :type-prescription)
  :short "Shift the rational x by i bits -- left if positive, right if negative. Like @(see ash), extended to rationals."
  :long "<p>The parallel with @(see ash) isn't perfect -- unlike ash, this
function preserves all the bits, i.e. a right shift doesn't truncate bits at
0.</p>"
  (* (lrfix x)
     (expt 2 i))
  ///
  (local (in-theory (disable ACL2::MOD-X-I*J-OF-POSITIVES
                             acl2::floor-bounded-by-/
                             ACL2::MOD-X-Y-=-X-FOR-RATIONALS)))
  
  (defthm ratshift-of-x-0
    (equal (ratshift 0 i) 0))

  (defthm ratshift-of-i-0
    (equal (ratshift x 0) (rfix x)))
  
  (defthmd ratshift-rec
    (equal (ratshift x i)
           (cond ((zip i) (rfix x))
                 ((< 0 i) (ratshift (* (rfix x) 2) (1- i)))
                 (t       (ratshift (/ (rfix x) 2) (1+ i)))))
    :hints (("goal" :expand ((expt 2 i))))
    :rule-classes ((:definition :install-body nil
                    :controller-alist ((ratshift t nil)))))

  (defun ratshift-ind (x i)
    (Declare (Xargs :measure (abs (ifix i))))
    (cond ((zip i) x)
          ((< 0 i) (ratshift-ind (* (rfix x) 2) (1- i)))
          (t       (ratshift-ind (/ (rfix x) 2) (1+ i)))))
  
  (defthmd ratshift-induct
    t
    :rule-classes ((:induction :pattern (ratshift x i)
                    :scheme (ratshift-ind x i))))

  ;; (local (in-theory (disable ratshift)))
  (local (in-theory (disable acl2::mod-=-0)))
  
  (defthm ratbitp-of-ratshift
    (equal (ratbitp j (ratshift x i))
           (ratbitp (- (ifix j) (ifix i)) x))
    :hints(("Goal" :in-theory (e/d (ratbitp
                                    floor-divide-out)))))

  (defthm ratshift-of-ratshift
    (equal (ratshift (ratshift x n) m)
           (ratshift x (+ (ifix n) (ifix m))))
    :hints(("Goal" :in-theory (enable ratshift)))))


(define rathead ((i integerp) (x rationalp))
  :returns (head rationalp :rule-classes :type-prescription)
  :short "Zero the upper bits of rational x, starting at bit i. Like @(see loghead), extended to rationals."
  (mod (lrfix x) (expt 2 i))
  ///
  (local (in-theory (disable ACL2::MOD-X-I*J-OF-POSITIVES
                             acl2::floor-bounded-by-/
                             ACL2::MOD-X-Y-=-X-FOR-RATIONALS)))
  
  (defthm rathead-of-x-0
    (equal (rathead i 0) 0))


  
  (defthmd rathead-rec
    (equal (rathead i x)
           (cond ((zip i) (mod (rfix x) 1))
                 ((< 0 i) (* (rathead (1- i) (/ (rfix x) 2)) 2))
                 (t       (/ (rathead (1+ i) (* (rfix x) 2)) 2))))
    :hints (("goal" :expand ((expt 2 i))
             :in-theory (enable mod-divide-out)))
    :rule-classes ((:definition :install-body nil
                    :controller-alist ((rathead t nil)))))

  (defun rathead-ind (i x)
    (Declare (Xargs :measure (abs (ifix i))))
    (cond ((zip i) x)
          ((< 0 i) (rathead-ind (1- i) (/ (rfix x) 2)))
          (t       (rathead-ind (1+ i) (* (rfix x) 2)))))
  
  (defthmd rathead-induct
    t
    :rule-classes ((:induction :pattern (rathead i x)
                    :scheme (rathead-ind i x))))

  ;; (local (in-theory (disable rathead
  ;;                            ACL2::MOD-X-Y-=-X+Y-FOR-RATIONALS)))
  
  ;; (local (defun ratbitp-of-rathead-ind (i j x)
  ;;          (Declare (Xargs :measure (abs (ifix i))))
  ;;          (cond ((zip i) (list j x))
  ;;                ((< 0 i) (ratbitp-of-rathead-ind (1- i) (1- (ifix j)) (/ (rfix x) 2)))
  ;;                (t (ratbitp-of-rathead-ind (1+ i) (1+ (ifix j)) (* (rfix x) 2))))))

  (local (Defthm integerp-half-expt-/-expt
           (implies (< (ifix j) (ifix i))
                    (integerp (* 1/2 (expt 2 i) (/ (expt 2 j)))))
           :hints (("goal" :use ((:instance (:theorem (implies (natp x) (integerp (expt 2 x))))
                                  (x (+ -1 (ifix i) (- (ifix j))))))
                    :in-theory (e/d (acl2::exponents-add-unrestricted)
                                    (acl2::expt-type-prescription-integerp))))))
  
  (defthm ratbitp-of-rathead
    (equal (ratbitp j (rathead i x))
           (and (< (ifix j) (ifix i))
                (ratbitp j x)))
    :hints(("Goal" :in-theory (enable ratbitp rathead)))))



(define rattail ((i integerp) (x rationalp))
  :returns (tail rationalp :rule-classes :type-prescription)
  :short "Zero the lower bits of rational x below bit i, and shift bit i to the 0 position. Like @(see logtail), extended to rationals."
  (floor (lrfix x) (expt 2 i))
  ///
  (local (in-theory (disable ACL2::MOD-X-I*J-OF-POSITIVES
                             acl2::floor-bounded-by-/
                             ACL2::MOD-X-Y-=-X-FOR-RATIONALS)))
  
  (defthm rattail-of-x-0
    (equal (rattail i 0) 0))


  
  (defthmd rattail-rec
    (equal (rattail i x)
           (cond ((zip i) (floor (rfix x) 1))
                 ((< 0 i) (rattail (1- i) (/ (rfix x) 2)))
                 (t       (rattail (1+ i) (* (rfix x) 2)))))
    :hints (("goal" :expand ((expt 2 i))
             :in-theory (enable floor-divide-out)))
    :rule-classes ((:definition :install-body nil
                    :controller-alist ((rattail t nil)))))

  (defun rattail-ind (i x)
    (Declare (Xargs :measure (abs (ifix i))))
    (cond ((zip i) x)
          ((< 0 i) (rattail-ind (1- i) (/ (rfix x) 2)))
          (t       (rattail-ind (1+ i) (* (rfix x) 2)))))
  
  (defthmd rattail-induct
    t
    :rule-classes ((:induction :pattern (rattail i x)
                    :scheme (rattail-ind i x))))
  
  (local (in-theory (disable acl2::mod-=-0)))
  
  (defthm ratbitp-of-rattail
    (equal (ratbitp j (rattail i x))
           (and (<= 0 (ifix j))
                (ratbitp (+ (ifix j) (ifix i)) x)))
    :hints(("Goal" :in-theory (e/d (ratbitp rattail))
            :do-not '(generalize fertilize eliminate-destructors)
            :cases ((<= 0 (ifix j))))
           (and stable-under-simplificationp
                '(:in-theory (e/d (mod-of-floor-gen)
                                  (floor-of-mod-gen)))))
    :otf-flg t))


(local (defthm mod-of-0
         (equal (mod 0 n) 0)
         :hints(("Goal" :in-theory (e/d (mod)
                                        ((force)))))))




(define ratsplice ((i integerp)
                   (lower rationalp)
                   (upper rationalp))
  :returns (splice rationalp :rule-classes :type-prescription)
  (+ (rathead i lower)
     (ratshift (rattail i upper) i))
  ///

  (local (in-theory (disable ACL2::MOD-X-I*J-OF-POSITIVES
                             acl2::floor-bounded-by-/
                             ACL2::MOD-X-Y-=-X-FOR-RATIONALS
                             acl2::mod-=-0)))
  
  (local (defthm integerp-lemma
            (implies (and (<= (ifix m) (ifix n))
                          (integerp y))
                     (integerp (* (expt 2 n)
                                  (/ (expt 2 m))
                                  y)))
            :hints (("Goal" :use ((:instance (:theorem (implies (and (natp n) (integerp y)) (integerp (* (expt 2 n) y))))
                                   (n (- (ifix n) (ifix m)))))))))

  (local (defthm integerp-lemma2
            (implies (and (< (ifix m) (ifix n))
                          (integerp y))
                     (integerp (* 1/2 (expt 2 n)
                                  (/ (expt 2 m))
                                  y)))
            :hints (("Goal" :use ((:instance (:theorem (implies (and (natp n) (integerp y)) (integerp (* (expt 2 n) y))))
                                   (n (+ -1 (- (ifix n) (ifix m))))))
                     :in-theory (e/d (acl2::exponents-add-unrestricted))))))

  (local (defthm integerp-lemma3
            (implies (and (< (ifix m) (ifix n))
                          (integerp y))
                     (integerp (* 1/2 (expt 2 n)
                                  (/ (expt 2 m)))))
            :hints (("Goal" :use ((:instance (:theorem (implies (and (natp n)) (integerp (expt 2 n))))
                                   (n (+ -1 (- (ifix n) (ifix m))))))
                     :in-theory (e/d (acl2::exponents-add-unrestricted))))))

  (local (defthm integerp-lemma4
            (implies (and (<= (ifix m) (ifix n)))
                     (integerp (* (/ (expt 2 m))
                                  (expt 2 n))))
            :hints (("Goal" :use ((:instance (:theorem (implies (and (natp n)) (integerp (expt 2 n))))
                                   (n (- (ifix n) (ifix m)))))
                     :in-theory (e/d (acl2::exponents-add-unrestricted))))))


  (local (in-theory (disable rfix)))

  (defthm ratbitp-of-ratslice
    (equal (ratbitp j (ratsplice i lower upper))
           (if (<= (ifix i) (ifix j))
               (ratbitp j upper)
             (ratbitp j lower)))
    :hints(("Goal" :in-theory (e/d (ratbitp rathead ratshift rattail)))
           (and stable-under-simplificationp
                (member-equal '(not (< (ifix j) (ifix i))) clause)
                '(:use ((:instance floor-plus-multiple
                         (x (mod (rfix lower) (expt 2 i)))
                         (i (* (expt 2 (- (ifix i) (ifix j))) (floor (rfix upper) (expt 2 i))))
                         (y (expt 2 j))))))
           (and stable-under-simplificationp
                (member-equal '(< (ifix j) (ifix i)) clause)
                '(:use ((:instance acl2::floor-x+i*k-i*j
                         (x (mod (rfix lower) (expt 2 i)))
                         (i (expt 2 i))
                         (k (floor (rfix upper) (expt 2 i)))
                         (j (expt 2 (- (ifix j) (ifix i))))))
                  :in-theory (enable acl2::exponents-add-unrestricted))))))



(local (defthm equal-0-of-leftshift
         (implies (natp sh)
                  (equal (equal 0 (ash x sh))
                         (zip x)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(local (defthm posp-of-leftshift
         (implies (and (natp sh)
                       (posp x))
                  (posp (ash x sh)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))
         :rule-classes :type-prescription))

(local
 (defthm integer-length-minus-1-is-exponent-pos
   (implies (posp x)
            (let ((scand (/ x (expt 2 (1- (integer-length x))))))
              (and (<= 1 scand)
                   (< scand 2))))
   :hints (("goal"
            :in-theory (enable* bitops::ihsext-inductions
                                multiply-out-<)
            :induct (integer-length x)
            :expand ((integer-length x)
                     (expt 2 (integer-length (logcdr x)))))
           (and stable-under-simplificationp
                '(:in-theory (enable logcons))))))

(local
 (defthm integer-length-minus-1-is-exponent-neg
   (implies (negp x)
            (let ((scand (/ x (expt 2 (1- (integer-length x))))))
              (and (<= -2 scand)
                   (< scand 1))))
   :hints (("goal"
            :in-theory (enable* bitops::ihsext-inductions
                                multiply-out-<)
            :induct (integer-length x)
            :expand ((integer-length x)
                     (expt 2 (integer-length (logcdr x)))))
           (and stable-under-simplificationp
                '(:in-theory (enable logcons))))))


(encapsulate nil
  (local (defun integer-length-of-negate-gen-ind (b x)
           (declare (xargs :measure (integer-length x)
                           :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs)))))
           (if (or (equal (integer-length x) 0)
                   (not (equal b 1)))
               (list x b)
             (integer-length-of-negate-gen-ind
              (b-not (logcar x)) (logcdr x)))))

  (local (defthm minus-of-logcons
           (equal (- (logcons x y))
                  (logcons x (+ (- (bfix x)) (- (ifix y)))))
           :hints(("Goal" :in-theory (enable logcons)))))

  (local
   (defthm integer-length-of-negate-gen
     (implies (and (integerp x)
                   (bitp b))
              (equal (integer-length (+ b (lognot x)))
                     (b* ((xlen (integer-length x)))
                       (cond ((equal x 0) 0)
                             ((and (equal b 1)
                                   (equal x (ash 1 (1- xlen))))
                              (1- xlen))
                             ((and (equal b 1)
                                   (equal x (- (ash 1 xlen))))
                              (1+ xlen))
                             (t xlen)))))
     :hints (("goal" :induct (integer-length-of-negate-gen-ind b x)
              :expand ((integer-length (+ 1 (lognot x)))
                       (integer-length x)
                       (ash 1 (+ 1 (integer-length (logcdr x))))
                       (ash 1 (integer-length (logcdr x))))
              :in-theory (enable bitp)))))
  

  (defthm integer-length-of-negate
    (implies (integerp x)
             (equal (integer-length (- x))
                    (b* ((xlen (integer-length x)))
                      (cond ((equal x (expt 2 (1- xlen)))
                             (1- xlen))
                            ((equal x (- (expt 2 xlen)))
                             (1+ xlen))
                            (t xlen)))))
    :hints (("goal" :use ((:instance integer-length-of-negate-gen
                           (b 1)))
             :in-theory (enable lognot bitops::ash-is-expt-*-x)
             :cases ((equal (integer-length x) 0))))))


(define ratmsb ((x rationalp))
  :returns (msb integerp :rule-classes :type-prescription)
  ;; We want the integer e such that bit e of x differs from bit e+1, and bits e+1 and above are the same
  ;; i.e. (rattail e+1 x) = 0 or -1, (ratbitp e x) != (ratbitp e+1 x)

  ;; For x=0 this isn't well-defined so we'll just return 0.
  ;; For positive x, this means 1 <= (ratshift x (- e)) < 2
  ;; For negative x, this means -2 <= (ratshift x (- e)) < 1.
  
  ;; That is, we want the integer e such that x = scand * 2^e, 1 <= scand < 2 or -2 <= scand < 1.
  ;; If x is an integer, e is (1- (integer-length (abs x))) by integer-length-minus-1-is-exponent above.
  
  ;; In general, we have x = n / d, integers.  Let en / ed be their respective
  ;; exponents, scn / scd their significands (1 <= scd < 2, and either 1 <= scn < 2 or -2 <= scn < 1).
  ;; n / d = scn * 2^en / (scd * 2^ed)
  ;;       = (scn / scd) * 2^(en - ed).
  ;; If x (and scn) is positive, scn / scd ranges from 1/2 < scn/scd < 2.
  ;; Two cases: if scn >= scd, then 1 <= scn / scd < 2 and the answer is en - ed.
  ;; Otherwise (scn < scd), then 1 < 2*scn/scd < 2 and the answer is en-ed-1.

  ;; If x (and scn) is negative, scn/scd ranges from -2 <= scn/scd < -1/2.
  ;; If (- scn) > scd, then -2 <= scn/scd < -1  and the answer is en - ed.
  ;; Otherwise ((-scn) <= scd), then -1 <= scn/scd < -1/2 and the answer is en-ed-1.


  (b* (((when (eql (mbe :logic (rfix x) :exec x) 0))
        0)
       (n (numerator x))
       (d (denominator x))
       (en (1- (integer-length n)))
       (ed (1- (integer-length d)))
       ((mv nnorm dnorm)
        (if (< en ed)
            (mv (ash n (- ed en)) d)
          (mv n (ash d (- en ed))))))
    (if (< nnorm 0)
        (if (< dnorm (- nnorm))
            (- en ed)
          (1- (- en ed)))
      (if (<= dnorm nnorm)
          (- en ed)
        (1- (- en ed)))))
  ///
  (local (defthm integer-length->-0
           (implies (and (not (equal (ifix x) 0))
                         (not (equal x -1)))
                    (posp (integer-length x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))
           :rule-classes :type-prescription))

  (defthm ratmsb-correct-positive
    (implies (and (rationalp x)
                  (< 0 x))
             (let ((scand (/ x (expt 2 (ratmsb x)))))
               (and (<= 1 scand)
                    (< scand 2))))
    :hints(("Goal" :in-theory (e/d (bitops::ash-is-expt-*-x
                                    acl2::exponents-add-unrestricted
                                    multiply-out-<)
                                   (rational-implies2
                                    ACL2::*-R-DENOMINATOR-R))
            :use ((:instance integer-length-minus-1-is-exponent-pos
                   (x (numerator x)))
                  (:instance integer-length-minus-1-is-exponent-pos
                   (x (denominator x)))
                  (:instance rational-implies2 (x x))))
           (and stable-under-simplificationp
                '(:nonlinearp t))))

  (defthm denominator-of-neg
    (equal (denominator (- x))
           (denominator x))
    :hints (("goal" :cases ((rationalp x)))))

  (local (defthm crock
           (implies (and (equal n (* x d))
                         (Rationalp x)
                         (integerp n)
                         (posp d)
                         (equal (* n ed)
                                (* d en))
                         (rationalp en)
                         (< 0 en)
                         (rationalp ed)
                         (< 0 ed))
                    (equal (* x ed) en))
           :hints (("goal" :nonlinearp t))))
  
  (local
   (defthm ratmsb-of-negate-pos
     (implies (and (rationalp x)
                   (< 0 x))
              (equal (ratmsb (- x))
                     (b* ((xmsb (ratmsb x)))
                       (cond ((equal x (expt 2 xmsb))
                              (1- xmsb))
                             ;; ((equal x (- (expt 2 (1+ (ratmsb x)))))
                             ;;  (1+ xmsb))
                             (t xmsb)))))
     :hints(("Goal" :in-theory (e/d (bitops::ash-is-expt-*-x
                                     acl2::exponents-add-unrestricted
                                     multiply-out-<)
                                    (rational-implies2
                                     ACL2::*-R-DENOMINATOR-R))
             :use ((:instance integer-length-minus-1-is-exponent-pos
                    (x (numerator x)))
                   (:instance integer-length-minus-1-is-exponent-pos
                    (x (denominator x)))
                   (:instance rational-implies2 (x x))))
            (and stable-under-simplificationp
                 '(:nonlinearp t)))
     :otf-flg t))

  ;; (local (defthm diff-of-expts
  ;;          (implies (< (expt 2 m) (expt 2 n))
  ;;                   (<= (* 2 (expt 2 m)) (expt 2 n)))
  ;;          :hints (("goal" :induct (expt 2 n)
  ;;                   :in-theory (enable expt)))))

  ;; (local (defthm expt-plus1
  ;;          (implies (integerp n)
  ;;                   (equal (expt 2 (+ 1 n))
  ;;                          (* 2 (expt 2 n))))
  ;;          :hints(("Goal" :in-theory (enable expt)))))

  ;; (local (defthm expt-minus1
  ;;          (implies (integerp n)
  ;;                   (equal (expt 2 (+ 1 n))
  ;;                          (* 2 (expt 2 n))))
  ;;          :hints(("Goal" :in-theory (enable expt)))))
  
  (defthm ratmsb-of-expt-2
    (implies (integerp n)
             (equal (ratmsb (expt 2 n))
                    n))
    :hints (("goal" :use ((:instance ratmsb-correct-positive
                           (x (expt 2 n)))
                          (:instance acl2::expt-is-increasing-for-base>1
                           (r 2) (i (+ 1 (ratmsb (expt 2 n)))) (j n))
                          (:instance acl2::expt-is-increasing-for-base>1
                           (r 2) (j (ratmsb (expt 2 n))) (i n)))
             :in-theory (e/d (multiply-out-<
                              acl2::exponents-add-unrestricted)
                             (ratmsb-correct-positive
                              ratmsb
                              acl2::expt-is-increasing-for-base>1
                              acl2::expt-is-weakly-increasing-for-base>1))))
    :otf-flg t)

  (defthm ratmsb-of-minus-expt-2
    (implies (integerp n)
             (equal (ratmsb (- (expt 2 n)))
                    (- n 1)))
    :hints (("goal" :use ((:instance ratmsb-correct-positive
                           (x (expt 2 n)))
                          (:instance acl2::expt-is-increasing-for-base>1
                           (r 2) (i (+ 1 (ratmsb (- (expt 2 n))))) (j (- n 1)))
                          (:instance acl2::expt-is-increasing-for-base>1
                           (r 2) (j (ratmsb (- (expt 2 n)))) (i (- n 1))))
             :in-theory (e/d (multiply-out-<
                              acl2::exponents-add-unrestricted)
                             (ratmsb-correct-positive
                              ratmsb
                              acl2::expt-is-increasing-for-base>1
                              acl2::expt-is-weakly-increasing-for-base>1))))
    :otf-flg t)
  
  (defthm ratmsb-of-negate
    (implies (rationalp x)
             (equal (ratmsb (- x))
                    (b* ((xmsb (ratmsb x)))
                      (cond ((equal x (expt 2 xmsb))
                             (1- xmsb))
                            ((equal x (- (expt 2 (1+ xmsb))))
                             (1+ xmsb))
                            (t xmsb)))))
    :hints (("goal" :use ((:instance ratmsb-of-negate-pos
                           (x (- x)))
                          (:instance ratmsb-of-negate-pos
                           (x x)))
             :in-theory (disable ratmsb-of-negate-pos
                                 ratmsb))))

  (defthm ratmsb-of-rfix
    (equal (ratmsb (rfix x))
           (ratmsb x)))
  
  (defthm ratmsb-correct-negative
    (implies (and (rationalp x)
                  (< x 0))
             (let ((scand (/ x (expt 2 (ratmsb x)))))
               (and (<= -2  scand)
                    (< scand -1))))
    :hints (("goal" :use ((:instance ratmsb-correct-positive
                           (x (- x))))
             :in-theory (e/d (acl2::exponents-add-unrestricted
                              multiply-out-<)
                             (ratmsb)))
            (and stable-under-simplificationp
                 '(:use ((:instance ratmsb-of-minus-expt-2
                          (n (ratmsb x))))
                   :in-theory (disable ratmsb ratmsb-of-minus-expt-2))))
    :otf-flg t)

  ;; (defthm rattail-of-ratmsb
  ;;   (equal (rattail (ratmsb x) x)
  ;;          (cond ((equal (rfix x) 0) 0)
  ;;                ((< x 0) -2)
  ;;                (t 1)))
  ;;   :hints(("Goal" :in-theory (e/d (rattail)
  ;;                                  (ratmsb)))))
  )


(define ratbits-collect ((r rationalp)
                      (from integerp)
                      (to integerp))
  :measure (abs (- (ifix from) (ifix to)))
  (b* (((when (eql (lifix from) (lifix to)))
        (list (ratbitp from r))))
    (cons (ratbitp from r)
          (ratbits-collect r (if (< (lifix from) (lifix to))
                              (+ 1 (lifix from))
                            (+ -1 (lifix from)))
                        to)))
  ///
   (local (in-theory (disable rfix))))
       
