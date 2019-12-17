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

(include-book "mult-defs")
(include-book "binary-fn-defs")

;;(include-book "pp-rules")

;(include-book "macros")

(include-book "meta/top")

(include-book "spec")

(local
 (in-theory (enable n2b f2 m2 m2-new d2 d2-new p+ b+ ba pp type-fix
                    bit-fix)))

(local
 (defthm merge-b+-to-b+
   ;; in case meta rule is disabled.
   (equal (merge-b+ a c)
          (sum a c))
   :hints (("Goal"
            :in-theory (e/d (merge-b+ b+ type-fix) ())))))

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (use-arithmetic-5 t))

#|
(defthm evenp-implies-integerp
  (implies  (evenp x)

           (integerp x))
  :hints (("Goal"
           :in-theory (e/d () ()))))||#
#|
(local
 (defthm if-half-is-integer-then-so-is-number
   (IMPLIES (AND (INTEGERP (* 1/2 A))
                 (ACL2-NUMBERP A))
            (INTEGERP A))))||#

(def-rp-rule$ t t
  hide-x-is-x-all
  ;; (syntaxp
  ;;  (and (not (equal (car x) 'bo))
  ;;       (not (equal (car x) 'ba))
  ;;       ;;(not (equal (caar x) 'lambda))
  ;;       ))
  (equal (hide x)
         x)
  :hints (("Goal"
           :expand (hide x))))

(deftheory hide-x-is-x-rules
  '(hide-x-is-x-all))

(def-rp-rule len-of-take
  (implies (natp a)
           (equal (len (take a x)) a))
  :hints (("Goal"
           :in-theory (e/d (take) ()))))

(def-rp-rule len-nthcdr
  (implies (<= n (len l))
           (equal (len (nthcdr n l))
                  (- (len l) (nfix n)))))

(def-rp-rule len-of-nthcdr
  (implies (natp a)
           (equal (len (nthcdr a x))
                  (nfix (- (len x) a )))))

(def-rp-rule$ t t
  true-list-take
  (true-listp (take a x)))

(def-rp-rule$ t t
  true-list-nthcdr
  (implies (true-listp x)
           (true-listp (nthcdr a x))))

(encapsulate
  nil
  ;;;;;;;;;;;;;;;;;;;;;;
  ;; [] rules
  ;;;;;;;;;;;;;;;;;;;;;;;
  (local (in-theory (enable [] []-take take []-cdr)))
  (local
   (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthmd take-is-[]-take
     (equal (take n x)
            ([]-take x n))
     :hints (("Goal"
              :in-theory (e/d (take #|TAKE-REDEFINITION||# ) ())))))

  (defthmd []-cdr-is-nth-cdr
    (equal ([]-cdr x n)
           (nthcdr n x)))

  (defthmd nth-is-car-nthcdr
    (equal (car (nthcdr n x))
           (nth n x)))

  (defthmd []-is-nth
    (equal ([] x n)
           (nth n x))
    :hints (("Goal"
             :in-theory
             (e/d (nth-is-car-nthcdr
                   []-cdr-is-nth-cdr)))))

  (def-rp-rule bitp-[]
    (implies (and (bit-listp a)
                  (natp n)
                  (< n (len a)))
             (bitp ([] a n)))
    :hints (("Goal"
             :in-theory (enable []-is-nth))))

  (def-rp-rule bitp-car-list
    (implies (and (bit-listp a)
                  (consp a))
             (bitp (car a)))
    :rule-classes :type-prescription)

  (def-rp-rule cdr-[]-cdr
    (implies (not (zp x))
             (equal (cdr ([]-cdr a x))
                    ([]-cdr a (1+ x)))))

  (def-rp-rule len-[]-cdr
    (implies (and (not (zp n))
                  (<= n (len x)))
             (equal (len ([]-cdr x n))
                    (- (len x) n))))

  (def-rp-rule pos-len-is-consp
    (implies (> (len x) 0)
             (consp x)))

  (def-rp-rule bit-listp-append
    (implies (and (bit-listp a)
                  (bit-listp b))
             (bit-listp (append a b))))

  (local
   (defthm lemma2
     (implies (and (NOT (ZP N))
                   (< N (LEN X)))
              (CONSP ([]-CDR X N)))))

  (defthmd array-cdr-1-is-cdr
    (equal ([]-cdr x 1)
           (cdr x))
    :hints (("Goal"
             :expand ([]-cdr x 1))))

  (def-rp-rule$ t t
    cons-of-car-and-cdr-to-[]
    (implies (consp a)
             (equal (cons ([] A 0) ([]-CDR A 1))
                    a))
    :hints (("Goal"
             :in-theory (e/d ([] []-cdr) ()))))

  (def-rp-rule$ t t
    cons-of-car-and-cdr-to-[]-2
    (implies (consp a)
             (equal (cons ([] A 0) (append ([]-CDR A 1) b))
                    (append a b)))
    :hints (("Goal"
             :in-theory (e/d ([] []-cdr) ()))))

  (def-rp-rule$ t t
    cons-of-[]-and-cdr
    (implies (> (len a) 0)
             (equal (cons ([] a 0) ([]-cdr a 1))
                    a)))

  (local
   (defthm []-cdr-to-cons-2-lemma
     (implies (and (true-listp a) (equal 1 (len a)))
              (equal (list (car a)) a))))

  (def-rp-rule []-cdr-to-cons-2
    (implies (and (not (zp n))
                  (syntaxp (or (acl2::variablep a)
                               (equal (car a) 'take)
                               (equal (car a) 'nthcdr)
                               (equal (car a) 'twos-complement-spec) ))
                  (= (1+ n) (len a))
                  (true-listp a))
             (and (equal ([]-cdr a n)
                         (cons ([] a n) nil))))
    :hints (("Goal"
             :in-theory (e/d
                         ([]-cdr-is-nth-cdr
                          nth-is-car-nthcdr
                          []-is-nth)
                         (cdr-[]-cdr)))))

  (def-rp-rule []-cdr-to-cons
    (implies (and (syntaxp (or (acl2::variablep a)
                               (equal (car a) 'take)
                               (equal (car a) 'nthcdr)
                               (equal (car a) 'twos-complement-spec) ))
                  (not (zp n))
                  (< (1+ n) (len a)))
             (equal ([]-cdr a n)
                    (cons ([] a n) ([]-cdr a (1+ n)))))
    :hints (("Goal"
             :in-theory (e/d
                         nil
                         (cdr-[]-cdr)))))

  (def-rp-rule []-take-to-list
    (implies (and (equal n (len a))
                  (true-listp a))
             (equal ([]-take a n)
                    a)))

  (def-rp-rule bit-listp-is-true-listp
    (implies (bit-listp x)
             (true-listp x)) )

  (def-rp-rule append-[]-take
    (implies
     (not (zp n))
     (equal (append ([]-take a n) (cons ([] a n) rest))
            (append ([]-take a (1+ n)) rest)))
    :hints (("Goal"
             :in-theory (enable []-is-nth))))

  (def-rp-rule append-nil
    (implies (true-listp a)
             (equal (append a nil)
                    a)))

  (def-rp-rule []-of-take
    (implies (and (natp a)
                  (natp i)
                  (< i a))
             (equal ([] (take a x) i)
                    ([] x i)))
    :hints (("Goal"
             :in-theory (e/d ([]-is-nth take-is-[]-take) ()))))

  (def-rp-rule []-of-nthcdr
    (implies (and (natp i1)
                  (natp i2))
             (equal ([] (nthcdr i1 v) i2)
                    ([] v (+ i1 i2))))
    :hints (("Goal"
             :in-theory (e/d ([]-is-nth) ()))))


  (deftheory []-rules
    '(append-[]-take
      []-of-take
      []-take-to-list
      cdr-[]-cdr
      []-cdr-to-cons-2
      []-cdr-to-cons
      len-[]-cdr
      pos-len-is-consp
      bit-listp-append
      bitp-car-list))

  (in-theory (disable []-rules)))

(local
 (in-theory (enable binaryp b+ m2 f2
                    mod floor d2 ~ merge-pp+
                    b2n)))
(local
 (in-theory (disable n2b)))

(local
 (defthm type-fix-n2b
   (equal (type-fix (n2b a))
          (type-fix a))
   :hints (("Goal"
            :in-theory (e/d (n2b type-fix) ())))))

(local
 (defthm hide-x-is-x
   (equal (hide x)
          x)
   :hints (("Goal"
            :expand (hide x)))))

(def-rp-rule m2-of-single-pp
  (implies t
           (equal (m2 (pp-sum (pp a)))
                  (pp a))))

(local
 (defthmd lemma1
   (implies
    (and (integerp y)
         (integerp x))
    (equal (mod (+ x y) 2)
           (if (equal (mod x 2) (mod y 2))
               0
             1)))))

#|(defthm b+-a-minus-a-backup1
  (equal (sum a b (-- a) c)
         (sum b c)))||#

(defthmd b+-a-minus-a-backup1-extra
  (equal (sum a b b2 (-- a) c)
         (sum b b2 c)))

(defthmd b+-a-minus-a-backup1-extra2
  (equal (sum a b b2 b3 (-- a) c)
         (sum b b2 b3 c)))

(defthmd b+-a-minus-a-backup1-extra3
  (equal (sum a b b2 b3 b4 (-- a) c)
         (sum b b2 b3 b4 c)))

(defthm b+-a-minus-a-backup2
  (equal (sum (-- a) b a c)
         (sum b c)))

(defthmd b+-a-minus-a-backup2-extra
  (equal (sum (-- a) b b2 a c)
         (sum b b2 c)))

(defthmd b+-a-minus-a-backup2-extra2
  (equal (sum (-- a) b b2 b3 a c)
         (sum b b2 b3 c)))

(defthmd b+-a-minus-a-backup2-extra3
  (equal (sum (-- a) b b2 b3 b4 a c)
         (sum b b2 b3 b4 c)))

(defthmd ba-comm
  (equal (ba y x)
         (ba x y))
  :hints (("Goal"
           :in-theory (e/d (binary-and) ()))))

(encapsulate
  nil

  (def-rp-rule$ t t
    b+-comm-1
    (implies (syntaxp (s-order x y))
             (equal (b+ y x)
                    (b+ x y)))
    :rule-classes ((:rewrite :loop-stopper nil)))

  (def-rp-rule$ t t
    b+-comm-1a
    (equal (b+ (f2 y) (p+ a b))
           (b+ (p+ a b) (f2 y))))

  (def-rp-rule$ t t
    b+-comm-1b
    (equal (b+ (d2 y) (p+ a b))
           (b+ (p+ a b) (d2 y))))

  (def-rp-rule$ t t
    b+-comm-1c
    (equal (b+ (f2 y) (m2 a))
           (b+ (m2 a) (f2 y))))

  (def-rp-rule$ t t
    b+-comm-1d
    (equal (b+ (d2 y) (m2 a))
           (b+ (m2 a) (d2 y))))

  (def-rp-rule$ t t
    b+-comm-1e
    (equal (b+ (p+ x y) (m2 a))
           (b+ (m2 a) (p+ x y))))

  (def-rp-rule$ t t
    b+-comm-f
    (implies (syntaxp (not (equal x ''t)))
             (equal (b+ t x)
                    (b+ x t))))

  (def-rp-rule$ t t
    b+-comm-1g
    (implies (syntaxp (< xn yn))
             (equal (b+ ([] y yn) ([] x xn))
                    (b+ ([] x xn) ([] y yn)))))

  (def-rp-rule$ t t
    b+-comm-2
    (implies (syntaxp (s-order x y))
             (equal (b+ y (b+ x z))
                    (merge-sum x y z)))
    :rule-classes ((:rewrite :loop-stopper nil)))

  (def-rp-rule$ t t
    b+-comm-2-[]
    (implies (syntaxp (< xn yn))
             (equal (b+ ([] y yn) (b+ ([] x xn) z))
                    (b+ ([] x xn) (b+ ([] y yn) z))))
    :rule-classes ((:rewrite :loop-stopper nil)))

  (deftheory b+-comm-rules
    '(b+-comm-1
      b+-comm-1a b+-comm-1b b+-comm-1c b+-comm-1d b+-comm-1e b+-comm-f
      b+-comm-1g
      b+-comm-2
      b+-comm-2-[]))

  #|(defthm b+-reorder-thm
  (equal (b+ (b+ x y) z)
  (b+ x (b+ y z))))||#

  (def-rp-rule$ t t
    b+-reorder-thm
    (equal (b+ (b+ x y) z)
           (merge-b+ (b+ x y) z)))

  (def-rp-rule$ t t
    b+-reorder-1a
    (equal (sum (sum a b) x y)
           (sum a b x y)));)

  (def-rp-rule$ t t
    b+-reorder-1b
    (implies (syntaxp (s-order x a))
             (equal (sum (sum a b) x y)
                    (sum x (sum a b) y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-rp-rule sum-pp->pp-sum-pp-1
  (equal (sum (pp a) c)
         (merge-sum (pp-sum (pp a)) c)))

(def-rp-rule sum-pp->pp-sum-pp-2
  (equal (sum x (pp a))
         (merge-sum x (pp-sum (pp a)))))

(def-rp-rule sum-pp+_merge1
  (equal (sum (pp-sum a b) (pp-sum c d))
         (merge-pp+ (pp-sum a b) (pp-sum c d)))
  :hints (("Goal"
           :expand (:free (x) (hide x)))))

(def-rp-rule sum-pp+_merge2
  (equal (sum (pp-sum a b) (pp-sum c d) e)
         (sum (merge-pp+ (pp-sum a b) (pp-sum c d)) e))
  :hints (("Goal"
           :expand (:free (x) (hide x)))))

(def-rp-rule c-of-single-pp-sum
  (equal (f2 (sum (pp-sum a b)))
         (f2 (pp-sum a b)))
  :hints (("Goal"
           :expand (:free (x) (hide x)))))

(def-rp-rule s-of-single-pp-sum
  (equal (m2 (sum (pp-sum a b)))
         (m2 (pp-sum a b)))
  :hints (("Goal"
           :expand (:free (x) (hide x)))))

(encapsulate
  nil

  (local
   (use-arithmetic-5 t))

  (local
   (in-theory (disable mod floor)))

  (def-rp-rule convert-d2-to-f2
    (equal (d2 (sum (-- (m2 a)) a))
           (f2-new a)))


  (def-rp-rule c-merge-1
    (equal (sum (f2 a) (f2 b))
           (d2-new (merge-sum (merge-sum (-- (m2-new a)) (-- (m2-new b)))
                              a b))))

  (defthmd c-merge-1-type-cond
    (evenp2 (merge-sum (merge-sum (-- (m2-new a)) (-- (m2-new b)))
                              a b))
    :hints (("Goal"
             :in-theory (e/d (evenp2) ()))))

  (rp::rp-attach-sc c-merge-1
                    c-merge-1-type-cond)

  (def-rp-rule c-merge-1-shortcut
    (and (equal (sum (f2 x) (c (m2 x) y))
                (f2-new (merge-b+ x y)))
         (equal (sum (c (m2 x) y) (f2 x))
                (f2-new (merge-b+ x y)))))

  #|(defthm c-merge-1-shortcut-2-
    (and (equal (sum (f2 x) (c (m2 x) y) z)
                (sum (f2-new (merge-b+ x y)) z))
         (equal (sum (c (m2 x) y) (f2 x) z)
                (sum (f2-new (merge-b+ x y)) z))))||#

  (def-rp-rule c-merge-2
    (implies (evenp2 a)
             (equal (sum (d2 a) (f2 b))
                    (d2-new (merge-sum a (-- (m2-new b)) b)))))

  (defthmd c-merge-2-slow
    (implies (evenp2 a)
             (equal (sum x (d2 a) (f2 b))
                    (sum x (d2-new (merge-sum a (-- (m2-new b)) b))))))

  (defthmd c-merge-2-side-cond
    (implies (evenp2 a)
             (evenp2 (merge-sum a (-- (m2-new b)) b)))
    :hints (("Goal"
             :in-theory (e/d (evenp2) ()))))

  (rp::rp-attach-sc c-merge-2
                    c-merge-2-side-cond)

  (rp::rp-attach-sc c-merge-2-slow
                    c-merge-2-side-cond)

  (def-rp-rule c-merge-2r
    (implies (evenp2 b)
             (equal (sum (f2 a) (d2 b))
                    (d2-new (merge-sum b (-- (m2-new a)) a)))))

  (defthmd c-merge-2r-slow
    (implies (evenp2 b)
             (equal (sum x (f2 a) (d2 b))
                    (sum x (d2-new (merge-sum b (-- (m2-new a)) a))))))

  (defthmd c-merge-2r-side-cond
    (implies (evenp2 b)
             (evenp2 (merge-sum b (-- (m2-new a)) a)))
    :hints (("Goal"
             :in-theory (e/d (evenp2) ()))))

  (rp::rp-attach-sc c-merge-2r
                    c-merge-2r-side-cond)

  (rp::rp-attach-sc c-merge-2r-slow
                    c-merge-2r-side-cond)

  (def-rp-rule c-merge-3
    (implies (and (evenp2 a)
                  (evenp2 b))
             (equal (sum (d2 a) (d2 b))
                    (d2-new (merge-b+ a b))))
    :hints (("Goal"
             :in-theory (e/d (evenp2) ()))))

  (defthmd c-merge-3-side-cond
    (implies (and (evenp2 a)
                  (evenp2 b))
             (evenp2  (merge-b+ a b)))
    :hints (("Goal"
             :in-theory (e/d (evenp2) ()))))

  (rp::rp-attach-sc c-merge-3
                    c-merge-3-side-cond))

(encapsulate
  nil

  (defun less-or-eq (x y)
    (<= x y))

  (defun less-than (x y)
    (< x y))

  (defun not-negp (x)
    (or (<= 0 x)
        (booleanp x)))

  (def-rp-rule mul-last-bit-save-from-m2-1
    (implies (and (less-than a 4) (not-negp a))
             (equal (m2 (f2 a)) (f2 a)))
    :instructions ((:dive 1 1)
                   :expand :top (:dive 1 2)
                   :expand :top (:casesplit (integerp a))
                   (:casesplit (< a 2))
                   :promote :s
                   :s :prove
                   :s :s
                   :prove :s))

  (defthmd mul-last-bit-save-from-m2-1-side-cond
    (implies (and (less-than a 4) (not-negp a))
             (bitp (f2 a)))
    :hints (("Goal"
             :cases ((equal a 0)
                     (equal a 1)
                     (equal a 2)
                     (equal a 3))
             :in-theory (e/d (less-than not-negp f2 type-fix) ()))))

  (rp-attach-sc mul-last-bit-save-from-m2-1
                mul-last-bit-save-from-m2-1-side-cond)

  #|(defthmd mul-last-bit-save-from-m2-1-for-f2o
  (implies (and (less-than a 4) (not-negp a))
  (equal (m2 (d2 a)) (d2 a)))
  :instructions ((:dive 1 1)
  :expand :top (:dive 1 2)
  :expand :top (:casesplit (integerp a))
  (:casesplit (< a 2))
  :promote :s
  :s :prove
  :s :s
  :prove :s))||#

  (def-rp-rule mul-last-bit-save-from-m2-2
    (equal (s 0 (f2 a)) (m2 (f2 a))))

  (defthmd mul-last-bit-save-from-m2-old
    (implies (and (less-than a 4) (not-negp a))
             (equal (equal (m2 (f2 a)) (f2 a))
                    t))
    :instructions ((:dive 1 1)
                   :expand :top (:dive 1 2)
                   :expand :top (:casesplit (integerp a))
                   (:casesplit (< a 2))
                   :promote :s
                   :s :prove
                   :s :s
                   :prove :s)))

#|(defthmd b+-of-n2b-1
  (equal (sum (n2b a) b)
         (sum a b)))||#

#|(defthmd b+-of-n2b-3
  (equal (sum a (n2b b))
         (sum a b)))||#

#|(defthmd pp+-of-n2b-1
  (equal (pp-sum (n2b a) b)
         (pp-sum a b)))||#

#|(defthmd pp+-of-n2b-3
  (equal (pp-sum a (n2b b))
         (pp-sum a b)))||#

(def-rp-rule mod-mod-2
  (equal (m2 (m2 x))
         (m2 x)))

(def-rp-rule type-fix-of-m2
  (equal (type-fix (m2 x))
         (m2 x)))

(def-rp-rule s-of-s
  (equal (s (m2 a) b)
         (m2-new (merge-b+ a b)))
  :hints (("Goal"
           :use ((:instance mod-mod-2 (x a)))
           :in-theory '((:COMPOUND-RECOGNIZER BOOLEANP-COMPOUND-RECOGNIZER)
                        (:DEFINITION B+)
                        (:e mod)
                        m2-new
                        (:DEFINITION M2)
                        (:DEFINITION SYNP)
                        (:DEFINITION type-p)
                        (:DEFINITION TYPE-FIX)
                        (:EXECUTABLE-COUNTERPART <)
                        (:EXECUTABLE-COUNTERPART RATIONALP)
                        (:EXECUTABLE-COUNTERPART integerp)
                        (:EXECUTABLE-COUNTERPART UNARY--)
                        (:REWRITE ACL2::|(+ 0 x)|)
                        (:REWRITE ACL2::|(+ x (- x))|)
                        (:REWRITE ACL2::|(+ y (+ x z))|)
                        (:REWRITE ACL2::|(+ y x)|)
                        (:REWRITE ACL2::|(mod (+ x (mod a b)) y)|)
                        (:REWRITE ACL2::|(mod (+ x y) z) where (<= 0 z)|
                                  . 1)
                        (:REWRITE ACL2::BUBBLE-DOWN-+-MATCH-1)
                        (:REWRITE MERGE-B+-TO-B+)
                        (:REWRITE ACL2::NORMALIZE-ADDENDS)
                        (:REWRITE TYPE-FIX-N2B)
                        (:TYPE-PRESCRIPTION ACL2::MOD-NONNEGATIVE)))))

(def-rp-rule f2-of-single-pp
  (implies t
           (equal (f2 (pp-sum (pp a)))
                  0)) ;;ax1
  :hints (("Goal"
           :expand (:free (x) (hide x)))))

(def-rp-rule f2-of-single-bitp
  (implies (bitp x)
           (equal (f2 (pp-sum x))
                  0)) ;;ax1
  :hints (("Goal"
           :expand (:free (x) (hide x)))))

#|(local
 (in-theory (disable F-GATES=B-GATES)))||#

(encapsulate
  nil
  (def-rp-rule b+-0
    (equal (sum 0 x y)
           (sum x y)))

  (def-rp-rule b+-0-2
    (equal (sum a 0 b)
           (sum a b)))

  (def-rp-rule b+-0-pp-sum
    (equal (sum 0 (pp-sum a b))
           (pp-sum a b)))

  (def-rp-rule b+-0-3
    (equal (sum b 0)
           (type-fix b)))

  (def-rp-rule b+-0-type-fix-1
    (equal (b+ 0 x)
           (type-fix x)))

  (def-rp-rule b+-nil-2
    (equal (sum nil y)
           (type-fix y))) ;;ax2

  (def-rp-rule b+-nil-3
    (equal (sum y nil)
           (type-fix y)));;ax2

  (def-rp-rule type-fix-sum
    (equal (type-fix (sum a b))
           (sum a b)))

  (def-rp-rule type-fix-pp-sum
    (and (equal (type-fix (pp-sum a b))
                (pp-sum a b))
         (equal (pp-sum (type-fix a) b)
                (pp-sum a b))
         (equal (pp-sum b (type-fix a))
                (pp-sum b a))))

  (def-rp-rule sum-type-fix-1
    (equal (sum a (type-fix b))
           (merge-sum a b)))

  (def-rp-rule sum-type-fix-2
    (equal (sum (type-fix a) b)
           (merge-sum a b)))

  (def-rp-rule m2-type-fix
    (equal (m2 (type-fix a))
           (m2 a)))

  (def-rp-rule f2-type-fix
    (equal (f2 (type-fix a))
           (f2-new a)))

  (def-rp-rule type-fix-of-f2
    (equal (type-fix (f2 a))
           (f2 a)))

  (def-rp-rule d2-type-fix
    (equal (d2 (type-fix a))
           (d2-new a))))

(encapsulate
  nil

  (local
   (use-arithmetic-5 nil))

  (local
   (include-book "ihs/quotient-remainder-lemmas" :dir :system))

  (local
   (defthmd m2-of-minus-m2-lemma1
     (implies (and (integerp a) (integerp b))
              (equal (mod (+ (- (mod a 2)) b) 2)
                     (mod (+ (- a) b) 2)))
     :hints (("Goal"
              :in-theory '((:EXECUTABLE-COUNTERPART BINARY-*)
                           (:EXECUTABLE-COUNTERPART UNARY-/)

                           (:REWRITE COMMUTATIVITY-OF-+)
                           (:REWRITE ACL2::SIMPLIFY-MOD-+-MOD))))))

  (def-rp-rule m2-of-minus-m2
    (equal (s (-- (m2 a)) b)
           (s (-- a) b))))

(def-rp-rule minus-ba+
  (equal (-- (pp-sum a b))
         (pp-sum (-- a) (-- b))))

(def-rp-rule minus-b+
  (equal (-- (b+ a b))
         (b+ (-- a) (-- b))))

(def-rp-rule b+-a-minus-a-0
  (equal (sum a (-- a) b)
         (sum b)));;ax2

(defthmd b+-a-minus-a-1
  (equal (sum a (-- a) b c)
         (sum b c)))

(def-rp-rule b+-a-minus-a-2
  (equal (sum (-- a) a b)
         (sum b)));;ax2

(defthmd b+-a-minus-a-3
  (equal (sum (-- a) a b c)
         (sum b c)))

(defthmd ba+-ba-0
  (equal (pp-sum a (-- a) b)
         (pp-sum b)))

(defthmd ba+-ba-1
  (equal (pp-sum (-- a) a b)
         (pp-sum b)))

(defthmd ba+-ba-2
  (equal (pp-sum (-- a) a)
         0))

(def-rp-rule a+-a-end-1
  (equal (sum a (-- a))
         0))

(def-rp-rule a+-a-end-2
  (equal (sum (-- a) a)
         0))

(def-rp-rule binaryp-natp
  (implies (binaryp a)
           (natp a)))

(in-theory (disable ba
                    (:DEFINITION BA)
                    (:e pp)
                    less-than less-or-eq
                    binaryp
                    not-negp
                    merge-pp+
                    merge-b+
                    hide-tmp
                    type-fix
                    p+
                    pp
                    --
                    b+ m2 f2 d2 d2-new
                    f2-new m2-new mod floor
                    n2b b2n))

(encapsulate
  nil

  (defthm f2-of-times2
    (implies t
             (equal (c (times2 a) b)
                    (merge-sum a (f2 (merge-sum b)))))
    :hints (("Goal"
             :do-not '(preprocess)
             :in-theory (e/d (merge-sum
                              f2
                              b+
                              type-fix
                              times2)
                             ()))))

  (local
   (defthm f2-of-minus-lemma1
     (equal (c (minus a) b)
            (f2 (sum (times2 (-- a)) a b)))
     :hints (("Goal"
              :in-theory (e/d (sum minus -- type-fix
                                   times2) ())))))

  (defthm f2-of-minus
    (implies t ;(bitp a)
             (equal (c (minus a) b)
                    (merge-sum (-- a) (f2 (merge-sum a b)))))
    :hints (("Goal"
             :in-theory (e/d () ())))))

(encapsulate
  nil

  (defthm s-of-times2
    (equal (s (times2 a) b)
           (s b))
    :hints (("Goal"
             :in-theory (e/d (m2 sum times2
                                 type-fix) ()))))

  (local
   (defthm s-of-minus-lemma
     (and (equal (s (minus a) b)
                 (m2 (sum (times2 (-- a)) a b)))
          (equal (s (-- a) b)
                 (m2 (sum (times2 (-- a)) a b))))
     :hints (("Goal"
              :in-theory (e/d (sum times2 -- type-fix minus) ())))))

  (defthm s-of-minus
    (and (equal (s (minus a) b)
                (m2 (merge-sum a b)))
         (equal (s (-- a) b)
                (m2 (merge-sum a b))))
    :hints (("Goal"
             :in-theory (e/d () ())))))

(encapsulate
  nil

  (local
   (use-arithmetic-5 t))

  (local
   (in-theory (e/d (not-negp type-fix n2b
                             merge-pp+
                             pp
                             less-than less-or-eq ba p+ b+ m2 f2)
                   ())))

  ;; (skip-proofs
  ;;  (defthm m2-range
  ;;    (and (less-than (m2 a) 2)
  ;;         (less-or-eq 0 (m2 a)))))

  ;; (defthm ba-range
  ;;   (less-or-eq (ba a b) 1))

  (def-rp-rule pp-range
    (less-or-eq (pp a) 1))

  (def-rp-rule and$-range
    (less-or-eq (and$ a b) 1))

  (def-rp-rule b+-pp-sum-range-1
    (implies (and
              (rationalp x)
              (less-than (sum c d) (1- x)))
             (less-than (sum (pp-sum (pp a) c)
                             d)
                        x)))

  (def-rp-rule b+-pp-sum-range-1-and$
    (implies (and
              (rationalp x)
              (less-than (sum (merge-pp-sum c) d) (1- x)))
             (less-than (sum (pp-sum (and$ a b) c)
                             d)
                        x)))

  (def-rp-rule b+-pp-sum-range-2
    (implies (and
              (rationalp x)
              (less-than (sum d) (1- x)))
             (less-than (sum (pp-sum (pp a)) d)
                        x)))

  (def-rp-rule b+-pp-sum-range-2-and$
    (implies (and
              (rationalp x)
              (less-than (sum d) (1- x)))
             (less-than (sum (pp-sum (and$ a b)) d)
                        x)))

  (def-rp-rule less-than-0
    (implies (< 0 x)
             (less-than 0 x)))

  (def-rp-rule pp-sum-range
    (implies (less-than (merge-pp+ c 0) (1- x))
             (less-than (pp-sum (pp a) c) x)))

  (def-rp-rule pp-sum-range-and$
    (implies (less-than (merge-pp+ c 0) (1- x))
             (less-than (pp-sum (and$ a b) c) x)))

  (def-rp-rule pp-sum-range-and$-2
    (implies (less-than 0 (1- x))
             (less-than (pp-sum (and$ a b)) x))
    :hints (("Goal"
             :in-theory (e/d (pp-sum type-fix and$ less-than) ()))))

  (def-rp-rule b+-floor-range
    (implies (and (posp x)
                  (less-than a (* 2 x)))
             (less-than (sum (f2 a))
                        x)))

  (def-rp-rule f2-range
    (implies (and (posp x)
                  (less-than a (* 2 x)))
             (less-than (f2 a)
                        x)))

  (def-rp-rule sum-is-not-neg
    (implies (And (not-negp x)
                  (not-negp y))
             (not-negp (sum x y)))
    :rule-classes :type-prescription)

  (def-rp-rule f2-is-not-neg
    (implies (not-negp x)
             (not-negp (f2 x)))
    :rule-classes :type-prescription)

  (def-rp-rule pp-sum-is-not-neg
    (implies (And (not-negp x)
                  (not-negp y))
             (not-negp (pp-sum x y)))
    :rule-classes :type-prescription)

  (def-rp-rule pp-is-not-negp
    (not-negp (pp x))
    :rule-classes :type-prescription)

  (def-rp-rule and-is-not-negp
    (not-negp (and$ x y))
    :rule-classes :type-prescription)

  (deftheory
    range-rules
    '(mul-last-bit-save-from-m2-old
      mul-last-bit-save-from-m2-1
      mul-last-bit-save-from-m2-2
      pp-range
      b+-pp-sum-range-1
      b+-pp-sum-range-2
      pp-sum-range-and$-2
      pp-sum-range
      b+-floor-range
      and$-range
      and-is-not-negp
      b+-pp-sum-range-1-and$
      b+-pp-sum-range-2-and$
      pp-sum-range-and$
      )))

(encapsulate
  nil
  (local
   (in-theory (disable cons-equal)))

  (def-rp-rule list-eq1
    (equal (equal (cons a b) (cons a c))
           (equal b c)))

  (def-rp-rule list-eq2
    (equal (equal (cons b nil) (cons c nil))
           (equal b c)))

  (def-rp-rule len-nil
    (equal (len nil)
           0))

  (def-rp-rule len-cons
    (equal (len (cons a b))
           (1+ (len b))))

  (def-rp-rule boolean-listp-nil
    (equal (boolean-listp nil)
           t))

  (def-rp-rule take-cons
    (implies (and (natp a)
                  (> a 0))
             (equal (take a (cons first rest))
                    (cons first
                          (take (1- a) rest)))))

  (def-rp-rule take-0
    (equal (take 0 x)
           nil))

  (def-rp-rule nthcdr-cons$
    (implies (and (natp a)
                  (> a 0))
             (equal (nthcdr a (cons first rest))
                    (nthcdr (1- a) rest))))

  (def-rp-rule nthcdr-0$
    (equal (nthcdr 0 lst)
           lst)))

(deftheory greedy-rules
  '((:rewrite mod-mod-2)
    (:rewrite a+-a-end-2)
    (:rewrite a+-a-end-1)
    (:rewrite b+-0)))

(deftheory useful-rules
  '(hide-x-is-x-rules
    []-rules
    #|resolve-assoc-eq-vals-correct||#))

(encapsulate
  nil

  (local
   (in-theory (enable repeat)))

  (def-rp-rule repeat-0
    (equal (repeat 0 x)
           nil))

  (def-rp-rule cdr-repeat
    (implies (posp n)
             (equal (cdr (repeat n x))
                    (repeat (1- n) x)))
    :hints (("Goal"
             :expand (repeat n x)
             :in-theory (e/d () ()))))

  (def-rp-rule car-repeat
    (implies (posp n)
             (equal (car (repeat n x))
                    x))
    :hints (("Goal"
             :expand (repeat n x)
             :in-theory (e/d () ())))))

(def-rp-rule bit-listp-cons
  (equal (bit-listp (cons x y))
         (and (bitp x)
              (bit-listp y))))

(def-rp-rule true-listp-cons
  (equal (true-listp (cons x y))
         (true-listp y)))

(def-rp-rule ~-of-pp
  (equal (~ (pp x))
         (pp (~ x)))
  :hints (("Goal"
           :in-theory (e/d (bitp pp ~) ()))))

(def-rp-rule minus-of-minus-is-term
  (equal (-- (-- a))
         (type-fix a))
  :hints (("Goal"
           :in-theory (e/d (-- type-fix) ()))))

(defthmd type-fix-when-natp
  (implies (natp x)
           (equal (type-fix x)
                  x))
  :hints (("Goal"
           :in-theory (e/d (type-fix) ()))))

(in-theory (disable b+-comm-rules))

(def-rp-rule bitp-m2
  (bitp (m2 x))
  :hints (("Goal"
           :in-theory (e/d (m2 mod bitp
                               floor
                               type-fix) ()))))

(def-rp-rule f2-of-and$
  (equal (f2 (and$ x y))
         0)
  :hints (("Goal"
           :in-theory (e/d (f2 and$) ()))))

(def-rp-rule m2-of-and$
  (equal (m2 (and$ x y))
         (and$ x y))
  :hints (("Goal"
           :in-theory (e/d (m2 and$) ()))))

(def-rp-rule m2-of-pp-sum-of-and$
  (equal (m2 (pp-sum (and$ a b)))
         (and$ a b))
  :hints (("Goal"
           :in-theory (e/d (and$
                            pp-sum) ()))))

(def-rp-rule f2-of-pp-sum-of-and$
  (equal (f2 (pp-sum (and$ a b)))
         0)
  :hints (("Goal"
           :in-theory (e/d (and$ f2 pp-sum) ()))))

(def-rp-rule m2-of-f2
  (implies (bitp (f2 a))
           (equal (m2 (f2 a))
                  (f2 a)))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(def-rp-rule equal-of-m2-of-f2
  (implies (bitp (f2 x))
           (and (equal (equal (f2 x)
                              (m2 (f2 x)))
                       t)
                (equal (equal (m2 (f2 x))
                              (f2 x))
                       t))))

(def-rp-rule binary-not-of-m2
  (equal (binary-not (m2 x))
         (m2-new (merge-sum 1 x)))
  :hints (("Goal"
           :in-theory (e/d (m2-new m2 binary-not
                                   merge-sum type-fix
                                   sum
                                   bitp
                                   mod
                                   floor) ()))))

#|(defthm sum-of-1
  (and (equal (sum 1 x)
              (merge-sum (merge-pp-sum 1) x))
       (equal (sum x 1)
              (merge-sum (merge-pp-sum 1) x))))||#

(def-rp-rule integerp-m2
  (integerp (m2 a))
  :hints (("Goal"
           :in-theory (e/d (m2 type-fix mod) ()))))

(def-rp-rule integerp-f2
  (integerp (f2 a))
  :hints (("Goal"
           :in-theory (e/d (f2 type-fix mod) ()))))

(def-rp-rule pp-sum-of-0
  (and (equal (pp-sum 0 x y)
              (pp-sum x y))
       (equal (pp-sum x y 0)
              (pp-sum x y))
       (equal (pp-sum x 0 y)
              (pp-sum x y)))
  :hints (("Goal"
           :in-theory (e/d (pp-sum
                            type-fix) ()))))

(def-rp-rule pp-sum-of-nil
  (equal (pp-sum nil x)
         (pp-sum 0 x))
  :hints (("Goal"
           :in-theory (e/d (pp-sum
                            type-fix) ()))))

(def-rp-rule pp-sum-of-0-fixorder
  (equal (pp-sum x 0)
         (pp-sum 0 x))
  :hints (("Goal"
           :in-theory (e/d (pp-sum
                            type-fix) ()))))

(def-rp-rule pp-sum-of-0-0
  (equal (pp-sum 0 0)
         0)
  :hints (("Goal"
           :in-theory (e/d (pp-sum
                            (:e p+)) ()))))



(def-rp-rule bit-of-bit-of-when-not-o
  (implies (and (> o-pos 0)
                (integerp o-pos))
           (equal (bit-of (bit-of x pos) o-pos)
                  0))
  :hints (("Goal"
           :in-theory (e/d (bit-of
                            zp)
                           ()))))

(def-rp-rule bit-of-bit-of-when-0
  (equal (bit-of (bit-of x pos) 0)
         (bit-of x pos))
  :hints (("Goal"
           :in-theory (e/d (bit-of) ()))))


;; pp-rules:

(def-rp-rule binary-xor-of-0
  (and (equal (binary-xor x 0)
              (bit-fix x))
       (equal (binary-xor 0 x)
              (bit-fix x)))
  :hints (("Goal"
           :in-theory (e/d (binary-xor
                            bit-fix
                            bitp) ()))))

(def-rp-rule binary-xor-of-1
  (and (equal (binary-xor x 1)
              (not$ x))
       (equal (binary-xor 1 x)
              (not$ x)))
  :hints (("Goal"
           :in-theory (e/d (binary-xor
                            bit-fix
                            not$
                            bitp) ()))))

(def-rp-rule not$-of-not$
  (equal (not$ (not$ x))
         (bit-fix x))
  :hints (("Goal"
           :in-theory (e/d (binary-not) ()))))


(def-rp-rule binary-?-of-constants
    (and (equal (binary-? 1 x y)
                (bit-fix x))
         (equal (binary-? 0 x y)
                (bit-fix y))
         (equal (binary-? x y 0)
                (and$ x y))
         (equal (binary-? x 1 y)
           (or$ x y))
         (equal (binary-? x 0 y)
                (and$ y (not$ x))))
    :hints (("Goal"
             :in-theory (e/d (binary-?
                              and$
                              not$
                              or$) ()))))

(def-rp-rule and$-of-0
  (and (equal (and$ 0 x)
              0)
       (equal (and$ x 0)
              0))
  :hints (("Goal"
           :in-theory (e/d (and$) ()))))

(def-rp-rule and$-of-1
  (and (equal (rp::and$ x 1)
              (rp::bit-fix x))
       (equal (rp::and$ 1 x)
              (rp::bit-fix x)))
  :hints (("Goal"
           :in-theory (e/d (rp::and$) ()))))

(def-rp-rule or$-of-0
  (and (equal (or$ 0 a)
              (bit-fix a))
       (equal (or$ a 0)
              (bit-fix a)))
  :hints (("Goal"
           :in-theory (e/d (or$) ()))))

(def-rp-rule or$-of-1
  (and (equal (or$ 1 a)
              1)
       (equal (or$ a 1)
              1))
  :hints (("Goal"
           :in-theory (e/d (or$) ()))))



(defconst *pp-rules*
  '(binary-xor-of-0
    and$-of-0
    not$-of-not$
    binary-?-of-constants
    and$-of-0
    binary-xor-of-1
    or$-of-0
    or$-of-1))



(def-rp-rule assoc-equal-opener
  (equal (assoc-equal key (cons (cons a b) rest))
         (if (equal key a)
             (cons a b)
           (assoc-equal key rest))))
           

(def-rp-rule f2-of-m2
  (equal (rp::f2 (rp::m2 rp::x))
         0)
  :hints (("Goal"
           :use ((:instance RP::BITP-M2))
           :in-theory (e/d (rp::f2 bitp)
                           (RP::BITP-M2)))))

(def-rp-rule type-fix-of-binary-fncs
  (and (equal (type-fix (binary-xor x y))
              (binary-xor x y))
       (equal (type-fix (binary-or x y))
              (binary-or x y))
       (equal (type-fix (binary-and x y))
              (binary-and x y))
       (equal (type-fix (binary-? x y z))
              (binary-? x y z))
       (equal (type-fix (binary-not x))
              (binary-not x)))
  :hints (("Goal"
           :in-theory (e/d (or$
                            not$
                            and$
                            binary-?
                            binary-xor) ()))))

