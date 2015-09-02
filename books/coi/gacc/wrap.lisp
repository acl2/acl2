; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

(in-package "GACC")

;A book about wrapped address ranges...

;(include-book "../lists/memberp")
(include-book "../bags/basic")

(include-book "../super-ihs/super-ihs")

(include-book "addr-range") ;bzo

(include-book "../lists/mixed")

(include-book "../lists/find-index")

(local (in-theory (disable ACL2::LOGHEAD-IDENTITY-2))) ;for efficiency... ;bzo, disable elsewhere?

(local (in-theory (enable list::memberp-when-not-memberp-of-cdr-cheap)))


;; [Jared] dumb speed hacking
(local (in-theory (disable acl2::UNSIGNED-BYTE-P-+-EASY
                           acl2::UNSIGNED-BYTE-P--OF-MINUS
                           acl2::LOGBITP-OF-ONE-LESS
                           acl2::LOGHEAD-LOWER-BOUND-WHEN-TOP-BIT-ONE
                           acl2::LOGHEAD-UPPER-BOUND-WHEN-TOP-BIT-ONE

                           ;; new rules
                           ACL2::|x < y  =>  0 < -x+y|
                           ;ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT
                           ;ACL2::EXPT-TYPE-PRESCRIPTION-INTEGERP
                           ;ACL2::EXPT-2-POSITIVE-RATIONAL-TYPE
                           default-+-2

                           )))


;;
;; OFFSET-RANGE-WRAP
;;


;reorder params?
;bzo is the 2nd call to loghead necessary?
;rename size param?
(defund offset-range-wrap (width base size)
  (declare (type integer base)
           (type (integer 0 *) size)
           (type (integer 0 *) width))
  (if (zp size)
      nil
    (cons (loghead width base)
          (offset-range-wrap width (loghead width (+ 1 (ifix base))) (+ -1 size)))))

;; (in-theory (disable (:executable-counterpart OFFSET-RANGE-WRAP)))

(defthm offset-range-wrap-when-size-is-not-positive
  (implies (<= size 0)
           (equal (offset-range-wrap width base size)
                  nil))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (offset-range-wrap width base size)
                  nil))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-when-width-is-zero
  (equal (offset-range-wrap 0 y size)
         (repeat size 0))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-when-width-is-zp
  (implies (zp width)
           (equal (offset-range-wrap width base size)
                  (repeat size 0)))
  :hints (("Goal" :in-theory (enable offset-range-wrap zp))))

(defthm offset-range-wrap-when-offset-is-not-an-integerp
  (implies (not (integerp offset))
           (equal (offset-range-wrap width offset numwords)
                  (offset-range-wrap width 0 numwords)))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-when-size-is-1
  (equal (offset-range-wrap width base 1)
         (list (loghead width base)))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm car-of-offset-range-wrap
  (equal (car (offset-range-wrap width base size))
         (if (zp size)
             nil
           (loghead width base)))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm consp-of-offset-range-wrap
  (equal (consp (offset-range-wrap width base size))
         (not (zp size)))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm integer-listp-of-offset-range-wrap
  (integer-listp (offset-range-wrap width base size))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-of-loghead
  (equal (offset-range-wrap width (loghead width base) size)
         (offset-range-wrap width base size))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-of-sum-hack
  (implies (and (syntaxp (quotep a))
                (not (acl2::unsigned-byte-p width a))
                (integerp a)
                (integerp b)
                )
           (equal (offset-range-wrap width (+ a b) size)
                  (offset-range-wrap width (+ (acl2::loghead width a) b) size)))
  :hints (("Goal" :use ((:instance offset-range-wrap-of-loghead (base (+ (acl2::loghead width a) b)))
                        (:instance offset-range-wrap-of-loghead (base (+ a b)))
                        )
           :in-theory (disable offset-range-wrap-of-loghead))))

(defthm not-memberp-of-offset-range-wrap-when-not-usbwidth
  (implies (not (unsigned-byte-p (nfix width) offset))
           (not (list::memberp offset (offset-range-wrap width base size))))
  :hints (("Goal" :expand (OFFSET-RANGE-WRAP WIDTH 0 SIZE)
           :in-theory (enable offset-range-wrap))))

(defthm memberp-of-offset-range-wrap-of-self
  (equal (bag::memberp offset (offset-range-wrap width offset size))
         (and (unsigned-byte-p (nfix width) offset)
              (integerp size)
              (< 0 size)))
  :hints (("Goal" :expand (offset-range-wrap width offset size)
           :in-theory (enable offset-range-wrap
                              list::memberp-of-cons
                              memberp-when-x-is-an-integer-listp))))

;bzo
;might this be expensive?

(defthmd not-equal-hack
  (implies (and (BAG::DISJOINT bag (OFFSET-RANGE-WRAP width offset1 size))
                (bag::memberp offset2 bag)
                (unsigned-byte-p width offset2) ;handle this better?
                (integerp size)
                (< 0 size)
                (equal width 16);bzo
                )
           (not (equal offset1 offset2)))
  :hints (("Goal" :in-theory (enable BAG::NOT-MEMBERP-FROM-DISJOINTNESS-ONE
                                     BAG::NOT-MEMBERP-FROM-DISJOINTNESS-two))))

;this may be expensive
;if we have a wrapping version of wx, this stuff may be nicer?
(defthmd use-DISJOINT-of-offset-range-wraps-hack
  (implies (and (BAG::DISJOINT (OFFSET-RANGE-WRAP width offset1 size1) (OFFSET-RANGE-WRAP width offset2 size2))
                (list::memberp offset3 (OFFSET-RANGE-WRAP width offset1 size1))
                (list::memberp offset4 (OFFSET-RANGE-WRAP width offset2 size2)))
           (not (equal offset3 offset4))))

(defthmd offset-range-wrap-const-opener ;bzo yuck!
  (implies (and (syntaxp (quotep size))
                (not (zp size))
                )
           (equal (offset-range-wrap width base size)
                  (cons (loghead width base)
                        (offset-range-wrap width (loghead width (+ 1 (ifix base)))
                                           (+ -1 size)))))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm offset-range-wrap-of-logext
  (equal (offset-range-wrap width (acl2::logext width base) size)
         (offset-range-wrap width base size))
  :hints (("Goal" :use ((:instance offset-range-wrap-of-loghead (base base))
                        (:instance offset-range-wrap-of-loghead (base (acl2::logext width base))))
           :in-theory (disable offset-range-wrap-of-loghead))))

(defthm offset-chop-first-arg-when-constant
  (implies (and (syntaxp (and (quotep offset) (quotep width)))
                (< 0 width) ;helps prevent loops
                (not (acl2::signed-byte-p width offset))
                (integerp offset)
                (integerp size))
           (equal (offset-range-wrap width offset size)
                  (offset-range-wrap width (acl2::logext width offset) size))))


;; (thm
;;  (implies (and (<= (loghead width offset2) (loghead width offset1))
;;                (<= (loghead width offset1) (loghead width (+ offset2 size2)))
;;                (integerp offset1)
;;                (integerp offset2)
;;                (integerp size1)
;;                (integerp size2))
;;           (not (bag::disjoint (offset-range-wrap width offset1 size1)
;;                               (offset-range-wrap width offset2 size2))))
;;  )


(defthm use-disjoint-of-offset-range-wraps-hack-better
  (implies (and (bag::disjoint (offset-range-wrap width offset1 size1)
                               bag)
                (list::memberp offset3 (offset-range-wrap width offset1 size1))
                (list::memberp offset4 bag))
           (not (equal offset3 offset4))))

;; [Jared] dumb speed hacking
(local (in-theory (disable use-disjoint-of-offset-range-wraps-hack-better)))

(defthm use-disjoint-of-offset-range-wraps-hack-better-alt
  (implies (and (bag::disjoint bag
                               (offset-range-wrap width offset1 size1))
                (list::memberp offset3 (offset-range-wrap width offset1 size1))
                (list::memberp offset4 bag))
           (not (equal offset3 offset4))))

(defthm use-disjoint-of-offset-range-wraps-hack-better-2
  (implies (and (bag::disjoint (offset-range-wrap width offset1 size1)
                               bag)
                (list::memberp offset4 (offset-range-wrap width offset1 size1))
                (list::memberp offset3 bag))
           (not (equal offset4 offset3))))

(defthm use-disjoint-of-offset-range-wraps-hack-better-alt-2
  (implies (and (bag::disjoint bag
                               (offset-range-wrap width offset1 size1))
                (list::memberp offset4 (offset-range-wrap width offset1 size1))
                (list::memberp offset3 bag))
           (not (equal offset4 offset3))))


(defthm cdr-of-offset-range-wrap
  (equal (cdr (offset-range-wrap width base size))
         (if (zp size)
             nil
           (offset-range-wrap width (+ 1 (ifix base)) (+ -1 size))))
  :hints (("Goal" :expand (OFFSET-RANGE-WRAP width BASE SIZE)
           :in-theory (enable offset-range-wrap))))


(defun offset-range-wrap-induct-with-x (width base size x)
  (if (zp size)
      x
      (cons (loghead width base)
            (offset-range-wrap-induct-with-x width (loghead width (+ 1 (ifix base))) (+ -1 size) x))))


(encapsulate
 ()


 ;;  (local (defthm memberp-of-offset-range-1
 ;;           (implies (list::memberp x (offset-range-wrap width y size))
 ;; ;                   (<= 0 (loghead width (- x y)))
 ;;                    )
 ;;           :hints (("Goal" :do-not '(generalize eliminate-destructors)
 ;;                    :induct ( OFFSET-RANGE-WRAP-induct-with-x y size x)
 ;;                    :in-theory (e/d (acl2::loghead-sum-split-into-2-cases
 ;;                                     list::memberp-of-cons
 ;;                                     offset-range-wrap)
 ;;                                    (ACL2::LOGHEAD-SUM-CHOP-FIRST-ARG-WHEN-CONSTANT
 ;;                                     ))))))

 (local (defthm memberp-of-offset-range-2
          (implies (and ; (integerp size)
     ;                (< 0 size)
                    (integerp y)
                    (integerp x)
                    )
                   (implies (list::memberp x (offset-range-wrap width y size))
                            (< (loghead (nfix width) (- x y)) size)))
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :induct ( OFFSET-RANGE-WRAP-induct-with-x width y size x)
                   :expand (LIST::MEMBERP X (OFFSET-RANGE-WRAP width Y SIZE))
                   :in-theory (e/d (acl2::loghead-sum-split-into-2-cases
                                    list::memberp-of-cons
                                    offset-range-wrap)
                                   (ACL2::LOGHEAD-SUM-CHOP-FIRST-ARG-WHEN-CONSTANT
                                    ))))))

 (local (defthm memberp-of-offset-range-3
          (implies (and (integerp size)
                        (< 0 size)
                        (integerp y)
                        (integerp x)
                        (< (loghead (nfix width) (- x y)) size)
     ;                        (<= 0 (loghead width (- x y)))
                        (unsigned-byte-p (nfix width) x)
                        (integerp width)
                        (< 0 width) ;bzo
                        )
                   (list::memberp x (offset-range-wrap width y size)))
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :induct ( OFFSET-RANGE-WRAP-induct-with-x width y size x)
                   :expand ((OFFSET-RANGE-WRAP width (+ 1 Y) (+ -1 SIZE)) ;gross?
                            (LIST::MEMBERP X (OFFSET-RANGE-WRAP width Y SIZE)))
                   :in-theory (e/d ( ;acl2::loghead-sum-split-into-2-cases
                                    ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES
                                    list::memberp-of-cons
                                    acl2::LOGHEAD-OF-ONE-LESS-THAN-X
                                    offset-range-wrap)
                                   (ACL2::LOGHEAD-SUM-CHOP-FIRST-ARG-WHEN-CONSTANT
     ;ACL2::UNSIGNED-BYTE-P-OF-X+1
                                    ))))))

 (local (defthm memberp-of-offset-range-4
          (implies (and (integerp size)
                        (< 0 size)
                        (integerp y)
                        (integerp x)
                        (< (loghead (nfix width) (- x y)) size)
     ;                        (<= 0 (loghead width (- x y)))
                        (unsigned-byte-p (nfix width) x)
                        (equal 0 width)
     ;                        (< 0 width) ;bzo
                        )
                   (list::memberp x (offset-range-wrap width y size)))
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :induct ( OFFSET-RANGE-WRAP-induct-with-x width y size x)
                   :expand ((OFFSET-RANGE-WRAP width (+ 1 Y) (+ -1 SIZE)) ;gross?
                            (LIST::MEMBERP X (OFFSET-RANGE-WRAP width Y SIZE)))
                   :in-theory (e/d ( ;acl2::loghead-sum-split-into-2-cases
                                    ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES
                                    list::memberp-of-cons
                                    acl2::LOGHEAD-OF-ONE-LESS-THAN-X
                                    offset-range-wrap)
                                   (ACL2::LOGHEAD-SUM-CHOP-FIRST-ARG-WHEN-CONSTANT
                                    ACL2::UNSIGNED-BYTE-P-FORWARD-TO-EXPT-BOUND
                                    ))))))

     ;bzo gen
     ;this seems to expensive to enable?

 (defthmd memberp-of-offset-range
   (implies (and (integerp width)
                 (<= 0 width) ;bzo
                 )
            (equal (list::memberp x (offset-range-wrap width y size))
                   (if (equal 0 width)
                       (if (and (integerp size)
                                (< 0 size))
                           (equal x 0)
                         nil)

                   (if (integerp y)
                       (and (< (loghead (nfix width) (- x y)) size)
                            (unsigned-byte-p width x)
                            (integerp size))
                     (list::memberp x (offset-range-wrap width 0 size))))))
   :otf-flg t
   :hints (("Goal" :in-theory (e/d (MEMBERP-WHEN-X-IS-AN-INTEGER-LISTP) ( memberp-of-offset-range-3
                                                                          memberp-of-offset-range-2))
            :use ( memberp-of-offset-range-3
                   (:instance  memberp-of-offset-range-2  (width width)))
            )))

)

;; (defthm consp-of-offset-range-wrap
;;   (equal (consp (offset-range-wrap 16 k size))
;;          (and (integerp size)
;;               (< 0 size)))
;;   :hints (("Goal" :in-theory (enable offset-range-wrap))))

(defthm memberp-of-offset-range-sum-self-hack
  (implies (and (integerp k)
                (integerp x)
                (integerp width)
                (<= 0 width)
                )
           (equal (list::memberp x (offset-range-wrap width (+ k x) size))
                  (and (unsigned-byte-p width x)
                       (< (loghead width (- k)) size)
     ;                       (<= 0 (loghead width (- k)))
                       (integerp size))))
  :hints (("Goal" :in-theory (enable memberp-when-x-is-an-integer-listp
                                     memberp-of-offset-range))))



(defthm memberp-of-offset-range-sum-self-hack-other
  (implies (and (integerp k)
                (integerp x)
                (integerp width)
                (<= 0 width)
                )
           (equal (list::memberp (loghead width (+ k x)) (offset-range-wrap width x size))
                  (and (< (loghead width k) size)
     ;                       (<= 0 (loghead width k))
                       (integerp size))))
  :hints (("Goal" :in-theory (enable memberp-when-x-is-an-integer-listp
                                     memberp-of-offset-range))))


(defthm memberp-loghead-offset-range-wrap-simplify-constants
  (implies (and (syntaxp (and (quotep k1) ;i think i want these syntaxp hyps, right?
                              (quotep k2)))
                (integerp x)
                (integerp y)
                (integerp k1)
                (integerp k2)
                (integerp size)
                (integerp width)
                (<= 0 width)
                )
           (equal (list::memberp (loghead width (+ k1 x)) (offset-range-wrap width (+ k2 y) size))
                  (list::memberp (loghead width (+ (- k1 k2) x)) (offset-range-wrap width y size))))
  :hints (("Goal" :in-theory (enable memberp-of-offset-range))))


(in-theory (enable MEMBERP-OF-OFFSET-RANGE))

(local (defthmd helper1
         (IMPLIES (AND (INTEGERP SIZE1)
                       (< 0 SIZE1)
;               (INTEGERP SIZE2)
;                (<= 0 SIZE2)
                       (INTEGERP BASE1)
                       (INTEGERP BASE2)
                       (integerp width)
                       (<= 0 width)

                       (BAG::SUBBAGP (OFFSET-RANGE-WRAP width BASE1 SIZE1)
                                     (OFFSET-RANGE-WRAP width BASE2 SIZE2)))
                  (< (LOGHEAD width (+ BASE1 (- BASE2)))
                     SIZE2))
         :hints (("Goal" :do-not '(generalize eliminate-destructors)
                  :induct (OFFSET-RANGE-WRAP width BASE1 SIZE1)
                  :in-theory (enable OFFSET-RANGE-WRAP)))))


;; This is basically a version of sblkp that handles wrapping.
;rename wrapped-range?
;generalize the width?
;bzo could weaken the guard...
(defund offset-rangep (width range)
  (declare (xargs :guard (integer-listp range)))
  (if (endp range)
      t
    (if (endp (cdr range))
        (unsigned-byte-p width (car range)) ;bzo use (integerp (car range)) ?
      (and (equal (car range) (loghead (nfix width) (+ -1 (cadr range))))
           (offset-rangep width (cdr range))))))


;bzo - disable for general use
(defthm integerp-of-car-of-offset-rangep
  (implies (offset-rangep width range)
           (equal (integerp (car range))
                  (< 0 (len range))))
  :hints (("Goal" :in-theory (enable offset-rangep))))


(local (defthmd helper2
         (implies (and (integerp size1)
                       (< 0 size1)
                       (integerp size2)
                       (<= 0 size2)
                       ;; (<= size2 65536)
                       (unsigned-byte-p width size2)

                       (integerp base1)
                       (integerp base2)
                       (bag::subbagp (offset-range-wrap width base1 size1)
                                     (offset-range-wrap width base2 size2))

                       (integerp width)
                       (<= 0 width)
                       )
                  (<= (+ size1 (loghead width (+ base1 (- base2)))) size2))
         :hints (("Goal" :do-not '(generalize eliminate-destructors)
;:induct (OFFSET-RANGE-WRAP '16 BASE1 SIZE1)
                  :in-theory (enable
                              ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES
                              ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT
                              OFFSET-RANGE-WRAP)))))


;bzo should offset-rangep chop its size parameter down to 16 bits?

(defthm offset-rangep-of-cdr
  (implies (offset-rangep width y)
           (offset-rangep width (cdr y)))
  :hints (("Goal" :in-theory (enable offset-rangep))))

;hung on cadr
;disable?
(defthm cadr-when-offset-rangep
  (implies (offset-rangep width x)
           (equal (cadr x)
                  (if (not (and (consp x) (consp (cdr x))))
                      nil
                    (loghead width (+ 1 (car x))))))
  :hints (("Goal" :in-theory (enable OFFSET-RANGEP))))

;move to bags?
(defthm subbagp-cdr-when-memberp-car
  (implies (and (list::memberp (car x) y)
                (not (list::memberp (car x) (cdr x)))
                )
           (equal (bag::subbagp (cdr x) y)
                  (bag::subbagp x y)
                  )))


(local (in-theory (disable len)))
(local (in-theory (enable list::len-of-cdr-better)))

(defthm offset-rangep-when-x-is-not-a-consp
  (implies (not (consp x))
           (offset-rangep width x))
  :hints (("Goal" :in-theory (enable offset-rangep))))

;; (thm
;;  (equal (OFFSET-RANGEP WIDTH (CONS X1 X2))
;;         (and (unsigned-byte-p 16 x1)
;;               (EQUAL x2 (LOGHEAD 16 (+ -1 (CAR x2))))
;;              (OFFSET-RANGEP WIDTH X2)))
;;  :hints (("Goal" :in-theory (enable OFFSET-RANGEP))))

(defthm offset-rangep-when-car-isnt-a-usb
  (implies (not (unsigned-byte-p width (car x)))
           (equal (offset-rangep width x)
                  (not (consp x))))
  :hints (("Goal" :in-theory (enable offset-rangep))))


(local (defthm helper-lemm
         (implies (and (consp x)
                       (offset-rangep width x)
                       )
                  (acl2-numberp (car x)))
         :hints (("Goal" :in-theory (enable offset-rangep)))))

(encapsulate
 ()
 (local (defthm yuck
          (IMPLIES (AND (CONSP X)
                        (CONSP (CDR X))
                        (NOT (UNSIGNED-BYTE-P width (CAR X)))
                        (EQUAL (CAR X)
                               (LOGHEAD width (+ -1 (CADR X))))
                        (OFFSET-RANGEP WIDTH (CDR X))
                        (LIST::MEMBERP A X))
                   (UNSIGNED-BYTE-P width A))))

 (local (defthm fw1
          (implies (and (offset-rangep width x)
                        (list::memberp a x))
                   (unsigned-byte-p width a))
          :rule-classes (:rewrite :forward-chaining)
          :hints (("Goal" :induct t
;                   :do-not '(generalize eliminate-destructors)
                   :in-theory (e/d ( ;ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES
                                    offset-rangep)
                                   (ACL2::LOGHEAD-IDENTITY-2))))))

 (local (defthm fw2
          (implies (offset-rangep width x)
                   (implies (list::memberp a x)
                            (< (loghead width (- a (car x))) (len x))))
          :otf-flg t
          :hints (("Goal" :induct t
                   :do-not-induct t
;                   :expand (OFFSET-RANGEP WIDTH X)
                   :do-not '(generalize eliminate-destructors)
                   :in-theory (enable ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES
                                      helper-lemm
                                      (:induction offset-rangep))))))

 (local (defthm bk
          (implies (and (offset-rangep width x)
;(unsigned-byte-p width (len x))
                        (<= 0 width)
                        (integerp width)
                        )
                   (implies (and (unsigned-byte-p width a)
                                 (< (loghead width (- a (car x))) (len x)))
                            (list::memberp a x)))
          :hints (("subgoal *1/3" :cases ((and (equal a (car x)) (integerp (CADR X)))
                                          (and (not (equal a (car x))) (integerp (CADR X)))
                                          (and (equal a (car x)) (not (integerp (CADR X))))
                                          ))
                  ("Goal" :induct t
                   :do-not '(generalize eliminate-destructors)
                   :expand ((LIST::MEMBERP 0 X)
                            (LIST::MEMBERP 65535 X))
                   :in-theory (e/d (ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES
                                    offset-rangep
                                    (:induction offset-rangep))
                                   (ACL2::LOGHEAD-IDENTITY-2
                                    ACL2::LOGHEAD-EQUAL-REWRITE-CONSTANT-CASE
;acl2::loghead-of-1
                                    ))))))

;could be quite expensive?

 (defthmd memberp-when-offset-rangep
   (implies (and (offset-rangep width x)
                 (<= 0 width)
                 (integerp width)
                 )
            (equal (list::memberp a x)
                   (and (unsigned-byte-p width a)
                        (< (loghead width (- a (car x))) (len x)))))
   :hints (("Goal" :use (bk fw1 fw2)
            :in-theory (disable bk fw1 fw2)))))

(defthm offset-range-hack
  (implies (offset-rangep width x)
           (equal (unsigned-byte-p width (car x))
                  (consp x)))
  :hints (("Goal" :in-theory (enable offset-rangep))))

(defthm offset-range-hack2
  (implies (and (offset-rangep width x)
                (consp x))
           (unsigned-byte-p width (car x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable offset-rangep))))



(local
 (encapsulate
  ()
  (local (defun induct4 (x y)
           (if (or (endp x) (endp y))
               (list x y)
             (induct4 (cdr x) (cdr y)))))

  ;; [Jared] dumb speed hacking
  (local (in-theory (disable ACL2::EXPT-TYPE-PRESCRIPTION-INTEGERP
                             ACL2::EXPT-2-POSITIVE-RATIONAL-TYPE
                             ACL2::EXPT-TYPE-PRESCRIPTION-NONZERO
                             ACL2::EXPT-TYPE-PRESCRIPTION-RATIONALP
                             ACL2::EXPT-TYPE-PRESCRIPTION-POSITIVE
                             ACL2::|x < y  =>  0 < y-x|
                             (:t expt)
                             (:t loghead)
                             (:TYPE-PRESCRIPTION ACL2::LOGHEAD-TYPE)
                             ACL2::LOGHEAD-COMPARE-HACK
                             ACL2::LOGHEAD-UPPER-BOUND
                             ACL2::LOGHEAD-NONNEGATIVE-LINEAR)))

  (defthmd hard-way
    (implies (and (offset-rangep width x)
                  (offset-rangep width y)
                  (< (loghead width (- (car x) (car y))) (loghead width (len y)))
                  (<= (+ (len x) (loghead width (- (car x) (car y)))) (loghead width (len y)))
                  (integerp width)
                  (<= 0 width)
                  )
             (bag::subbagp x y))
    :hints (("subgoal *1/2" :use ((:instance subbagp-cdr-when-memberp-car)
                                  (:instance bag::SUBBAGP-FROM-SUBBAGP-OF-CDR-CHEAP (bag::y y) (bag::x (cdr x))))
             :expand ( ;(OFFSET-RANGEP 16 Y)
;(OFFSET-RANGEP 16 X)
;(OFFSET-RANGEP width Y)
;(OFFSET-RANGEP width X)
                      )
             :in-theory (e/d (ACL2::LOGHEAD-OF-ONE-LESS-THAN-X
                              ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES
                              memberp-when-offset-rangep)
                             (bag::SUBBAGP-FROM-SUBBAGP-OF-CDR-CHEAP
                              LIST::FIX-EQUIV ;bzo

                              subbagp-cdr-when-memberp-car)))
            ("Goal" :do-not '(generalize eliminate-destructors)
             :induct (induct4 x y)
             )
            ))))

;; (thm
;;  (implies (and (offset-rangep width x)
;;                (offset-rangep width y)
;;                )
;;           (equal (bag::subbagp x y)
;;                  (if (consp x)
;;                      (and (consp y)
;;                           (< (loghead width (- (car x) (car y))) (loghead width (len y)))
;;                           (<= (+ (len x) (loghead width (- (car x) (car y)))) (loghead width (len y)))
;;                           )
;;                    t))))


(defthm offset-rangep-of-offset-range-wrap
  (implies (and (integerp width)
                (<= 0 width))
           (offset-rangep width (offset-range-wrap width base size)))
  :hints (("Goal" :in-theory (enable offset-rangep offset-range-wrap))))

(defthm len-of-offset-range-wrap
  (implies (and (integerp width)
                (<= 0 width))
           (equal (len (offset-range-wrap width base size))
                  (nfix size)))
  :hints (("Goal" :induct t
           :expand (OFFSET-RANGE-WRAP WIDTH 0 SIZE)
           :in-theory (enable offset-range-wrap))))

(local (defthmd helper3
         (IMPLIES (AND (<= (+ SIZE1 (LOGHEAD width (+ BASE1 (- BASE2))))
                           (loghead width SIZE2))
                       (< (LOGHEAD width (+ BASE1 (- BASE2))) (loghead width SIZE2))
                       (<= 0 SIZE2)
                       (INTEGERP BASE1)
                       (INTEGERP BASE2)
                       (integerp width)
                       (<= 0 width) )
                  (BAG::SUBBAGP (OFFSET-RANGE-WRAP width BASE1 SIZE1)
                                (OFFSET-RANGE-WRAP width BASE2 SIZE2)))
         :hints (("Goal" :in-theory (e/d (zp) ( hard-way))
                  :use (:instance hard-way (x  (OFFSET-RANGE-WRAP width BASE1 SIZE1)) (y (OFFSET-RANGE-WRAP width BASE2 SIZE2)))))))


(defthm large-OFFSET-RANGE-WRAP-contains-all
  (IMPLIES (AND (<= (expt 2 width) SIZE) ;note this
                (INTEGERP SIZE)
                (integerp width)
                (<= 0 width)
                )
           (equal (MEMBERP val (OFFSET-RANGE-WRAP WIDTH BASE SIZE))
                  (unsigned-byte-p width val)))
  :hints (("Goal" :in-theory (enable MEMBERP-OF-OFFSET-RANGE))))

(defthm count-when-OFFSET-RANGE-WRAP-just-misses
  (IMPLIES (AND (<= SIZE (expt 2 width))
                (INTEGERP BASE)
                (INTEGERP WIDTH)
                (<= 0 WIDTH))
           (equal (BAG::COUNT (LOGHEAD WIDTH BASE)
                              (OFFSET-RANGE-WRAP WIDTH (+ 1 BASE)
                                                 (+ -1 SIZE)))
                  0)))

(defthm subbagp-when-contains-all
  (IMPLIES (AND (NOT (UNSIGNED-BYTE-P WIDTH SIZE2))
                (<= SIZE1 (expt 2 width)) ;(UNSIGNED-BYTE-P WIDTH SIZE1)
;                (INTEGERP SIZE1)
;                (<= 0 SIZE1)
                (integerp size2)
                (<= 0 size2)
                (INTEGERP BASE1)
                (INTEGERP BASE2)
                (integerp width)
                (<= 0 width)
                )
           (SUBBAGP (OFFSET-RANGE-WRAP WIDTH BASE1 SIZE1)
                    (OFFSET-RANGE-WRAP WIDTH BASE2 SIZE2)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct t
           :do-not-induct t
           :in-theory (enable OFFSET-RANGE-WRAP))))


(encapsulate
 ()

 ;;we sort of prove this half by appealing to offset-rangep.
 (local (defthm subbagp-of-two-offset-range-wraps-helper
          (implies (and (integerp size2)
                        (<= 0 size2)
                        (integerp base1)
                        (integerp base2)
                        (unsigned-byte-p width size2) ;drop?
                        (<= size1 (expt 2 width))
                        (integerp width)
                        (<= 0 width)
                        )
                   (equal (bag::subbagp (offset-range-wrap width base1 size1)
                                        (offset-range-wrap width base2 size2))
                          (or ; (not (unsigned-byte-p width size2))
                           (<= size1 0)
                           (not (integerp size1))
                           (and (< (loghead width (- base1 base2)) size2)
                                (<= (+ size1 (loghead width (+ base1 (- base2))))
                                    size2)))))
          :otf-flg t
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :use ((:instance helper2)
                         (:instance helper3)
                         (:instance helper1))
                   :in-theory (disable helper2
                                       helper3
                                       hard-way
                                       helper1
                                       )))))

 (defthm subbagp-of-two-offset-range-wraps
   (implies (and (<= size1 (expt 2 width)) ;may be hard to relieve?
                 (integerp size2)
                 (<= 0 size2)
                 (integerp base1)
                 (integerp base2)
                 (integerp width)
                 (<= 0 width)
                 )
            (equal (bag::subbagp (offset-range-wrap width base1 size1)
                                 (offset-range-wrap width base2 size2))
                   (if (not (unsigned-byte-p width size2))
                       t
                     (or (<= size1 0)
                         (not (integerp size1))
                         (and (< (loghead width (- base1 base2)) size2)
                              (<= (+ size1 (loghead width (+ base1 (- base2))))
                                  size2))))))
   :hints (("Goal" :in-theory (disable  subbagp-of-two-offset-range-wraps-helper)
            :use (:instance  subbagp-of-two-offset-range-wraps-helper)))
   :otf-flg t
   ))

(defthm disjoint-of-two-offset-ranges
  (implies (and (BAG::DISJOINT (OFFSET-RANGE-WRAP width base3 size3)
                               (OFFSET-RANGE-WRAP width base4 size4))
                (< (loghead width (- base1 base3)) size3)
                (<= (+ size1 (loghead width (+ base1 (- base3))))
                    size3)
                (< (loghead width (- base2 base4)) size4)
                (<= (+ size2 (loghead width (+ base2 (- base4))))
                    size4)

;             (integerp size3)
;            (<= 0 size3)
                (case-split (integerp base1))
                (case-split (integerp base3))
                (unsigned-byte-p width size3)

;             (integerp size4)
;            (<= 0 size4)
                (case-split (integerp base2))
                (case-split (integerp base4))
                (unsigned-byte-p width size4)
                (integerp width)
                (<= 0 width)

                )
           (BAG::DISJOINT (OFFSET-RANGE-WRAP width base1 size1)
                          (OFFSET-RANGE-WRAP width base2 size2))
           )
  :hints (("Goal" :in-theory (enable BAG::SUBBAGP-DISJOINT))))


(defthm offset-range-wrap-of-sum-of-loghead
  (implies (integerp y)
           (equal (offset-range-wrap width (+ x (loghead width y)) size)
                  (offset-range-wrap width (+ x y) size)))
  :hints (("Goal" :in-theory (disable offset-range-wrap-of-loghead)
           :use ((:instance offset-range-wrap-of-loghead (base (+ x y)))
                 (:instance offset-range-wrap-of-loghead (base (+ x (loghead width y))))))))

(include-book "../util/syntaxp")


(defthm offset-range-wrap-subst-in-sum-offset
  (implies (and (equal (loghead width off2) off3)
                (syntaxp (acl2::smaller-term off3 off2))
                (integerp off2)
                (integerp off1)
                )
           (equal (offset-range-wrap width (+ off1 off2) size)
                  (offset-range-wrap width (+ off1 off3) size))))

(defthm offset-range-wrap-subst-in-sum-offset-2
  (implies (and (equal (loghead width off2) (loghead width off3))
                (syntaxp (acl2::smaller-term off3 off2))
                (integerp off2)
                (integerp off1)
                )
           (equal (offset-range-wrap width (+ off1 off2) size)
                  (if (integerp off3)

                      (offset-range-wrap width (+ off1 off3) size)
                    (offset-range-wrap width off1 size)
                    )))
  :hints (("Goal" :use ((:instance offset-range-wrap-of-sum-of-loghead (x off1) (y off2))
                        (:instance offset-range-wrap-of-sum-of-loghead (x off1) (y off3)))
           :in-theory (disable offset-range-wrap-of-sum-of-loghead
                               offset-range-wrap-subst-in-sum-offset
                               ))))

(defthm offset-range-wrap-subst
  (implies (and (equal (loghead width off1) (loghead width off2))
                (syntaxp (acl2::smaller-term off2 off1))
                )
           (equal (offset-range-wrap width off1 size)
                  (offset-range-wrap width off2 size)))
  :hints (("Goal" :use ((:instance offset-range-wrap-of-loghead (base off2))
                        (:instance offset-range-wrap-of-loghead (base off1))
                        )
           :in-theory (disable offset-range-wrap-of-loghead
                               ))))




(local (defun induct4 (x y)
         (if (or (endp x) (endp y))
             (list x y)
           (induct4 (cdr x) (cdr y)))))


;; (thm
;;  (IMPLIES (AND (OFFSET-RANGEP WIDTH X)
;;               (EQUAL (LEN X) (LEN Y))
;;               (OFFSET-RANGEP WIDTH Y)
;;               (CONSP X)
;;               (EQUAL (CAR X) (CAR Y)))
;;          (LIST::EQUIV X Y))
;;  :hints (("Goal" :induct (induct4 x y)
;;           :in-theory (enable OFFSET-RANGEP))))

;; (thm
;;  (implies (offset-rangep width x)
;;           (equal (list::equiv x y)
;;                  (and (equal (len x) (len y))
;;                       (offset-rangep width y)
;;                       (or (equal 0 (len x))
;;                           (equal (car x)
;;                                  (car y))))))
;;  :otf-flg t
;;  :hints (("Goal" :induct (induct4 x y)
;;           :in-theory (enable OFFSET-RANGEP))))


(defthmd equiv-of-two-offset-ranges
  (implies (and (offset-rangep width x)
                (offset-rangep width y))
           (equal (list::equiv x y)
                  (and (equal (len x) (len y))
                       (or (equal 0 (len x))
                           (equal (car x)
                                  (car y))))))
  :hints (("Goal" :induct (induct4 x y)
           :in-theory (enable OFFSET-RANGEP))))

;BZO change offset-rangep to enfore true-listp as well?
(defthm equiv-of-two-offset-ranges-true-list-case
  (implies (and (offset-rangep width x)
                (offset-rangep width y)
                (true-listp x)
                (true-listp y)
                )
           (equal (equal x y)
                  (and (equal (len x) (len y))
                       (or (equal 0 (len x))
                           (equal (car x)
                                  (car y))))))
  :hints (("Goal" :use (:instance  equiv-of-two-offset-ranges))))

(defthm equal-of-two-offset-range-wraps
  (implies (and (integerp width)
                (<= 0 width))
           (equal (equal (offset-range-wrap width base1 size1)
                         (offset-range-wrap width base2 size2))
                  (and (equal (nfix size1) (nfix size2))
                       (or (equal 0 (nfix size1))
                           (equal (loghead width base1)
                                  (loghead width base2))))))
  :hints (("Goal"
           :use (:instance EQUIV-OF-TWO-OFFSET-RANGES-TRUE-LIST-CASE
                           (x  (offset-range-wrap width base1 size1))
                           (y  (offset-range-wrap width base2 size2))))))

(defun get-enabled-structure (pspv)
  (strip-cdrs
   (cdr
    (access enabled-structure
            (access rewrite-constant
                    (access prove-spec-var pspv :rewrite-constant)
                    :current-enabled-structure)
            :theory-array))))

(defun turn-on-expensive-rules (stable-under-simplificationp pspv)
  (if stable-under-simplificationp
      `(:in-theory (union-theories ',(get-enabled-structure pspv)
                                   '((:rewrite ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES)
                                     (:rewrite acl2::loghead-of-minus)
                                     )))
    nil))



(encapsulate
 ()

 (local (in-theory (disable ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT)))

 (local (defthm bk
          (implies (and (integerp size1)
                        (integerp size2)
                        (integerp base1)
                        (integerp base2)
                        (integerp width)
                        (< 0 width)
                        (<= size1 (loghead width (- base2 base1)))
                        (<= size2 (loghead width (- base1 base2)))
                        )
                   (bag::disjoint (offset-range-wrap width base1 size1)
                                  (offset-range-wrap width base2 size2)))
          :hints ((turn-on-expensive-rules acl2::stable-under-simplificationp acl2::pspv)
                  ("Goal" :do-not '(generalize eliminate-destructors)
                   :in-theory (e/d (offset-range-wrap
                                    ;;ACL2::LOGHEAD-OF-ONE-MORE-THAN-X
                                    )
                                   ( ;MEMBERP-OF-OFFSET-RANGE
                                    ACL2::LOGHEAD-IDENTITY-2 ;think about this...
                                    SUBBAGP-OF-TWO-OFFSET-RANGE-WRAPS))))))

 (local (defthm fw
          (implies (and (integerp size1)
                        (integerp size2)
                        (integerp base1)
                        (integerp base2)
                        (integerp width)
                        (< 0 width)
                        (< 0 size1)
                        (< 0 size2)
                        (bag::disjoint (offset-range-wrap width base1 size1)
                                       (offset-range-wrap width base2 size2))
                        )
                   (not (< (loghead width (- base2 base1)) size1)))
          :hints ((turn-on-expensive-rules acl2::stable-under-simplificationp acl2::pspv)
                  ("Goal" :do-not '(generalize eliminate-destructors)
                   :induct t
                   :in-theory (e/d (offset-range-wrap
                                    )
                                   (LIST::MEMBERP-OF-CONS
                                                                        ACL2::LOGHEAD-IDENTITY-2 ;think about this...
                                    USE-DISJOINT-OF-OFFSET-RANGE-WRAPS-HACK-BETTER-2
                                    USE-DISJOINT-OF-OFFSET-RANGE-WRAPS-HACK-BETTER-alt
                                    USE-DISJOINT-OF-OFFSET-RANGE-WRAPS-HACK-BETTER-alt-2
                                    ACL2::UNSIGNED-BYTE-P-OF-ONE-LESS-THAN-X
                                    ACL2::LOGHEAD-OF-MINUS))))))

;At some point later in our books we probably disable this..
 (defthm disjoint-of-two-offset-range-wraps
   (implies (and (integerp width)
                 (< 0 width))
            (equal (bag::disjoint (offset-range-wrap width base1 size1)
                                  (offset-range-wrap width base2 size2))
                   (or (not (integerp size1))
                       (not (integerp size2))
                       (<= size1 0)
                       (<= size2 0)

                       (and (<= size1 (loghead width (- (ifix base2) (ifix base1))))
                            (<= size2 (loghead width (- (ifix base1) (ifix base2))))))))
   :hints (("Goal" :use ((:instance bk (base1 (ifix base1)) (base2 (ifix base2)))
                         (:instance fw (base1 (ifix base1)) (base2 (ifix base2)))
                         (:instance fw (size1 size2) (size2 size1) (base1 (ifix base2)) (base2 (ifix base1))))
            :in-theory (disable fw bk )))))

(defthm disjoint-of-offset-range-wraps-shift
  (implies (and (integerp i)
                (integerp j)
                (integerp k)
                (integerp width)
                (< 0 width))
           (equal (bag::disjoint (offset-range-wrap width (+ j i) size)
                                 (offset-range-wrap width (+ k i) size))
                  (or (bag::disjoint (offset-range-wrap width j size)
                                     (offset-range-wrap width k size))
                      (not (integerp size))
                      (<= size 0))))
  :hints (("Goal" :in-theory (enable disjoint-of-two-offset-range-wraps))))

;bzo gen
(defthm offset-range-wrap-of-logext-special
  (equal (gacc::offset-range-wrap 31 (logext 32 x) 2)
         (gacc::offset-range-wrap 31 x 2)))

(defthm unique-of-offset-range-wrap
  (implies (and (<= numwords (expt 2 width))
                (natp width))
           (bag::unique (offset-range-wrap width offset numwords)))
  :hints (("Goal" :expand (OFFSET-RANGE-WRAP width 0 NUMWORDS)
           :in-theory (enable offset-range-wrap
                              memberp-of-offset-range))))


(defun sub1-sub1-induct (m n)
  (if (zp n)
      (list m n)
    (sub1-sub1-induct (+ -1 m) (+ -1 n))))

;bzo gen and move
(defthm nth-of-repeat
  (implies (and (natp n)
                (natp num)
                (< n num))
           (equal (nth n (repeat num item))
                  item))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (sub1-sub1-induct num n)
           :in-theory (enable REPEAT))))


(encapsulate
 ()
 (local (defun my-induct (numbytes offset n width)
          (if (zp n)
              (list numbytes offset n)
            (my-induct (+ -1 numbytes) (loghead width (+ 1 (ifix offset))) (+ -1 n) width))))

 (defthm nth-of-offset-range-wrap
   (implies (natp width)
            (equal (nth n (offset-range-wrap width base size))
                   (if (< (nfix n) (nfix size))
                       (loghead width (+ (ifix base) (nfix n)))
                     nil)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :induct (my-induct size base n width)
            :in-theory (enable offset-range-wrap nth
                               ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES)))))

(defthm memberp-of-offset-range-wrap-same
  (implies (natp width)
           (equal (list::memberp (loghead width offset) (offset-range-wrap width offset numwords))
                  (not (zp numwords)))))

(defthm not-memberp-of-one-smaller-offset-range
  (implies (and (not (list::memberp x (offset-range-wrap width offset2 numwords)))
                (integerp offset2)
                )
           (not (list::memberp x (offset-range-wrap width (+ 1 offset2) (+ -1 numwords)))))
  :hints (("Goal" :expand (offset-range-wrap width offset2 numwords)
           :in-theory (disable ACL2::LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT ;bzo
                               ))))


(defthm offset-range-wrap-sum-integer-and-non-integer
  (implies (and (integerp n)
                (not (integerp c)))
           (equal (offset-range-wrap width (+ c n) size)
                  (if (acl2-numberp c)
                      (offset-range-wrap width 0 size)
                    (offset-range-wrap width n size)))))

(defthm offset-range-wrap-of-sum-loghead
  (implies (and (integerp base)
                (integerp n)
                (integerp m)
                (<= 0 m)
                (<= m n))
           (equal (gacc::offset-range-wrap m (+ 1 (loghead n base)) size)
                  (gacc::offset-range-wrap m (+ 1 base) size))))

(defthm offset-range-wrap-of-sum-of-loghead-lemma
  (implies (and (integerp a)
                (natp width))
           (equal (offset-range-wrap width (+ 1 (loghead width a) b) size)
                  (offset-range-wrap width (+ 1 a b) size))))

(defthm offset-range-wrap-of-sum-of-loghead-lemma-two
  (implies (and (integerp a)
                (natp width))
           (equal (offset-range-wrap width (+ 1 b (loghead width a)) size)
                  (offset-range-wrap width (+ 1 b a) size))))

(encapsulate
 ()

 (local (defun my-induct (numbytes offset n width)
          (if (zp n)
              (list numbytes offset n)
            (my-induct (+ -1 NUMBYTES) (LOGHEAD width (+ 1 (IFIX OFFSET))) (+ -1 N) width))))

 (defthm nthcdr-of-offset-range-wrap
   (implies (and (natp width)
                 (integerp offset) ;drop?
                 )
            (equal (nthcdr n (offset-range-wrap width offset numbytes))
                   (offset-range-wrap width (+ (ifix offset) (nfix n))
                                      (+ (nfix numbytes) (- (nfix n))))))
   :hints (("Goal" :induct (my-induct numbytes offset n width)
            :do-not '(generalize eliminate-destructors)
            :expand ((OFFSET-RANGE-WRAP width (+ N OFFSET) (+ (- N) NUMBYTES))
                     )
            :in-theory (e/d (offset-range-wrap
                             nthcdr
                             ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES
                             )
                            ((:executable-counterpart force)))))))


;slow proof?
(defthm find-index-of-offset-range-wrap
  (implies (and (< (acl2::loghead 16 (- ad offset)) numwords)
                (natp numwords)
                (integerp ad)
                (integerp offset)
                (acl2::unsigned-byte-p 16 ad)
                )
           (equal (list::find-index ad (gacc::offset-range-wrap 16 offset numwords))
                  (acl2::loghead 16 (- ad offset))))
  :hints (("Goal" :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable gacc::offset-range-wrap
                              ACL2::LOGHEAD-SUM-SPLIT-INTO-2-CASES
                              (:definition list::find-index)))))

(defthmd OFFSET-RANGE-WRAP-opener
  (implies (syntaxp (quotep GACC::SIZE))
           (equal (GACC::OFFSET-RANGE-WRAP GACC::WIDTH GACC::BASE GACC::SIZE)
                  (AND (NOT (ZP GACC::SIZE))
                       (CONS (LOGHEAD GACC::WIDTH GACC::BASE)
                             (GACC::OFFSET-RANGE-WRAP
                              GACC::WIDTH
                              (LOGHEAD GACC::WIDTH (+ 1 (IFIX GACC::BASE)))
                              (+ -1 GACC::SIZE))))))
  :hints (("Goal" :in-theory (enable offset-range-wrap))))
