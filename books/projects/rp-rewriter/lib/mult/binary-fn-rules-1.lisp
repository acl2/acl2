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

;; A rewriting mechanism to simplify binary functions.
;; This method -seems- reliable but it is probably too slow to be used all the
;; time.
;; Also its final format is not friendly for f2-new and m2-new meta functions.

(in-package "RP")

(include-book "mult-defs")

(include-book "binary-fn-defs")

(include-book "misc/untranslate-patterns" :dir :system)

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5))

(rp::def-rw-opener-error
 binary-or-opener-error
 (binary-or x y))

(rp::def-rw-opener-error
 binary-xor-opener-error
 (binary-xor x y))

(rp::def-rw-opener-error
 binary-?-opener-error
 (binary-? test x y))

(rp::def-rw-opener-error
 binary-and-opener-error
 (binary-and x y))

(local
 (in-theory (enable sum2 times)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  nil
  ;; binary-? to binary-and or binary-or

  (defthm rid-of-binary-?
    (implies (and (bitp test)
                  (bitp x)
                  (bitp y))
             (equal (binary-? test x y)
                    (sum2 (times test x)
                          (-- (times test y))
                          y)))
    :hints (("Goal"
             :in-theory (e/d (binary-? binary-and binary-not
                                       binary-or
                                       rp::type-fix) ()))))

  (defthmd rid-of-binary-?-m2
    (implies (and (bitp test)
                  (bitp x)
                  (bitp y))
             (equal (binary-? test x y)
                    (m2 (sum2 (times test x)
                              (times test y)
                              y))))
    :hints (("Goal"
             :in-theory (e/d (binary-? binary-and binary-not
                                       binary-or
                                       rp::type-fix) ()))))

  (defthmd rid-of-binary-?-m2-side-cond
    (implies (and (bitp test)
                  (bitp x)
                  (bitp y))
             (and (bitp (m2 (sum2 (times test x)
                                  (times test y)
                                  y)))
                  (bitp (times test x))
                  (bitp (times test y)))))

  (rp::rp-attach-sc rid-of-binary-?-m2
                    rid-of-binary-?-m2-side-cond)

  (defthmd rid-of-binary-?-side-cond
    (implies (and (bitp test)
                  (bitp x)
                  (bitp y))
             (and (bitp (sum2 (times test x)
                              (-- (times test y))
                              y))
                  (bitp (times test x))
                  (bitp (times test y)))))

  (rp::rp-attach-sc rid-of-binary-?
                    rid-of-binary-?-side-cond)

  (defthm binary-?-to-times
    (implies t
             (equal (binary-? x y 0)
                    (and$ x y)))
    :hints (("Goal"
             :in-theory (e/d (binary-?
                              bit-fix
                              binary-and) ()))))
  #|
  (defthmd binary-?-to-times-side-cond
  (implies (and (bitp x)
  (bitp y))
  (bitp (times x y))))

  (rp::rp-attach-sc binary-?-to-times
  binary-?-to-times-side-cond)||#

  (defthm binary-?-to-binary-or
    (equal (binary-? x 1 y)
           (binary-or x y))
    :hints (("Goal"
             :in-theory (e/d (binary-?
                              binary-or) ())))))

(encapsulate
  nil

  (local
   (in-theory (enable measure-lemmas)))

  (defun binary-fns-lexorder (x y)
    ;; returns (mv order equal-x-y)
    (declare (xargs :guard t
                    :measure (+ (cons-count x) (cons-count y))))
    (let* ((x (rp::ex-from-rp x))
           (y (rp::ex-from-rp y)))
      (cond ((atom x)
             (cond
              ((atom y)
               (if (equal x y)
                   (mv nil t)
                 (mv (or (equal x nil)
                         (and (alphorder x y)
                              (not (equal y nil))))
                     nil)))
              (t
               (b* (((mv order-res &) (binary-fns-lexorder x (car y))))
                 (mv order-res nil)))))
            ((atom y)
             (b* (((mv order-res &) (binary-fns-lexorder (car x) y)))
               (mv order-res nil)))
            ((or (equal (car x) (car y))
                 ;;(rp-equal-cnt2 (car x) (car y) 50)
                 )
             (binary-fns-lexorder (cdr x) (cdr y)))
            (t (b* (((mv order-res equal-x-y)
                     (binary-fns-lexorder (car x) (car y))))
                 (if equal-x-y
                     (binary-fns-lexorder (cdr x) (cdr y))
                   (mv order-res nil)))))))

  (encapsulate
    nil

    (defthmd binary-fnslexorder-sanity-lemma1
      (implies (equal x y)
               (NOT (MV-NTH 0
                            (binary-fns-lexorder x y))))
      :hints (("Goal"
               :induct (binary-fns-lexorder X y)
               :in-theory (e/d () ()))))

    (defthmd binary-fns-sanity-lemma2
      (implies (mv-nth 1 (binary-fns-lexorder x y))
               (not (mv-nth 0 (binary-fns-lexorder x y)))))

    (defthmd finary-fns-sanity-lemma3
      (implies (MV-NTH 1 (binary-fns-lexorder x y))
               (MV-NTH 1 (binary-fns-lexorder y x))))

    (defthmd
      binary-fns-sanity
      (implies (MV-NTH 0 (binary-fns-lexorder X Y))
               (NOT (MV-NTH 0 (binary-fns-lexorder Y X))))
      :otf-flg t
      :hints (("Goal"
               :in-theory (e/d (rp::ex-from-rp
                                finary-fns-sanity-lemma3
                                binary-fns-sanity-lemma2
                                rp::is-rp
                                binary-fnslexorder-sanity-lemma1) ())))))

  (defun mv-nth-0-binary-fns-lexorder (term1 term2)
    (b* (((mv res &) (binary-fns-lexorder term1 term2)))
      res)))

(defthm not-of-not
  (equal (not$ (not$ x))
         (bit-fix x))
  :hints (("Goal"
           :in-theory (e/d (binary-not) ()))))

(encapsulate
  nil

  #|(define ex-from-binary-not (x)
  (if (case-match x (('binary-not &) t) (& nil)) (cadr x) x))||#

  (defun ex-from-rp/binary-not/-- (term)
    (case-match term
      (('-- x)
       (ex-from-rp/binary-not/-- x))
      (('rp & x)
       (ex-from-rp/binary-not/-- x))
      (('binary-not x)
       (ex-from-rp/binary-not/-- x))
      (& term)))

  (defun ex-from-rp/binary-not/--/b+/b-* (term)
    (case-match term
      (('-- x)
       (ex-from-rp/binary-not/--/b+/b-* x))
      (('rp & x)
       (ex-from-rp/binary-not/--/b+/b-* x))
      (('binary-not x)
       (ex-from-rp/binary-not/--/b+/b-* x))
      (('b+2 x &)
       (ex-from-rp/binary-not/--/b+/b-* x))
      (('b-* x &)
       (ex-from-rp/binary-not/--/b+/b-* x))
      (& term)))

  (defun times-order (x y)
    (b* ((x (ex-from-rp/binary-not/-- x))
         (y (ex-from-rp/binary-not/-- y))
         (x-is-sum (and (consp x)
                        (equal (car x) 'b+2)))
         (y-is-sum (and (consp y)
                        (equal (car y) 'b+2))))
      (cond ((or (and (consp x)
                      (equal (car x) 'b-*))
                 (and (consp y)
                      (equal (car y) 'b-*)))
             nil)
            ((or x-is-sum y-is-sum)
             (not x-is-sum))
            (t
             (mv-nth-0-binary-fns-lexorder y x)))))

  (defthmd sanity-times-order
    (implies (times-order x y)
             (not (times-order y x)))
    :hints (("Goal"
             :in-theory (e/d (mv-nth-0-binary-fns-lexorder
                              binary-fns-sanity)
                             (binary-fns-lexorder)))))

  

  (defun sum2-order (x y)
    (b* ((x (ex-from-rp/binary-not/-- x))
         (y (ex-from-rp/binary-not/-- y))
         (x-is-sum (and (consp x)
                        (equal (car x) 'b+2)))
         (y-is-sum (and (consp y)
                        (equal (car y) 'b+2)))
         (x-is-times (and (consp x)
                          (equal (car x) 'b-*)))
         (y-is-times (and (consp y)
                          (equal (car y) 'b-*))))
      (cond ((or x-is-sum
                 y-is-sum)
             nil)
            ((or x-is-times y-is-times)
             (if (and x-is-times y-is-times)
                 (mv-nth-0-binary-fns-lexorder y x)
               (not y-is-times)))
            ((or (quotep x)
                 (integerp x)
                 (quotep y)
                 (integerp y))
             (not (or (quotep x)
                      (integerp x))))
            (t
             (mv-nth-0-binary-fns-lexorder y x)))))

  (defthmd sanity-sum2-order
    (implies (sum2-order x y)
             (not (sum2-order y x)))
    :hints (("Goal"
             :in-theory (e/d (mv-nth-0-binary-fns-lexorder
                              binary-fns-sanity
                              sum2-order)
                             (binary-fns-lexorder))))))

(defthmd times-put-not-back-1
  (implies (and (syntaxp (or (atom b)
                             (not (or (equal (car b) 'b+2)
                                      (equal (car b) 'b-*)
                                      (equal (car b) '--)
                                      (equal (car b) 'binary-not)))))
                (bitp b))
           (equal (times a (sum2 (-- b) 1) x)
                  (times a (not$ b) x)))
  :hints (("Goal"
           :in-theory (e/d (binary-not
                            b-*
                            b+2
                            type-fix) ()))))

(defthmd times-put-not-back-2
  (implies (and (syntaxp (or (atom b)
                             (not (or (equal (car b) 'b+2)
                                      (equal (car b) 'b-*)
                                      (equal (car b) '--)
                                      (equal (car b) 'binary-not)))))
                (bitp b))
           (equal (times a (sum2 (-- b) 1))
                  (times a (not$ b))))
  :hints (("Goal"
           :in-theory (e/d (binary-not
                            b-*
                            b+2
                            type-fix) ()))))

(defthm times-comm-1
  (implies (syntaxp (times-order x y))
           (equal (times y x)
                  (times x y)))
  :hints (("Goal"
           :in-theory (e/d (binary-and) ()))))

(defthm times-comm-2
  (implies (syntaxp (times-order x y))
           (equal (times y x z)
                  (times x y z)))
  :hints (("Goal"
           :in-theory (e/d (rp::type-fix) ()))))

(defthm times-comm-2-2
  (implies (syntaxp (times-order x y))
           (equal (times y x z)
                  (times x y z)))
  :hints (("Goal"
           :in-theory (e/d (rp::type-fix) ()))))

(defthm times-reorder
  (equal (times (times x y) z)
         (times x (times y z)))
  :hints (("Goal"
           :in-theory (e/d (rp::type-fix) ()))))

(encapsulate
  nil

  (defthm binary-or-of-1-1
    (equal (or$ a 1)
           1)
    :hints (("Goal"
             :in-theory (e/d (bitp binary-or) ()))))

  (defthm binary-or-of-1-2
    (equal (or$ 1 a)
           1)
    :hints (("Goal"
             :in-theory (e/d (bitp binary-or) ()))))

  (defthm binary-and-of-1-1
    (equal (and$ 1 a)
           (bit-fix a))
    :hints (("Goal"
             :in-theory (e/d (bitp binary-and) ()))))

  (defthm binary-and-of-1-2
    (equal (and$ a 1)
           (bit-fix a))
    :hints (("Goal"
             :in-theory (e/d (bitp binary-and) ()))))

  (defthm binary-and-of-0-1
    (equal (and$ a 0)
           0)
    :hints (("Goal"
             :in-theory (e/d (bitp binary-and) ()))))

  (defthm binary-and-of-0-2
    (equal (and$ 0 a)
           0)
    :hints (("Goal"
             :in-theory (e/d (bitp binary-and) ()))))

  (defthm binary-or-of-0-1
    (equal (or$ a 0)
           (bit-fix a))
    :hints (("Goal"
             :in-theory (e/d (bitp binary-or) ()))))

  (defthm binary-or-of-0-2
    (equal (or$ 0 a)
           (bit-fix a))
    :hints (("Goal"
             :in-theory (e/d (bitp binary-or) ()))))

  (defthm binary-xor-of-constant
    (and (equal (binary-xor a 0)
                (bit-fix a))
         (equal (binary-xor 0 a)
                (bit-fix a))
         (equal (binary-xor 1 a)
                (not$ a))
         (equal (binary-xor a 1)
                (not$ a))
         (equal (binary-xor a a)
                0))
    :hints (("Goal"
             :in-theory (e/d (binary-xor binary-not) ()))))

  (defthm binary-and-comm-1
    (implies (syntaxp (and (or (atom x)
                               (not (equal (car (rp::ex-from-rp x))
                                           'binary-and)))
                           (rp::mv-nth-0-binary-fns-lexorder x y)))
             (equal (and$ y x)
                    (and$ x y)))
    :hints (("Goal"
             :in-theory (e/d (binary-and) ()))))

  (defthm binary-and-comm-2
    (implies (syntaxp (and (or (atom x)
                               (not (equal (car (rp::ex-from-rp x))
                                           'binary-and)))
                           (rp::mv-nth-0-binary-fns-lexorder x y)))
             (equal (and$ y x z)
                    (and$ x y z)))
    :hints (("Goal"
             :in-theory (e/d (binary-and) ()))))

  (defthm binary-and-reorder
    (implies t
             (equal (and$ (and$ x y) z)
                    (and$ x y z)))
    :hints (("Goal"
             :in-theory (e/d (binary-and) ()))))

  (defthm binary-or-comm-1
    (implies (syntaxp (and (or (atom x)
                               (not (equal (car (rp::ex-from-rp x))
                                           'binary-or)))
                           (rp::mv-nth-0-binary-fns-lexorder x y)))
             (equal (or$ y x)
                    (or$ x y)))
    :hints (("Goal"
             :in-theory (e/d (binary-or) ()))))

  (defthm binary-or-comm-2
    (implies (syntaxp (and (or (atom x)
                               (not (equal (car (rp::ex-from-rp x))
                                           'binary-or)))
                           (rp::mv-nth-0-binary-fns-lexorder x y)))
             (equal (or$ y x z)
                    (or$ x y z)))
    :hints (("Goal"
             :in-theory (e/d (binary-or) ()))))

  (defthm binary-or-reorder
    (implies t
             (equal (or$ (or$ x y) z)
                    (or$ x y z)))
    :hints (("Goal"
             :in-theory (e/d (binary-or) ())))))

(defthm binary-not-of-binary-times
  (implies (and (bitp x)
                (bitp y))
           (equal (not$ (times x y))
                  (sum2 1 (-- (times x y)))))
  :hints (("Goal"
           :in-theory (e/d (binary-or
                            binary-and
                            rp::type-fix
                            binary-not) ()))))

(defthmd binary-not-of-binary-times-side-cond
  (implies (and (bitp x)
                (bitp y))
           (and (bitp (sum2 1 (-- (times x y)))))))

(rp::rp-attach-sc binary-not-of-binary-times
                  binary-not-of-binary-times-side-cond)

(defthm rid-of-binary-xor
  (implies (and (bitp x)
                (bitp y))
           (equal (binary-xor x y)
                  (sum2 y
                        x
                        (-- (times x y))
                        (-- (times x y)))))
  :hints (("Goal"
           :in-theory (e/d (binary-xor
                            binary-and
                            binary-or
                            bitp
                            binary-not) ()))))

(defthmd rid-of-binary-xor-m2
  (implies (and (bitp x)
                (bitp y))
           (equal (binary-xor x y)
                  (m2 (sum2 y
                            x))))
  :hints (("Goal"
           :in-theory (e/d (binary-xor
                            binary-and
                            binary-or
                            bitp
                            binary-not) ()))))

(defthmd rid-of-binary-xor-m2-side-cond
  (implies (and (bitp x)
                (bitp y))
           (bitp (m2 (sum2 y
                           x))))
  :hints (("Goal"
           :in-theory (e/d (binary-xor
                            binary-and
                            binary-or
                            bitp
                            binary-not) ()))))

(defthmd rid-of-binary-xor-side-cond
  (implies (and (bitp x)
                (bitp y))
           (and (bitp  (sum2 y
                             x
                             (-- (times x y))
                             (-- (times x y))))

                (bitp  (times x y))))
  :hints (("Goal"
           :in-theory (e/d (binary-xor
                            binary-and
                            binary-or
                            bitp
                            binary-not) ()))))

(rp::rp-attach-sc rid-of-binary-xor
                  rid-of-binary-xor-side-cond)

(rp::rp-attach-sc rid-of-binary-xor-m2
                  rid-of-binary-xor-m2-side-cond)

(defthm b+-of-binary-not
  (equal (b+2 (binary-not x) y)
         (sum2 1 (-- (bit-fix x)) y))
  :hints (("Goal"
           :in-theory (e/d (binary-not b+2 rp::type-fix) ()))))

(defthm b+-of-binary-not-2
  (equal (b+2 y (binary-not x))
         (sum2 1 (-- (bit-fix x)) y))
  :hints (("Goal"
           :in-theory (e/d (binary-not bitp b+2 rp::type-fix) ()))))

(defthm --of-binary-not
  (implies (bitp x)
           (equal (-- (not$ x))
                  (sum2 x -1)))
  :hints (("Goal"
           :in-theory (e/d (b+2 binary-not
                                rp::type-fix) ()))))

(defthm rid-of-binary-or
  (implies (and (bitp x)
                (bitp y))
           (equal (binary-or x y)
                  (sum2 x y
                        (-- (times x y)))))
  :hints (("Goal"
           :in-theory (e/d (b+2 merge-b+ rp::type-fix
                                binary-or
                                binary-and) ()))))

(defthmd rid-of-binary-or-m2
  (implies (and (bitp x)
                (bitp y))
           (equal (binary-or x y)
                  (m2 (sum2 x y
                            (times x y)))))
  :hints (("Goal"
           :in-theory (e/d (b+2 merge-b+ rp::type-fix
                                binary-or
                                binary-and) ()))))

(defthmd rid-of-binary-or-side-cond
  (implies (and (bitp x)
                (bitp y))
           (and (bitp
                 (sum2 x y
                       (-- (times x y))))
                (bitp
                 (times x y)))))

(defthmd rid-of-binary-or-m2-side-cond
  (implies (and (bitp x)
                (bitp y))
           (and (bitp
                 (m2 (sum2 x y (times x y))))
                (bitp
                 (times x y)))))

(rp::rp-attach-sc rid-of-binary-or
                  rid-of-binary-or-side-cond)

(rp::rp-attach-sc rid-of-binary-or-m2
                  rid-of-binary-or-m2-side-cond)
#|
(defthmd times-var-var-and-sum
  (equal (times a b (sum x y))
         (times a (merge-sum (times b (merge-sum x y)))))
  :hints (("Goal"
           :in-theory (e/d (b+ type-fix) ()))))||#

(defthm b+-of-two-ands-with-same-var
  (equal (sum2 (times a b) (times a c) x)
         (sum2 (times a (sum2 b c)) x))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-2
  (equal (sum2 (times a b) (times a c))
         (sum2 (times a (sum2 b c))))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-3
  (equal (sum2 a (times a c) x)
         (sum2 (times a (sum2 1 c)) x))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-4
  (equal (sum2 a (times a c))
         (sum2 (times a (sum2 1 c))))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-5
  (equal (sum2 (times a c) a  x)
         (sum2 (times a (sum2 1 c)) x))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-6
  (equal (sum2 (times a c) a)
         (sum2 (times a (sum2 1 c))))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-minus
  (equal (sum2 (times a b) (-- (times a c)) x)
         (sum2 (times a (sum2 b (-- c))) x))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-minus-2
  (equal (sum2 (times a b) (-- (times a c)))
         (sum2 (times a (sum2 b (-- c)))))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-minus-3
  (equal (sum2 (-- (times a b)) (times a c) x)
         (sum2 (times a (sum2 (-- b) c)) x))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-minus-4
  (equal (sum2 (-- (times a b)) (times a c))
         (sum2 (times a (sum2 (-- b) c))))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-minus-5
  (equal (sum2 (-- (times a b)) a x)
         (sum2 (times a (sum2 (-- b) 1)) x))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-minus-6
  (equal (sum2 (-- (times a b)) a)
         (sum2 (times a (sum2 (-- b) 1))))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-minus-7
  (equal (sum2 a (-- (times a b)) x)
         (sum2 (times a (sum2 (-- b) 1)) x))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-minus-8
  (equal (sum2 a (-- (times a b)))
         (times a (sum2 (-- b) 1)))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix) ()))))

(defthm b+-of-two-ands-with-same-var-minus-9
  (equal (sum2 (-- (times a b)) (-- (times a c)) d)
         (sum2 (-- (times a (sum2 b c))) d))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 rp::type-fix -- b-*) ()))))

(defthm b+-of-two-ands-with-same-var-minus-10
  (equal (sum2 (-- (times a b)) (-- (times a c)))
         (-- (times a (sum2 b c))))
  :hints (("Goal"
           :in-theory (e/d (binary-and b+2 -- b-* rp::type-fix) ()))))

(DEFTHM |(sum2 (times a b) (-- a) c)|
  (equal (sum2 (times a b) (-- a) c)
         (sum2 (times a (sum2 b -1)) c))
  :hints (("Goal"
           :in-theory (e/d (b+2
                            rp::type-fix
                            --
                            b-*) ()))))

(DEFTHM |(sum2 (times a b) (-- a))|
  (equal (sum2 (times a b) (-- a))
         (times a (sum2 b -1)))
  :hints (("Goal"
           :in-theory (e/d (b+2
                            rp::type-fix
                            --
                            b-*) ()))))

(DEFTHM |(sum2 (-- a) (times a b))|
  (equal (sum2 (-- a) (times a b))
         (times a (sum2 b -1)))
  :hints (("Goal"
           :in-theory (e/d (b+2
                            rp::type-fix
                            --
                            b-*) ()))))

(DEFTHM |(sum2 (-- a) (times a b) c)|
  (equal (sum2 (-- a) (times a b) c)
         (sum2 (times a (sum2 b -1)) c))
  :hints (("Goal"
           :in-theory (e/d (b+2
                            rp::type-fix
                            --
                            b-*) ()))))

(defthm times-of-sums
  (equal (times (sum2 a b)
                (sum2 x y))
         (sum2 (times a (sum2 x y))
               (times b (sum2 x y))))
  :hints (("Goal"
           :in-theory (e/d (rp::type-fix
                            b+2) ()))))

(defthm times-of-sum-of-same-var
  (implies (bitp a)
           (equal (times a (sum2 a b))
                  (times a (sum2 1 b)))))

(defthm times-of-sum-of-same-var-minus
  (implies (bitp a)
           (equal (times a (sum2 (-- a) b))
                  (times a (sum2 -1 b)))))

(defthm times-of-sum-of-same-var-minus-2
  (implies (bitp a)
           (equal (times a (sum2 (-- (times a x)) b))
                  (times a (sum2 (-- x) b))))
  :hints (("Goal"
           :in-theory (e/d (type-fix) ()))))

(defthm times-with-1
  (equal (times 1 a)
         (rp::type-fix a))
  :hints (("Goal"
           :in-theory (e/d (rp::type-fix) ()))))

(defthm times-with-1-bitp
  (implies (bitp a)
           (equal (times 1 a)
                  a))
  :hints (("Goal"
           :in-theory (e/d (rp::type-fix) ()))))

(defthm times-of-same-var
  (implies (bitp a)
           (equal (times a a b)
                  (times a b)))
  :hints (("Goal"
           :in-theory (e/d (rp::type-fix) ()))))

(defthm times-of-same-var-2
  (implies (bitp a)
           (equal (times a a)
                  (times a)))
  :hints (("Goal"
           :in-theory (e/d (rp::type-fix) ()))))

(defthm rid-of-binary-and
  (implies (and (bitp a)
                (bitp b))
           (equal (and$ a b)
                  (times a b))))

(defthmd rid-of-binary-and-side-cond
  (implies (and (bitp a)
                (bitp b))
           (bitp (times a b))))

(rp::rp-attach-sc rid-of-binary-and
                  rid-of-binary-and-side-cond)

(defthm type-fix-of-times
  (equal (times (type-fix x) y)
         (times x y))
  :hints (("Goal"
           :in-theory (e/d (type-fix) ()))))

(defthm type-fix-of-times-2
  (equal (times x (type-fix y))
         (times x y))
  :hints (("Goal"
           :in-theory (e/d (type-fix) ()))))

(defthm times-sum-of-the-same-var
  (implies (bitp b)
           (equal (times b (sum2 b x))
                  (times b (sum2 1 x)))))

(defthm times-sum-of-the-same-var-2
  (implies (bitp b)
           (equal (times b (sum2 (times b y) x))
                  (times b (sum2 y x))))
  :hints (("Goal"
           :in-theory (e/d (b+2 type-fix) ()))))

(defthm times-minus-sum
  (equal (times (-- b) (sum2 x y))
         (times b (sum2 (-- x) (-- y))))
  :hints (("Goal"
           :in-theory (e/d (b-* b+2 -- rp::type-fix) ()))))

(defthm fix-times-hier-1
  (implies (syntaxp (times-order (ex-from-rp/binary-not/--/b+/b-* b)
                                 (ex-from-rp/binary-not/--/b+/b-* a)))
           (equal (times a (sum2 b c))
                  (sum2 (times a b)
                        (times a c))))
  :hints (("Goal"
           :in-theory (e/d (b+2
                            type-fix) ()))))

#|(defthm times--times
  (and (equal (times a (-- (times b c)))
              (-- (times a b c)))
       (equal (times (-- (times b c)) a)
              (-- (times a b c))))
  :hints (("Goal"
           :in-theory (e/d (b-* rp::type-fix) ()))))||#

(defthm times--times-2
  (and (equal (times a (-- b))
              (-- (times a b)))
       (equal (times (-- b) a)
              (-- (times b a))))
  :hints (("Goal"
           :in-theory (e/d (b-* rp::type-fix) ()))))

(defthm times-0
  (equal (times a 0)
         0))

(defthm times-1
  (equal (times a 1)
         (type-fix a))
  :hints (("Goal"
           :in-theory (e/d (type-fix) ()))))

(defthm type-fix-times
  (equal (type-fix (times a b))
         (times a b))
  :hints (("Goal"
           :in-theory (e/d (b-* type-fix) ()))))

(defthm bit-fix-of-bitp
  (implies (bitp x)
           (equal (bit-fix x)
                  x)))

(defthm times-a-not-a-1
  (implies (bitp a)
           (equal (times a (not$ a) b)
                  0))
  :hints (("Goal"
           :in-theory (e/d (b-*) ()))))

(defthm times-a-not-a-2
  (implies (bitp a)
           (equal (times a (not$ a))
                  0))
  :hints (("Goal"
           :in-theory (e/d (b-*) ()))))

(defthm times-a-not-a-3
  (implies (bitp a)
           (equal (times (not$ a) a  b)
                  0))
  :hints (("Goal"
           :in-theory (e/d (b-* bitp) ()))))

(defthm times-a-not-a-4
  (implies (bitp a)
           (equal (times (not$ a) a )
                  0))
  :hints (("Goal"
           :in-theory (e/d (b-* bitp) ()))))

(defthm |(sum2 (times (not$ a) b) (times a c) d)|
  (implies (bitp a)
           (equal (sum2 (times (not$ a) b) (times a c) d)
                  (sum2 (times a (sum2 c (-- b))) b d)))
  :hints (("Goal"
           :in-theory (e/d (b+2 type-fix) ()))))

(defthm |(sum2  (times a c) (times (not$ a) b) d)|
  (implies (bitp a)
           (equal (sum2  (times a c) (times (not$ a) b) d)
                  (sum2 (times a (sum2 c (-- b))) b d)))
  :hints (("Goal"
           :in-theory (e/d (b+2 rp::type-fix
                                bitp b-* --) ()))))

(defthm |(sum2  (times a c) (times (not$ a) b))|
  (implies (bitp a)
           (equal (sum2  (times a c) (times (not$ a) b))
                  (sum2 (times a (sum2 c (-- b))) b)))
  :hints (("Goal"
           :in-theory (e/d (b+2 rp::type-fix
                                bitp b-* --) ()))))

(defthm |(sum2 (times (Not$ a) b) c)|
  (implies (bitp a)
           (equal (sum2 (times (Not$ a) b) c)
                  (sum2 (-- (times a b)) b c)))
  :hints (("Goal"
           :in-theory (e/d (b+2 -- b-*
                                rp::type-fix binary-not
                                bitp) ()))))

(defthm |(-- (times (not$ a) b))|
  (implies (bitp a)
           (equal (-- (times (not$ a) b))
                  (sum2 (times a b)
                        (-- b))))
  :hints (("Goal"
           :in-theory (e/d (b+2
                            b-*
                            --
                            binary-not
                            rp::type-fix
                            bitp) ()))))

(defthm times--1
  (equal (times x -1)
         (-- x))
  :hints (("Goal"
           :in-theory (e/d (-- type-fix b-*) ()))))

#|(defthm rid-of-not-in-times
  (implies (bitp x)
           (and (equal (times (not$ x) y)
                       (merge-sum y (-- (times y x))))
                (equal (times y (not$ x))
                       (merge-sum y (-- (times y x))))))
  :hints (("Goal"
           :in-theory (e/d (bitp b-* type-fix b+ --) ()))))||#

(defthm rid-of-not
  (implies (bitp x)
           (equal (not$ x)
                  (sum2 1 (-- x))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(defthmd rid-of-not-side-cond
  (implies (bitp x)
           (bitp (sum2 1 (-- x))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(rp::rp-attach-sc rid-of-not
                  rid-of-not-side-cond)

(in-theory (disable b-*))

(deftheory rid-of-m2
  '(rid-of-binary-?-m2
    rid-of-binary-xor-m2
    rid-of-binary-or-m2))

(defthm times-1-v2
  (equal (times 1 x)
         (type-fix x)))

(defthm times-of-minus
  (equal (times (minus a) b)
         (-- (times a b)))
  :hints (("Goal"
           :in-theory (e/d (times
                            ifix
                            type-fix
                            minus
                            --) ()))))
(defthm sum2-comm-1
  (implies (syntaxp (sum2-order a b))
           (equal (sum2 b a)
                  (sum2 a b))))

(defthm sum2-comm-2
  (implies (syntaxp (sum2-order a b))
           (equal (sum2 b a c)
                  (sum2 a b c))))

(defthm sum2-reorder
  (implies t
           (equal (sum2 (sum2 a b) c)
                  (sum2 a b c))))

(defthm sum2-of---
  (and (equal (sum2 (-- a) a b)
              (type-fix b))
       (equal (sum2 a (-- a) b)
              (type-fix b))
       (equal (sum2 a (-- a))
              0)
       (equal (sum2 (-- a) a)
              0)
       (equal (sum2 -1 1 b)
              (type-fix b))
       (equal (sum2 1 -1 b)
              (type-fix b))))

(defthm sum2-of-0
  (and (equal (sum2 a 0)
              (type-fix a))
       (equal (sum2 0 a)
              (type-fix a))))

(defthm sum2-and-type-fix
  (and (equal (sum2 (type-fix a) b)
              (sum2 a b))
       (equal (sum2 b (type-fix a))
              (sum2 b a))
       (equal (type-fix (sum2 a b))
              (sum2 a b))))

(defthm sum-is-sum2
  (and (equal (pp-sum a b)
              (sum2 a b))
       (equal (sum a b)
              (sum2 a b))))

(defthm --of-sum2
  (and (equal (-- (sum2 a b))
              (sum2 (-- a) (-- b))))
  :hints (("Goal"
           :in-theory (e/d (-- type-fix sum2) ()))))

(defthm type-fix-of-natp
  (implies (natp x)
           (equal (type-fix x)
                  x))
  :hints (("Goal"
           :in-theory (e/d (type-fix) ()))))

(defun does-times-has-sum2 (term)
  (declare (xargs :measure (cons-count term)
                  :hints (("Goal"
                           :in-theory (e/d (measure-lemmas) ())))))
  (b* ((term (ex-from-rp term)))
    (case-match term
      (('b-* a b)
       (b* ((a (ex-from-rp a)))
         (case-match a
           (('b+2 & &)
            t)
           (& (does-times-has-sum2 b)))))
      (('b+2 & &)
       t)
      (& nil))))

(defthm --of-times
  (implies (syntaxp (does-times-has-sum2 a))
           (and (equal (-- (times a b))
                       (times (-- a) b))
                (equal (-- (times b a))
                       (times b (-- a))))))
