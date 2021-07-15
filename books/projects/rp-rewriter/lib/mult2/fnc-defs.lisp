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

(include-book "ihs/basic-definitions" :dir :system)

(include-book "misc/total-order" :dir :system)

(include-book "projects/rp-rewriter/top" :dir :system)

(include-book "centaur/svl/bits-sbits" :dir :system)

(progn
  (define binary-sum (x y)
    (+ (ifix x)
       (ifix y))
    :returns (res integerp))

  (add-rp-rule integerp-of-binary-sum)

  (defmacro sum (&rest rp::rst)
    (cond ((null rp::rst) 0)
          ((null (cdr rp::rst))
           (list 'ifix (car rp::rst)))
          (t (xxxjoin 'binary-sum rp::rst))))

  (add-macro-fn sum binary-sum t))

(define -- (x)
  (- (ifix x)))

(define sum-list (lst)
  (if (atom lst)
      0
    (sum (car lst)
         (sum-list (cdr lst))))
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-sum-list))

(define s (pp-lst c/d)
  (mod (sum (sum-list pp-lst)
            c/d)
       2)
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-s))

(define c (s-lst pp-lst c/d)
  (floor (sum (sum-list s-lst)
              (sum-list pp-lst)
              c/d)
         2)
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-c))

(define d-sum (s-lst pp-lst c/d)
  (sum (sum-list s-lst)
       (sum-list pp-lst)
       c/d)
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-d-sum))

(define d ((d-sum integerp))
  (floor (sum d-sum (-- (mod (ifix d-sum) 2))) 2)
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-d))

(define s-spec (lst)
  (mod (sum-list lst) 2)
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-s-spec))


(define c-spec (lst)
  (floor (sum-list lst) 2)
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-c-spec))

(define s-c-spec (lst)
  (list (s-spec lst)
        (c-spec lst)))

(define c-s-spec (lst)
  (list (c-spec lst)
        (s-spec lst)))

(define c-res (s-lst pp-lst c/d)
  (sum (sum-list pp-lst)
       (sum-list s-lst)
       c/d)
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-c-res))

#|(define d-new (s pp c/d new)
  (sum (c-new s pp c/d new)
       (-- (mod (+ (sum-list s)
                   (sum-list pp)
                   (sum-list c/d)
                   (sum-list new))
                2)))
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-d-new))||#


(define bit-fix (x)
  (if (bitp x)
      x
    0)
  ///
  (def-rp-rule bit-fix-opener
    (implies (bitp x)
             (equal (bit-fix x) x))))


(define binary-not (bit)
  (- 1 (bit-fix bit))
  ///
  (def-rp-rule natp-bitp-binary-not
    (and (bitp (binary-not x))
         (natp (binary-not x)))
    :hints (("Goal"
             :in-theory (e/d (binary-not bitp) ())))))

(defmacro not$ (term)
  `(binary-not ,term))

(add-macro-fn not$ binary-not t)

(define binary-and (bit1 bit2)
  (if (and (equal (bit-fix bit1) 1)
           (equal (bit-fix bit2) 1))
      1
    0)
  ///
  (def-rp-rule bitp-binary-and
    (and (bitp (binary-and x y))
         (natp (binary-and x y)))))

(defmacro and$ (&rest rp::rst)
  (cond ((null rp::rst) 0)
        ((null (cdr rp::rst))
         (list 'bit-fix (car rp::rst)))
        (t (xxxjoin 'binary-and rp::rst))))

(add-macro-fn and$ binary-and t)

(define and-list (lst)
  (if (atom lst)
      1
    (if (atom (cdr lst))
        (car lst)
      (and$ (car lst)
            (and-list (cdr lst))))))

(define binary-or (bit1 bit2)
  (if (and (equal (bit-fix bit1) 0)
           (equal (bit-fix bit2) 0))
      0
    1)
  ///

  (def-rp-rule bitp-binary-or
    (and (bitp (binary-or x y))
         (natp (binary-or x y)))))

(defmacro or$ (&rest rp::rst)
  (cond ((null rp::rst) 0)
        ((null (cdr rp::rst))
         (list 'bit-fix (car rp::rst)))
        (t (xxxjoin 'binary-or rp::rst))))

(add-macro-fn or$ binary-or t)

(define binary-xor (bit1 bit2)
  (if (equal (bit-fix bit1) (bit-fix bit2))
      0
    1)
  ///
  (def-rp-rule bitp-binary-xor
    (and (bitp (binary-xor x y))
         (natp (binary-xor x y)))))

(define binary-? (test x y)
  (if (equal (bit-fix test) 1)
      (bit-fix x)
    (bit-fix y))
  ///
  (def-rp-rule natp-bitp-binary-?*
    (and (natp (binary-? test x y))
         (bitp (binary-? test x y)))))

(defun binary-cond-macro (clauses)
  (declare (xargs :guard (cond-clausesp clauses)))
  (if (consp clauses)
      (if (and (eq (car (car clauses)) t)
               (eq (cdr clauses) nil))
          (if (cdr (car clauses))
              (car (cdr (car clauses)))
            (car (car clauses)))
        (if (cdr (car clauses))
            (list 'binary-?
                  (car (car clauses))
                  (car (cdr (car clauses)))
                  (binary-cond-macro (cdr clauses)))
          (list 'or$
                (car (car clauses))
                (binary-cond-macro (cdr clauses)))))
    nil))

(defmacro binary-cond (&rest acl2::clauses)
  (declare (xargs :guard (cond-clausesp acl2::clauses)))
  (binary-cond-macro acl2::clauses))


(define sort-sum (x)
  ;; trigger function to be used by a meta to sort and convert (sum d b a c)
  ;; (sum-list (list a b c d))
  (ifix x))

(define s-of-c-trig (x)
  x
  ///
  (add-rp-rule s-of-c-trig))

(define evenpi (term)
  (evenp (ifix term)))


(define small-alphorder ((x)
                         (y))
  (cond ((symbolp x)
         (cond ((symbolp y)
                (symbol< x y))
               (t nil)))
        ((integerp x)
         (cond ((integerp y)
                (< x y))
               (t (symbolp y))))
        (t
         nil))
  ///

  (defthm small-alphorder-sanity
    (implies (and (small-alphorder a b))
             (not (small-alphorder b a)))
    :hints (("Goal"
             :in-theory (e/d (ACL2::BAD-ATOM<= alphorder) ())))))

(encapsulate
  nil

  (local
   (in-theory (enable measure-lemmas)))

  (defun lexorder2 (x y)
    ;; returns (mv order equal-x-y)
    (declare (xargs :guard t
                    :measure (+ (cons-count x) (cons-count y))))
    (let ((x (ex-from-rp-loose x))
          (y (ex-from-rp-loose y)))
      (cond ((atom x)
             (cond
              ((atom y)
               (if (equal x y)
                   (mv nil t)
                 (mv (small-alphorder x y)
                     #|(or (equal x nil)
                     (and (small-alphorder x y) ;
                     (not (equal y nil))))||#
                     nil)))
              (t
               (b* (((mv order-res &) (lexorder2 x (car y))))
                 (mv order-res nil)))))
            ((atom y)
             (b* (((mv order-res &) (lexorder2 (car x) y)))
               (mv order-res nil)))
            ((or (equal (car x) (car y)))
             (lexorder2 (cdr x) (cdr y)))
            (t (b* (((mv order-res equal-x-y)
                     (lexorder2 (car x) (car y))))
                 (if equal-x-y
                     (lexorder2 (cdr x) (cdr y))
                   (mv order-res nil)))))))

  (encapsulate
    nil

    (defthmd lexorder2-sanity-lemma1
      (implies (equal x y)
               (NOT (MV-NTH 0
                            (LEXORDER2 x y))))
      :hints (("Goal"
               :induct (LEXORDER2 X y)
               :in-theory (e/d () ()))))

    (defthmd lexorder2-sanity-lemma2
      (implies (MV-NTH 1 (LEXORDER2 x y))
               (not (MV-NTH 0 (LEXORDER2 x y)))))

    (defthmd lexorder2-sanity-lemma3
      (implies (MV-NTH 1 (LEXORDER2 x y))
               (MV-NTH 1 (LEXORDER2 y x))))

    (defthmd
      lexorder2-sanity
      (implies (MV-NTH 0 (LEXORDER2 X Y))
               (NOT (MV-NTH 0 (LEXORDER2 Y X))))
      :otf-flg t
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp-loose
                                lexorder2-sanity-lemma3
                                lexorder2-sanity-lemma2
                                is-rp
                                lexorder2-sanity-lemma1) ()))))))

(define adder-b+ ((x )
                  (y ))
  (+ (ifix x)
     (ifix y)))

(defmacro adder-sum (&rest rst)
  (cond ((null rst) 0)
        ((null (cdr rst))
         (list 'adder-b+ (car rst) 0))
        (t (xxxjoin 'adder-b+ rst))))

(add-macro-fn adder-sum adder-b+ t)

(define bit-of ((num integerp)
                (pos natp))
  :returns (res bitp)
  (bit-fix (acl2::logbit pos num))
  ///
  (add-rp-rule bitp-of-bit-of))


(rp::def-rw-opener-error
 s-spec-opener-error
 (rp::s-spec x))

(rp::def-rw-opener-error
 c-spec-opener-error
 (rp::c-spec x))

(rp::def-rw-opener-error
 s-c-spec-opener-error
 (rp::s-c-spec x))

(rp::def-rw-opener-error
 c-s-spec-opener-error
 (rp::c-s-spec x))

(rp::def-rw-opener-error
 sort-sum-opener-error
 (sort-sum x))

;; for proofs:
(define m2 (x)
  (mod (ifix x) 2))

(define f2 (x)
  (floor (ifix x) 2))

(define d2 (x)
  (f2 (sum x (-- (m2 x)))))

(define times2 (x)
  (sum x x))

(define quarternaryp (term)
  :inline t
  (or (equal term 0)
      (equal term 1)
      (equal term 2)
      (equal term 3)))

(define ba2 (n1 i1 n2 i2)
  :verify-guards nil
  (and$ (bit-of n1 i1)
        (bit-of n2 i2))
  ///
  (def-rp-rule bitp-ba2
    (bitp (ba2 n1 i1 n2 i2))))

(define ba3 (n1 i1 n2 i2 n3 i3)
  :verify-guards nil
  (and$ (bit-of n1 i1)
        (bit-of n2 i2)
        (bit-of n3 i3))
  ///
  (def-rp-rule bitp-ba3
    (bitp (ba3 n1 i1 n2 i2 n3 i3))))

(define ba4 (n1 i1 n2 i2 n3 i3 n4 i4)
  :verify-guards nil
  (and$ (bit-of n1 i1)
        (bit-of n2 i2)
        (bit-of n3 i3)
        (bit-of n4 i4))
  ///
  (def-rp-rule bitp-ba4
    (bitp (ba4 n1 i1 n2 i2 n3 i3 n4 i4))))

(define is-rp-bitp (term)
  (case-match term
    (('rp ''bitp &)
     t)))

(define adder-mux ((select bitp)
                   (i0 bitp)
                   (i1 bitp))
  :returns (res bitp)
  (if (equal (bit-fix select) 0)
      (bit-fix i0)
    (bit-fix i1))
  ///
  (add-rp-rule bitp-of-adder-mux))

(define m2-p (term)
    :inline t
    (case-match term (('m2 &) t))
    ///
    (defthm m2-p-implies-fc
      (implies (m2-p term)
               (case-match term (('m2 &) t)))
      :rule-classes :forward-chaining))
