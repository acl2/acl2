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

(include-book "binary-fn-defs")

(include-book "ihs/basic-definitions" :dir :system)

(include-book "misc/total-order" :dir :system)

(define bit-listp (lst)
  :enabled t
  (if (atom lst)
      (eq lst nil)
    (and (bitp (car lst))
         (bit-listp (cdr lst)))))

(define type-p (x)
  :enabled t
  (or ;(booleanp x)
   (integerp x)))

(define type-fix (x)
  :enabled t
;(if (booleanp x)
;   (if x 1 0)
  (if (type-p x)
      x
    0))
 ; )

(defun bit-fix (x)
  (declare (xargs :guard t))
  (if (bitp x) x 0))

(define p+
  ((x (type-p x))
   (y (type-p y)))
  :enabled t
  (+ (type-fix x)
     (type-fix y))
  ///
  (disable-exc-counterpart p+))

(define merge-pp+
  ((x (type-p x))
   (y (type-p y)))
  :enabled t
  (p+ x y)
  ///
  (disable-exc-counterpart merge-pp+))

(define bin-xor (a b)
  (if (or (and (equal a 0) (equal b 1))
          (and (equal a 1) (equal b 0)))
      1
    0)
  ///
  (def-rp-rule booleanp-bin-xor
    (bitp (bin-xor a b))))

(define bin-or (a b)
  (if (or (equal a 1) (equal b 1)) 1 0)
  ///
  (def-rp-rule booleanp-bin-or
    (bitp (bin-or a b))))

(define bin-and (a b)
  (if (and (eql a 1) (eql b 1)) 1 0)
  ///
  (def-rp-rule booleanp-bin-and
    (bitp (bin-and a b))))

(define m2 (x)
  :guard (type-p x)
  :enabled t
;(n2b
  (mod (type-fix x) 2))
;)

(define m2-new (x)
  :guard (type-p x)
  :enabled t
;(n2b
  (m2 x))

(define f2 (x)
  :guard (type-p x)
  :enabled t
  (floor (type-fix x) 2))

(define f2-new (x)
  :guard (type-p x)
  :enabled t
  (f2 x))

#|(define b-m2+
  ((x (type-p x))
   (y (type-p y)))
  :enabled t
  (m2
   (+ (m2 x)
      (m2 y))))||#

(define b+
  ((x (type-p x))
   (y (type-p y)))
  :enabled t
  (+ (type-fix x)
     (type-fix y)))

#|

;;not used:
(define sort-b+ (x)
  ;; to be used when a b+ expression is created for the first time, and the
  ;; inputs are not ordered.
  :enabled t
  x)||#

(define merge-b+
  ((x (type-p x))
   (y (type-p y)))
  :enabled t
  (b+ x y))

#|(define merge-b-m2+
  ((x (type-p x))
   (y (type-p y)))
  :enabled t
  (b-m2+ x y))||#

(defmacro pp-sum (&rest rst)
  (cond ((null rst) 0)
        ((null (cdr rst))
         (list 'p+ 0 (car rst)))
        (t (xxxjoin 'p+ rst))))

(defmacro merge-pp-sum (&rest rst)
  (cond ((null rst) 0)
        ((null (cdr rst))
         (list 'merge-pp+ (car rst) 0))
        (t (xxxjoin 'merge-pp+ rst))))

(defmacro sum (&rest rst)
  (cond ((null rst) 0)
        ((null (cdr rst))
         (list 'type-fix (car rst)))
        (t (xxxjoin 'b+ rst))))

#|(defmacro sum-m2 (&rest rst)
  (cond ((null rst) 0)
        ((null (cdr rst))
         (list 'm2 (car rst)))
        (t (xxxjoin 'b-m2+ rst))))||#

(defmacro merge-sum (&rest rst)
  (cond ((null rst) 0)
        ((null (cdr rst))
         (list 'merge-b+ (car rst) 0))
        (t (xxxjoin 'merge-b+ rst))))

(defmacro merge-sum-m2 (&rest rst)
  ;;;; not used !!!!
  (cond ((null rst) 0)
        ((null (cdr rst))
         (list 'merge-b-m2+ (car rst) 0))
        (t (xxxjoin 'merge-b-m2+ rst))))

(add-macro-fn sum b+ t)
#|(add-macro-fn sum-m2 b-m2+ t)||#
(add-macro-fn pp-sum p+ t)
(add-macro-fn merge-pp-sum merge-pp+ t)

(add-macro-fn merge-sum merge-b+ t)
(add-macro-fn merge-sum-m2 merge-b-m2+ t)

(define --
  ((x (type-p x)))
  :enabled t
  (- (type-fix x)))

(define times2 (x)
  (declare (xargs :guard (type-p x)))
  (b+ x x))

(define minus (x)
  (declare (xargs :guard (type-p x)))
  (-- x))

(define hide-tmp (x)
  :enabled t
  x)

(define hide-hons (x)
  :enabled t
  x)

(define []-cdr (x n)
  :verify-guards nil
  (if (zp n)
      x
    (cdr ([]-cdr x (1- n)))))

(define []-take (x n)
  :verify-guards nil
  (if (zp n)
      nil
    (cons (car x)
          ([]-take (cdr x) (1- n)))))

(define [] (x n)
  :verify-guards nil
  (car ([]-cdr x n)))

(defmacro c (&rest rst)
  (cond ((null rst) 0)
        ((null (cdr rst))
         (list 'f2 (list 'b+ (car rst) 0)))
        (t `(f2 ,(xxxjoin 'b+ rst)))))

#|(defmacro co (&rest rst)
  (cond ((null rst) 0)
        ((null (cdr rst))
         (list 'f2o (list 'b+ (car rst) 0)))
        (t `(f2o ,(xxxjoin 'b+ rst)))))||#

(defmacro s (&rest rst)
  (cond ((null rst) 0)
        ((null (cdr rst))
         (list 'm2 (list 'b+ (car rst) 0)))
        (t `(m2 ,(xxxjoin 'b+ rst)))))

(defun v-to-nat (v)
  (declare (xargs :guard t))
  (if (atom v)
      0
    (+ (bit-fix (car v))
       (* 2 (v-to-nat (cdr v))))))

(defun v-to-int (vector)
  (b* ((n (v-to-nat vector))
       (v-len (len vector))
       (n (if (> n (1- (expt 2 (1- v-len))))
              (-  n (expt 2 v-len))
            n)))
    n))

(defun nat-to-v (x n)
  (declare (xargs :guard (and (natp x) (natp n))))
  (if (zp n)
      nil
    (cons (bit-fix (mod x 2))
          (nat-to-v (floor x 2) (1- n)))))

(defun int-to-v (n v-len)
  (b* ((n
        (if (< n 0)
            (+ (expt 2 v-len) n)
          n)))
    (nat-to-v n v-len)))

(defun binaryp (x)
  (or (equal x 0)
      (equal x 1)))

(defun mbinaryp (x)
  (or (equal x 0)
      (equal x -1)))

(defun binary-listp (lst)
  (if (atom lst)
      (equal lst nil)
    (and (binaryp (car lst))
         (binary-listp (cdr lst)))))

(define b2n (x)
  :enabled t
;(if (booleanp x)
;   (if x 1 0)
  (if (integerp x)
      x
    0))
  ;)

(define n2b (x)
  :enabled t
;(if (equal x 0)
;   nil
; (if  (equal x 1)
;    t
  (type-fix x))
   ; )
  ;)

(define m2-f2 (x)
  ;; There are a lot of terms of the form (list (m2 x) (f2 x))
  ;; X can be a very large term and
  ;; We want x to be simplified first to reduce the total number of
  ;; simplifications
  :guard (type-p x)
  :enabled nil
  (list  (m2 x)
         (f2 x))
  ///
  (def-rp-rule m2-f2-def
    (equal (m2-f2 x)
           (list  (m2 x)
                  (f2 x)))))

(define quarternaryp (x)
  :enabled t
  (or (equal x 0)
      (equal x 1)
      (equal x 2)
      (equal x 3)))

(define m2-f2-[0-3] (x)
  ;; There are a lot of terms of the form (list (m2 x) (f2 x))
  ;; X can be a very large term and
  ;; We want x to be simplified first to reduce the total number of
  ;; simplifications
  :guard t
  :enabled nil
  (if (quarternaryp x)
      (list  (m2 x)
             (f2 x))
    (list nil nil))
  ///
  ;; (defthm m2-f2-[0-3]-def-side-cond
  ;;   (implies
  ;;    (quarternaryp x)
  ;;    (and (booleanp (m2 x))
  ;;         (booleanp (f2 x)))))

  (def-rp-rule m2-f2-[0-3]-def
    (implies (quarternaryp x)
             (equal (m2-f2-[0-3] x)
                    (list (m2-new x)
                          (f2-new x)))))

  (defthmd m2-f2-[0-3]-def-sc
    (implies (quarternaryp x)
             (and (bitp (m2-new x))
                  (bitp (f2-new x))))))

(rp-attach-sc m2-f2-[0-3]-def
              m2-f2-[0-3]-def-sc)

(define d2 (x)
  :guard (type-p x)
  :enabled t
  (sum (-- (m2 x)) (f2 x))) ; it is divide by 2

(define d2-new (x)
  :guard (type-p x)
  :enabled t
  (d2 x))

(define ba
  ((a (bitp a))
   (b (bitp b)))
  :enabled t
  (binary-and a b)
  ///
  (def-rp-rule$ t t ba-type
    (bitp (ba a b))
    :rule-classes :type-prescription))

(define pp ((a (bitp a)))
  :enabled t
  (bit-fix a)
  ///
  (def-rp-rule pp-type
    (bitp (pp a))
    :rule-classes
    :type-prescription)

  (disable-exc-counterpart pp))

(define ~ (x)
  (if (bitp x) (- 1 x) 1)
  ///
  (def-rp-rule bitp-of-~
    (bitp (~ x)))

  (def-rp-rule natp-of-~
    (natp (~ x))))

(define evenp2 (term)
  (evenp (type-fix term)))


(define small-alphorder ((x atom)
                         (y atom))
  (cond ((integerp x)
         (cond ((integerp y)
                (< x y))
               (t (symbolp y))))
        ((symbolp x)
         (cond ((symbolp y)
                (symbol< x y))
               (t nil)))
        (t
         nil))
  ///
  
  (defthm small-alphorder-sanity
    (implies (and (atom a)
                  (atom b)
                  (small-alphorder a b))
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
                         (and (small-alphorder x y)
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


(define adder-b+ ((x type-p)
                  (y type-p))
  (b+ x y))

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
