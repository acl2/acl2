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

(include-book "../mult-defs")

;; pp-sum order:

(progn
  (defund-inline should-sum-terms-cancel (term1 term2)
    (declare (xargs :verify-guards t))
    (b* (;;(term1 (ex-from-rp term1))
         ;;(term2 (ex-from-rp term2))
         )
      (or (and (case-match term1 (('-- &) t))
               (rp-equal-cnt (cadr term1) term2 0))
          (and (case-match term2 (('-- &) t))
               (rp-equal-cnt (cadr term2) term1 0)))))

  #|(define is-a-type-fixed-fnc (term)
  :inline t
  (case-match term
  (('b+ & &) t)
  (('m2 &) t)
  (('f2 &) t)
  (('d2 &) t)
  (('-- &) t)
  (('p+ & &) t)
  (('merge-b+ & &) t)
  (('bit-of & &) t)
  (('binary-and & &) t)
  (('binary-or & &) t)
  (('binary-xor & &) t)
  (('binary-? & &) t)
  (('merge-pp+ & &) t)))||#

  (define pp-order-has-priority? (term)
    :inline t
    (case-match term
      (('binary-and ('binary-not &) &)
       t)
      (('binary-or & &)
       t)
      (('binary-not &)
       t)
      (('quote &)
       t)))

  (define ex-from-rp/type-fix/-- (x)
    (cond ((and (consp x)
                (consp (cdr x)))
           (if (or (equal (car x) '--)
                   (equal (car x) 'type-fix))
               (ex-from-rp/type-fix/-- (cadr x))
             (if (and (equal (car x) 'rp)
                      (consp (cddr x)))
                 (ex-from-rp/type-fix/-- (caddr x))
               x)))
          (t x)))
    ;; (case-match x
    ;;   (('rp & y)
    ;;    (ex-from-rp/type-fix/-- y))
    ;;   (('-- y)
    ;;    (ex-from-rp/type-fix/-- y))
    ;;   (('type-fix y)
    ;;    (ex-from-rp/type-fix/-- y))
    ;;   (& x)))

  (local
   (defthm m-lemma1
     (implies t
              (<= (cons-count (EX-FROM-RP/TYPE-FIX/-- X))
                  (cons-count X)))
     :hints (("Goal"
              :induct (EX-FROM-RP/TYPE-FIX/-- X)
              :do-not-induct t
              :in-theory (e/d (ex-from-rp/type-fix/--
                               cons-count) ())))))

  (define pp-list-order ((x true-listp)
                         (y true-listp))
    (cond ((or (atom x)
               (atom y))
           (not (atom y)))
          ((equal (car x) (car y))
           (pp-list-order (cdr x) (cdr y)))
          (t
           (b* (((mv res &)
                 (lexorder2 (car x) (car y))))
             res))))

  (defthm pp-list-order-sanity
    (implies (pp-list-order x y)
             (not (pp-list-order y x)))
    :hints (("Goal"
             :in-theory (e/d (pp-list-order
                              lexorder2-sanity)
                             (lexorder2)))))

  (define pp-order-and$ (x y)
    (b* (((mv car-x last-x) (if (and (consp x)
                                     (eq (car x) 'binary-and)
                                     (consp (cdr x))
                                     (consp (cddr x)))
                                (mv (cadr x) nil)
                              (mv x t)))
         ((mv car-y last-y) (if (and (consp Y)
                                     (eq (car y) 'binary-and)
                                     (consp (cdr y))
                                     (consp (cddr y)))
                                (mv (cadr y) nil)
                              (mv y t))))
      (cond ((equal car-x car-y)
             (if (and (not last-y)
                      (not last-x))
                 (pp-order-and$ (caddr x)
                                (caddr y))
               (not last-y)))
            (t
             (b* (((mv lex-order &)
                   ;;lex-order
                   (lexorder2 car-x car-y)))
               lex-order)))))

  (defthm pp-order-and$-sanity
    (implies (pp-order-and$ x y)
             (not (pp-order-and$ y x)))
    :hints (("Goal"
             :in-theory (e/d (pp-order-and$
                              lexorder2-sanity
                              lexorder2-sanity-lemma3
                              lexorder2-sanity-lemma1
                              lexorder2-sanity-lemma2)
                             (lexorder2)))))

  (define pp-order (x y)
    (b* ((x (ex-from-rp/type-fix/-- x))
         (y (ex-from-rp/type-fix/-- y)))
      (cond ((or (and (consp x) (eq (car x) 'p+))
                 (and (consp y) (eq (car y) 'p+)))
             nil)
            ((equal x y)
             nil)
            ((or (equal x ''0)
                 (equal y ''0))
             (not (equal y ''0)))
            ((or (and (consp x) (eq (car x) 'binary-and))
                 (and (consp y) (eq (car y) 'binary-and)))
             (pp-order-and$ x y))
            #|((or (equal x '(pp '1))
                 (equal y '(pp '1)))
             (not (equal y '(pp '1))))||#
            (t
             (b* (((mv res &) (lexorder2 x y))) res)))))

  (local
   (defthm pp-order-sanity
     (implies (pp-order x y)
              (not (pp-order y x)))
     :hints (("Goal"
              :in-theory (e/d (pp-order
                               lexorder2-sanity)
                              (lexorder2)))))))

;; (pp-order '(binary-and a (binary-and b c)) '(binary-and a b)) = nil
;; (pp-list-order '(a b c) '(a b)) = nil

;; (pp-list-order '(a b c) '(a)) = nil
;; (pp-order '(binary-and a (binary-and b c)) 'a) = nil

;; (pp-order '(binary-and a (binary-and b c)) ''1) = t
;; (pp-list-order '(a b c) '('1)) = t

;; (pp-order '(binary-and a (binary-and b c)) '(binary-and a (binary-and b c)))
;; = nil
;; (pp-list-order '(a b c) '(a b c)) nil

;; (pp-list-order '(a b c) '(a c d)) = t
;; (pp-order '(binary-and a (binary-and b c)) '(binary-and a (binary-and c d))) =t

;; (pp-list-order '(a b c) '(a a d)) = nil
;; (pp-order '(binary-and a (binary-and b c)) '(binary-and a (binary-and a d)))
;; = nil

;; (pp-order 'a 'b) = t
;; (pp-list-order '(a) '(b)) = t

#|(pp-order '(BIT-OF IN1 '7)
          '(-- (BINARY-AND (BIT-OF IN1 '6)
                    (BINARY-AND (BIT-OF IN1 '7)
                                (BIT-OF IN2 '0)))))

(pp-order '(-- (BINARY-AND (BIT-OF IN1 '6)
                    (BINARY-AND (BIT-OF IN1 '7)
                                (BIT-OF IN2 '0))))
          '(BIT-OF IN1 '7))

(pp-list-order '((BIT-OF IN1 '6) (BIT-OF IN1 '7)
                 (BIT-OF IN2 '0))
               '((BIT-OF IN1 '7)))

(pp-list-order '((BIT-OF IN1 '7))
               '((BIT-OF IN1 '6) (BIT-OF IN1 '7)
                 (BIT-OF IN2 '0)))
||#

;; (pp-order '(BINARY-AND (BIT-OF IN1 '6)
;;                        (BINARY-AND (BIT-OF IN1 '7)
;;                                    (BIT-OF IN2 '7)))
;;           '(BINARY-AND (BIT-OF IN1 '6) (BINARY-AND (BIT-OF IN1 '7) (BIT-OF IN2
;;                                                                            '6))))

;; (pp-list-order '((BIT-OF IN1 '6)
;;                  (BIT-OF IN1 '7)
;;                  (BIT-OF IN2 '7))
;;                '((BIT-OF IN1 '6) (BIT-OF IN1 '7) (BIT-OF IN2 '6)))

(define merge-pp-and (x y)
  (and$ x y))

(define merge-pp-or (x y)
  (or$ x y))

(defmacro merge-pp-and$ (&rest rp::rst)
  (cond ((null rp::rst) 0)
        ((null (cdr rp::rst))
         (list 'bit-fix (car rp::rst)))
        (t (xxxjoin 'merge-pp-and rp::rst))))

(add-macro-fn merge-pp-and$ merge-pp-and t)

(defmacro merge-pp-or$ (&rest rp::rst)
  (cond ((null rp::rst) 0)
        ((null (cdr rp::rst))
         (list 'bit-fix (car rp::rst)))
        (t (xxxjoin 'merge-pp-or rp::rst))))

(add-macro-fn merge-pp-or$ merge-pp-or t)

(progn
  (define pp-or$-order (x y)
    (b* ((x (ex-from-rp x))
         (y (ex-from-rp y))
         (x (case-match x (('binary-not a) a) (& x)))
         (y (case-match y (('binary-not a) a) (& y)))
         (x-is-or (case-match x (('binary-or & &) t)))
         (y-is-or (case-match y (('binary-or & &) t))))
      (cond ((or x-is-or y-is-or)
             nil)
            (t
             (b* (((mv res &)
                   (lexorder2 x y)))
               res)))))

  (defthmd sanity-or$-order
    (implies (pp-or$-order x y)
             (not (pp-or$-order y x)))
    :hints (("Goal"
             :in-theory (e/d (pp-or$-order
                              lexorder2-sanity
                              lexorder2-sanity-lemma2)
                             ())))))

(progn
  (define pp-and$-order (x y)
    (b* ((x (ex-from-rp x))
         (y (ex-from-rp y))
         (x~ (case-match x (('binary-not &) t)))
         (y~ (case-match y (('binary-not &) t)))
         (x-is-and (case-match x (('binary-and & &) t)))
         (y-is-and (case-match y (('binary-and & &) t)))
         (x-is-or (case-match x (('binary-or & &) t)))
         (y-is-or (case-match y (('binary-or & &) t))))
      (cond ((or x-is-and y-is-and)
             nil)
            ;; push not$'s to the beginning
            ((or x~ y~)
             (if (and x~ y~)
                 (b* (((mv res &)
                       (lexorder2 x y)))
                   res)
               (not y~)))
            ;; push or$'s to the end.
            ((or x-is-or
                 y-is-or)
             (if (and x-is-or
                      y-is-or)
                 nil
               y-is-or))
            (t
             (b* (((mv res &)
                   (lexorder2 x y)))
               res)))))

  (defthmd sanity-and$-order
    (implies (pp-and$-order x y)
             (not (pp-and$-order y x)))
    :hints (("Goal"
             :in-theory (e/d (pp-and$-order
                              lexorder2-sanity)
                             ())))))

(define flatten-pp (x)
  :enabled t
  x)
