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

(include-book "summation-tree-meta-fncs")

(local
 (include-book "lemmas"))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arith-5
  :disabled t))

(local
 (in-theory (e/d (sum-comm-1-loop-stopper
                  sum-comm-2-loop-stopper)
                 (sum-comm-1
                  sum-comm-2))))

(local
 (defthmd rp-evl-of-ex-from-rp-reverse
   (implies (syntaxp (atom x))
            (equal (rp-evlt x a)
                   (rp-evlt (ex-from-rp x) a)))
   :hints (("goal"
            :in-theory (e/d (ex-from-rp
                             is-rp) ())))))


(local
 (defthm when-ex-from-rp-is-1
   (implies (equal (ex-from-rp term) ''1)
            (equal (rp-evlt term a)
                   1))
   :hints (("goal"
            :in-theory (e/d (ex-from-rp is-rp)
                            (ex-from-rp-lemma1))))))

(local
 (defthm when-ex-from-rp-is-0
   (implies (equal (ex-from-rp term) ''0)
            (equal (rp-evlt term a)
                   0))
   :hints (("goal"
            :in-theory (e/d (ex-from-rp is-rp)
                            (ex-from-rp-lemma1))))))

;;;;;;;;;;;;;;;;
;; EVAL LEMMAS

(progn
  (local
   (defthmd eval-of-binary-not-1
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          'binary-not)
                   (consp term)
                   (consp (cdr term))
                   (not (cddr term)))
              (equal (rp-evlt term a)
                     (binary-not (rp-evlt (cadr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of-binary-not
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          'binary-not)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (not (cddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (binary-not (rp-evlt (cadr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of-binary-not-1)
                              (evl-of-extract-from-rp)))))))

(progn
  (local
   (defthmd eval-of---1
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          '--)
                   (consp term)
                   (consp (cdr term))
                   (not (cddr term)))
              (equal (rp-evlt term a)
                     (-- (rp-evlt (cadr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of----
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          '--)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (not (cddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (-- (rp-evlt (cadr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of---1)
                              (evl-of-extract-from-rp)))))))

(progn
  (local
   (defthmd eval-of-bit-of-1
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          'bit-of)
                   (consp term)
                   (consp (cdr term))
                   (consp (cddr term))
                   (not (cdddr term)))
              (equal (rp-evlt term a)
                     (bit-of (rp-evlt (cadr term) a)
                             (rp-evlt (caddr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of-bit-of
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          'bit-of)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (consp (cddr (ex-from-rp term)))
                   (not (cdddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (bit-of (rp-evlt (cadr (ex-from-rp term)) a)
                             (rp-evlt (caddr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of-bit-of-1)
                              (evl-of-extract-from-rp)))))))

(progn
  (local
   (defthmd eval-of-binary-?-1
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          'binary-?)
                   (consp term)
                   (consp (cdr term))
                   (consp (cddr term))
                   (consp (cdddr term))
                   (not (cddddr term)))
              (equal (rp-evlt term a)
                     (binary-? (rp-evlt (cadr term) a)
                               (rp-evlt (caddr term) a)
                               (rp-evlt (cadddr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of-binary-?
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          'binary-?)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (consp (cddr (ex-from-rp term)))
                   (consp (cdddr (ex-from-rp term)))
                   (not (cddddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (binary-? (rp-evlt (cadr (ex-from-rp term)) a)
                               (rp-evlt (caddr (ex-from-rp term)) a)
                               (rp-evlt (cadddr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of-binary-?-1)
                              (evl-of-extract-from-rp)))))))

(progn
  (local
   (defthmd eval-of-binary-or-1
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          'binary-or)
                   (consp term)
                   (consp (cdr term))
                   (consp (cddr term))
                   (not (cdddr term)))
              (equal (rp-evlt term a)
                     (binary-or (rp-evlt (cadr term) a)
                                (rp-evlt (caddr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of-binary-or
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          'binary-or)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (consp (cddr (ex-from-rp term)))
                   (not (cdddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (binary-or (rp-evlt (cadr (ex-from-rp term)) a)
                                (rp-evlt (caddr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of-binary-or-1)
                              (evl-of-extract-from-rp)))))))

(progn
  (local
   (defthmd eval-of-binary-xor-1
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          'binary-xor)
                   (consp term)
                   (consp (cdr term))
                   (consp (cddr term))
                   (not (cdddr term)))
              (equal (rp-evlt term a)
                     (binary-xor (rp-evlt (cadr term) a)
                                 (rp-evlt (caddr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of-binary-xor
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          'binary-xor)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (consp (cddr (ex-from-rp term)))
                   (not (cdddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (binary-xor (rp-evlt (cadr (ex-from-rp term)) a)
                                 (rp-evlt (caddr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of-binary-xor-1)
                              (evl-of-extract-from-rp)))))))

(progn
  (local
   (defthmd eval-of-binary-and-1
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car term)
                          'binary-and)
                   (consp term)
                   (consp (cdr term))
                   (consp (cddr term))
                   (not (cdddr term)))
              (equal (rp-evlt term a)
                     (binary-and (rp-evlt (cadr term) a)
                                 (rp-evlt (caddr term) a))))
     :hints (("goal"
              :in-theory (e/d ()
                              (evl-of-extract-from-rp))))))

  (local
   (defthm eval-of-binary-and
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (equal (car (ex-from-rp term))
                          'binary-and)
                   (consp (ex-from-rp term))
                   (consp (cdr (ex-from-rp term)))
                   (consp (cddr (ex-from-rp term)))
                   (not (cdddr (ex-from-rp term))))
              (equal (rp-evlt term a)
                     (binary-and (rp-evlt (cadr (ex-from-rp term)) a)
                                 (rp-evlt (caddr (ex-from-rp term)) a))))
     :hints (("goal"
              :in-theory (e/d (rp-evl-of-ex-from-rp-reverse
                               eval-of-binary-and-1)
                              (evl-of-extract-from-rp)))))))

(local
 (defthmd not$-to-pp-sum
   (implies (bitp a)
            (equal (not$ a)
                   (sum 1 (-- a))))))

(progn
  (local
   (defthmd pp-has-bitp-rp-implies-lemma
     (implies (and (pp-has-bitp-rp term)
                   (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (eval-and-all (context-from-rp term nil) a))
              (bitp (rp-evlt term a)))
     :hints (("goal"
              :induct (pp-has-bitp-rp term)
              :do-not-induct t
              :in-theory (e/d (pp-has-bitp-rp
                               is-rp
                               is-if
                               eval-and-all
                               context-from-rp)
                              (bitp
                               ex-from-rp-lemma1
                               valid-sc))))))

  (local
   (defthm pp-has-bitp-rp-implies
     (implies (and (pp-has-bitp-rp term)
                   (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (valid-sc term a))
              (bitp (rp-evlt term a)))
     :hints (("goal"
              :induct (pp-has-bitp-rp term)
              :expand ((valid-sc term a))
              :do-not-induct t
              :in-theory (e/d (pp-has-bitp-rp
                               pp-has-bitp-rp-implies-lemma
                               is-rp
                               is-if)
                              (bitp
                               rp-trans
                               ex-from-rp-lemma1
                               context-from-rp
                               valid-sc-ex-from-rp-2
                               not-include-rp
                               rp-evl-of-rp-call
                               valid-sc
                               eval-and-all)))))))

(local
 (defthm pp-term-p-is-bitp
   (implies (and (pp-term-p term)
                 (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (valid-sc term a))
            (bitp (rp-evlt term a)))
   :hints (("goal"
            :in-theory (e/d ()
                            (valid-sc
                             bitp
                             rp-trans
                             sum
                             not$-to-pp-sum))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ARITH LEMMAS

(local
 (in-theory (disable rp-evlt-of-ex-from-rp)))

(local
 (encapsulate
   nil
   (local
    (in-theory (disable +-IS-SUM)))
   (local
    (use-arith-5 t))
   (defthm floor-of-two-is-less
     (implies (and (> x 2)
                   (integerp x))
              (< (floor x 2)
                 x)))

   (defthm floor-of-len-is-less-than-lst
     (implies (and (consp lst)
                   (consp (cdr lst)))
              (< (FLOOR (LEN LST) 2) (LEN LST)))
     :hints (("Goal"
              :in-theory (e/d (len) ()))))

   (defthm fix-less-than-with-smm
     (implies (consp lst)
              (< 2 (+ 2 (LEN lst)))))))

(progn
  (local
   (defun bit-listp (lst)
     (if (atom lst)
         (equal lst nil)
       (and (bitp (car lst))
            (bit-listp (cdr lst))))))

  (local
   (defun bit-list-listp (lst)
     (if (atom lst)
         (equal lst nil)
       (and (bit-listp (car lst))
            (bit-list-listp (cdr lst))))))

  (local
   (defun rp-evlt-lst-lst (lst a)
     (if (atom lst)
         nil
       (cons (rp-evlt-lst (car lst) a)
             (rp-evlt-lst-lst (cdr lst) a)))))

  (local
   (define times$ (x y)
     :verify-guards nil
     (b* ((x (ifix x))
          (y (ifix y)))
       (* x y)))))

(local
 (defthm times$-of-1-and-0
   (and (equal (times$ 1 x)
               (ifix x))
        (equal (times$ x 1)
               (ifix x))
        (equal (times$ x 0)
               0)
        (equal (times$ 0 x)
               0))
   :hints (("goal"
            :in-theory (e/d (times$ and$) ())))))

(local
 (defthm len-equals-2
   (implies (and (integerp x)
                 (integerp y))
            (equal (EQUAL (+ x (len lst)) y)
                   (equal (len lst) (- y x))))
   :hints (("Goal"
            :in-theory (e/d () (+-IS-SUM))))))

(progn (local
        (defthm bit-listp-lemma
          (implies (bit-listp (rp-evlt-lst lst a))
                   (bit-listp (rp-evlt-lst (cdr lst) a)))))

       (local
        (defthm bit-listp-lemma-2
          (implies (and (bit-listp (rp-evlt-lst lst a))
                        (consp lst))
                   (bitp (rp-evlt (car lst) a))))))

(progn
  (local
   (defthmd or$-to-pp-sum
     (implies (and (bitp x)
                   (bitp y))
              (equal (or$ x y)
                     (sum x y (-- (and$ x y)))))
     :hints (("goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthmd binary-xor-to-pp-sum
     (implies (and (bitp x)
                   (bitp y))
              (equal (binary-xor  x y)
                     (sum x y
                          (-- (and$ x y))
                          (-- (and$ x y)))))))

  (local
   (defthmd binary-?-to-pp-sum
     (implies (and (bitp x)
                   (bitp test)
                   (bitp y))
              (equal (binary-? test  x y)
                     (sum y (and$ test x)
                          (-- (and$ test y)))))))

  (local
   (defthm ---of-pp-sum
     (implies t
              (equal (-- (sum x y))
                     (sum (-- x) (-- y))))
     :hints (("goal"
              :in-theory (e/d (bitp sum --)
                              (+-IS-SUM))))))

  (local
   (defthm --of--
     (equal (-- (-- x))
            (ifix x))
     :hints (("Goal"
              :in-theory (e/d (--) ())))))

  (local
   (defthm type-fix-of-fncs
     (and (equal (ifix (and$ a b))
                 (and$ a b))
          (equal (ifix (sum a b))
                 (sum a b)))
     :hints (("goal"
              :in-theory (e/d (and$ ifix) ())))))

  (local
   (defthm type-fix-of--
     (equal (ifix (-- x))
            (-- x))))

  (local
   (defthm type-fix-when-integerp
     (implies (integerp x)
              (equal (ifix x)
                     x))))

  (local
   (defthm type-fix-when-bitp
     (implies (bitp x)
              (equal (ifix x)
                     x))))

  (local
   (defthm integerp-of-fncs
     (and (integerp (sum x y))
          (integerp (-- x))
          (integerp (and$ x y))
          (integerp (or$ x y))
          (integerp (not$ x)))))

  (local
   (defthm bitp-implies-integerp
     (implies (bitp x)
              (integerp x))))

  (local
   (defthm when-minus-of-x-is-zero
     (implies (and (integerp x)
                   (equal (- x) 0))
              (equal x 0))
     :rule-classes :forward-chaining))

  (local
   (defthm when-minus-of-x-is-1
     (implies (and (integerp x)
                   (equal (- x) 1))
              (equal x -1))
     :rule-classes :forward-chaining))

  (local
   (defthm binar-and-abs-is-and$-2-lemma
     (equal (EQUAL (- (IFIX X)) 0)
            (equal (ifix x) 0))))

  (local
   (defthm binar-and-abs-is-and$-2-lemma-2
     (equal (EQUAL (- (IFIX X)) 1)
            (equal (ifix x) -1))))

  (local
   (defthm binar-and-abs-is-and$-2
     (and (implies (and (bitp x)
                        (bitp y))
                   (equal (times$ x y)
                          (and$ x y)))
          (implies (and (bitp x)
                        (bitp (-- y)))
                   (equal (times$ x y)
                          (-- (and$ x (-- y)))))
          (implies (and (bitp (-- x))
                        (bitp y))
                   (equal (times$ x y)
                          (-- (and$ (-- x) y))))
          (implies (and (bitp (-- x))
                        (bitp (-- y)))
                   (equal (times$ x y)
                          (and$ (-- x) (-- y)))))
     :hints (("goal"
              :in-theory (e/d (times$
                               bit-fix --
                               and$) ())))))
  (local
   (defthm pp-sum-equals
     (equal (equal (sum a x)
                   (sum a y))
            (equal (ifix x)
                   (ifix y)))))

  (local
   (defthm --of--equals
     (equal (equal (-- x)
                   (-- y))
            (equal (ifix x)
                   (ifix y)))
     :hints (("Goal"
              :in-theory (e/d (--) ())))))

  (local
   (defthm and$-of-1-0
     (implies t
              (and (equal (and$ x 1)
                          (bit-fix x))
                   (equal (and$ 1 x)
                          (bit-fix x))
                   (equal (and$ 0 x)
                          0)
                   (equal (and$ x 0)
                          0)))
     :hints (("goal"
              :in-theory (e/d (and$) ())))))

  (local
   (defthm pp-sum-of-negated-sum
     (and (equal (sum a (-- a) b)
                 (ifix b))
          (equal (sum a (-- a))
                 0)
          (equal (sum (-- a) a b)
                 (ifix b))
          (equal (sum (-- a) a)
                 0))
     :hints (("goal"
              :in-theory (e/d (sum
                               --
                               ifix)
                              (+-IS-SUM))))))

  (local
   (defthm and$-assoc
     (equal (and$ (and$ a b) c)
            (and$ a b c))
     :hints (("goal"
              :in-theory (e/d (and$) ())))))

  (local
   (defthm and$-comm-loop=stopper
     (and (equal (and$ b a c)
                 (and$ a b c))
          (equal (and$ b a)
                 (and$ a b)))
     :hints (("goal"
              :in-theory (e/d (and$) ()))))))

(local
 (encapsulate
   nil

   (local
    (use-arith-5 t))

   (defthmd and$-is-times
     (implies (and (bitp x)
                   (bitp y))
              (equal (and$ x y)
                     (times$ x y))))

   (defthm type-fix-of-times
     (equal (ifix (times$ a b))
            (times$ a b))
     :hints (("goal"
              :in-theory (e/d (times$ ifix) ()))))

   (defthm times$-of---
     (and (equal (times$ a (-- b))
                 (-- (times$ a b)))
          (equal (times$ (-- a) b)
                 (-- (times$ a b))))
     :hints (("goal"
              :in-theory (e/d (-- times$ ifix) ()))))

   (defthm times$-distribute-over-pp-sum
     (and (equal (times$ x (sum a b))
                 (sum (times$ x a)
                      (times$ x b)))
          (equal (times$ (sum a b) x)
                 (sum (times$ x a)
                      (times$ x b))))
     :hints (("goal"
              :in-theory (e/d (times$ sum
                                      ifix)
                              (+-IS-SUM)))))

   (defthm times$-comm
     (and (equal (times$ b (times$ a c))
                 (times$ a (times$ b c)))
          (equal (times$ b a)
                 (times$ a b)))
     :hints (("goal"
              :in-theory (e/d (times$) ()))))

   (defthm times$-reoder
     (equal (times$ (times$ a b) c)
            (times$ a (times$ b c)))
     :hints (("goal"
              :in-theory (e/d (times$) ()))))))

(local
 (defthm and$-of-repeated-vars
   (and (equal (and$ a a b)
               (and$ a b))
        (equal (and$ a a)
               (bit-fix a)))
   :hints (("Goal"
            :in-theory (e/d (and$) ())))))

(local
 (progn
   (defthm len-to-consp
     (implies (not (zp size))
              (equal (equal (len x) size)
                     (and (consp x)
                          (equal (len (cdr x)) (1- size)))))
     :hints (("Goal"
              :in-theory (e/d (len) ()))))

   (defthm len-to-consp-when-o
     (equal (equal (len x) 0)
            (atom x)))

   (defthm len-to-consp-when-less-than-2
     (equal (< (LEN X) 2)
            (not (and (consp x)
                      (consp (cdr x)))))
     :hints (("Goal"
              :in-theory (e/d (len) (+-IS-SUM)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; pp-lists-to-term lemmas

(local
 (progn
   (defthm append-returns-bit-list-listp
     (implies (and (mult-formula-checks state)
                   (booleanp sign)
                   (bit-list-listp (rp-evlt-lst-lst lst1 a))
                   (bit-list-listp (rp-evlt-lst-lst lst2 a))
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (append lst1 lst2)
                                a)))
     :hints (("goal"
              :in-theory (e/d (rp-evlt-lst-lst
                               and$-pp-lists
                               and$-pp-lists-aux
                               pp-term-to-pp-lists
                               bit-list-listp) ()))))

   (defthm append-returns-bit-list-listp-with-strip-cdrs
     (implies (and (mult-formula-checks state)
                   (booleanp sign)
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a))
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (strip-cdrs (append lst1 lst2))
                                a)))
     :hints (("goal"
              :in-theory (e/d (rp-evlt-lst-lst
                               and$-pp-lists
                               and$-pp-lists-aux
                               pp-term-to-pp-lists
                               bit-list-listp) ()))))

   (defthm append-returns-bit-listp
     (implies (and (mult-formula-checks state)
                   (booleanp sign)
                   (bit-listp (rp-evlt-lst lst1 a))
                   (bit-listp (rp-evlt-lst lst2 a))
                   (rp-evl-meta-extract-global-facts))
              (bit-listp
               (rp-evlt-lst (append lst1 lst2)
                            a)))
     :hints (("goal"
              :in-theory (e/d (rp-evlt-lst-lst
                               and$-pp-lists
                               and$-pp-lists-aux
                               pp-term-to-pp-lists
                               bit-list-listp) ()))))))

(local
 (defthm append-equal
   (and (equal (equal (append a x) (append a y))
               (equal x y))
        (implies (and (true-listp x)
                      (true-listp y))
                 (equal (equal (append x a) (append y a))
                        (equal x y))))))

(local
 (defthm append-equal2
   (implies (and (force (equal x k))
                 (force (equal y l)))
            (equal (equal (append x y a) (append k l a))
                   t))))

(progn
  (define pp-lists-to-term-and$ ((cur true-listp))
    (cond ((atom cur)
           ''1)
          ((atom (cdr cur))
           (car cur))
          (t
           `(binary-and ,(car cur)
                        ,(pp-lists-to-term-and$ (cdr cur))))))

  (define pp-lists-to-term-p+ ((lst pp-lists-p))
    (cond ((atom lst)
           ''0)
          ((atom (cdr lst))
           (b* ((cur (pp-lists-to-term-and$ (cdar lst))))
             (if (caar lst)
                 `(-- ,cur)
               `(ifix ,cur))))
          (t
           (b* ((cur (pp-lists-to-term-and$ (cdar lst))))
             (if (caar lst)
                 `(binary-sum (-- ,cur) ,(pp-lists-to-term-p+ (cdr lst)))
               `(binary-sum ,cur ,(pp-lists-to-term-p+ (cdr lst))))))))

  ;; auxilary function used only in the local lemmas for correctness proofs.
  (local
   (define apply-sign-to-pp-lists (lst sign)
     :returns (res pp-lists-p
                   :hyp (pp-lists-p lst))
     :verify-guards nil
     (if (atom lst)
         nil
       (acons (xor sign (caar lst))
              (cdar lst)
              (apply-sign-to-pp-lists (cdr lst) sign))))))

(progn
  (local
   (defthm bitp-of-eval-of-pp-lists-to-term-aux
     (implies (and (bit-listp (rp-evlt-lst lst a))
                   (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts))
              (bitp (rp-evlt (pp-lists-to-term-and$ lst) a)))
     :hints (("goal"
              :in-theory (e/d (pp-lists-to-term-and$) ())))))

  (local
   (defthm eval-of-append-of-pp-lists-to-term-aux
     (implies  (and (mult-formula-checks state)
                    (rp-evl-meta-extract-global-facts)
                    (bit-listp (rp-evlt-lst cur a))
                    (bit-listp (rp-evlt-lst cur2 a)))
               (equal (rp-evlt (pp-lists-to-term-and$ (append cur cur2)) a)
                      (and$ (rp-evlt (pp-lists-to-term-and$ cur) a)
                            (rp-evlt (pp-lists-to-term-and$ cur2) a))))
     :hints (("goal"
              :do-not-induct t
              :induct (pp-lists-to-term-and$ cur)
              :in-theory (e/d (pp-lists-to-term-and$)
                              (bitp
                               rp-evl-lst-of-cons
                               (:rewrite acl2::consp-of-append)
                               bit-listp))))))

  (local
   (defthm integerp-of-eval-of-pp-lists-to-term-aux
     (implies (and (integer-listp (rp-evlt-lst lst a))
                   (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts))
              (integerp (rp-evlt (pp-lists-to-term-and$ lst) a)))
     :hints (("goal"
              :in-theory (e/d (pp-lists-to-term-and$) ())))))

  (local
   (defthm integerp-of-eval-of-pp-lists-to-term
     (implies (and (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a))
                   (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts))
              (integerp (rp-evlt (pp-lists-to-term-p+ lst) a)))
     :hints (("goal"
              :do-not-induct t
              :induct (pp-lists-to-term-p+ lst)
              :in-theory (e/d (pp-lists-to-term-p+)
                              (sum --
                                   and$
                                   bitp
                                   ifix))))))

  (local
   (defthm integerp-of-eval-of-pp-lists-to-term-forward-chaining
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a)))
              (integerp (rp-evlt (pp-lists-to-term-p+ lst) a)))
     :rule-classes :forward-chaining
     :hints (("goal"
              :in-theory (e/d (pp-lists-to-term-p+) ()))))))

(local
 (defthm pp-lists-to-term-of-apply-sign-to-pp-lists
   (implies (and (mult-formula-checks state)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a))
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt (pp-lists-to-term-p+ (apply-sign-to-pp-lists lst t)) a)
                   (-- (rp-evlt (pp-lists-to-term-p+ lst) a))))
   :hints (("goal"
            :do-not-induct t
            :induct (pp-lists-to-term-p+ lst)
            :in-theory (e/d (pp-lists-to-term-p+
                             APPLY-SIGN-TO-PP-LISTS)
                            (--
                             sum
                             ifix
                             integerp))))))

(local
 (defthm pp-lists-to-term-of-append
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a))
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a)))
            (equal (rp-evlt (pp-lists-to-term-p+ (append lst1 lst2)) a)
                   (sum (rp-evlt (pp-lists-to-term-p+ lst1) a)
                        (rp-evlt (pp-lists-to-term-p+ lst2) a))))
   :hints (("goal"
            :induct (pp-lists-to-term-p+ lst1)
            :do-not-induct t
            :in-theory (e/d (pp-lists-to-term-p+)
                            (sum
                             --
                             ifix))))))

(local
 (defthm apply-sign-to-pp-lists-of-sign=nil
   (implies (pp-lists-p lst)
            (equal (apply-sign-to-pp-lists lst nil)
                   lst))
   :hints (("Goal"
            :in-theory (e/d (apply-sign-to-pp-lists) ())))))

(local
 (defthm apply-sign-to-pp-lists-of-append
   (implies t
            (equal (apply-sign-to-pp-lists (append x1 x2) sign)
                   (append (apply-sign-to-pp-lists x1 sign)
                           (apply-sign-to-pp-lists x2 sign))))
   :hints (("Goal"
            :in-theory (e/d (apply-sign-to-pp-lists) ())))))

(local
 (defthm apply-sign-to-pp-lists-of-apply-sign-to-pp-lists
   (equal (apply-sign-to-pp-lists (apply-sign-to-pp-lists lst s1) s2)
          (apply-sign-to-pp-lists lst (xor s1 s2)))
   :hints (("Goal"
            :in-theory (e/d (apply-sign-to-pp-lists) ())))))

(local
 (defthm bit-list-listp-of-apply-sign-to-pp-lists
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a)))
            (bit-list-listp
             (rp-evlt-lst-lst
              (strip-cdrs (apply-sign-to-pp-lists lst1
                                                  sign))
              a)))
   :hints (("Goal"
            :in-theory (e/d (apply-sign-to-pp-lists) ())))))

(local
 (defthmd sign-convert-apply-sign-to-pp-lists
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a)))
            (equal (rp-evlt (pp-lists-to-term-p+
                             (apply-sign-to-pp-lists lst t))
                            a)
                   (-- (rp-evlt (pp-lists-to-term-p+
                                 (apply-sign-to-pp-lists lst nil))
                                a))))
   :hints (("goal"
            :do-not-induct t
            :induct (apply-sign-to-pp-lists lst sign)
            :in-theory (e/d (pp-term-to-pp-lists
                             and$-pp-lists
                             apply-sign-to-pp-lists
                             and$-pp-lists-aux
                             pp-lists-to-term-p+)
                            (--
                             sum
                             and$))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sorting lemmas

(local
 (defthm bit-list-p-with-constants-1
   (equal (bit-listp (cons 1 rest))
          (bit-listp rest))))

(local
 (defthm bit-list-p-def
   (equal (bit-listp (cons x rest))
          (and (bitp x)
               (bit-listp rest)))))

(progn
  (local
   (defthm PP-LISTS-TO-TERM-AND$-def-1
     (implies (consp rest)
              (equal (PP-LISTS-TO-TERM-AND$ (cons x rest))
                     `(binary-and ,x ,(PP-LISTS-TO-TERM-AND$ rest))))
     :hints (("Goal"
              :in-theory (e/d (pp-lists-to-term-and$) ())))))

  (local
   (defthm PP-LISTS-TO-TERM-AND$-def-2
     (implies (atom rest)
              (equal (PP-LISTS-TO-TERM-AND$ (cons x rest))
                     x))
     :hints (("Goal"
              :in-theory (e/d (pp-lists-to-term-and$) ())))))

  (local
   (defthm PP-LISTS-TO-TERM-AND$-def
     (implies t
              (equal (PP-LISTS-TO-TERM-AND$ (cons x rest))
                     (if (consp rest)
                         `(binary-and ,x ,(PP-LISTS-TO-TERM-AND$ rest))
                       x)))
     :hints (("Goal"
              :in-theory (e/d (pp-lists-to-term-and$) ()))))))

(progn
  (local
   (defthm PP-LISTS-TO-TERM-p+-def
     (implies t
              (equal (pp-lists-to-term-p+ (cons x rest))
                     (COND
                      ((ATOM rest)
                       (B* ((CUR (PP-LISTS-TO-TERM-AND$ (cdr x))))
                         (IF (car x)
                             (CONS '-- (CONS CUR 'NIL))
                             `(ifix ,CUR))))
                      (T
                       (B*
                           ((CUR (PP-LISTS-TO-TERM-AND$ (CDR x))))
                         (IF (car x)
                             (CONS 'binary-sum
                                   (CONS (CONS '-- (CONS CUR 'NIL))
                                         (CONS (PP-LISTS-TO-TERM-P+ rest)
                                               'NIL)))
                             (CONS 'binary-sum
                                   (CONS CUR
                                         (CONS (PP-LISTS-TO-TERM-P+ rest)
                                               'NIL)))))))))
     :hints (("Goal"
              :in-theory (e/d (pp-lists-to-term-p+) ()))))))

(local
 (encapsulate
   nil

   (defthm atom-merge-sorted-and$-lists
     (equal (CONSP (MERGE-SORTED-AND$-LISTS LST1 lst2))
            (not (and (atom lst1)
                      (atom lst2))))
     :hints (("Goal"
              :in-theory (e/d (merge-sorted-and$-lists) ()))))

   (local
    (defthm dummy-lemma1
      (implies (equal x (and$ a b))
               (equal (equal x
                             (and$ a x))
                      t))))

   (defthm eval-of-list-to-term-of-merge-sorted-and$-list
     (implies (and (mult-formula-checks state)
                   (force (bit-listp (rp-evlt-lst lst1 a)))
                   (force (bit-listp (rp-evlt-lst lst2 a)))
                   (force (true-listp lst1))
                   (force (true-listp lst2))
                   (rp-evl-meta-extract-global-facts))
              (equal (rp-evlt
                      (pp-lists-to-term-and$
                       (merge-sorted-and$-lists lst1 lst2))
                      a)
                     (and$ (rp-evlt (pp-lists-to-term-and$ lst1) a)
                           (rp-evlt (pp-lists-to-term-and$ lst2) a))))
     :hints (("Goal"
              :induct (MERGE-SORTED-AND$-LISTS lst1 lst2)
              :do-not-induct t
              :in-theory (e/d (;;pp-lists-to-term-and$
                               ;; for soem reason when this is enabled, the proof
                               ;; does too many case-splits.
                               MERGE-SORTED-AND$-LISTS)
                              (len
                               sum valid-sc
                               --
                               and$ or$
                               bitp
                               bit-listp
                               true-listp)))
             ("Subgoal *1/6"
              :expand ((PP-LISTS-TO-TERM-AND$ LST2)))
             ("Subgoal *1/5"
              :expand ((PP-LISTS-TO-TERM-AND$ LST1)))
             ("Subgoal *1/4"
              :do-not-induct t
              :expand ((PP-LISTS-TO-TERM-AND$ LST2)
                       (PP-LISTS-TO-TERM-AND$ LST1)))))

   (defthm bit-listp-of-merge-sorted-and$-lists
     (implies (and (bit-listp (rp-evlt-lst lst1 a))
                   (bit-listp (rp-evlt-lst lst2 a)))
              (bit-listp (rp-evlt-lst (MERGE-SORTED-AND$-LISTS LST1 lst2)
                                      a)))
     :hints (("Goal"
              :do-not-induct t
              :induct (MERGE-SORTED-AND$-LISTS LST1 lst2)
              :in-theory (e/d (bit-listp
                               merge-sorted-and$-lists)
                              (bitp
                               floor)))))))

(local
 (encapsulate
   nil

   (local
    (defthm bitp-bitlistp-lemma
      (IMPLIES (AND (consp lst)
                    (BIT-LISTP (RP-EVLT-LST LST A)))
               (BITP (RP-EVLT (CAR LST) A)))
      :hints (("Goal"
               :in-theory (e/d (bitp bit-listp) ())))))

   (local
    (defthm consp-bit-listp-lemma
      (IMPLIES (AND (NOT (ZP SIZE))
                    (< SIZE (LEN LST)))
               (consp lst))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (len bitp bit-listp) ())))))

   (defthm bit-listp-of-CUT-LIST-BY-HALF
     (implies (and (bit-listp (rp-evlt-lst lst a))
                   (< size (len lst)))
              (and (bit-listp (rp-evlt-lst (MV-NTH 0
                                                   (CUT-LIST-BY-HALF LST size))
                                           a))
                   (bit-listp (rp-evlt-lst (MV-NTH 1
                                                   (CUT-LIST-BY-HALF LST size))
                                           a))))
     :hints (("Goal"
              :do-not-induct t
              :induct (CUT-LIST-BY-HALF LST size)
              :in-theory (e/d (bit-listp
                               cut-list-by-half)
                              (bitp
                               +-IS-SUM)))))

   (defthm bit-list-listp-of-CUT-LIST-BY-HALF
     (implies (and (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a))
                   (< size (len lst)))
              (and (bit-list-listp (rp-evlt-lst-lst (strip-cdrs
                                                     (MV-NTH 0
                                                             (CUT-LIST-BY-HALF LST size)))
                                                    a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs (MV-NTH 1
                                                                        (CUT-LIST-BY-HALF LST size)))
                                                    a))))
     :hints (("Goal"
              :do-not-induct t
              :induct (CUT-LIST-BY-HALF LST size)
              :in-theory (e/d (
                               bit-list-listp
                               cut-list-by-half)
                              (bitp
                               +-IS-SUM
                               bit-listp)))))

   (local
    (defthm lemma1
      (implies (NOT (CONSP (MV-NTH 0 (CUT-LIST-BY-HALF lst size))))
               (equal (MV-NTH 1 (CUT-LIST-BY-HALF lst size))
                      lst))
      :hints (("Goal"
               :in-theory (e/d (cut-list-by-half) ())))))

   (defthm eval-of-CUT-LIST-BY-HALF
     (implies (and (mult-formula-checks state)
                   (force (bit-listp (rp-evlt-lst lst a)))
                   (force (true-listp lst))
                   (force (< size (len lst)))
                   (rp-evl-meta-extract-global-facts))
              (equal (AND$ (RP-EVLT (PP-LISTS-TO-TERM-AND$
                                     (MV-NTH 0
                                             (CUT-LIST-BY-HALF LST size)))
                                    A)
                           (RP-EVLT (PP-LISTS-TO-TERM-AND$
                                     (MV-NTH 1
                                             (CUT-LIST-BY-HALF LST size)))
                                    A))
                     (RP-EVLT (PP-LISTS-TO-TERM-AND$
                               lst)
                              A)))
     :hints (("Goal"
              :do-not-induct t
              :induct (CUT-LIST-BY-HALF LST size)
              :expand ((PP-LISTS-TO-TERM-AND$ LST))
              :in-theory (e/d (cut-list-by-half)
                              (bitp len
                                    true-listp
                                    +-IS-SUM)))))

   (local
    (defthm PP-LISTS-TO-TERM-P+-when-not-consp
      (implies (atom x)
               (equal (PP-LISTS-TO-TERM-P+ x)
                      ''0))
      :hints (("Goal"
               :in-theory (e/d (PP-LISTS-TO-TERM-P+) ())))))

   (defthm eval-of-CUT-LIST-BY-HALF-with-pp-sum
     (implies (and (mult-formula-checks state)
                   (force (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a)))
                   (force (pp-lists-p lst))
                   (force (< size (len lst)))
                   (rp-evl-meta-extract-global-facts))
              (equal (sum (RP-EVLT (PP-LISTS-TO-TERM-p+
                                    (MV-NTH 0
                                            (CUT-LIST-BY-HALF LST size)))
                                   A)
                          (RP-EVLT (PP-LISTS-TO-TERM-p+
                                    (MV-NTH 1
                                            (CUT-LIST-BY-HALF LST size)))
                                   A))
                     (RP-EVLT (PP-LISTS-TO-TERM-p+
                               lst)
                              A)))
     :hints (("Goal"
              :do-not-induct t
              :induct (CUT-LIST-BY-HALF LST size)
              :expand ((PP-LISTS-TO-TERM-p+ LST))
              :in-theory (e/d (cut-list-by-half)
                              (bitp
                               sum
                               --
                               +-IS-SUM
                               len
                               true-listp)))))))

(local
 (defthm pos-len-implies-fc
   (implies (< 0 (LEN LST))
            (consp lst))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (len) ())))))

(local
 (defthmd pp-lists-p-implies-true-listp
   (implies (pp-lists-p x)
            (true-listp x))))

(local
 (defthm bit-listp-of-sort-and$-list
   (implies (bit-listp (rp-evlt-lst lst a))
            (and (bit-listp (rp-evlt-lst (sort-and$-list LST size)
                                         a))))
   :hints (("Goal"
            :do-not-induct t
            :induct (sort-and$-list LST size)
            :in-theory (e/d (bit-listp
                             sort-and$-list
                             pp-lists-p-implies-true-listp
                             )
                            (bitp
                             +-IS-SUM
                             FLOOR2-IF-F2
                             floor))))))

;; MAIN LEMMA 2: sort-and$-list-is-correct
(local
 (defthm eval-of-list-to-term-of-sort-and$-list
   (implies (and (mult-formula-checks state)
                 (bit-listp (rp-evlt-lst lst a))
                 (true-listp lst)
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt
                    (pp-lists-to-term-and$
                     (sort-and$-list lst len))
                    a)
                   (rp-evlt (pp-lists-to-term-and$ lst) a)))
   :hints (("Goal"
            :do-not-induct t
            :induct (sort-and$-list lst len)
            :in-theory (e/d (sort-and$-list
                             )
                            (floor
                             +-IS-SUM
                             FLOOR2-IF-F2
                             (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                             (:DEFINITION TRUE-LISTP)
                             (:DEFINITION RP-TERMP)
                             (:DEFINITION RP-TERM-LISTP)
                             (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                             (:REWRITE PP-LISTS-P-IMPLIES-TRUE-LISTP)
                             (:DEFINITION PP-LISTS-P)
                             (:DEFINITION ACL2::APPLY$-BADGEP)
                             (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                             (:REWRITE IS-IF-RP-TERMP)
                             (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                             (:DEFINITION SUBSETP-EQUAL)
                             (:DEFINITION MEMBER-EQUAL)
                             (:REWRITE DEFAULT-CDR)
                             (:REWRITE RP-TERMP-CADR)
                             (:REWRITE IS-RP-PSEUDO-TERMP)
                             (:REWRITE RP-TERMP-CADDR)
                             (:REWRITE ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                             (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE ACL2::O-P-O-INFP-CAR)
                             (:TYPE-PRESCRIPTION RP-TERM-LISTP)
                             (:DEFINITION NATP)
                             (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 3)
                             (:TYPE-PRESCRIPTION MEMBER-EQUAL)
                             (:TYPE-PRESCRIPTION PP-LISTS-P)
                             len))))))

;; proofs with merge-sorted-pp-lists-simple are easier to work with
#|(local
 (define merge-sorted-pp-lists-simple
   ((first pp-lists-p)
    (second pp-lists-p))
   :measure
   (+ (acl2-count first)
      (acl2-count second))
   :returns
   (res pp-lists-p
        :hyp (and (pp-lists-p first)
                  (pp-lists-p second)))
   :verify-guards nil
   (cond
    ((atom first) second)
    ((atom second) first)
    (t
     (b*
         ((sign1 (caar first))
          (term1 (cdar first))
;(term1 (sort-and$-list term1 (len term1)))
          (sign2 (caar second))
          (term2 (cdar second))
          #|(term2 (sort-and$-list term2 (len term2)))||#)
       (cond
        ((and (not (equal sign1 sign2))
              (equal term1 term2))
         (merge-sorted-pp-lists-simple (cdr first) (cdr second)))
        ((pp-list-order term1 term2)
         (acons sign1 term1
                (merge-sorted-pp-lists-simple (cdr first) second)))
        (t (acons sign2 term2
                  (merge-sorted-pp-lists-simple first (cdr second))))))))
   ///

   (local
    (defthm lemma1
      (implies (consp first)
               (equal (merge-sorted-pp-lists
                       first
                       (cdr (car first)) #|(sort-and$-list (cdr (car first)) (len (cdr (car first))))||#
                       second sim2)
                      (merge-sorted-pp-lists first nil second sim2)))
      :hints (("goal"
               :do-not-induct t
               :expand ((merge-sorted-pp-lists
                         first
                         (cdr (car first)) #|(sort-and$-list (cdr (car first)) (len (cdr (car first))))||#
                         second sim2)
                        (merge-sorted-pp-lists first nil second sim2))
               :in-theory (e/d () ())))))

   (local
    (defthm lemma2
      (implies (consp second)
               (equal (merge-sorted-pp-lists
                       first
                       sim1
                       second
                       (cdr (car second)) #|(sort-and$-list (cdr (car second)) (len (cdr (car second))))||#)
                      (merge-sorted-pp-lists first sim1 second nil)))
      :hints (("goal"
               :do-not-induct t
               :expand ((merge-sorted-pp-lists
                         first
                         sim1
                         second
                         (cdr (car second)) #|(sort-and$-list (cdr (car second)) (len (cdr (car second))))||#)
                        (merge-sorted-pp-lists first sim1 second nil))
               :in-theory (e/d () ())))))

   (defthm merge-sorted-pp-lists_to_merge-sorted-pp-lists-simple
     (implies t
              (equal (merge-sorted-pp-lists first nil second nil)
                     (merge-sorted-pp-lists-simple first second)))
     :hints (("goal"
              :induct (merge-sorted-pp-lists-simple first second)
              :in-theory (e/d (merge-sorted-pp-lists
                               merge-sorted-pp-lists-simple
                               ) ()))))))||#

(local
 (encapsulate
   nil

   (define two-pp-list-cancel-each-other (lst1 lst2)
     :enabled t
     :hints (("Goal"
              :in-theory (e/d () (+-IS-SUM))))
     :verify-guards nil
     (if (or (atom lst1)
             (atom lst2))
         (and (atom lst1)
              (atom lst2))
       (and (not (equal (caar lst1)
                        (caar lst2)))
            (equal (cdar lst1) ;(SORT-AND$-LIST (cdar lst1) (len (cdar lst1)))
                   (cdar lst2) ;(SORT-AND$-LIST (cdar lst2) (len (cdar lst2)))
                   )
            (two-pp-list-cancel-each-other (cdr lst1)
                                           (cdr lst2)))))

   (defthm when-SORT-AND$-LIST-is-equal-with-opposite-signs
     (implies (and #|(EQUAL (SORT-AND$-LIST lst1 size1)
               (SORT-AND$-LIST lst2 size2))||#
               (equal lst1 lst2)
               (mult-formula-checks state)
               (rp-evl-meta-extract-global-facts)
               (bit-listp (rp-evlt-lst lst1 a))
               (bit-listp (rp-evlt-lst lst2 a))
               (true-listp lst1)
               (true-listp lst2))
              (and (equal (sum (RP-EVLT (pp-lists-to-term-and$ LST1)
                                        A)
                               (-- (RP-EVLT (pp-lists-to-term-and$ LST2)
                                            A)))
                          0)
                   (equal (sum (-- (RP-EVLT (pp-lists-to-term-and$ LST1)
                                            A))
                               (RP-EVLT (pp-lists-to-term-and$ LST2)
                                        A))
                          0)))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance eval-of-list-to-term-of-sort-and$-list
                               (lst lst1)
                               (len size1))
                    (:instance eval-of-list-to-term-of-sort-and$-list
                               (lst lst2)
                               (len size2)))
              :in-theory (e/d ()
                              (sum
                               eval-of-list-to-term-of-sort-and$-list
                               --)))))

   (defthm two-pp-list-cancel-each-other-implies
     (implies (and (two-pp-list-cancel-each-other lst1 lst2)
                   (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a))
                   (pp-lists-p lst1)
                   (pp-lists-p lst2))
              (equal (sum (RP-EVLT (PP-LISTS-TO-TERM-P+ LST1)
                                   A)
                          (RP-EVLT (PP-LISTS-TO-TERM-P+ LST2)
                                   A))
                     0))
     :hints (("Goal"
              :induct (two-pp-list-cancel-each-other lst1 lst2)
              :in-theory (e/d (PP-LISTS-TO-TERM-P+)
                              (sum
                               --)))))

   (defthm two-pp-list-cancel-each-other-implies-2
     (implies (and (two-pp-list-cancel-each-other lst1 lst2)
                   (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a))
                   (pp-lists-p lst1)
                   (pp-lists-p lst2))
              (equal (RP-EVLT (PP-LISTS-TO-TERM-P+
                               (merge-sorted-pp-lists
                                lst1 LST2))
                              A)
                     0))
     :hints (("Goal"
              :do-not-induct t
              :induct (two-pp-list-cancel-each-other lst1 lst2)
              :in-theory (e/d (PP-LISTS-TO-TERM-P+
                               merge-sorted-pp-lists)
                              (sum
                               --)))))

   (defthm atom-merge-sorted-pp-lists
     (equal (CONSP (merge-sorted-pp-lists LST1 lst2))
            (not (two-pp-list-cancel-each-other lst1 lst2)))
     :hints (("Goal"
              :do-not-induct t
              :induct (merge-sorted-pp-lists LST1 lst2)
              :in-theory (e/d (merge-sorted-pp-lists)
                              ()))))

   (defthm pp-sum-equals-2
     (implies (integerp a)
              (equal (equal a (sum x y a))
                     (equal (sum x y) 0)))
     :hints (("Goal"
              :in-theory (e/d (sum ifix)
                              (+-IS-SUM)))))

   (defthm eval-of-list-to-term-of-merge-sorted-pp-lists
     (implies (and (mult-formula-checks state)
                   (force (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a)))
                   (force (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a)))
                   (force (pp-lists-p lst1))
                   (force (pp-lists-p lst2))
                   (rp-evl-meta-extract-global-facts))
              (equal (rp-evlt
                      (pp-lists-to-term-p+
                       (merge-sorted-pp-lists lst1 lst2))
                      a)
                     (sum (rp-evlt (pp-lists-to-term-p+ lst1) a)
                          (rp-evlt (pp-lists-to-term-p+ lst2) a))))
     :hints (("Goal"
              :induct (merge-sorted-pp-lists lst1 lst2)
              :do-not-induct t
              :in-theory (e/d (;;pp-lists-to-term-and$
                               ;; for soem reason when this is enabled, the proof
                               ;; does too many case-splits.
                               merge-sorted-pp-lists)
                              (len
                               sum valid-sc
                               --
                               and$ or$
                               TWO-PP-LIST-CANCEL-EACH-OTHER
                               bitp
                               bit-listp
                               ;;PP-LISTS-P
;BIT-LIST-LISTP
                               true-listp)))
             ("Subgoal *1/5"
              :expand ((PP-LISTS-TO-TERM-P+ LST2)))
             ("Subgoal *1/4"
              :expand ((PP-LISTS-TO-TERM-P+ LST1)
                       (TWO-PP-LIST-CANCEL-EACH-OTHER NIL LST2)))
             ("Subgoal *1/3"
              :expand ((PP-LISTS-TO-TERM-P+ LST1)
                       (PP-LISTS-TO-TERM-P+ LST2)))))

   (defthm bit-list-list-of-merge-sorted-pp-lists
     (implies (and (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a)))
              (bit-list-listp (rp-evlt-lst-lst (strip-cdrs (merge-sorted-pp-lists LST1 lst2))
                                               a)))
     :hints (("Goal"
              :do-not-induct t
              :induct (merge-sorted-pp-lists LST1 lst2)
              :in-theory (e/d (bit-listp
                               bit-list-listp
                               merge-sorted-pp-lists)
                              (bitp
                               floor)))))))

(local
 (defthm cut-list-by-half-returns-pp-lists
   (implies (and (pp-lists-p lst)
                 (< size (len lst)))
            (and (pp-lists-p (mv-nth 0 (cut-list-by-half lst size)))
                 (pp-lists-p (mv-nth 1 (cut-list-by-half lst size)))))
   :hints (("Goal"
            :in-theory (e/d (cut-list-by-half) (+-IS-SUM))))))

(local
 (defthm bit-list-listp-of-sort-pp-lists
   (implies (and (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a))
                 (pp-lists-p lst))
            (bit-list-listp (rp-evlt-lst-lst (strip-cdrs (sort-pp-lists lst
                                                                        size))
                                             a)))
   :hints (("Goal"
            :do-not-induct t
            :induct (sort-pp-lists lst size)
            :in-theory (e/d (sort-pp-lists)
                            (floor
                             +-IS-SUM
                             FLOOR2-IF-F2))))))

(local
 (defthm eval-of-sort-pp-lists-is-correct
   (implies (and (mult-formula-checks state)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst) a))
                 (pp-lists-p lst)
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt (pp-lists-to-term-p+ (sort-pp-lists lst size)) a)
                   (rp-evlt (pp-lists-to-term-p+ lst) a)))
   :hints (("Goal"
            :do-not-induct t
            :induct (sort-pp-lists lst size)
            :in-theory (e/d (sort-pp-lists
                             len
                             PP-LISTS-TO-TERM-P+)
                            (floor
                             bitp
                             --
                             +-IS-SUM
                             FLOOR2-IF-F2
                             sum))))))

(local
 (defthm consp-of-apply-sign
   (equal (consp (apply-sign-to-pp-lists lst sign))
          (consp lst))
   :hints (("Goal"
            :in-theory (e/d (apply-sign-to-pp-lists) ())))))

(local
 (defthm len-of-apply-sign
   (equal (len (apply-sign-to-pp-lists lst sign))
          (len lst))
   :hints (("Goal"
            :in-theory (e/d (apply-sign-to-pp-lists len) ())))))

(local
 (defthm merge-sorted-pp-lists-simple-of-apply-sign
   (implies (and (pp-lists-p lst1)
                 (pp-lists-p lst2))
            (equal (merge-sorted-pp-lists (apply-sign-to-pp-lists lst1 sign)
                                          (apply-sign-to-pp-lists lst2 sign))
                   (apply-sign-to-pp-lists (merge-sorted-pp-lists lst1 lst2)
                                           sign)))
   :hints (("Goal"
            :induct (merge-sorted-pp-lists lst1 lst2)
            :do-not-induct t
            :in-theory (e/d (apply-sign-to-pp-lists
                             merge-sorted-pp-lists) ())))))

(local
 (defthmd merge-sorted-pp-lists-simple-of-apply-sign-reverse
   (implies (and (pp-lists-p lst1)
                 (pp-lists-p lst2))
            (equal (apply-sign-to-pp-lists (merge-sorted-pp-lists lst1 lst2)
                                           sign)
                   (merge-sorted-pp-lists (apply-sign-to-pp-lists lst1 sign)
                                          (apply-sign-to-pp-lists lst2 sign))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d () ())))))

(local
 (defthm merge-sorted-pp-lists-simple-of-apply-sign-2
   (implies (and (pp-lists-p lst1)
                 (pp-lists-p lst2)
                 (syntaxp (or (atom lst2)
                              (not (equal (car lst2) 'apply-sign-to-pp-lists)))))
            (equal (merge-sorted-pp-lists (apply-sign-to-pp-lists lst1 sign)
                                          lst2)
                   (apply-sign-to-pp-lists (merge-sorted-pp-lists
                                            lst1
                                            (apply-sign-to-pp-lists lst2 sign))
                                           sign)))
   :hints (("Goal"
;:induct (merge-sorted-pp-lists-simple lst1 lst2)
            :do-not-induct t
            :in-theory (e/d (merge-sorted-pp-lists-simple-of-apply-sign-reverse)
                            (merge-sorted-pp-lists-simple-of-apply-sign))))))

(local
 (defthm cut-list-by-half-of-signed-pp-lists-0
   (implies (and (pp-lists-p lst)
                 (< size (len lst)))
            (equal (mv-nth
                    0
                    (cut-list-by-half (apply-sign-to-pp-lists lst sign) size))
                   (apply-sign-to-pp-lists
                    (mv-nth 0
                            (cut-list-by-half lst size))
                    sign)))
   :hints (("Goal"
            :in-theory (e/d (cut-list-by-half
                             apply-sign-to-pp-lists)
                            (+-IS-SUM))))))

(local
 (defthm cut-list-by-half-of-signed-pp-lists-1
   (implies (and (pp-lists-p lst)
                 (< size (len lst)))
            (equal (mv-nth
                    1
                    (cut-list-by-half (apply-sign-to-pp-lists lst sign) size))
                   (apply-sign-to-pp-lists
                    (mv-nth 1
                            (cut-list-by-half lst size))
                    sign)))
   :hints (("Goal"
            :in-theory (e/d (cut-list-by-half
                             apply-sign-to-pp-lists)
                            (+-IS-SUM))))))

(local
 (defthm PP-LISTS-P-implies-fc
   (implies (PP-LISTS-P x)
            (IF (ATOM X)
                (EQ X NIL)
                (AND (CONSP (CAR X))
                     (BOOLEANP (CAAR X))
                     (TRUE-LISTP (CDAR X))
                     (PP-LISTS-P (CDR X)))))
   :rule-classes :forward-chaining))

(local
 (defthmd pos-len-is
   (equal (< 0 (LEN LST))
          (consp lst))
   :hints (("Goal"
            :in-theory (e/d (len)
                            (+-IS-SUM))))))

(local
 (encapsulate
   nil
   (local
    (defthm sort-pp-lists-of-apply-sign-dummy-lemma1
      (IMPLIES (AND (CONSP LST)
                    (CONSP (CDR LST))
                    (NOT (CONSP (CDDR LST)))
                    (PP-LISTS-P LST)
                    (CONSP (CADR LST))
                    (CAR (CADR LST)))
               (equal (EQUAL (CADR LST)
                             (CONS T (CDR (CADR LST))))
                      t))))

   (local
    (defthm sort-pp-lists-of-apply-sign-dummy-lemma2
      (IMPLIES (AND (CONSP (CDR LST))
                    (PP-LISTS-P LST)
                    (CAR (CADR LST)))
               (equal (EQUAL T (CAR (CADR LST)))
                      t))))

   (local
    (defthm sort-pp-lists-of-apply-sign-dummy-lemma3
      (IMPLIES (AND (CONSP LST)
                    (CONSP (CDR LST))
                    (PP-LISTS-P LST)
                    (NOT (CAR (CADR LST))))
               (equal (EQUAL (CADR LST)
                             (CONS NIL (CDR (CADR LST))))
                      t))))

   (local
    (defthm sort-pp-lists-of-apply-sign-dummy-lemma4
      (IMPLIES (AND (CONSP LST)
                    (CONSP (CDR LST))
                    (PP-LISTS-P LST)
                    (CAR (CADR LST)))
               (equal (EQUAL (CADR LST)
                             (CONS t (CDR (CADR LST))))
                      t))))

   (local
    (defthm  sort-pp-lists-of-apply-sign-dummy-lemma5
      (implies (and (consp lst)
                    (consp (cdr lst))
                    (not (consp (cddr lst)))
                    (equal (car (car lst)) (car (cadr lst)))
                    (pp-lists-p lst))
               (equal
                (equal (cadr lst)
                       (cons (car (car lst))
                             (cdr (cadr lst))))
                t))))

   (defthm sort-pp-lists-of-apply-sign
     (implies (and (pp-lists-p lst))
              (equal (sort-pp-lists (apply-sign-to-pp-lists lst sign) size)
                     (apply-sign-to-pp-lists (sort-pp-lists lst size)
                                             sign)))
     :otf-flg t
     :hints (("Goal"
              :induct (sort-pp-lists lst size)
              :do-not-induct t
              :in-theory (e/d (apply-sign-to-pp-lists
                               sort-pp-lists
                               pos-len-is)
                              (pp-lists-p
                               +-IS-SUM
                               floor
;xor
                               floor2-if-f2
                               merge-sorted-pp-lists-simple-of-apply-sign-2)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FLATTEN LEMMAS

(local
 (progn
   (defthm and$-pp-lists-aux-returns-bit-list-listp
     (implies (and (mult-formula-checks state)
                   (booleanp sign)
                   (bit-listp (rp-evlt-lst cur a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs acc) a))
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (strip-cdrs (and$-pp-lists-aux cur lst2 acc sign))
                                a)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists-aux cur lst2 acc sign)
              :in-theory (e/d (rp-evlt-lst-lst
                               and$-pp-lists
                               and$-pp-lists-aux
                               pp-term-to-pp-lists
                               bit-list-listp) ()))))

   (defthm and$-pp-lists-returns-bit-list-listp
     (implies (and (mult-formula-checks state)
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a))
                   (bit-list-listp (rp-evlt-lst-lst (strip-cdrs acc) a))
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (strip-cdrs (and$-pp-lists lst1 lst2 acc sign))
                                a)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists lst1 lst2 acc sign)
              :in-theory (e/d (rp-evlt-lst-lst
                               and$-pp-lists
                               and$-pp-lists-aux
                               pp-term-to-pp-lists
                               bit-list-listp) ()))))

   (defthm pp-term-to-pp-lists-returns-bit-list-listp
     (implies (and (mult-formula-checks state)
                   (pp-term-p term)
                   (booleanp sign)
                   (valid-sc term a)
                   (rp-evl-meta-extract-global-facts))
              (bit-list-listp
               (rp-evlt-lst-lst (strip-cdrs (pp-term-to-pp-lists term sign))
                                a)))
     :hints (("goal"
              :do-not-induct t
              :induct (pp-term-to-pp-lists term sign)
              :in-theory (e/d (rp-evlt-lst-lst
                               pp-term-to-pp-lists
                               bit-list-listp) ()))))))

(progn
  (local
   (defthm and$-pp-lists-aux-extract-acc
     (implies (and (syntaxp (not (equal acc ''nil))))
              (equal (and$-pp-lists-aux cur lst2 acc sign)
                     (append (and$-pp-lists-aux cur lst2 nil sign)
                             acc)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists-aux cur lst2 acc sign)
              :in-theory (e/d (and$-pp-lists-aux
                               and$-pp-lists)
                              (sum
                               --
                               ifix))))))

  (local
   (defthm and$-pp-lists-extract-acc
     (implies (and (syntaxp (not (equal acc ''nil)))
                   (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts))
              (equal (and$-pp-lists lst1 lst2 acc sign)
                     (append (and$-pp-lists lst1 lst2 nil sign)
                             acc)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists lst1 lst2 acc sign)
              :in-theory (e/d (pp-lists-to-term-p+
                               and$-pp-lists)
                              (sum
                               --
                               ifix))))))

  (local
   (defthm and$-pp-lists-aux-extract-sign-and-acc
     (implies (and (syntaxp (not (and (equal acc ''nil)
                                      (equal sign ''nil)))))
              (equal (and$-pp-lists-aux cur lst2 acc sign)
                     (append (apply-sign-to-pp-lists
                              (and$-pp-lists-aux cur lst2 nil nil)
                              sign)
                             acc)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists-aux cur lst2 acc sign)
              :in-theory (e/d (and$-pp-lists-aux
                               and$-pp-lists
                               APPLY-SIGN-TO-PP-LISTS)
                              (sum
                               --
                               ifix))))))

  (local
   (defthm and$-pp-lists-extract-sign-and-acc
     (implies (syntaxp (not (and (equal acc ''nil)
                                 (equal sign ''nil))))
              (equal (and$-pp-lists lst1 lst2 acc sign)
                     (append (apply-sign-to-pp-lists
                              (and$-pp-lists lst1 lst2 nil nil)
                              sign)
                             acc)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists lst1 lst2 acc sign)
              :in-theory (e/d (pp-lists-to-term-p+
                               APPLY-SIGN-TO-PP-LISTS
                               and$-pp-lists)
                              (sum
                               --
                               ifix))))))

  (local
   (defthm true-list-fix-of-apply-sign-to-pp-lists
     (equal (true-list-fix (apply-sign-to-pp-lists lst sign))
            (apply-sign-to-pp-lists lst sign))
     :hints (("Goal"
              :in-theory (e/d (apply-sign-to-pp-lists) ())))))

  (local
   (defthm and$-pp-lists-aux-of-applied-sign
     (implies (booleanp sign)
              (equal (and$-pp-lists-aux cur
                                        (apply-sign-to-pp-lists lst2 sign)
                                        acc cur-sign)
                     (append (apply-sign-to-pp-lists
                              (and$-pp-lists-aux cur lst2 nil cur-sign)
                              sign)
                             acc)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists-aux cur lst2 acc cur-sign)
              :in-theory (e/d (and$-pp-lists-aux
                               APPLY-SIGN-TO-PP-LISTS) ())))))

  (local
   (defthm and$-pp-lists-of-applied-with-same-sign
     (implies (booleanp sign)
              (equal (and$-pp-lists (apply-sign-to-pp-lists lst1 sign)
                                    (apply-sign-to-pp-lists lst2 sign)
                                    acc main-sign)
                     (and$-pp-lists lst1
                                    lst2
                                    acc main-sign)))
     :hints (("goal"
              :do-not-induct t
              :induct (and$-pp-lists lst1
                                     lst2
                                     acc main-sign)
              :in-theory (e/d (and$-pp-lists
                               APPLY-SIGN-TO-PP-LISTS)
                              ())))))

  (local
   (defthm pp-term-to-pp-lists-extract-sign-lemma-dummy-lemma
     (implies (and (EQUAL (APPLY-SIGN-TO-PP-LISTS x T) z)
                   (EQUAL (APPLY-SIGN-TO-PP-LISTS k T) m))
              (equal (and$-pp-lists z m acc main-sign)
                     (and$-pp-lists x
                                    k
                                    acc main-sign)))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (APPLY-SIGN-TO-PP-LISTS)
                              (and$-pp-lists
                               apply-sign-to-pp-lists
                               AND$-PP-LISTS-EXTRACT-SIGN-AND-ACC))))))

  (local
   (defthm pp-term-to-pp-lists-extract-sign-lemma-dummy-lemma-2
     (implies (and (EQUAL (PP-TERM-TO-PP-LISTS (cadr x) T)
                          (APPLY-SIGN-TO-PP-LISTS a T))
                   (EQUAL (PP-TERM-TO-PP-LISTS (caddr z) T)
                          (APPLY-SIGN-TO-PP-LISTS b T))
                   (pp-lists-p a)
                   (pp-lists-p b)
                   (pp-lists-p lst-x))
              (EQUAL
               (merge-sorted-pp-lists
                (merge-sorted-pp-lists (PP-TERM-TO-PP-LISTS (cadr x) T)
                                       (PP-TERM-TO-PP-LISTS (caddr z) T))
                lst-x)
               (APPLY-SIGN-TO-PP-LISTS
                (merge-sorted-pp-lists
                 (merge-sorted-pp-lists
                  a b)
                 (APPLY-SIGN-TO-PP-LISTS lst-x T))
                T)))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d ()
                              (and$-pp-lists
                               apply-sign-to-pp-lists
                               AND$-PP-LISTS-EXTRACT-SIGN-AND-ACC))))))

  (local
   (defthm pp-term-to-pp-lists-extract-sign-lemma-dummy-lemma-3
     (implies (and (EQUAL (PP-TERM-TO-PP-LISTS (cadr x) T)
                          (APPLY-SIGN-TO-PP-LISTS a T))
                   (pp-lists-p a)
                   (booleanp sign))
              (EQUAL
               (merge-sorted-pp-lists `((,sign '1))
                                      (PP-TERM-TO-PP-LISTS (CADR x) T))
               (APPLY-SIGN-TO-PP-LISTS (merge-sorted-pp-lists
                                        `((,(not sign) '1))
                                        a)
                                       T)))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (merge-sorted-pp-lists-simple-of-apply-sign-reverse)
                              (and$-pp-lists
                               merge-sorted-pp-lists-simple-of-apply-sign
                               apply-sign-to-pp-lists
                               AND$-PP-LISTS-EXTRACT-SIGN-AND-ACC))))))

  (local
   (defthm pp-term-to-pp-lists-extract-sign-lemma-dummy-lemma-4
     (implies (and (EQUAL (PP-TERM-TO-PP-LISTS (cadr x) nil)
                          (APPLY-SIGN-TO-PP-LISTS a T))
                   (pp-lists-p a))
              (EQUAL
               (merge-sorted-pp-lists `((t '1))
                                      (PP-TERM-TO-PP-LISTS (CADR x) nil))
               (APPLY-SIGN-TO-PP-LISTS (merge-sorted-pp-lists
                                        `((nil '1))
                                        a)
                                       T)))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (merge-sorted-pp-lists-simple-of-apply-sign-reverse)
                              (and$-pp-lists
                               merge-sorted-pp-lists-simple-of-apply-sign
                               apply-sign-to-pp-lists
                               AND$-PP-LISTS-EXTRACT-SIGN-AND-ACC))))))

  (local
   (defthmd pp-term-to-pp-lists-extract-sign-lemma
     (implies (and (booleanp sign)
                   (booleanp s2))
              (equal (pp-term-to-pp-lists term sign)
                     (apply-sign-to-pp-lists
                      (pp-term-to-pp-lists term (xor s2 sign))
                      s2)))
     :otf-flg t
     :hints (("goal"
              :do-not-induct t
              :induct (pp-term-to-pp-lists term sign)
              :in-theory (e/d (pp-term-to-pp-lists
                               APPLY-SIGN-TO-PP-LISTS)
                              (sum
                               --
                               ifix)))
             ("subgoal *1/2"
              :in-theory (e/d (pp-term-to-pp-lists)
                              (sum
                               and$-pp-lists-of-applied-with-same-sign
                               --
                               ifix))
              :use ((:instance and$-pp-lists-of-applied-with-same-sign
                               (lst1 (pp-term-to-pp-lists (cadr (ex-from-rp term))
                                                          t))
                               (lst2 (pp-term-to-pp-lists (caddr (ex-from-rp term))
                                                          t))
                               (sign t)
                               (acc nil)
                               (main-sign nil)))))))

  (local
   (defthm pp-term-to-pp-lists-extract-sign
     (implies (and (syntaxp (not (and (equal sign ''nil))))
                   (booleanp sign))
              (equal (pp-term-to-pp-lists term sign)
                     (apply-sign-to-pp-lists
                      (pp-term-to-pp-lists term nil)
                      sign)))
     :otf-flg t
     :hints (("goal"
              :do-not-induct t
              :use ((:instance pp-term-to-pp-lists-extract-sign-lemma
                               (s2 t)))
              :in-theory (e/d (APPLY-SIGN-TO-PP-LISTS)
                              (sum
                               --
                               ifix)))))))

(local
 (defthm and$-pp-lists-aux-is-correct-lemma-2
   (implies (and (bitp x)
                 (bitp (sum (-- x) y))
                 (not (bitp y))
                 (integerp y))
            (and (equal x 1)
                 (equal y 2)))
   :hints (("Goal"
            :in-theory (e/d (sum)
                            (+-IS-SUM))))
   :rule-classes :forward-chaining))

(local
 (defthm and$-pp-lists-aux-is-correct
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (pp-lists-p lst2)
                 (bit-listp (rp-evlt-lst cur a))
                 (true-listp cur)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a)))
            (equal (rp-evlt (pp-lists-to-term-p+ (and$-pp-lists-aux cur lst2 nil nil)) a)
                   (times$ (rp-evlt (pp-lists-to-term-and$ cur) a)
                           (rp-evlt (pp-lists-to-term-p+ lst2) a))))
   :hints (("goal"
            :induct (and$-pp-lists-aux cur lst2 nil nil)
            :do-not-induct t
            :expand (#|(pp-lists-to-term (cons (cons (car (car lst2))
                     (append cur (cdr (car lst2))))
                     (and$-pp-lists-aux cur (cdr lst2)
                     nil nil)))||#)
            :in-theory (e/d (and$-pp-lists-aux
                             pp-lists-to-term-p+
                             and$-is-times
                             pp-lists-to-term-and$)
                            (sum
                             binar-and-abs-is-and$-2
                             and$
                             times$
                             --
                             sum
                             ifix
                             bitp
                             true-listp))))))

(local
 (defthm and$-pp-lists-is-correct
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts)
                 (pp-lists-p lst1)
                 (pp-lists-p lst2)
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst2) a))
                 (bit-list-listp (rp-evlt-lst-lst (strip-cdrs lst1) a)))
            (equal (rp-evlt (pp-lists-to-term-p+ (and$-pp-lists lst1 lst2 nil nil)) a)
                   (times$ (rp-evlt (pp-lists-to-term-p+ lst1) a)
                           (rp-evlt (pp-lists-to-term-p+ lst2) a))))
   :hints (("goal"
            :induct (and$-pp-lists lst1 lst2 nil nol)
            :do-not-induct t
            :in-theory (e/d (pp-lists-to-term-p+
                             and$-is-times
                             pp-lists-to-term-and$
                             and$-pp-lists)
                            (sum
                             times$
                             binar-and-abs-is-and$-2
                             and$
                             --
                             bitp
                             true-listp))))))

;; MAIN LEMMA1.
(defthm rp-evlt_of_pp-lists-to-term_of_pp-term-to-pp-lists
  (implies (and (mult-formula-checks state)
                (pp-term-p term)
                (booleanp sign)
                (valid-sc term a)
                (rp-evl-meta-extract-global-facts))
           (equal (rp-evlt (pp-lists-to-term-p+
                            (pp-term-to-pp-lists term sign))
                           a)
                  (if sign
                      (-- (rp-evlt term a))
                    (rp-evlt term a))))
  :hints (("goal"
           :do-not-induct t
           :induct (pp-term-to-pp-lists term sign)
           :in-theory (e/d (pp-term-to-pp-lists
                            not$-to-pp-sum
                            or$-to-pp-sum
                            binary-xor-to-pp-sum
                            binary-?-to-pp-sum
                            ---of-pp-sum
                            pp-lists-to-term-and$
                            pp-lists-to-term-p+
                            APPLY-SIGN-TO-PP-LISTS
                            len)
                           (--
                            sum
                            valid-sc
                            and$
                            bitp
                            or$
                            ifix
                            (:REWRITE VALID-SC-EX-FROM-RP-2)
                            (:DEFINITION EVAL-AND-ALL)
                            valid-sc
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE DEFAULT-CDR)
                            (:DEFINITION RP-TERMP)
                            (:TYPE-PRESCRIPTION VALID-SC)
                            (:META ACL2::MV-NTH-CONS-META)
                            (:REWRITE PP-LISTS-P-IMPLIES-TRUE-LISTP)
                            (:REWRITE DEFAULT-CAR)
                            integerp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; :i-am-here

(local
 (defthm PP-LISTS-TO-TERM-AND$-redef
   (implies (and (mult-formula-checks state)
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt (PP-LISTS-TO-TERM-AND$ lst) a)
                   (and-list (rp-evlt `(list . ,lst) a))))
   :hints (("Goal"
            :induct (PP-LISTS-TO-TERM-AND$ lst)
            :do-not-induct t
            :expand ((:free (x y)
                            (RP-EVL-OF-TRANS-LIST (cons x y) a)))
            :in-theory (e/d (PP-LISTS-TO-TERM-AND$
                             and-list)
                            ())))))

(local
 (defthm pp-lists-to-term-p+-to-pp-lists-to-term-pp-lst
   (implies (and (mult-formula-checks state)
                 (pp-lists-p lst)
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt (pp-lists-to-term-p+ lst) a)
                   (rp-evlt `(sum-list (list . ,(pp-lists-to-term-pp-lst lst))) a)))
   :hints (("Goal"
            :do-not-induct t
            :expand ((RP-EVL-OF-TRANS-LIST NIL A)
                     (:free (x y) (RP-EVL-OF-TRANS-LIST (cons x y) a))
                     (:free (x y) (and-list (cons x y))))
            :induct (pp-lists-to-term-p+ lst)
            :in-theory (e/d (pp-lists-to-term-p+
                             pp-lists-to-term-pp-lst) ())))))

(local
 (defthm pp-lists-to-term-pp-lst_of_pp-term-to-pp-lists
   (implies (and (mult-formula-checks state)
                 (pp-term-p term)
                 (booleanp sign)
                 (valid-sc term a)
                 (rp-evl-meta-extract-global-facts))
            (equal (rp-evlt `(sum-list (list . ,(pp-lists-to-term-pp-lst
                                                 (pp-term-to-pp-lists term sign))))
                            a)
                   (if sign
                       (-- (rp-evlt term a))
                     (rp-evlt term a))))
   :hints (("goal"
            :do-not-induct t
            :use ((:instance rp-evlt_of_pp-lists-to-term_of_pp-term-to-pp-lists))
            :in-theory (e/d ()
                            (--
                             rp-evlt_of_pp-lists-to-term_of_pp-term-to-pp-lists
                             sum
                             valid-sc
                             and$
                             bitp
                             or$
                             ifix
                             (:REWRITE VALID-SC-EX-FROM-RP-2)
                             (:DEFINITION EVAL-AND-ALL)
                             valid-sc
                             (:REWRITE ACL2::O-P-O-INFP-CAR)
                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION RP-TERMP)
                             (:TYPE-PRESCRIPTION VALID-SC)
                             (:META ACL2::MV-NTH-CONS-META)
                             (:REWRITE PP-LISTS-P-IMPLIES-TRUE-LISTP)
                             (:REWRITE DEFAULT-CAR)
                             integerp))))))

;; A MAIN LEMMA
(defthm pp-flatten-correct
  (implies (and (mult-formula-checks state)
                (pp-term-p term)
                (booleanp sign)
                (valid-sc term a)
                (rp-evl-meta-extract-global-facts))
           (and (equal (rp-evlt `(sum-list ,(pp-flatten term sign)) a)
                       (if sign
                           (-- (rp-evlt term a))
                         (rp-evlt term a)))
                (equal (sum-list (rp-evlt (pp-flatten term sign) a))
                       (if sign
                           (-- (rp-evlt term a))
                         (rp-evlt term a)))
                ))
  :hints (("Goal"
           :do-not-induct t
           :expand ((RP-EVL-OF-TRANS-LIST NIL A))
           :use ((:instance pp-lists-to-term-pp-lst_of_pp-term-to-pp-lists))
           :in-theory (e/d (pp-flatten)
                           (pp-lists-to-term-pp-lst_of_pp-term-to-pp-lists
                            PP-TERM-P
                            ;;RP-TRANS
                            VALID-SC
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:DEFINITION IS-SYNP$INLINE)
                            (:REWRITE NOT-INCLUDE-RP)
                            (:DEFINITION RP-TERMP)
                            ;;RP-TRANS-LST
                            )))))

(progn

  (create-regular-eval-lemma bit-of 2 mult-formula-checks)
  (create-regular-eval-lemma ifix 1 mult-formula-checks)
  (create-regular-eval-lemma binary-and 2 mult-formula-checks)
  (create-regular-eval-lemma binary-sum 2 mult-formula-checks)

  (defthm valid-rp-bitp-lemma
    (implies (and (mult-formula-checks state)
                  (valid-sc term a)
                  (rp-evl-meta-extract-global-facts)
                  (case-match term (('rp ''bitp &) t)))
             (and (bitp (rp-evlt (caddr term) a))
                  (bitp (rp-evlt term a))))
    :hints (("Goal"
             :in-theory (e/d (is-rp
                              valid-sc-single-step
                              is-if)
                             (valid-sc)))))

  (defthm bitp-of-bits-of-term-with-ex-from-rp
    (implies (and (mult-formula-checks state)
                  (rp-evl-meta-extract-global-facts)
                  (b* ((term (ex-from-rp term)))
                    (case-match term (('bit-of & &) t))))
             (and (bitp (rp-evlt term a))
                  (bitp (rp-evl term a))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance rp-evlt-of-ex-from-rp)
                   (:instance rp-evl-of-ex-from-rp))
             :in-theory (e/d (is-rp
                              is-if)
                             (valid-sc
                              rp-evl-of-ex-from-rp
                              EVL-OF-EXTRACT-FROM-RP
                              rp-evlt-of-ex-from-rp)))))

  
  (local
   (defthm SORT-SUM-META-AUX-returns-bit-list-listp
     (implies (and (MV-NTH 0 (SORT-SUM-META-AUX term))
                   (mult-formula-checks state)
                   (valid-sc term a)
                   (rp-evl-meta-extract-global-facts))
              (BIT-LIST-LISTP
               (RP-EVLT-LST-LST (STRIP-CDRS (MV-NTH 1 (SORT-SUM-META-AUX term)))
                                A)))
     :hints (("Goal"
              :induct (SORT-SUM-META-AUX term)
              :do-not-induct t
              :expand ((RP-TRANS-LST (CDR TERM))
                       (RP-TRANS-LST (CDdR TERM))
                       (RP-TRANS-LST (CDddR TERM)))
              :in-theory (e/d (SORT-SUM-META-AUX)
                              (bitp
                               valid-sc
                               rp-trans))))))

  (local
   (defthm valid-sort-sum-meta-aux-is-integerp
     (implies (and (mult-formula-checks state)
                   (rp-evl-meta-extract-global-facts)
                   (MV-NTH 0 (SORT-SUM-META-AUX term)))
              (integerp (rp-evlt term a)))
     :hints (("Goal"
              :in-theory (e/d (SORT-SUM-META-AUX) ())))))


  (defthm PP-LISTS-TO-TERM-P+-SORT-SUM-META-AUX
    (implies (and (mult-formula-checks state)
                  (valid-sc term a)
                  (rp-evl-meta-extract-global-facts)
                  (MV-NTH 0 (SORT-SUM-META-AUX term)))
             (EQUAL
              (rp-evlt (pp-lists-to-term-p+ (mv-nth 1 (sort-sum-meta-aux term))) a)
              (rp-evlt term A)))
    :hints (("Goal"
             :induct (MV-NTH 1 (SORT-SUM-META-AUX term))
             :do-not-induct t
             :Expand ((true-listp (cdr term))
                      (RP-TRANS-LST (CDR TERM))
                      (RP-TRANS-LST (CDdR TERM)))
             ;; :expand ((SORT-AND$-LIST (CDR TERM) 2)
             ;;          (SORT-AND$-LIST (CDR (CADR TERM)) 2))
             :in-theory (e/d (SORT-SUM-META-AUX
                              rp-evlt-of-ex-from-rp
;ifix-bit-fix-equiv
                              is-if is-rp context-from-rp eval-and-all
                              true-listp
                              PP-LISTS-TO-TERM-P+)
                             (PP-LISTS-TO-TERM-AND$-REDEF
                              (:DEFINITION EX-FROM-RP)
                              (:REWRITE VALID-SC-CADR)
                              (:REWRITE VALID-SC-CADDR)
                              (:DEFINITION EVAL-AND-ALL)
                              (:REWRITE DEFAULT-CDR)
                              (:REWRITE DEFAULT-CAR)
                              (:REWRITE ACL2::O-P-O-INFP-CAR)
                              (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                              (:DEFINITION RP-TRANS)
                              (:REWRITE ATOM-RP-TERMP-IS-SYMBOLP)
                              (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                              (:REWRITE EVAL-OF-BIT-OF)
                              (:REWRITE EVAL-OF-BINARY-XOR)
                              (:REWRITE EVAL-OF-BINARY-OR)
                              (:DEFINITION INCLUDE-FNC)
                              (:DEFINITION RP-TERMP)
                              VALID-SC-EX-FROM-RP-2
                              rp-evl-of-ex-from-rp-reverse
                              bitp
                              PP-LISTS-TO-TERM-P+-TO-PP-LISTS-TO-TERM-PP-LST)))))

  ;; A MAIN LEMMA
  (defthm sort-sum-meta-correct
    (implies (and (mult-formula-checks state)
                  (rp-evl-meta-extract-global-facts)
                  (valid-sc term a))
             (equal (rp-evlt (mv-nth 0 (sort-sum-meta term)) a)
                    (rp-evlt term a)))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance pp-lists-to-term-p+-to-pp-lists-to-term-pp-lst
                              (lst (SORT-PP-LISTS (MV-NTH 1 (SORT-SUM-META-AUX (CADR TERM)))
                                                  (LEN (MV-NTH 1
                                                               (SORT-SUM-META-AUX (CADR TERM)))))))
                   (:instance EVAL-OF-SORT-PP-LISTS-IS-CORRECT
                              (lst (MV-NTH 1 (SORT-SUM-META-AUX (CADR TERM))))
                              (size (LEN (MV-NTH 1 (SORT-SUM-META-AUX (CADR TERM)))))))
             :in-theory (e/d (sort-sum-meta
                              SORT-SUM
                              )
                             (pp-lists-to-term-p+-to-pp-lists-to-term-pp-lst
                              PP-LISTS-TO-TERM-AND$-REDEF
                              EVAL-OF-SORT-PP-LISTS-IS-CORRECT)))))

  (defthm sort-sum-meta-valid-rp-meta-rulep-local
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (mult-formula-checks state))
             (let ((rule (make rp-meta-rule-rec
                               :fnc 'sort-sum-meta
                               :trig-fnc 'sort-sum
                               :dont-rw t
                               :valid-syntax t)))
               (and (valid-rp-meta-rulep rule state)
                    (rp-meta-valid-syntaxp-sk rule state))))
    :otf-flg t
    :hints (("Goal"
             :in-theory (e/d (rp-meta-valid-syntaxp)
                             (rp-termp
                              rp-term-listp
                              valid-sc))))))

#|(defthm eval-of-sort-pp-flatten-main-is-correct
(implies (and (mult-formula-checks state)
(valid-sc term a)
(rp-evl-meta-extract-global-facts))
(equal (rp-evlt (flatten-pp-main term) a)
(rp-evlt term a)))
:hints (("Goal"
:do-not-induct t
:in-theory (e/d (flatten-pp-main
eval-of---1)
(floor
pp-term-p
bitp
EVAL-OF----
--
sum)))))||#
