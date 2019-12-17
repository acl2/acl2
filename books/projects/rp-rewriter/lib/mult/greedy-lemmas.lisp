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

;(include-book "macros")

;; LEmmas that are used to prove meta functions and rewrite rules to be used
;; during multiplier proofs.
;; This book is not to be included while doing multiplier proofs.

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5))

(defthm all-sums-is-sum
  (and (equal (pp-sum a b)
              (sum a b))
       (equal (merge-sum a b)
              (sum a b))
       (equal (merge-pp-sum a b)
              (sum a b)))
  :hints (("Goal"
           :in-theory (e/d (pp-sum
                            merge-sum
                            merge-pp-sum
                            sum
                            type-fix) ()))))

(defthm m2-new-is-m2
  (equal (m2-new a)
         (m2 a))
  :hints (("Goal"
           :in-theory (e/d (m2-new) ()))))

(defthm f2-new-is-f2
  (equal (f2-new a)
         (f2 a))
  :hints (("Goal"
           :in-theory (e/d (f2-new) ()))))

(defthm d2-new-is-d2
  (equal (d2-new a)
         (d2 a))
  :hints (("Goal"
           :in-theory (e/d (f2-new) ()))))

(defthm sum-of-single-element
  (and (equal (sum a 0)
              (type-fix a))
       (equal (sum 0 a)
              (type-fix a)))
  :hints (("Goal"
           :in-theory (e/d (sum type-fix) ()))))

(defthm type-fix-of-functions
  (and (equal (type-fix (sum a b))
              (sum a b))
       (equal (type-fix (m2 a))
              (m2 a))
       (equal (type-fix (f2 a))
              (f2 a))
       (equal (type-fix (-- a))
              (-- a)))
  :hints (("Goal"
           :in-theory (e/d (sum type-fix
                                m2
                                f2
                                sum) ()))))

(defthm functions-of-type-fix
  (and (equal (f2 (type-fix a))
              (f2 a))
       (equal (m2 (type-fix a))
              (m2 a))
       (equal (d2 (type-fix a))
              (d2 a))
       (equal (-- (type-fix a))
              (-- a))
       (equal (sum (type-fix a) b)
              (sum a b))
       (equal (sum a (type-fix b))
              (sum a b))
       (equal (evenp2 (type-fix b))
              (evenp2 b)))
  :hints (("Goal"
           :in-theory (e/d (evenp2 sum f2 -- m2 type-fix)
                           (evenp)))))

(local
 (use-arithmetic-5 t))

(defthm f2-of-repeated-terms-1
  (implies t
           (equal (c a a b)
                  (merge-sum a (f2 (merge-sum b)))))
  :hints (("Goal"
           :do-not '(preprocess)
           :in-theory (e/d (merge-sum
                            f2
                            b+
                            type-fix
                            times2)
                           ()))))

(encapsulate
  nil

  (defthm f2-of-repeated-terms-2
    (implies t
             (equal (c a a)
                    (type-fix a)))
    :hints (("Goal"
             :do-not '(preprocess)
             :in-theory (e/d (merge-sum
                              f2
                              b+
                              type-fix
                              times2)
                             ()))))

  (local
   (defthmd f2-of-minus-lemma1
     (equal (c (-- a) b)
            (f2 (sum (-- a) (-- a) a b)))
     :hints (("Goal"
              :in-theory (e/d (sum minus -- type-fix
                                   times2) ())))))

  (defthm f2-of-minus
    (equal (c (-- a) b)
           (merge-sum (-- a) (f2 (merge-sum a b))))
    :hints (("Goal"
             :use ((:instance f2-of-minus-lemma1))
             :in-theory (e/d () (f2 -- sum)))))

  (defthm f2-of-minus-2
    (equal (f2 (-- a))
           (merge-sum (-- a) (f2 a)))
    :hints (("Goal"
             :use ((:instance f2-of-minus
                              (b 0)))
             :in-theory (e/d (f2
                              type-fix
                              --)
                             (f2-of-minus))))))

(defthm sum-comm-1-with-loop-stopper
  (equal (sum b a)
         (sum a b))
  :hints (("Goal"
           :in-theory (e/d (sum) ()))))

(defthm sum-comm-2-with-loop-stopper
  (equal (sum b a c)
         (sum a b c))
  :hints (("Goal"
           :in-theory (e/d (sum) ()))))

(defthm sum-reorder
  (equal (sum (sum a b) c)
         (sum a b c))
  :hints (("Goal"
           :in-theory (e/d (sum type-fix) ()))))

(defthmd push-elements-into-f2
  (equal (sum a (f2 b))
         (f2 (sum a a b)))
  :hints (("Goal"
           :in-theory (e/d (sum f2 type-fix) ()))))

(defthmd push-elements-into-d2
  (equal (sum a (d2 b))
         (d2 (sum a a b)))
  :hints (("Goal"
           :in-theory (e/d (sum d2 type-fix) ()))))

(add-invisible-fns b+ --)

(defthm sum-and--
  (and (equal (sum (-- a) a b)
              (type-fix b))
       (equal (sum a (-- a) b)
              (type-fix b))
       (equal (sum a (-- a))
              0)
       (equal (sum (-- a) a)
              0))
  :hints (("Goal"
           :in-theory (e/d (sum --) ()))))

(defthm type-of-functions
  (and (type-p   (-- a))
       (integerp (-- a))
       (type-p   (f2 a))
       (integerp (f2 a))
       (type-p   (m2 a))
       (integerp (m2 a))
       (type-p   (sum a b))
       (integerp (sum a b)))
  :hints (("Goal"
           :in-theory (e/d (sum m2 f2 -- type-p
                                type-fix) ()))))

(defthm sum-of-the-same-var
  (and (equal (equal (sum a b)
                     (sum a c))
              (equal (type-fix b)
                     (type-fix c)))
       (equal (equal (sum b a)
                     (sum c a))
              (equal (type-fix b)
                     (type-fix c))))
  :hints (("Goal"
           :in-theory (e/d (sum type-fix) ()))))
(defthm --of--
  (equal (-- (-- a))
         (type-fix a))
  :hints (("Goal"
           :in-theory (e/d (-- type-fix) ()))))


(local
 (defthmd m2-of-neg-lemma
   (and (equal (s (-- a) b)
               (m2 (sum (-- a) (-- a) a b)))
        (equal (m2 (-- a))
               (m2 (sum (-- a) (-- a) a))))
   :hints (("Goal"
            :in-theory (e/d (sum  -- type-fix ) ())))))

(defthm m2-sum-of-repeated-vars
  (and (equal (m2 (sum a a b))
              (m2 b))
       (equal (m2 (sum a a))
              0))
  :hints (("Goal"
           :in-theory (e/d (m2 sum
                               type-fix) ()))))

(defthm m2-of-neg
  (and (equal (m2 (sum (-- a) b))
              (m2 (sum a b)))
       (equal (m2 (-- a))
              (m2 a)))
  :hints (("Goal"
           :use ((:instance m2-of-neg-lemma))
           :in-theory (e/d ()
                           (type-fix
                            m2
                            SUM-AND--
                            --
                            sum
                            (:type-prescription --))))))

(defthm m2-sum-of-single-var
  (equal (m2 (sum a 0))
         (m2 a))
  :hints (("Goal"
           :in-theory (e/d (m2 sum type-fix) ()))))

(defthm m2-of-m2
  (and (equal (m2 (m2 a))
              (m2 a))
       (equal (m2 (sum (m2 a) b))
              (m2 (sum a b))))
  :hints (("Goal"
           :in-theory (e/d (m2 sum type-fix) ()))))


(defthm sum-of-var-and-0
  (equal (sum a 0)
         (type-fix a))
  :hints (("Goal"
           :in-theory (e/d (sum type-fix) ()))))

(defthmd m2-when-not-type-p
  (implies (not (type-p x))
           (equal (m2 x) 0))
  :hints (("Goal"
           :in-theory (e/d (type-p m2) ()))))

(defthmd f2-when-not-type-p
  (implies (not (type-p x))
           (equal (f2 x) 0))
  :hints (("Goal"
           :in-theory (e/d (type-p f2) ()))))



(defthm evenp2-of-repeated-vars
  (and (equal (evenp2 (sum a a b))
              (evenp2 b))
       (equal (evenp2 (sum b a a))
              (evenp2 b)))
  :hints (("Goal"
           :in-theory (e/d (evenp2 sum type-fix)
                           ()))))
