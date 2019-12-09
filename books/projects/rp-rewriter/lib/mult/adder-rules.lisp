; ADDER RULEs - lemmas to prove ppx adders correct

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

(include-book "meta/adder-rules-meta")

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5))

(def-rp-rule$ t t
  and$-is-adder-and$
  (equal (and$ a b)
         (merge-adder-and a b))
  :hints (("Goal"
           :in-theory (e/d (adder-and$
                            merge-adder-and) ()))))

(def-rp-rule$ t t
  or$-is-adder-or$
  (equal (or$ a b)
         (adder-or$ a b))
  :hints (("Goal"
           :in-theory (e/d (adder-or$) ()))))

(local
 (in-theory (enable merge-adder-sum)))

(def-rp-rule$ t t sum-is-adder-b+
  (equal (sum a b)
         (merge-adder-b+ a b))
  :hints (("Goal"
           :in-theory (e/d (sum adder-b+
                                merge-adder-b+) ()))))

(def-rp-rule$ t t
  pp-sum-is-adder-b+
  (equal (pp-sum a b)
         (merge-adder-b+ a b))
  :hints (("Goal"
           :in-theory (e/d (pp-sum sum adder-b+
                                   merge-adder-b+) ()))))

(def-rp-rule$ t t
  merge-pp-sum-is-adder-b+
  (equal (merge-pp-sum a b)
         (merge-adder-b+ a b))
  :hints (("Goal"
           :in-theory (e/d (pp-sum sum adder-b+
                                   merge-adder-b+
                                   merge-pp-sum) ()))))

(def-rp-rule$ t t
  merge-sum-is-adder-b+
  (equal (merge-sum a b)
         (merge-adder-b+ a b))
  :hints (("Goal"
           :in-theory (e/d (pp-sum sum adder-b+
                                   merge-adder-b+
                                   merge-pp-sum) ()))))

(def-rp-rule$ t t
  pp-sum-is-adder-b+-2
  (and (equal (m2 (pp-sum a b))
              (m2 (merge-adder-b+ a b)))
       (equal (f2 (pp-sum a b))
              (f2 (merge-adder-b+ a b))))
  :hints (("Goal"
           :in-theory (e/d (pp-sum sum adder-b+
                                   merge-adder-b+) ()))))

(def-rp-rule$ t t
  adder-sum-comm1
  (implies (syntaxp (adder-sum-order a b))
           (equal (adder-b+ b a)
                  (adder-b+ a b)))
  :hints (("Goal"
           :in-theory (e/d (adder-b+ sum type-fix) ()))))

(def-rp-rule$ t t
  adder-sum-comm2
  (implies (syntaxp (adder-sum-order a b))
           (equal (adder-b+ b (adder-b+ a c))
                  (adder-b+ a (adder-b+ b c))))
  :hints (("Goal"
           :in-theory (e/d (adder-b+ sum type-fix) ()))))

(def-rp-rule$ t t
  adder-sum-reorder
  (implies t
           (equal (adder-b+ (adder-b+ a b) c)
                  (adder-b+ a (adder-b+ b c))))
  :hints (("Goal"
           :in-theory (e/d (adder-b+ sum type-fix) ()))))

(def-rp-rule$ t t
  adder-adder-and-comm1
  (implies (syntaxp (and (adder-and$-order a b)))
           (equal (adder-and b a)
                  (adder-and a b)))
  :hints (("Goal"
           :in-theory (e/d (adder-and and$) ()))))

(def-rp-rule$ t t
  adder-adder-and-comm2
  (implies (syntaxp (adder-and$-order a b))
           (equal (adder-and b (adder-and a c))
                  (adder-and a (adder-and b c))))
  :hints (("Goal"
           :in-theory (e/d (adder-and and$) ()))))

(def-rp-rule$ t t
  b-and-reorder
  (equal (adder-and (adder-and a b) c)
         (adder-and a (adder-and b c)))
  :hints (("Goal"
           :in-theory (e/d (adder-and
                            and$) ()))))

(def-rp-rule$ t t
  b-or-comm1
  (implies (syntaxp (adder-or$-order a b))
           (equal (adder-or b a)
                  (adder-or a b)))
  :hints (("Goal"
           :in-theory (e/d (adder-or
                            or$) ()))))

(def-rp-rule$ t t
  b-or-comm2
  (implies (syntaxp (adder-or$-order a b))
           (equal (adder-or b (adder-or a c))
                  (adder-or a (adder-or b c))))
  :hints (("Goal"
           :in-theory (e/d (adder-or
                            or$) ()))))

(def-rp-rule$ t t
  b-or-reorder
  (equal (adder-or (adder-or a b) c)
         (adder-or a (adder-or b c)))
  :hints (("Goal"
           :in-theory (e/d (adder-or or$) ()))))

(local
 (defthm merge-adder-sum-is-adder-sum
   (equal (merge-adder-b+ x y)
          (adder-sum x y))
   :hints (("Goal"
            :do-not '(preprocess generalize fertilize)
            :expand (merge-adder-b+ x y)
            :in-theory (e/d ()
                            (merge-adder-sum
                             adder-sum))))))

#|(progn
  (def-rp-rule$ t t
    binary-not-to-adder-sum
    (implies (bitp a)
             (equal (binary-not a)
                    (merge-adder-sum (-- a) 1)))
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (defthmd binary-not-to-adder-sum-side-cond
    (implies (bitp a)
             (bitp (merge-adder-sum (-- a) 1))))

  (rp-attach-sc binary-not-to-adder-sum
                binary-not-to-adder-sum-side-cond)

  (def-rp-rule$ t t
    m2-of-adder-sum-1
    (equal (m2 (adder-sum 1 rest))
           (merge-adder-sum 1 (-- (m2 rest))))
    :hints (("Goal"
             :in-theory (e/d (adder-sum m2 type-fix sum --) ()))))

  (defthmd m2-of-adder-sum-1-side-cond
    (bitp (m2 rest)))

  (rp-attach-sc m2-of-adder-sum-1
                m2-of-adder-sum-1-side-cond)

  (def-rp-rule$ t t
    adder-and-of-subtracted
    (implies (and (bitp a)
                  (bitp x)
                  (bitp y)
                  (bitp (adder-sum x (-- y))))
             (and (equal (adder-and a (adder-sum x (-- y)))
                         (merge-adder-sum  (merge-adder-and a x) (-- (merge-adder-and a y))))
                  (equal (adder-and (adder-sum x (-- y)) a)
                         (merge-adder-sum  (merge-adder-and a x) (-- (merge-adder-and a y))))))
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule$ t t
    adder-and-of-subtracted-2
    (implies (and (bitp a)
                  (bitp x)
                  (bitp y)
                  (bitp (adder-sum (-- y) x)))
             (and (equal (adder-and a (adder-sum (-- y) x))
                         (merge-adder-sum  (merge-adder-and a x) (-- (merge-adder-and a y))))
                  (equal (adder-and (adder-sum (-- y) x) a)
                         (merge-adder-sum  (merge-adder-and a x) (-- (merge-adder-and a y))))))
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (defthmd adder-and-of-subtracted-side-cond
    (implies (and (bitp a)
                  (bitp x)
                  (bitp y)
                  (bitp (adder-sum x (-- y))))
             (and (bitp (merge-adder-sum  (merge-adder-and a x) (-- (merge-adder-and a
                                                                         y)))))))

  (defthmd adder-and-of-subtracted-2-side-cond
    (implies (and (bitp a)
                  (bitp x)
                  (bitp y)
                  (bitp (adder-sum (-- y) x)))
             (and (bitp (merge-adder-sum  (merge-adder-and a x) (-- (merge-adder-and a
                                                                         y)))))))

  (rp-attach-sc adder-and-of-subtracted
                adder-and-of-subtracted-side-cond)

  (rp-attach-sc adder-and-of-subtracted-2
                adder-and-of-subtracted-2-side-cond))||#


  ;; (def-rp-rule$ t t
  ;;   adder-or-of-subtracted
  ;;   (implies (and (bitp a)
  ;;                 (bitp x)
  ;;                 (bitp y)
  ;;                 (bitp (adder-sum x (-- y))))
  ;;            (and (equal (adder-or a (adder-sum x (-- y)))
  ;;                        (merge-adder-sum  (adder-or a x) (-- (adder-or a y))))
  ;;                 (equal (adder-or (adder-sum x (-- y)) a)
  ;;                        (merge-adder-sum  (adder-or a x) (-- (adder-or a y))))))
  ;;   :hints (("Goal"
  ;;            :in-theory (e/d (bitp) ()))))

  ;; (defthmd adder-or-of-subtracted-side-cond
  ;;   (implies (and (bitp a)
  ;;                 (bitp x)
  ;;                 (bitp y)
  ;;                 (bitp (adder-sum x (-- y))))
  ;;            (and (bitp (merge-adder-sum  (adder-or a x) (-- (adder-or a
  ;;                                                                      y)))))))

  ;; (def-rp-rule$ t t
  ;;   adder-or-of-subtracted-2
  ;;   (implies (and (bitp a)
  ;;                 (bitp x)
  ;;                 (bitp y)
  ;;                 (bitp (adder-sum (-- y) x)))
  ;;            (and (equal (adder-or a (adder-sum (-- y) x))
  ;;                        (merge-adder-sum  (adder-or a x) (-- (adder-or a y))))
  ;;                 (equal (adder-or (adder-sum (-- y) x) a)
  ;;                        (merge-adder-sum  (adder-or a x) (-- (adder-or a y))))))
  ;;   :hints (("Goal"
  ;;            :in-theory (e/d (bitp) ()))))

(def-rp-rule$ t t
  bin-xor-is-s
  (implies (and (bitp a)
                #|(syntaxp (and (equal (car a) '[])
                (equal (car b) '[])))||#
                (bitp b)
                )
           (equal (binary-xor a b)
                  (m2 (merge-adder-b+ a b))))
  :hints (("Goal"
           :in-theory (e/d (binary-xor
                            booleanp
                            m2
                            bitp
                            m2
                            b+
                            type-fix) ()))))
(defthmd
  bin-xor-is-s-sc
  (implies (and (bitp a)
                (bitp b))
           (bitp (m2 (merge-adder-sum a b))))
  :hints (("Goal"
           :in-theory (e/d (booleanp) ()))))

(rp-attach-sc bin-xor-is-s
              bin-xor-is-s-sc)

(def-rp-rule$ t t
  bin-and-is-c
  (implies (and (bitp a)
                (syntaxp (and (equal (car a) '[])
                              (equal (car b) '[])))
                (bitp b))
           (equal (adder-and a b)
                  (f2 (merge-adder-sum a b))))
  :hints (("Goal"
           :in-theory (e/d (f2
                            adder-and
                            type-fix
                            n2b b+) ()))))

(def-rp-rule$ t t
  bin-and-is-c-1
  (implies (and (bitp a)
                (bitp b))
           (equal (adder-sum (adder-and a b) x)
                  (merge-adder-sum (f2 (merge-adder-sum a b)) x)))
  :hints (("Goal"
           :in-theory (e/d (f2
                            adder-and
                            type-fix
                            n2b b+) ()))))

(def-rp-rule$ t t
  bin-and-is-c-2
  (implies (and (bitp a)
                (bitp b))
           (equal (adder-sum x (adder-and a b))
                  (merge-adder-sum x
                                   (f2 (merge-adder-sum a b)))))
  :hints (("Goal"
           :in-theory (e/d (f2
                            adder-and
                            type-fix
                            n2b b+) ()))))

(progn
  (def-rp-rule$ t t
    bin-and-is-c-3
    (implies (and (bitp ([] a ai))
                  (bitp ([] b bi)))
             (equal  (adder-and$ ([] a ai) ([] b bi) x)
                     (adder-and$ x (f2 (merge-adder-sum ([] a ai) ([] b bi))))))
    :hints (("Goal"
             :in-theory (e/d (f2
                              adder-and
                              type-fix
                              and$
                              n2b b+) ()))))

  (defthmd bin-and-is-c-3-side-cond
    (implies (and (bitp ([] a ai))
                  (bitp ([] b bi)))
             (bitp (f2 (merge-adder-sum ([] a ai) ([] b bi)))))
    :hints (("Goal"
             :in-theory (e/d (f2
                              adder-and
                              type-fix
                              n2b b+) ()))))
  (rp-attach-sc bin-and-is-c-3
                bin-and-is-c-3-side-cond))

(defthmd bin-and-is-c-sc
  (implies (and (bitp a)
                (bitp b))
           (bitp (f2 (merge-adder-sum a b))))
  :hints (("Goal"
           :in-theory (e/d (booleanp) ()))))

(rp-attach-sc bin-and-is-c
              bin-and-is-c-sc)

(rp-attach-sc bin-and-is-c-1
              bin-and-is-c-sc)

(rp-attach-sc bin-and-is-c-2
              bin-and-is-c-sc)

#|(rp-attach-sc b-and-pair-is-c
              bin-and-is-c-sc)||#

(def-rp-rule$ t t
  c-of-same-c
  (implies (and (bitp a)
                (bitp b))
           (equal (c a b (c a b))
                  (c a b)))
  :hints (("Goal"
           :in-theory '((:e f2)
                        (:e b+)
                        bitp
                        (:e n2b)
                        (:e type-fix)))))

(def-rp-rule$ t t
  bin-or-p1
  (implies (and (bitp a1)
                (bitp a2)
                (bitp b))
           (equal (adder-or (f2 (adder-sum a1 a2))
                            (adder-and (m2 (adder-sum a1 a2)) b))
                  (f2 (merge-adder-sum a1 a2 b))))
  :hints (("Goal"
           :in-theory (e/d (f2 adder-or
                               n2b
                               m2 b+ type-fix) ()))))

(def-rp-rule$ t t
  bin-or-p1a
  (implies (and (bitp a1)
                (bitp a2)
                (bitp b))
           (equal (adder-or (adder-and (m2 (adder-sum a1 a2)) b)
                            (f2 (adder-sum a1 a2)))
                  (f2 (merge-adder-sum a1 a2 b))))
  :hints (("Goal"
           :in-theory (e/d (f2 adder-or
                               n2b
                               m2 b+ type-fix) ()))))

(def-rp-rule$ t t
  bin-or-p1b
  (implies (and (bitp a1)
                (bitp a2)
                (bitp b))
           (equal (adder-or (adder-and a1 a2)
                            (adder-and (m2 (adder-sum a1 a2)) b))
                  (f2 (merge-adder-sum a1 a2 b))))
  :hints (("Goal"
           :in-theory (e/d (f2 adder-or

                               n2b
                               m2 b+ type-fix) ()))))

(def-rp-rule$ t t
  bin-or-p1b-v2
  (implies (and (bitp a1)
                (bitp a2)
                (bitp b))
           (equal (adder-or (adder-and b (m2 (adder-sum a1 a2)))
                            (adder-and a1 a2))
                  (f2 (merge-adder-sum a1 a2 b))))
  :hints (("Goal"
           :use ((:instance bin-or-p1b))
           :in-theory (e/d (adder-or
                            adder-sum )
                           (bin-or-p1b)))))

(def-rp-rule$ t t
  bin-or-p1b-v3
  (implies (and (bitp a1)
                (bitp a2)
                (bitp b))
           (equal (adder-or (adder-and (m2 (adder-sum a1 a2)) b)
                            (adder-and a1 a2))
                  (f2 (merge-adder-sum a1 a2 b))))
  :hints (("Goal"
           :use ((:instance bin-or-p1b))
           :in-theory (e/d (adder-or
                            adder-sum )
                           (bin-or-p1b)))))

(def-rp-rule$ t t
  bin-or-p1c
  (implies (and (bitp a1)
                (bitp a2)
                (bitp b))
           (equal (adder-or (f2 (adder-sum a1 a2))
                            (adder-and b (m2 (adder-sum a1 a2))))
                  (f2 (merge-adder-sum a1 a2 b))))
  :hints (("Goal"
           :in-theory (e/d (f2 adder-or
                               n2b
                               m2 b+ type-fix) ()))))

(def-rp-rule$ t t
  bin-or-p2a
  (implies (and (bitp a1)
                (bitp a2)
                (bitp y)
                (bitp x))
           (equal (adder-or (f2 (adder-sum a1 a2 x))
                            (adder-and (m2 (adder-sum a1 a2)) y))
                  (f2 (merge-adder-sum  a1 a2 (adder-or x y)))))
  :hints (("Goal"
           :in-theory (e/d (f2 adder-or
                               adder-and
                               n2b
                               m2 b+ type-fix) ()))))

(def-rp-rule$ t t
  bin-or-p2b
  (implies (and (bitp a1)
                (bitp a2)
                (bitp y)
                (bitp c-in)
                (bitp x))
           (equal (adder-or (adder-and$ c-in (m2 (adder-sum a1 a2)) y)
                            (f2 (adder-sum a1 a2 x)))
                  (f2 (merge-adder-sum  a1 a2 (adder-or x (adder-and c-in y))))))
  :hints (("Goal"
           :in-theory (e/d (f2 adder-or
                               bitp
                               adder-and
                               n2b
                               m2 b+ type-fix) ()))))

(def-rp-rule$ t t
  bin-or-p2c
  (implies (and (bitp a1)
                (bitp a2)
                (bitp x)
                (bitp y))
           (equal (adder-or (adder-and (m2 (adder-sum a1 a2)) y)
                            (f2 (adder-sum a1 a2 x)))
                  (f2 (merge-adder-sum a1 a2 (adder-or x y)))))
  :hints (("Goal"
           :in-theory (e/d (f2 adder-or
                               n2b
                               bitp
                               m2 b+ type-fix) ()))))

(def-rp-rule$ t t
  bin-or-p3
  (implies (and (bitp a1)
                (bitp a2)
                (bitp y)
                (bitp x))
           (equal (adder-or$ (f2 (adder-sum a1 a2 x))
                             (adder-and (m2 (adder-sum a1 a2)) y)
                             z)
                  (adder-or$ (f2 (merge-adder-sum a1 a2 (adder-or x y)))
                             z)))
  :hints (("Goal"
           :in-theory (e/d (f2 adder-or
                               adder-and
                               n2b
                               bitp
                               or$
                               m2 b+ type-fix) ()))))

(def-rp-rule$ t t
  or-of-and-of-the-same
  (implies t
           (and (equal (adder-or$ (adder-and$ single x)
                                  (adder-and$ single y))
                       (adder-and$ single (adder-or$ x y)))))
  :hints (("Goal"
           :in-theory (e/d (f2 adder-or
                               adder-and
                               n2b
                               bitp
                               and$
                               or$
                               m2 b+ type-fix) ()))))

(defthmd bin-or-p2-sc
  (implies (and (bitp a1)
                (bitp a2)
                (bitp y)
                (bitp x))
           (bitp (f2 (merge-adder-sum a1 a2 (adder-or x y)))))
  :hints (("Goal"
           :in-theory (e/d (f2 adder-or
                               n2b
                               m2 b+ type-fix) ()))))

(defthmd bin-or-p2-v2-sc
  (implies (and (bitp a1)
                (bitp a2)
                (bitp y)
                (bitp x)
                (bitp c-in))
           (bitp (f2 (merge-adder-sum a1 a2 (adder-or x (adder-and$ c-in y))))))
  :hints (("Goal"
           :in-theory (e/d (f2 adder-or
                               n2b
                               bitp
                               m2 b+ type-fix) ()))))

(defthmd bin-or-p1-sc
  (implies (and (bitp a1)
                (bitp a2)
                (bitp b))
           (bitp (f2 (merge-adder-sum a1 a2 b))))
  :hints (("Goal"
           :in-theory (e/d (f2 adder-or
                               quarternaryp
                               n2b
                               m2 b+ type-fix) ()))))

(rp-attach-sc bin-or-p1
              bin-or-p1-sc)

(rp-attach-sc bin-or-p1a
              bin-or-p1-sc)

(rp-attach-sc bin-or-p1b
              bin-or-p1-sc)

(rp-attach-sc bin-or-p1b-v2
              bin-or-p1-sc)

(rp-attach-sc bin-or-p1b-v3
              bin-or-p1-sc)

(rp-attach-sc bin-or-p1c
              bin-or-p1-sc)

#|(rp-attach-sc bin-or-p1b-v2-b-and-pair
              bin-or-p1-sc)||#

(rp-attach-sc bin-or-p2a
              bin-or-p2-sc)

(rp-attach-sc bin-or-p2c
              bin-or-p2-sc)

(rp-attach-sc bin-or-p2b
              bin-or-p2-v2-sc)

(rp-attach-sc bin-or-p3
              bin-or-p2-sc)

(def-rp-rule$ t t
  adder-sum-of-pp-sum
  (and (equal (adder-sum (pp-sum a b) x)
              (merge-adder-sum a b x))
       (equal (adder-sum x (pp-sum a b))
              (merge-adder-sum a b x)))
  :hints (("Goal"
           :in-theory (e/d (adder-sum
                            pp-sum
                            ) ()))))

(def-rp-rule$ t t
  pp-sum-of-adder-sum
  (and (equal (pp-sum (adder-sum a b) x)
              (merge-adder-sum a b x))
       (equal (pp-sum x (adder-sum a b))
              (merge-adder-sum a b x)))
  :hints (("Goal"
           :in-theory (e/d (adder-sum
                            pp-sum
                            ) ()))))

(def-rp-rule$ t t
  adder-sum-of-0
  (and (equal (adder-sum 0 x)
              (type-fix x))
       (equal (adder-sum x 0)
              (type-fix x)))
  :hints (("Goal"
           :in-theory (e/d (adder-sum
                            sum
                            type-fix) ()))))

(def-rp-rule$ t t
  adder-type-fix
  (and (equal (adder-sum (type-fix x) y)
              (merge-adder-sum x y))
       (equal (adder-sum y (type-fix x))
              (merge-adder-sum y x)))
  :hints (("Goal"
           :in-theory (e/d (adder-sum
                            type-fix
                            sum) ()))))

(def-rp-rule$ t t
  m2-of-adder-sum-m2
  (equal (m2 (adder-sum (m2 x) y))
         (m2 (merge-adder-sum x y)))
  :hints (("Goal"
           :in-theory (e/d (adder-sum
                            m2) ()))))

(def-rp-rule$ t t
  dummy-adder-final-step1
  (implies (and (bitp rest)
                (bitp x))
           (equal (equal (adder-and$ x rest)
                         (m2 (f2 (adder-sum x rest))))
                  t))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(def-rp-rule$ t t
  adder-sum-of-nil
  (equal (adder-sum nil x)
         (type-fix x))
  :hints (("Goal"
           :in-theory (e/d (adder-sum
                            type-fix) ()))))

(def-rp-rule$ t t
  adder-sum-of-nil-2
  (equal (adder-sum nil x y)
         (merge-adder-sum x y))
  :hints (("Goal"
           :in-theory (e/d (adder-sum
                            type-fix) ()))))

(def-rp-rule$ t t
  some-combination-1
  (implies (and (bitp x)
                (bitp a)
                (bitp b))
           (equal (adder-or$ (adder-and$ a x)
                             (adder-and$ b (adder-or$ x a)))
                  (f2 (merge-adder-sum a b x))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(defthmd some-combination-1-side-cond
  (implies (and (bitp x)
                (bitp a)
                (bitp b))
           (bitp (f2 (merge-adder-sum a b x))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(rp-attach-sc some-combination-1
              some-combination-1-side-cond)

(progn
  (def-rp-rule$ t t
    adder-or-of-and-and-nots-with-m2
    (implies (and (bitp a)
                  (bitp b)
                  (bitp y))
             (equal (adder-or (adder-and (m2 (adder-b+ a b)) (not$ y))
                              (adder-and (m2 (adder-sum 1 a b)) y))
                    (m2 (merge-adder-sum a b y))))
    :hints (("Goal"
             :in-theory (e/d (adder-sum m2 sum type-fix adder-or adder-and and$
                                        or$ bitp) ()))))

  (def-rp-rule$ t t
    adder-or-of-and-and-nots-with-f2
    (implies (and (bitp a)
                  (bitp b)
                  (bitp y))
             (equal (adder-or (adder-and (f2 (adder-b+ a b)) (not$ y))
                              (adder-and (f2 (adder-sum 1 a b)) y))
                    (f2 (merge-adder-sum a b y))))
    :hints (("Goal"
             :in-theory (e/d (adder-sum m2 sum type-fix adder-or adder-and and$
                                        or$ bitp) ()))))

  (defthmd adder-or-of-and-and-nots-with-f2-side-cond
    (implies (and (bitp a)
                  (bitp b)
                  (bitp y))
             (bitp  (f2 (merge-adder-sum a b y))))
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (rp-attach-sc adder-or-of-and-and-nots-with-f2
                adder-or-of-and-and-nots-with-f2-side-cond)

  (defthmd adder-or-of-and-and-nots-with-m2-side-cond
    (implies (and (bitp a)
                  (bitp b)
                  (bitp y))
             (bitp  (m2 (merge-adder-sum a b y))))
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (rp-attach-sc adder-or-of-and-and-nots-with-m2
                adder-or-of-and-and-nots-with-m2-side-cond))

(def-rp-rule$ t t
  bit-of-adder-fncs
  (and (equal (bit-of (adder-and a b) 0)
              (adder-and a b))
       (equal (bit-of (adder-or a b) 0)
              (adder-or a b)))
  :hints (("Goal"
           :in-theory (e/d (adder-and
                            adder-or
                            bit-of) ()))))

(encapsulate
  nil

  (local
   (in-theory (enable adder-and$ and$ or$ adder-or$)))

  (def-rp-rule$ t t adder-and-of-1 (equal (adder-and x 1) (bit-fix x)))
  (def-rp-rule$ t t adder-and-of-1-v2 (equal (adder-and 1 x) (bit-fix x)))
  (def-rp-rule$ t t adder-and-of-0 (equal (adder-and x 0) 0))
  (def-rp-rule$ t t adder-and-of-0-v2 (equal (adder-and 0 x) 0))
  (def-rp-rule$ t t adder-or-of-0 (equal (adder-or x 0) (bit-fix x)))
  (def-rp-rule$ t t adder-or-of-0-v2 (equal (adder-or 0 x) (bit-fix x)))
  (def-rp-rule$ t t adder-or-of-1 (equal (adder-or x 1) 1))
  (def-rp-rule$ t t adder-or-of-1-v2 (equal (adder-or 1 x) 1))

  (def-rp-rule$ t t adder-or-of-the-same
    (equal (adder-or x x)
           (bit-fix x)))

  (def-rp-rule$ t t adder-and-of-the-same
    (equal (adder-and x x)
           (bit-fix x))))

(defconst *adder-rules*
  '(m2-of-adder-sum-m2
    bin-or-p2a

    ;; adder-adder-and-comm1
    ;; adder-adder-and-comm2
    ;; b-and-reorder

    ;;b-and-comm2-a
    adder-sum-of-0
    adder-type-fix
    sum-is-adder-b+
    ;; adder-sum-of-pp-sum
    ;; pp-sum-of-adder-sum
    pp-sum-is-adder-b+
    pp-sum-is-adder-b+-2
    merge-pp-sum-is-adder-b+
    merge-sum-is-adder-b+

    ;; adder-sum-comm1
    ;; adder-sum-comm2
    ;; adder-sum-reorder

    some-combination-1

    bin-or-p1
    bin-or-p1a
    bin-or-p1b
    bin-or-p1b-v2
    bin-or-p1b-v3
    bin-or-p1c
    
    bin-or-p2c

    booleanp-bin-and
    bin-xor-is-s
    sum-is-adder-b+
    BOOLEANP-BIN-or
    bin-and-is-c-1
    bin-and-is-c-2
    #|b-and-pair-is-c||#
    booleanp-bin-xor
    b-or-reorder
    b-or-comm1
    b-or-comm2

    or-of-and-of-the-same

    dummy-adder-final-step1

    bin-or-p3
    bin-and-is-c-3

    adder-sum-of-nil
    adder-sum-of-nil-2
    ;;adder-and$-of-single-element

    and$-is-adder-and$
    or$-is-adder-or$
    bitp-adder-and
    bitp-adder-or

    adder-or-of-and-and-nots-with-m2
    adder-or-of-and-and-nots-with-f2

    adder-and-of-1
    adder-and-of-1-v2
    adder-and-of-0
    adder-and-of-0-v2

    adder-or-of-0
    adder-or-of-0-v2
    adder-or-of-1
    adder-or-of-1-v2

    adder-or-of-the-same
    adder-and-of-the-same

    bit-of-adder-fncs

    ;; m2-of-adder-sum-1
    ;; binary-not-to-adder-sum
    ;; adder-and-of-subtracted
    ;; adder-and-of-subtracted-2
    ))

(deftheory adder-rules
  *adder-rules*)

(deftheory adder-greedy-rules
  '(c-of-same-c
    adder-adder-and-comm2
    b-or-reorder
    b-or-comm1
    b-or-comm2))

(in-theory (disable adder-greedy-rules))
(in-theory (disable adder-rules))
