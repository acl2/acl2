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

(include-book "fnc-defs")

(local
 (include-book "lemmas"))

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5))

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

(def-rp-rule not$-of-not$
  (equal (not$ (not$ x))
         (bit-fix x))
  :hints (("Goal"
           :in-theory (e/d (binary-not
                            bit-fix) ()))))

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

(def-rp-rule equal-of-s-of-c
  (implies (bitp x)
           (equal (equal x (s hash-code nil (list x)))
                  t))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(rp::def-rp-rule
 binary-append-opener-cons
 (equal (append (cons x y) rest)
        (cons x (append y rest))))

(rp::def-rp-rule
 binary-append-opener-nil
 (equal (append nil rest)
        rest))

(rp::def-rp-rule
 assoc-equal-opener-cons
 (equal (assoc-equal key (cons (cons a b) rest))
        (if (equal key a)
            (cons a b)
          (assoc-equal key rest))))

(rp::def-rp-rule
 assoc-equal-opener-nil
 (equal (assoc-equal key nil)
        nil))

(def-rp-rule m2-is-bitp
  (bitp (m2 x)))

;; (def-rp-rule binary-xor-1-of-s
;;   (equal (binary-xor 1 (s hash-code pp c/d))
;;          (s-spec (list 1 (s hash-code pp c/d))))
;;   :hints (("Goal"
;;            :in-theory (e/d (binary-xor m2) ()))))

;; (def-rp-rule binary-not-of-s
;;   (equal (binary-not (s hash-code pp c/d))
;;          (s-spec (list 1 (s hash-code pp c/d))))
;;   :hints (("Goal"
;;            :in-theory (e/d (binary-xor m2) ()))))

;; (def-rp-rule binary-not-of-s-c-res
;;   (implies (bitp (s-c-res x y z))
;;            (equal (binary-not (s-c-res x y z))
;;                   (s-spec (list 1 (s-c-res x y z)))))
;;   :hints (("Goal"
;;            :in-theory (e/d (bitp) ()))))


(def-rp-rule binary-xor-of-1
  (implies (bitp x)
           (and (equal (rp::binary-xor 1 x)
                       (rp::binary-not x))
                (equal (rp::binary-xor x 1)
                       (rp::binary-not x))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(progn
  (def-rp-rule$ t t binary-xor-1-of-s
    (and (equal (binary-xor 1 (s hash-code pp c/d))
                (sum 1 (-- (s hash-code pp c/d))))
         (equal (binary-xor (s hash-code pp c/d) 1)
                (sum 1 (-- (s hash-code pp c/d)))))
    :hints (("Goal"
             :in-theory (e/d (binary-xor m2)
                             ()))))

  (def-rp-rule$ t t binary-not-of-s
    (equal (binary-not (s hash-code pp c/d))
           (sum 1 (-- (s hash-code pp c/d))))
    :hints (("Goal"
             :in-theory (e/d (binary-xor m2) ()))))

  (def-rp-rule$ t t binary-not-of-c
    (implies (bitp (c hash-code s pp c/d))
             (equal (binary-not (c hash-code s pp c/d))
                    (sum 1 (-- (c hash-code s pp c/d)))))
    :hints (("Goal"
             :in-theory (e/d (binary-xor m2) ()))))

  (def-rp-rule$ t t binary-not-of-s-c-res
    (implies (bitp (s-c-res s pp c/d))
             (equal (binary-not (s-c-res s pp c/d))
                    (sum 1 (-- (s-c-res s pp c/d)))))
    :hints (("Goal"
             :in-theory (e/d (binary-xor m2) ()))))

  (defthmd binary-not-of-s-side-cond
    (bitp (sum 1 (-- (s hash-code pp c/d))))
    :hints (("Goal"
             :in-theory (e/d (m2  bitp) ()))))

  (defthmd binary-not-of-c-side-cond
    (implies (bitp (c hash-code s pp c/d))
             (bitp (sum 1 (-- (c hash-code s pp c/d)))))
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (defthmd binary-not-of-s-c-res-side-cond
    (implies (bitp (s-c-res s pp c/d))
             (bitp (sum 1 (-- (s-c-res s pp c/d)))))
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule binary-not-of-binary-sum
    (implies (bitp (sum a b))
             (equal (not$ (sum a b))
                    (sum 1 (-- a) (-- b))))
    :hints (("Goal"
             :in-theory (e/d (sum ifix --)
                             (+-IS-SUM)))))

  (defthm binary-not-of-binary-sum-side-cond
    (implies (bitp (sum a b))
             (bitp (sum 1 (-- a) (-- b))))
    :hints (("Goal"
             :in-theory (e/d (bitp -- ifix sum)
                             (+-IS-SUM)))))

  (rp-attach-sc binary-not-of-binary-sum
                binary-not-of-binary-sum-side-cond)

  (rp-attach-sc binary-xor-1-of-s
                binary-not-of-s-side-cond)

  (rp-attach-sc binary-not-of-s
                binary-not-of-s-side-cond)

  (rp-attach-sc binary-not-of-c
                binary-not-of-c-side-cond)

  (rp-attach-sc binary-not-of-s-c-res
                binary-not-of-s-c-res-side-cond))



(def-rp-rule --of---
  (equal (-- (-- a))
         (ifix a))
  :hints (("Goal"
           :in-theory (e/d (--) ()))))

(disable-exc-counterpart --)

(def-rp-rule --of-sum
  (equal (-- (sum a b))
         (sum (-- a) (-- b)))
  :hints (("Goal"
           :in-theory (e/d (sum --)
                           (+-IS-SUM)))))

(rp::def-rp-rule
 sum-of-negated
 (and (equal (rp::sum x (rp::-- x) other)
             (ifix other))
      (equal (rp::sum (rp::-- x) x other)
             (ifix other)))
 :hints (("Goal"
          :in-theory (e/d (rp::sum
                           rp::--)
                          (+-IS-SUM)))))

(def-rp-rule equal-sides-to-s
  (implies (and (bitp side1)
                (bitp side2)
                (syntaxp (and (or (and (not (equal side1 0))
                                       (not (equal side1 ''0)))
                                  (and (unpack-booth-later-enabled)
                                       (not (include-fnc side2 'and-list))
                                       (include-fnc side2 'binary-or)))
                              (or (and (not (equal side2 0))
                                       (not (equal side2 ''0)))
                                  (and (unpack-booth-later-enabled)
                                       (not (include-fnc side1 'and-list))
                                       (include-fnc side1 'binary-or)))
                              
                              (or ;;(pp-has-bitp-rp side1)
                               (single-s-p (ex-from-rp-loose side1))
                               (s-c-res-p (ex-from-rp-loose side1))
                               (single-c-p (ex-from-rp-loose side1))
                               (binary-fnc-p (ex-from-rp-loose side1))
                               (binary-sum-p (ex-from-rp-loose side1))
                               
                               (single-s-p (ex-from-rp-loose side2))
                               (s-c-res-p (ex-from-rp-loose side2))
                               (single-c-p (ex-from-rp-loose side2))
                               (binary-fnc-p (ex-from-rp-loose side2))
                               (binary-sum-p (ex-from-rp-loose side2))
                                  ;;(bit-of-p (ex-from-rp-loose side1))
                               )
                              #|(or (pp-has-bitp-rp side2)
                                  (single-s-p (ex-from-rp-loose side2))
                                  (bit-of-p (ex-from-rp-loose side2))
                                  (binary-fnc-p (ex-from-rp-loose side2)))||#)))
           (equal (equal side1 side2)
                  (equal (unpack-booth (s-spec (list 2 side1 side2)))
                         0)))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))




(def-rp-rule$ nil nil
  s-c-spec-with-zero
  (and (equal (s-c-spec (list 0 a b))
              (s-c-spec (list a b)))
       (equal (s-c-spec (list a b 0))
              (s-c-spec (list a b)))
       (equal (s-c-spec (list a 0 b))
              (s-c-spec (list a b)))
       (equal (s-c-spec (list 0 a))
              (s-c-spec (list a)))
       (equal (s-c-spec (list a 0))
              (s-c-spec (list a)))

       (equal (c-s-spec (list 0 a b))
              (c-s-spec (list a b)))
       (equal (c-s-spec (list a b 0))
              (c-s-spec (list a b)))
       (equal (c-s-spec (list a 0 b))
              (c-s-spec (list a b)))
       (equal (c-s-spec (list 0 a))
              (c-s-spec (list a)))
       (equal (c-s-spec (list a 0))
              (c-s-spec (list a)))

       (equal (c-spec (list 0 a b))
              (c-spec (list a b)))
       (equal (c-spec (list a b 0))
              (c-spec (list a b)))
       (equal (c-spec (list a 0 b))
              (c-spec (list a b)))
       (equal (c-spec (list 0 a))
              (c-spec (list a)))
       (equal (c-spec (list a 0))
              (c-spec (list a)))

       (equal (s-spec (list 0 a b))
              (s-spec (list a b)))
       (equal (s-spec (list a b 0))
              (s-spec (list a b)))
       (equal (s-spec (list a 0 b))
              (s-spec (list a b)))
       (equal (s-spec (list 0 a))
              (s-spec (list a)))
       (equal (s-spec (list a 0))
              (s-spec (list a))))
  :hints (("Goal"
           :in-theory (e/d (s-c-spec
                            c-s-spec
                            s-spec c-spec sum-list
                            sum)
                           ()))))

(def-rp-rule$ nil nil
  s-c-spec-with-one
  (implies (bitp a)
           (and (equal (s-c-spec (list 1 a))
                       (list (not$ a) a))
                (equal (s-c-spec (list a 1))
                       (list (not$ a) a))

                (equal (c-spec (list 1 a))
                       a)
                (equal (c-spec (list a 1))
                       a)

                (equal (s-spec (list 1 a))
                       (not$ a))
                (equal (s-spec (list a 1))
                       (not$ a))

                (equal (c-s-spec (list 1 a))
                       (list a (not$ a)))
                (equal (c-s-spec (list a 1))
                       (list a (not$ a)))))
  :hints (("Goal"
           :in-theory (e/d (bitp)
                           ()))))


(def-rp-rule plus-with-0
  (implies (integerp a)
           (and (equal (+ a 0)
                       a)
                (equal (+ 0 a)
                       a))))
