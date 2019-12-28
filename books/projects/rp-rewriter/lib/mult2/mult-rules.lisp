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
           (equal (equal x (s nil x))
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


(def-rp-rule binary-xor-1-of-s
  (equal (binary-xor 1 (s pp c/d))
         (s-spec (list 1 (s pp c/d))))
  :hints (("Goal"
           :in-theory (e/d (binary-xor m2) ()))))

(def-rp-rule binary-not-of-s
  (equal (binary-not (s pp c/d))
         (s-spec (list 1 (s pp c/d))))
  :hints (("Goal"
           :in-theory (e/d (binary-xor m2) ()))))
