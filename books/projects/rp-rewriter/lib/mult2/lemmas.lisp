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
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))


(defthm consp-of-rp-trans-lst
  (equal (CONSP (RP-TRANS-LST lst))
         (consp lst))
  :hints (("Goal"
           :induct (len lst)
           :do-not-induct t
           :in-theory (e/d () ()))))

(progn
  (defthm sum-comm-1
    (equal (sum b a)
           (sum a b))
    :hints (("Goal"
             :in-theory (e/d (sum) ()))))

  (defthm sum-comm-2
    (equal (sum b a c)
           (sum a b c))
    :hints (("Goal"
             :in-theory (e/d (sum) ()))))

  (defthm sum-assoc
    (equal (sum (sum a b) c)
           (sum a b c))
    :hints (("Goal"
             :in-theory (e/d (sum) ()))))

  (defthm sum-of-0
    (and (equal (sum 0 a)
                (ifix a))
         (equal (sum a 0)
                (ifix a)))
    :hints (("Goal"
             :in-theory (e/d (sum) ()))))

  (defthm sum-of-ifix
    (and (equal (sum (ifix x) y)
                (sum x y))
         (equal (sum x (ifix y))
                (sum x y)))
    :hints (("Goal"
             :in-theory (e/d (ifix sum) ()))))

  (defthm ifix-opener
    (implies (integerp x)
             (equal (ifix x)
                    x))
    :hints (("Goal"
             :in-theory (e/d (ifix) ())))))


(in-theory (disable ifix))



(defthm sum-list-of-append
  (EQUAL (SUM-LIST (APPEND lst1 lst2))
         (SUM (sum-list lst1)
              (sum-list lst2)))
  :hints (("Goal"
           :in-theory (e/d (sum-list) ()))))

(defthm sum-list-of-true-list-fix
  (equal (SUM-LIST (TRUE-LIST-FIX lst))
         (SUM-LIST lst))
  :hints (("Goal"
           :in-theory (e/d (sum-list true-list-fix) ()))))


