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

;; Definitions for binary functions to be used by multiplier rules

(in-package "RP")

(include-book "projects/rp-rewriter/top" :dir :system)

(define b+2
  ((x (integerp x))
   (y (integerp y)))
  (+ (ifix x)
     (ifix y)))

(define b-*
  ((x (integerp x))
   (y (integerp y)))
  (* (ifix x)
     (ifix y)))

(defmacro times (&rest rst)
  (cond ((null rst) 0)
        ((null (cdr rst))
         (list 'type-fix (car rst)))
        (t (xxxjoin 'b-* rst))))

(defmacro sum2 (&rest rst)
  (cond ((null rst) 0)
        ((null (cdr rst))
         (list 'type-fix (car rst)))
        (t (xxxjoin 'b+2 rst))))

(add-macro-fn times b-* t)

(add-macro-fn sum2 b+2 t)

(defun bit-fix (rp::x)
  (declare (xargs :guard t))
  (if (bitp rp::x)
      rp::x
    0))

(def-rp-rule bit-fix-opener
  (implies (bitp x)
           (equal (bit-fix x) x)))

(in-theory (disable bit-fix))

#|(define subt ((x type-p))
  (-- x))||#

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


#|(define has-pp-binary-not-atom (term)
  (b* ((term (ex-from-rp-loose term)))
    (case-match term
      (('p+ ('binary-not x) rest)
       (or (atom x)
           (has-pp-binary-not-atom rest)))
      (('b+ x y)
       (or (has-pp-binary-not-atom x)
           (has-pp-binary-not-atom y)))
      (('m2 x)
       (has-pp-binary-not-atom x))
      (('m2-new x)
       (has-pp-binary-not-atom x))
      (('f2-new x)
       (has-pp-binary-not-atom x))
      (('f2 x)
       (has-pp-binary-not-atom x)))))||#
