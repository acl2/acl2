; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
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
; Shilpi Goel         <shigoel@cs.utexas.edu>

;; This book contains the specification of the following instructions:
;; div  idiv

(in-package "X86ISA")

(include-book "../rflags-spec"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

;; ======================================================================

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (local (set-default-hints '((acl2::nonlinearp-default-hint++
                              id stable-under-simplificationp hist nil))))

 (defthm floor-bounds
   (implies (and (natp src)
                 (natp dst)
                 (< dst m))
            (< (floor dst src) m))
   :rule-classes (:rewrite :linear))

 (local (in-theory (e/d* () ((:rewrite acl2::|(expt x (+ m n)) non-zero x|)
                             (:rewrite bitops::|(* 1/2 (expt 2 n))|)
                             (:rewrite acl2::|(* c (* d x))|)
                             (:rewrite acl2::|(< (+ c/d x) y)|)))))

 (defthm sign-extension-of-non-zero-natp-is-non-zero
   (implies (and (unsigned-byte-p n x)
                 (not (equal x 0)))
            (not (equal (logext n x) 0)))
   :hints (("Goal" :in-theory (e/d* (acl2::logext**
                                     logcar logcdr
                                     acl2::ihsext-inductions
                                     ifix)
                                    ()))))

 (defthm-signed-byte-p signed-byte-p-of-rem
   :hyp (and (signed-byte-p (* 2 n) x)
             (signed-byte-p n y)
             (not (equal y 0)))
   :bound n
   :concl (rem x y)
   :gen-linear t
   :gen-type t)

 (defthm integerp-rem
   (implies (and (integerp x)
                 (integerp y))
            (integerp (rem x y)))
   :hints (("Goal" :in-theory (e/d (rem) (force (force)))))
   :rule-classes :type-prescription)

 (defthm-signed-byte-p signed-byte-p-of-truncate-when-y-is-positive
   :hyp (and (signed-byte-p m x)
             (integerp y)
             (< 0 y))
   :bound m
   :concl (truncate x y)
   :gen-linear t
   :gen-type t)

 (defthm-signed-byte-p signed-byte-p-of-truncate-when-y-is-negative
   :hyp (and (signed-byte-p (1- m) x)
             (< 0 m)
             (integerp y)
             (< y 0))
   :bound m
   :concl (truncate x y)
   :gen-linear t
   :gen-type t)

 (defthm-signed-byte-p signed-byte-p-of-truncate
   :hyp (and (signed-byte-p (1- m) x)
             (< 0 m)
             (integerp y)
             (not (equal y 0)))
   :bound m
   :concl (truncate x y)
   :hints (("Goal" :cases ((< 0 y) (< y 0))))
   :gen-linear t
   :gen-type t))

;; ======================================================================
;; Unsigned Divide: DIV
;; ======================================================================

(define div-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (let* ((size*2       (* 2 size))
         (max-quotient (loghead size -1))
         (fn-name   (mk-name "DIV-SPEC-" size))
         (str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst    :type (unsigned-byte ,size*2))
        (src    :type (unsigned-byte ,size)))

       :guard (not (equal src 0))
       :parents (div-spec)

       (b* ((dst (mbe :logic (n-size ,size*2 dst)
                      :exec dst))
            (src (mbe :logic (n-size ,size src)
                      :exec src))

            (quotient
             (the (unsigned-byte ,size*2) (floor dst src)))
            (remainder
             (the (unsigned-byte ,size) (mod dst src)))

            (overflow?
             (< ,max-quotient quotient))

            ((when overflow?)
             (mv (list (cons 'quotient quotient)
                       (cons 'remainder remainder))
                 0 0)))

           (mv overflow? quotient remainder))

       ///

       (local (in-theory (e/d (loghead ifix) ())))

       (defthm-unsigned-byte-p ,(mk-name "N" str-nbits "-MV-NTH-1-" fn-name)
         :hyp (not (mv-nth 0 (,fn-name dst src)))
         :bound ,size
         :concl (mv-nth 1 (,fn-name dst src))
         :gen-type t
         :gen-linear t)

       (defthm-unsigned-byte-p ,(mk-name "MV-NTH-2-" fn-name)
         :hyp (and (unsigned-byte-p ,size src)
                   (< 0 src))
         :bound ,size
         :concl (mv-nth 2 (,fn-name dst src))
         :gen-type t
         :gen-linear t))
    ))

(make-event (div-spec-gen  8))
(make-event (div-spec-gen 16))
(make-event (div-spec-gen 32))
(make-event (div-spec-gen 64))

(define div-spec
  ((size   :type (member 1 2 4 8))
   dst src)

  :guard (and (not (equal src 0))
              (case size
                (1 (and (n08p src) (n16p  dst)))
                (2 (and (n16p src) (n32p  dst)))
                (4 (and (n32p src) (n64p  dst)))
                (8 (and (n64p src) (n128p dst)))
                (otherwise nil)))

  :prepwork
  ((local (in-theory (e/d () (unsigned-byte-p)))))

  :inline t
  :no-function t
  :parents (instruction-semantic-functions)
  :short "Specification for the @('DIV') (unsigned divide) instruction"

  (case size
    (1 (div-spec-8  dst src))
    (2 (div-spec-16 dst src))
    (4 (div-spec-32 dst src))
    (8 (div-spec-64 dst src))
    (otherwise (mv nil 0 0)))

  ///

  (defthm-unsigned-byte-p mv-nth-1-div-spec
    :hyp   (and (member size '(1 2 4 8))
                (not (mv-nth 0 (div-spec size dst src))))
    :bound (ash size 3)
    :concl (mv-nth 1 (div-spec size dst src))
    :gen-linear t
    :hyp-t (and (syntaxp (quotep size))
                (force (member size '(1 2 4 8)))
                (not (mv-nth 0 (div-spec size dst src))))
    :gen-type t)

  (defthm-unsigned-byte-p mv-nth-2-div-spec
    :hyp   (and (member size '(1 2 4 8))
                (not (equal src 0))
                (unsigned-byte-p (ash size 3) src))
    :bound (ash size 3)
    :concl (mv-nth 2 (div-spec size dst src))
    :gen-linear t
    :hyp-t (and (syntaxp (quotep size))
                (force (member size '(1 2 4 8)))
                (force (not (equal src 0)))
                (force (unsigned-byte-p (ash size 3) src)))
    :gen-type t))

;; ======================================================================
;; Signed Divide: IDIV
;; ======================================================================

(define idiv-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (b* ((size*2                 (* 2 size))
       (size*2+1               (1+ size*2))
       (?smallest-neg-quotient (- (1- (expt 2 (1- size)))))
       (?largest-pos-quotient  (expt 2 (1- size)))
       (fn-name                (mk-name "IDIV-SPEC-" size))
       (str-nbits              (if (eql size 8) "08" size)))

      `(define ,fn-name
         ((dst    :type (unsigned-byte ,size*2))
          (src    :type (unsigned-byte ,size)))

         :parents (idiv-spec)
         :guard (not (equal src 0))
         :guard-hints (("Goal" :in-theory (e/d (n08-to-i08
                                                n16-to-i16
                                                n32-to-i32
                                                n64-to-i64)
                                               ())))

         (b* ((dst-int (the (signed-byte ,size*2) (ntoi ,size*2 dst)))
              (src-int (the (signed-byte ,size)   (ntoi ,size   src)))

              ;; Lisp's floor truncates to negative infinity.  We want
              ;; truncation towards 0 for idiv.  Hence, we use truncate
              ;; and rem.  For unsigned divide, we could safely use
              ;; floor and mod since truncating to negative infinity is
              ;; the same as truncating to zero for unsigned numbers.

              ;;  7  idiv   4  :  1,  3
              ;;  7  idiv  -4  : -1,  3
              ;; -7  idiv   4  : -1, -3
              ;; -7  idiv  -4  :  1, -3

              (quotient-int
               (the (signed-byte ,size*2+1) (truncate dst-int src-int)))
              (remainder-int
               (the (signed-byte ,size) (rem dst-int src-int)))

              (overflow?
               (or (< (the (signed-byte ,size*2+1) quotient-int)
                      ,smallest-neg-quotient)
                   (< ,largest-pos-quotient
                      (the (signed-byte ,size*2+1) quotient-int))))

              ((when overflow?)
               (mv (list (cons 'quotient-int  quotient-int)
                         (cons 'remainder-int remainder-int))
                   0 0))

              (quotient  (the (unsigned-byte ,size) (n-size ,size quotient-int)))
              (remainder (the (unsigned-byte ,size) (n-size ,size remainder-int))))

             (mv overflow? quotient remainder))

         ///

         (local (in-theory (e/d (loghead ifix) ())))

         (defthm-unsigned-byte-p ,(mk-name "N" str-nbits "-MV-NTH-1-" fn-name)
           :hyp (not (mv-nth 0 (,fn-name dst src)))
           :bound ,size
           :concl (mv-nth 1 (,fn-name dst src))
           :gen-type t
           :gen-linear t)

         (defthm-unsigned-byte-p ,(mk-name "MV-NTH-2-" fn-name)
           :hyp (and (unsigned-byte-p ,size src)
                     (< 0 src))
           :bound ,size
           :concl (mv-nth 2 (,fn-name dst src))
           :gen-type t
           :gen-linear t)

         )))

(local (in-theory (e/d () (mod floor truncate rem signed-byte-p))))

(make-event (idiv-spec-gen  8))
(make-event (idiv-spec-gen 16))
(make-event (idiv-spec-gen 32))
(make-event (idiv-spec-gen 64))

(define idiv-spec
  ((size   :type (member 1 2 4 8))
   dst src)

  :guard (and (not (equal src 0))
              (case size
                (1 (and (n08p src) (n16p  dst)))
                (2 (and (n16p src) (n32p  dst)))
                (4 (and (n32p src) (n64p  dst)))
                (8 (and (n64p src) (n128p dst)))
                (otherwise nil)))

  :prepwork
  ((local (in-theory (e/d () (unsigned-byte-p)))))

  :inline t
  :no-function t
  :parents (instruction-semantic-functions)
  :short "Specification for the @('IDIV') (unsigned idivide) instruction"

  (case size
    (1 (idiv-spec-8  dst src))
    (2 (idiv-spec-16 dst src))
    (4 (idiv-spec-32 dst src))
    (8 (idiv-spec-64 dst src))
    (otherwise (mv nil 0 0)))

  ///

  (defthm-unsigned-byte-p mv-nth-1-idiv-spec
    :hyp   (and (member size '(1 2 4 8))
                (not (mv-nth 0 (idiv-spec size dst src))))
    :bound (ash size 3)
    :concl (mv-nth 1 (idiv-spec size dst src))
    :gen-linear t
    :hyp-t (and (syntaxp (quotep size))
                (force (member size '(1 2 4 8)))
                (not (mv-nth 0 (idiv-spec size dst src))))
    :gen-type t)

  (defthm-unsigned-byte-p mv-nth-2-idiv-spec
    :hyp   (and (member size '(1 2 4 8))
                (not (equal src 0))
                (unsigned-byte-p (ash size 3) src))
    :bound (ash size 3)
    :concl (mv-nth 2 (idiv-spec size dst src))
    :gen-linear t
    :hyp-t (and (syntaxp (quotep size))
                (force (member size '(1 2 4 8)))
                (force (not (equal src 0)))
                (force (unsigned-byte-p (ash size 3) src)))
    :gen-type t)

  )

;; ======================================================================
