; MULTIPLIER RULES

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2022 Intel Corporation

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

;; This  book includes  all  the  major books  in  the multiplier  verification
;; library  and  adds some  "bridge  rules"  to  convert expressions  from  SVL
;; (svexes)  to  expressions  recognized  by the  rewriter/meta  rules  of  the
;; multiplier verification library.

(in-package "RP")

(include-book "fnc-defs")

(include-book "svl-spec")

(include-book "meta-top")

(include-book "mult-rules")

(include-book "adder-rules")

(include-book "centaur/svl/top-bare" :dir :system)

(include-book "doc")

(local
 (include-book "lemmas"))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/ihs-extensions" :dir :system)
  use-ihs-extensions
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/logops-lemmas" :dir :system)
  use-ihs-logops-lemmas
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/quotient-remainder-lemmas" :dir :system)
  use-qr-lemmas
  :disabled t))

;; This  book includes  different books  with meta  rules in  them, RP-Rewriter
;; needs this event in such cases so  that it creates a new function that calls
;; all the meta rules and attaches them to its internal functions.
(attach-meta-fncs svl-mult-rules)

;; An RP-Rewriter suitable saturate function. Users may need to add a rewrite
;; rule to convert their saturate function in terms of this function.
(define saturate-for-rp ((num integerp)
                         (num-size posp)
                         (dest-size posp)
                         (signed booleanp))
  :verify-guards nil
  (cond ((>= dest-size num-size)
         (loghead dest-size num))
        (signed
         (sv::4vec-?* (sv::4vec-== (svl::bits num (1- num-size) 1) 1)
                      (sv::4vec-?* (sv::4vec-== (svl::bits num (1- dest-size)
                                                           (- num-size
                                                              dest-size))
                                                (svl::bits -1 0
                                                           (- num-size
                                                              dest-size)))
                                   (loghead dest-size num)
                                   (loghead dest-size
                                            (- (expt 2 (1- dest-size)))))
                      (sv::4vec-?* (sv::4vec-== (svl::bits num (1- dest-size)
                                                           (- num-size
                                                              dest-size))
                                                0)
                                   (loghead dest-size num)
                                   (1- (expt 2 (1- dest-size))))))
        (t (sv::4vec-?* (sv::4vec-== (svl::bits num dest-size (- num-size dest-size)) 0)
                        (loghead dest-size num)
                        (1- (expt 2 dest-size)))))
  ///
  (rp::add-rp-rule saturate-for-rp))

;; ---------------------------------------------------------------------------
;; misc lemmas

(def-rp-rule sign-ext-compress
  (implies (bitp x)
           (and (equal (svl::4vec-concat$ 1 x (rp::-- x))
                       (rp::-- x))
                (equal (logapp 1 x (rp::-- x))
                       (rp::-- x))
                (equal (svl::4vec-concat$ 1 x (unary-- x))
                       (rp::-- x))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(def-rp-rule minus-of-minus
  (implies (integerp x)
           (equal (- (- x))
                  x)))

(def-rp-rule integerp-of-bit-of
  (integerp (bit-of num pos)))

(def-rp-rule integerp-of-binary-fncs
  (and (integerp (binary-or x y))
       (integerp (binary-xor x y))
       (integerp (binary-and x y))
       (integerp (binary-? x y z))
       (integerp (binary-not x))
       (integerp (bit-of x y))))

(def-rp-rule integerp--
  (integerp (-- x)))

(local
 (defthm bits-when-bitp-start=0
   (implies (bitp x)
            (equal (svl::bits x 0 1)
                   x))
   :hints (("Goal"
            :in-theory (e/d (bitp) ())))))

(defthmd equal-of-concat$-with-hyp
  (implies (equal x1 x2)
           (equal (equal (svl::4vec-concat$ 1 x1 rest1)
                         (svl::4vec-concat$ 1 x2 rest2))
                  (equal (sv::4vec-fix rest1)
                         (sv::4vec-fix rest2))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(def-rp-rule nth-of-cons
  (and (equal (nth 0 (cons a b)) a)
       (implies (posp index)
                (equal (nth index (cons a b))
                       (nth (1- index) b)))))

(def-rp-rule integer-listp-of-cons
  (equal (integer-listp (cons a b))
         (and (integerp a)
              (integer-listp b))))

(def-rp-rule svex-env-fix$inline-opener
  (implies (sv::svex-env-p x)
           (equal (sv::svex-env-fix$inline x)
                  x)))

(def-rp-rule sv::svex-alist-eval-for-symbolic-is-svex-alist-eval
  (equal (sv::svex-alist-eval-for-symbolic x y z)
         (sv::svex-alist-eval x y)))

(rp::add-rp-rule acl2::fast-logext-fn)

;; ---------------------------------------------------------------------------
;; 4vec-?* lemmas
(progn
  ;; The rewrite rule  4vec-?*-of-with-bitp-cond has a larger rhs  than lhs and
  ;; it can potentially  cause infinite rewriting. i don't expect  ever that to
  ;; be the  case with the examples  i have seen with  sv::4vec-?* and existing
  ;; rewrite rules about  4vec functions but it is still  possible. to minimize
  ;; the    risk    of    infinite    rewriting,   i    use    this    funciton
  ;; 4vec-?*-of-with-bitp-cond-syn-check for syntactic check
  (define 4vec-?*-of-with-bitp-cond-syn-check (term lst)
    :hints (("goal"
             :in-theory (e/d ()
                             (+-is-sum))))
    (cond (lst
           (or (atom term)
               (and (4vec-?*-of-with-bitp-cond-syn-check (car term) nil)
                    (4vec-?*-of-with-bitp-cond-syn-check (cdr term) t))))
          (t (case-match term
               (('sv::4vec-rsh ('quote x) y)
                (if (and (integerp x)
                         (> x  100000)) ;; some  limit that we  should probably
                    ;; never reach
                    nil
                  (4vec-?*-of-with-bitp-cond-syn-check y nil)))
               (& (or (atom term)
                      (and (atom (car term))
                           (4vec-?*-of-with-bitp-cond-syn-check (cdr term)
                                                                t))))))))

  (def-rp-rule 4vec-?*-of-with-bitp-cond
    (implies (and (bitp x)
                  (integerp y)
                  (integerp z)
                  (syntaxp (and (4vec-?*-of-with-bitp-cond-syn-check y nil)
                                (4vec-?*-of-with-bitp-cond-syn-check z nil))))
             (equal (sv::4vec-?* (-- x) y z)
                    (svl::4vec-concat 1
                                      (sv::4vec-?* x
                                                   (sv::4vec-part-select 0 1 y)
                                                   (sv::4vec-part-select 0 1 z))
                                      (sv::4vec-?* (-- x)
                                                   (sv::4vec-rsh 1 y)
                                                   (sv::4vec-rsh 1 z)))))

    :hints (("goal"
             :use ((:instance svl::4vec-?*-of-with-bitp-cond
                              (svl::x x)
                              (svl::y y)
                              (svl::z z)))
             :in-theory (e/d (--) (svl::4vec-?*-of-with-bitp-cond)))))

  (def-rp-rule 4vec-?*-of-bits-with--cond
    (implies (and (bitp x)
                  (bitp y)
                  (bitp z))
             (equal (sv::4vec-?* (-- x) y z)
                    (sv::4vec-?* x y z)))
    :hints (("goal"
             :in-theory (e/d (bitp) ())))))


;; -------------------------------------------------------------------------
;; 4vec-symwildeq lemmas

(def-rp-rule 4vec-symwildeq-of-1-with-bitp
  (implies (bitp x)
           (equal (sv::4vec-symwildeq 1 x)
                  (-- x)))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(progn
  (def-rp-rule 4vec-symwildeq-with-constant
    (implies (and (integerp x)
                  (posp y)
                  (syntaxp (or (integerp y)
                               (and (quotep y)
                                    (integerp (unquote y))))))
             (equal (sv::4vec-symwildeq x y)
                    (-- (sv::4vec-bitand
                         (if (equal (acl2::logcar y) 1)
                             (acl2::logcar x)
                           (svl::4vec-bitnot$ 1 (acl2::logcar x)))
                         (-- (sv::4vec-symwildeq (acl2::logcdr x)
                                                 (acl2::logcdr
                                                  y)))))))
    :hints (("Goal"
             :use ((:instance svl::4VEC-SYMWILDEQ-with-constant
                              (svl::x x)
                              (svl::y y)))
             :in-theory (e/d* (--)
                              (svl::4VEC-SYMWILDEQ-with-constant
                               (:DEFINITION FLOOR)

                               (:DEFINITION ACL2::IFLOOR$INLINE)
                               (:DEFINITION ACL2::IMOD$INLINE)
                               (:DEFINITION ACL2::LOGCAR$INLINE)
                               (:DEFINITION ACL2::LOGCDR$INLINE))))))

  (def-rp-rule 4vec-symwildeq-with-bits-and-zero
    (implies (and (integerp x)
                  (posp size)
                  (natp start))
             (equal (sv::4vec-symwildeq (svl::bits x start size) 0)
                    (-- (sv::4vec-bitand (svl::4vec-bitnot$ 1 (svl::bits x start 1))
                                         (-- (sv::4vec-symwildeq (svl::bits x (1+ start)
                                                                            (1- size))
                                                                 0))))))
    :hints (("Goal"
             :use ((:instance svl::4VEC-SYMWILDEQ-with-constant
                              (svl::x (svl::bits x start size))
                              (svl::y 0)))
             :cases ((>= size 2))
             :in-theory (e/d (svl::logcar-to-bits
                              svl::logcdr-to-4vec-rsh
                              --)
                             (+-IS-SUM
                              (:definition acl2::ifloor$inline)
                              (:definition acl2::imod$inline)
                              (:definition acl2::logcar$inline)
                              (:definition acl2::logcdr$inline)
                              (:definition floor))))))

  (def-rp-rule 4vec-symwildeq-with-concat$-and-zero
    (implies (and (integerp x)
                  (integerp y)
                  (posp size))
             (equal (sv::4vec-symwildeq (svl::4vec-concat$ size x y) 0)
                    (-- (sv::4vec-bitand (svl::4vec-bitnot$ 1 (svl::bits x 0 1))
                                         (-- (sv::4vec-symwildeq (sv::4vec-rsh 1
                                                                               (svl::4vec-concat$ size x y))
                                                                 0))))))
    :hints (("goal"
             :cases ((>= size 2))
             :expand ((SVL::4VEC-BITNOT$ 1 (SVL::4VEC-CONCAT$ SIZE X Y)))
             ;;:expand ((SVL::4VEC-CONCAT$ SIZE X Y))
             :use ((:instance svl::4VEC-SYMWILDEQ-with-constant
                              (svl::x (svl::4vec-concat$ size x y))
                              (svl::y 0)))
             :in-theory (e/d (svl::logcar-to-bits
                              SV::4VEC->lower
                              SVL::4VEC-BITNOT$
                              ;;sv::4vec-concat
                              SV::4VEC->UPPER
                              svl::logcdr-to-4vec-rsh
                              ;;SVL::4VEC-CONCAT$
                              --
                              SVL::BITS-OF-CONCAT-1-NO-SYNTAXP)
                             (+-IS-SUM
                              (:definition acl2::ifloor$inline)
                              (:definition acl2::imod$inline)
                              (:definition acl2::logcar$inline)
                              (:definition acl2::logcdr$inline)
                              (:definition floor))))))

  (def-rp-rule 4vec-symwildeq-with-bitp
    (implies (and (bitp x))
             (and (equal (sv::4vec-symwildeq x 0)
                         (-- (svl::4vec-bitnot$ 1 x)))
                  (equal (sv::4vec-symwildeq x 1)
                         (-- x))))
    :hints (("Goal"
             :in-theory (e/d (bitp) ())))))

;; ---------------------------------------------------------------------------
;; 4vec-== lemmas
(progn
  (def-rp-rule 4vec-==-with-constant
    (implies (and (integerp x)
                  (posp y)
                  (syntaxp (or (integerp y)
                               (and (quotep y)
                                    (integerp (unquote y))))))
             (equal (sv::4vec-== x y)
                    (-- (sv::4vec-bitand (if (equal (acl2::logcar y) 1)
                                             (acl2::logcar x)
                                           (svl::4vec-bitnot$ 1 (acl2::logcar x)))
                                         (-- (sv::4vec-== (acl2::logcdr x)
                                                          (acl2::logcdr y)))))))
    :hints (("Goal"
             :use ((:instance svl::4vec-==-with-constant
                              (svl::x x)
                              (svl::y y)))
             :in-theory (e/d (--)
                             (svl::4vec-==-with-constant)))))

  (def-rp-rule 4vec-==-with-bits-and-zero
    (implies (and (integerp x)
                  (posp size)
                  (natp start))
             (equal (sv::4vec-== (svl::bits x start size) 0)
                    (-- (sv::4vec-bitand (svl::4vec-bitnot$ 1 (svl::bits x start 1))
                                         (-- (sv::4vec-== (svl::bits x (1+ start)
                                                                     (1- size))
                                                          0))))))
    :hints (("goal"
             :use ((:instance svl::4vec-==-with-constant
                              (svl::x (svl::bits x start size))
                              (svl::y 0)))
             :in-theory (e/d (svl::logcar-to-bits
                              svl::logcdr-to-4vec-rsh
                              --)
                             (+-IS-SUM
                              (:definition acl2::ifloor$inline)
                              (:definition acl2::imod$inline)
                              (:definition acl2::logcar$inline)
                              (:definition acl2::logcdr$inline)
                              (:definition floor))))))

  (def-rp-rule 4vec-==-with-concat-and-zero
    (implies (and (integerp x)
                  (integerp y)
                  (posp size))
             (equal (sv::4vec-== (svl::4vec-concat$ size x y) 0)
                    (-- (sv::4vec-bitand (svl::4vec-bitnot$ 1 (svl::bits x 0 1))
                                         (-- (sv::4vec-== (sv::4vec-rsh 1 (svl::4vec-concat$ size x y))
                                                          0))))))
    :hints (("goal"
             :cases ((>= size 2))
             :expand ((SVL::4VEC-BITNOT$ 1 (SVL::4VEC-CONCAT$ SIZE X Y)))
             ;;:expand ((SVL::4VEC-CONCAT$ SIZE X Y))
             :use ((:instance svl::4vec-==-with-constant
                              (svl::x (svl::4vec-concat$ size x y))
                              (svl::y 0)))
             :in-theory (e/d (svl::logcar-to-bits
                              SV::4VEC->lower
                              SVL::4VEC-BITNOT$
                              ;;sv::4vec-concat
                              SV::4VEC->UPPER
                              svl::logcdr-to-4vec-rsh
                              ;;SVL::4VEC-CONCAT$
                              --
                              SVL::BITS-OF-CONCAT-1-NO-SYNTAXP)
                             (+-IS-SUM
                              (:definition acl2::ifloor$inline)
                              (:definition acl2::imod$inline)
                              (:definition acl2::logcar$inline)
                              (:definition acl2::logcdr$inline)
                              (:definition floor))))))

  (def-rp-rule 4vec-==-with-bit-of
    (implies (and (integerp x)
                  (natp start))
             (and (equal (sv::4vec-== (bit-of x start) 0)
                         (-- (svl::4vec-bitnot$ 1 (bit-of x start))))
                  (equal (sv::4vec-== (bit-of x start) 1)
                         (-- (bit-of x start)))))
    :hints (("Goal"
             :expand ((bit-of x start))
             :in-theory (e/d () ())))))

(def-rp-rule 4vec-==-of=bitp-and-constant-bitp
  (implies (bitp x)
           (and (equal (sv::4vec-== x 0)
                       (-- (binary-not x)))
                (equal (sv::4vec-== x 1)
                       (-- x))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))


;; ---------------------------------------------------------------------------
;; SVL functions (bits, 4vec-rsh, etc.) and bit-of lemmas

(encapsulate
  nil

  (local
   (use-arithmetic-5 t))

  (defthm bits-is-bit-of-nosyntaxp
    (implies (and (integerp num)
                  (natp start))
             (equal (svl::bits num start 1)
                    (bit-of num start)))
    :hints (("goal"
             :in-theory (e/d (bitp
                              oddp
                              evenp
                              bit-of
                              sv::4vec-part-select
                              svl::bits
                              sv::4vec->lower
                              sv::2vec
                              sv::4vec-rsh
                              sv::4vec->upper
                              sv::4vec-zero-ext
                              sv::4vec
                              sv::4vec-shift-core
                              logbitp
                              ifix
                              mod
                              expt
                              ash
                              logbit
                              loghead
                              )
                             (svl::bitp-bits-size=1
                              (:rewrite sv::4vec-equal)
                              (:definition acl2::expt2$inline)
                              (:rewrite acl2::remove-weak-inequalities)
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-zero-ext-is-bits
                              svl::4vec-zero-ext-is-4vec-concat
                              svl::4vec-concat$-of-term2=0

                              svl::4vec-part-select-is-bits)))))

  (def-rp-rule bits-is-bit-of
    (implies (and (syntaxp (atom (ex-from-rp num)))
                  (integerp num)
                  (natp start))
             (equal (svl::bits num start 1)
                    (bit-of num start)))
    :hints (("Goal"
             :in-theory (e/d (bits-is-bit-of-nosyntaxp) ()))))

  (def-rp-rule integerp-of-nth
    (implies (and (integer-listp lst)
                  (natp index)
                  (< index (len lst)))
             (integerp (nth index lst)))
    :hints (("Goal"
             :in-theory (e/d (sum)
                             (+-IS-SUM)))))

  (def-rp-rule bits-is-bit-of-for-nth
    (implies (and (natp start)
                  (force (natp x))
                  (force (< x (len y)))
                  (integer-listp y))
             (equal (svl::bits (nth x y) start 1)
                    (bit-of (nth x y) start)))
    :hints (("Goal"
             :in-theory (e/d (bits-is-bit-of-nosyntaxp) ()))))

  (defthmd bits-is-bit-of-reverse
    (implies (and (integerp num)
                  (natp start))
             (equal (bit-of num start)
                    (svl::bits num start 1)))))

(def-rp-rule bits-of-bit-of-out-of-range
  (implies (and (posp start)
                (natp size))
           (equal (svl::bits (bit-of x pos) start size)
                  0)))

(def-rp-rule bits-of-bit-of
  (equal (svl::bits (bit-of x pos) 0 1)
         (bit-of x pos))
  :otf-flg t
  :hints (("Goal"
           :do-not '(preprocess)
           :cases ((bitp (bit-of x pos)))
           :in-theory (e/d (bitp)
                           (BITP-OF-BIT-OF
                            (:TYPE-PRESCRIPTION BIT-OF))))
          ("Subgoal 2"
           :in-theory (e/d () ()))))

(def-rp-rule 4vec-rsh-of-bit-of-out-of-range
  (implies (posp amount)
           (equal (sv::4vec-rsh amount (bit-of x pos))
                  0)))


;; ---------------------------------------------------------------------------
;; 4vec   logical  operators   (4vec-?,   4vec-?*,  4vec-bitxor,   4vec-bitand,
;; 4vec-bitor,  4vec-bitnot) to  binary-fncs  (binary-?, binary-?,  binary-xor,
;; binary-and, binary-or, binary-not, respectively)
(progn
  (def-rp-rule 4vec-?-is-binary-?-when-bitp
    (implies (and (bitp x)
                  (bitp y)
                  (bitp z))
             (equal (sv::4vec-? x y z)
                    (binary-? x y z)))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-?-is-binary-?-when-integerp-1
    (implies (and (integerp x)
                  (natp start)
                  (bitp y)
                  (bitp z))
             (and (equal (sv::4vec-? (svl::bits x start 1) y z)
                         (binary-? (bits-to-bit-of (svl::bits x start 1)) y z))
                  (equal (sv::4vec-? y (svl::bits x start 1) z)
                         (binary-? y (bits-to-bit-of (svl::bits x start 1)) z))
                  (equal (sv::4vec-? y z (svl::bits x start 1))
                         (binary-? y z (bits-to-bit-of (svl::bits x start 1))))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-?-is-binary-?-when-integerp-2
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (integerp y)
                  (bitp z))
             (and (equal (sv::4vec-? (svl::bits x start1 1) (svl::bits y start2 1) z)
                         (binary-? (bits-to-bit-of (svl::bits x start1 1)) (bits-to-bit-of (svl::bits y start2 1)) z))
                  (equal (sv::4vec-? (svl::bits x start1 1) z (svl::bits y start2 1))
                         (binary-? (bits-to-bit-of (svl::bits x start1 1)) z (bits-to-bit-of (svl::bits y start2 1))))
                  (equal (sv::4vec-? z (svl::bits x start1 1) (svl::bits y start2 1))
                         (binary-? z (bits-to-bit-of (svl::bits x start1 1)) (bits-to-bit-of (svl::bits y start2 1))))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-?-is-binary-?-when-integerp-3
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (natp start3)
                  (integerp y)
                  (integerp z))
             (and (equal (sv::4vec-? (svl::bits x start1 1) (svl::bits y start2 1) (svl::bits z start3 1))
                         (binary-? (bits-to-bit-of (svl::bits x start1 1))
                                   (bits-to-bit-of (svl::bits y start2 1))
                                   (bits-to-bit-of (svl::bits z start3 1))))
                  ))
    :hints (("goal"
             :in-theory (e/d (bitp) ())))))

(progn
  (def-rp-rule 4vec-?*-is-binary-?-when-bitp
    (implies (and (bitp x)
                  (bitp y)
                  (bitp z))
             (equal (sv::4vec-?* x y z)
                    (binary-? x y z)))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-?*-is-binary-?-when-integerp-1
    (implies (and (integerp x)
                  (natp start)
                  (bitp y)
                  (bitp z))
             (and (equal (sv::4vec-?* (svl::bits x start 1) y z)
                         (binary-? (bit-of x start) y z))
                  (equal (sv::4vec-?* y (svl::bits x start 1) z)
                         (binary-? y (bit-of x start) z))
                  (equal (sv::4vec-?* y z (svl::bits x start 1))
                         (binary-? y z (bit-of x start)))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-?*-is-binary-?-when-integerp-2
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (integerp y)
                  (bitp z))
             (and (equal (sv::4vec-?* (svl::bits x start1 1) (svl::bits y start2 1) z)
                         (binary-? (bits-to-bit-of (svl::bits x start1 1)) (bits-to-bit-of (svl::bits y start2 1)) z))
                  (equal (sv::4vec-?* (svl::bits x start1 1) z (svl::bits y start2 1))
                         (binary-? (bits-to-bit-of (svl::bits x start1 1)) z (bits-to-bit-of (svl::bits y start2 1))))
                  (equal (sv::4vec-?* z (svl::bits x start1 1) (svl::bits y start2 1))
                         (binary-? z (bits-to-bit-of (svl::bits x start1 1)) (bits-to-bit-of (svl::bits y start2 1))))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-?*-is-binary-?-when-integerp-3
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (natp start3)
                  (integerp y)
                  (integerp z))
             (and (equal (sv::4vec-?* (svl::bits x start1 1) (svl::bits y start2 1) (svl::bits z start3 1))
                         (binary-? (bits-to-bit-of (svl::bits x start1 1))
                                   (bits-to-bit-of (svl::bits y start2 1))
                                   (bits-to-bit-of (svl::bits z start3 1))))
                  ))
    :hints (("goal"
             :in-theory (e/d (bitp) ())))))

(progn
  (def-rp-rule 4vec-bitxor-is-binary-xor-when-bitp
    (implies (and (bitp x)
                  (bitp y))
             (and (equal (sv::4vec-bitxor x y)
                         (binary-xor x y))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-bitxor-is-binary-xor-when-integerp-1
    (implies (and (integerp x)
                  (natp start)
                  (bitp y))
             (and (equal (sv::4vec-bitxor (svl::bits x start 1)  y)
                         (binary-xor (bits-to-bit-of (svl::bits x start 1))
                                     y))
                  (equal (sv::4vec-bitxor y (svl::bits x start 1))
                         (binary-xor y
                                     (bits-to-bit-of (svl::bits x start 1))))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-bitxor-is-binary-xor-when-integerp-2
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (integerp y))
             (and (equal (sv::4vec-bitxor (svl::bits x start1 1) (svl::bits y start2 1))
                         (binary-xor (bits-to-bit-of (svl::bits x start1 1))
                                     (bits-to-bit-of (svl::bits y start2 1))))))
    :hints (("goal"
             :in-theory (e/d (bitp) ())))))

(progn
  (encapsulate
    nil
    (local
     (use-arithmetic-5 t))

    (def-rp-rule
      4vec-bitand-to-binary-and-when-atleast-one-is-bitp
      (implies (or (and (bitp x)
                        (integerp (svl::bits y 0 1)))
                   (and (bitp y)
                        (integerp (svl::bits x 0 1))))
               (equal (sv::4vec-bitand x y)
                      (binary-and (svl::bits x 0 1)
                                  (svl::bits y 0 1))))
      :hints (("Goal"
               :in-theory (e/d (bitp
                                bit-of
                                svl::Bits
                                SV::4VEC-PART-SELECT
                                SV::3VEC-BITAND
                                SV::4VEC->UPPER
                                SV::4VEC->LOWER
                                SV::3VEC-FIX
                                sv::4vec-bitand
                                SV::4VEC-ZERO-EXT
                                )
                               (mod2-is-m2

                                SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
                                +-IS-SUM
                                floor2-if-f2))))))

  (def-rp-rule 4vec-bitand-is-binary-and-when-bitp
    (implies (and (bitp x)
                  (bitp y))
             (and (equal (sv::4vec-bitand x y)
                         (binary-and x y))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-bitand-is-binary-and-when-integerp-1
    (implies (and (integerp x)
                  (natp start)
                  (bitp y))
             (and (equal (sv::4vec-bitand (svl::bits x start 1)  y)
                         (binary-and (bits-to-bit-of (svl::bits x start 1)) y))
                  (equal (sv::4vec-bitand y (svl::bits x start 1))
                         (binary-and y (bits-to-bit-of (svl::bits x start 1))))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-bitand-is-binary-and-when-integerp-2
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (integerp y))
             (and (equal (sv::4vec-bitand (svl::bits x start1 1) (svl::bits y start2 1))
                         (binary-and (bits-to-bit-of (svl::bits x start1 1)) (bits-to-bit-of (svl::bits y start2 1))))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  ;; Below side-conditions are probably unnecessary but I am keeping them
  ;; because they don't hurt and may be useful some day
  (defthm 4vec-bitand-is-binary-and-side-cond
    (and (bitp (binary-and (svl::bits x 0 1)
                           (svl::bits y 0 1)))
         (bitp (binary-and x y))
         (bitp (binary-and (bits-to-bit-of (svl::bits x start 1)) y))
         (bitp (binary-and y (bits-to-bit-of (svl::bits x start 1))))
         (bitp (binary-and (bits-to-bit-of (svl::bits x start1 1))
                           (bits-to-bit-of (svl::bits y start2 1))))))

  (rp-attach-sc 4vec-bitand-to-binary-and-when-atleast-one-is-bitp
                4vec-bitand-is-binary-and-side-cond)

  (rp-attach-sc 4vec-bitand-is-binary-and-when-bitp
                4vec-bitand-is-binary-and-side-cond)

  (rp-attach-sc 4vec-bitand-is-binary-and-when-integerp-1
                4vec-bitand-is-binary-and-side-cond)

  (rp-attach-sc 4vec-bitand-is-binary-and-when-integerp-2
                4vec-bitand-is-binary-and-side-cond))

(progn
  (def-rp-rule 4vec-bitor-is-binary-or-when-bitp
    (implies (and (bitp x)
                  (bitp y))
             (and (equal (sv::4vec-bitor x y)
                         (binary-or x y))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-bitor-is-binary-or-when-integerp-1
    (implies (and (integerp x)
                  (natp start)
                  (bitp y))
             (and (equal (sv::4vec-bitor (svl::bits x start 1)  y)
                         (binary-or (bits-to-bit-of (svl::bits x start 1)) y))
                  (equal (sv::4vec-bitor y (svl::bits x start 1))
                         (binary-or y (bits-to-bit-of (svl::bits x start 1))))))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule 4vec-bitor-is-binary-or-when-integerp-2
    (implies (and (integerp x)
                  (natp start1)
                  (natp start2)
                  (integerp y))
             (and (equal (sv::4vec-bitor (svl::bits x start1 1) (svl::bits y start2 1))
                         (binary-or (bits-to-bit-of (svl::bits x start1 1)) (bits-to-bit-of (svl::bits y start2 1))))))
    :hints (("goal"
             :in-theory (e/d (bitp) ())))))

(def-rp-rule 4vec-bitor-of---
  (implies (and (bitp x)
                (bitp y))
           (equal (sv::4vec-bitor (-- x)
                                  (-- y))
                  (-- (binary-or x y))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(encapsulate
  nil
  (local
   (use-arithmetic-5 t))
  (def-rp-rule 4vec-bitnot$-binary-not-when-integerp
    (implies (and (integerp x))
             (equal (svl::4vec-bitnot$ 1 x)
                    (binary-not (bit-of x 0))))
    :hints (("Goal"
             :in-theory (e/d (bitp
                              SV::4VEC-BITNOT
                              SV::3VEC-BITNOT
                              SV::4VEC->LOWER
                              SV::4VEC->UPPER
                              SV::4VEC
                              SV::4VEC-PART-SELECT
                              svl::4vec-bitnot$
                              bit-of
                              not$
                              m2
                              f2
                              SV::4VEC-CONCAT
                              )
                             (+-IS-SUM
                              SVL::LOGBITP-TO-BITS
                              MOD2-IS-M2
                              floor2-if-f2
                              SVL::4VEC-CONCAT$-OF-TERM2=0
                              SVL::EQUAL-OF-4VEC-CONCAT-WITH-SIZE=1)))))

  (def-rp-rule 4vec-bitnot$-binary-not-when-bitp
    (implies (bitp x)
             (equal (svl::4vec-bitnot$ 1 x)
                    (binary-not x)))
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule convert-4vec-bitnot$-binary-not-when-in-bits
    (implies (and (integerp x)
                  (natp start))
             (equal (svl::4vec-bitnot$ 1 (svl::bits x start 1))
                    (binary-not (bits-to-bit-of (svl::bits x start 1)))))
    :hints (("Goal"
             :in-theory (e/d (bitp) ())))))



;; --------------------------------------------------------------------------------
;; SVL/4vec functions and their trivial interactions with this book's functions

(def-rp-rule bits-of---bitp-neg
  (implies (bitp x)
           (equal (svl::bits (-- x) 0 1)
                  x))
  :hints (("goal"
           :in-theory (e/d (bitp) ()))))

(def-rp-rule 4vec-fix=-of-binary-fns
  (and (equal (svl::4vec-fix (binary-not s))
              (binary-not s))
       (equal (svl::4vec-fix (or$ x y))
              (or$ x y))
       (equal (svl::4vec-fix (and$ x y))
              (and$ x y))
       (equal (svl::4vec-fix (binary-xor x y))
              (binary-xor x y))
       (equal (svl::4vec-fix (adder-and x y))
              (adder-and x y))
       (equal (svl::4vec-fix (m2 x))
              (m2 x))
       (equal (svl::4vec-fix (f2 x))
              (f2 x))))

(def-rp-rule 3vec-fix-of-binary-fncs
  (and (equal (sv::3vec-fix (binary-and a b))
              (binary-and a b))
       (equal (sv::3vec-fix (binary-or a b))
              (binary-or a b))
       (equal (sv::3vec-fix (binary-xor a b))
              (binary-xor a b))
       (equal (sv::3vec-fix (binary-? a b c))
              (binary-? a b c))
       (equal (sv::3vec-fix (binary-not a))
              (binary-not a)))
  :hints (("goal"
           :in-theory (e/d (binary-?
                            binary-and
                            binary-not
                            binary-or
                            binary-xor)
                           (equal-sides-to-s)))))

(def-rp-rule 4vec-rsh-of-binary-fncs
  (implies (posp size)
           (and (equal (sv::4vec-rsh size (binary-or x y))
                       0)
                (equal (sv::4vec-rsh size (binary-and x y))
                       0)
                (equal (sv::4vec-rsh size (binary-xor x y))
                       0)
                (equal (sv::4vec-rsh size (binary-? x y z))
                       0)
                (equal (sv::4vec-rsh size (binary-not x))
                       0))))

(def-rp-rule 4vec-==-of-binary-fncs-with-1
  (implies t
           (and (equal (SV::4VEC-== 1 (binary-or x y))
                       (-- (binary-or x y)))
                (equal (SV::4VEC-== (binary-or x y) 1)
                       (-- (binary-or x y)))
                (equal (SV::4VEC-== 1 (binary-and x y))
                       (-- (binary-and x y)))
                (equal (SV::4VEC-== (binary-and x y) 1)
                       (-- (binary-and x y)))
                (equal (SV::4VEC-== 1 (binary-xor x y))
                       (-- (binary-xor x y)))
                (equal (SV::4VEC-== (binary-xor x y) 1)
                       (-- (binary-xor x y)))
                (equal (SV::4VEC-== 1 (binary-not x))
                       (-- (binary-not x)))
                (equal (SV::4VEC-== (binary-not x) 1)
                       (-- (binary-not x)))
                (equal (SV::4VEC-== 1 (binary-? x y z))
                       (-- (binary-? x y z)))
                (equal (SV::4VEC-== (binary-? x y z) 1)
                       (-- (binary-? x y z)))))
  :otf-flg t
  :hints (("Goal"
           :use ((:instance (:TYPE-PRESCRIPTION BIT-FIX))
                 (:instance (:TYPE-PRESCRIPTION BIT-FIX)
                            (x y))
                 (:instance (:TYPE-PRESCRIPTION BIT-FIX)
                            (x z)))
           :in-theory (e/d (or$
                            and$
                            not$
                            binary-xor
                            binary-?)
                           ((:TYPE-PRESCRIPTION BIT-FIX))))))

(def-rp-rule 4vec-fix-of-bit-of
  (equal (svl::4vec-fix (bit-of x pos))
         (bit-of x pos))
  :hints (("goal"
           :in-theory (e/d (bit-of
                            bitp)
                           (bit-fix)))))

(def-rp-rule 3vec-fix-of-bit-of
  (equal (sv::3vec-fix (bit-of x index))
         (bit-of x index)))

(encapsulate
  nil
  (local
   (use-arithmetic-5 t))
  (defthmd bits-of-binary-fns-lemma
    (implies (and (not (zp start))
                  (bitp x))
             (equal (svl::bits x start 1 )
                    0)))

  (defthmd bits-of-binary-fns-lemma-2
    (implies (and (posp size)
                  (bitp x))
             (equal (svl::bits x 0 size )
                    x)))

  (def-rp-rule bits-of-binary-fns
    (implies (not (zp start))
             (and (equal (svl::bits (or$ x y) start 1 )
                         0)
                  (equal (svl::bits (and$ x y) start 1 )
                         0)
                  (equal (svl::bits (and-list hash-code x) start 1 )
                         0)
                  (equal (svl::bits (not$ x) start 1 )
                         0)
                  (equal (svl::bits (binary-xor x y) start 1 )
                         0)
                  (equal (svl::bits (binary-? x y z) start 1 )
                         0)
                  (equal (svl::bits (bit-of x y) start 1 )
                         0)
                  (equal (svl::bits (adder-and x y) start 1 )
                         0)))
    :hints (("goal"
             :do-not '(preprocess)
             :in-theory (e/d (bits-of-binary-fns-lemma)
                             (svl::4vec-part-select-is-bits
                              +-is-sum
                              svl::4vec-zero-ext-is-bits
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-concat$-of-term2=0
                              svl::4vec-zero-ext-is-4vec-concat)))))

  (def-rp-rule bits-of-binary-fns-start=0
    (implies (posp size)
             (and (equal (svl::bits (or$ x y) 0 size )
                         (or$ x y))
                  (equal (svl::bits (and$ x y) 0 size )
                         (and$ x y))
                  (equal (svl::bits (and-list hash-code x) 0 size )
                         (and-list hash-code x))
                  (equal (svl::bits (not$ x) 0 size )
                         (not$ x))
                  (equal (svl::bits (binary-xor x y) 0 size )
                         (binary-xor x y))
                  (equal (svl::bits (binary-? x y z) 0 size )
                         (binary-? x y z))
                  (equal (svl::bits (bit-of x y) 0 size )
                         (bit-of x y))
                  (equal (svl::bits (adder-and x y) 0 size )
                         (adder-and x y))
                  (equal (svl::bits (adder-or x y) 0 size )
                         (adder-or x y))))
    :hints (("goal"
             :do-not '(preprocess)
             :in-theory (e/d (bits-of-binary-fns-lemma-2)
                             (svl::4vec-part-select-is-bits
                              bits-is-bit-of
                              +-is-sum
                              svl::4vec-zero-ext-is-bits
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-concat$-of-term2=0
                              svl::4vec-zero-ext-is-4vec-concat))))))

(encapsulate
  nil

  (local
   (use-arithmetic-5 t))

  (local
   (defthm lemma1
     (implies (and (not (zp start))
                   (bitp x))
              (equal (bit-of x start)
                     0))
     :hints (("goal"
              :in-theory (e/d (bitp bit-of) ())))))

  (local
   (defthm lemma2
     (implies (and (bitp x))
              (equal (bit-of x 0)
                     x))
     :hints (("goal"
              :in-theory (e/d (bitp bit-of) ())))))

  ;; these lemmas are left disabled because "bit-of" should only appear when
  ;; the first argument is an atom. so we should not need these lemmas. but i
  ;; leave these lemmas here just in case.

  (def-rp-rule :disabled t
    bit-of-binary-fns
    (implies (not (zp start))
             (and (equal (bit-of (or$ x y) start )
                         0)
                  (equal (bit-of (and$ x y) start)
                         0)
                  (equal (bit-of (not$ x) start)
                         0)
                  (equal (bit-of (binary-xor x y) start )
                         0)
                  (equal (bit-of (binary-? x y z) start )
                         0)))
    :hints (("goal"
             :do-not '(preprocess)
             :in-theory (e/d (bitp)
                             (svl::4vec-part-select-is-bits
                              equal-sides-to-s
                              svl::4vec-zero-ext-is-bits
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-concat$-of-term2=0
                              svl::4vec-zero-ext-is-4vec-concat)))))

  (def-rp-rule :disabled t
    bit-of-binary-fns-start=0
    (implies t
             (and (equal (bit-of (or$ x y) 0 )
                         (or$ x y))
                  (equal (bit-of (and$ x y) 0)
                         (and$ x y))
                  (equal (bit-of (not$ x) 0)
                         (not$ x))
                  (equal (bit-of (binary-xor x y) 0)
                         (binary-xor x y))
                  (equal (bit-of (binary-? x y z) 0)
                         (binary-? x y z))))
    :hints (("goal"
             :do-not '(preprocess)
             :in-theory (e/d ()
                             (svl::4vec-part-select-is-bits
                              svl::4vec-zero-ext-is-bits
                              svl::convert-4vec-concat-to-4vec-concat$
                              svl::4vec-concat$-of-term2=0
                              svl::4vec-zero-ext-is-4vec-concat)))))

  (def-rp-rule :disabled t
    bit-of-4vec-bitnot-main
    (implies (bitp x)
             (equal (bit-of (sv::4vec-bitnot x) 0)
                    (svl::4vec-bitnot$ 1 x)))
    :hints (("goal"
             :in-theory (e/d (bitp) (bitp-of-bit-of
                                     (:type-prescription bit-of)
                                     )))))

  (def-rp-rule :disabled t
    bit-of-4vec-bitnot
    (equal (bit-of (sv::4vec-bitnot (bit-of x start)) 0)
           (svl::4vec-bitnot$ 1 (bit-of x start)))
    :hints (("goal"
             :use ((:instance bitp-of-bit-of
                              (num x)
                              (pos start)))
             :in-theory (e/d (bitp) (bitp-of-bit-of
                                     (:type-prescription bit-of)))))))

(def-rp-rule bits-of-4vec-==-binary-fncs
  (and (equal (svl::bits (sv::4vec-== (binary-or x y) 1) '0 '1)
              (binary-or x y))
       (equal (svl::bits (sv::4vec-== (binary-and x y) 1) '0 '1)
              (binary-and x y)))
  :hints (("goal"
           :in-theory (e/d (bitp and$ or$)
                           (equal-sides-to-s)))))

(progn
  (def-rp-rule bits-0-1-of-s
    (equal (svl::bits (s hash-code pp c/d) 0 1)
           (s hash-code pp c/d))
    :hints (("goal"
             :in-theory (e/d () ()))))

  (def-rp-rule bits-0-1-of-m2
    (equal (svl::bits (m2 x) 0 1)
           (m2 x))
    :hints (("goal"
             :in-theory (e/d () ()))))

  (def-rp-rule bits-1-1-of-s
    (implies (and (not (zp start))
                  (natp size))
             (equal (svl::bits (s hash-code pp c/d) start size)
                    0)))

  (def-rp-rule bits-1-1-of-m2
    (implies (and (not (zp start))
                  (natp size))
             (equal (svl::bits (m2 x) start size)
                    0))))

(progn
  (rp::def-rp-rule
    bits-of-c-when-bit-when-start>0
    (implies (and (bitp (rp::c hash-code x y z))
                  (posp start))
             (equal (svl::bits (rp::c hash-code x y z) start 1)
                    0))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (rp::def-rp-rule
    bits-of-c-when-bit-when-start-0
    (implies (and (bitp (rp::c hash-code x y z)))
             (equal (svl::bits (rp::c hash-code x y z) 0 1)
                    (rp::c  hash-code x y z)))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (defthm bits-of-c-when-bit-when-start-0-side-cond
    (implies (and (bitp (rp::c hash-code x y z)))
             (bitp (rp::c hash-code x y z)))
    :rule-classes nil)

  (rp-attach-sc bits-of-c-when-bit-when-start-0
                bits-of-c-when-bit-when-start-0-side-cond))

(progn
  (rp::def-rp-rule
    bits-of-s-c-res-when-bit-when-start>0
    (implies (and (bitp (rp::s-c-res x y z))
                  (posp start))
             (equal (svl::bits (rp::s-c-res x y z) start 1)
                    0))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (rp::def-rp-rule
    bits-of-s-c-res-when-bit-when-start=0
    (implies (and (bitp (rp::s-c-res x y z)))
             (equal (svl::bits (rp::s-c-res x y z) 0 1)
                    (rp::s-c-res x y z)))
    :hints (("goal"
             :in-theory (e/d (bitp) ()))))

  (defthm
    bits-of-s-c-res-when-bit-when-start=0-side-cond
    (implies (and (bitp (rp::s-c-res x y z)))
             (bitp (rp::s-c-res x y z)))
    :rule-classes nil)

  (rp-attach-sc bits-of-s-c-res-when-bit-when-start=0
                bits-of-s-c-res-when-bit-when-start=0-side-cond))

(def-rp-rule
  concat-of-adder-and-is-f2
  (implies (bitp other)
           (and (equal (svl::4vec-concat$ size
                                          (adder-and (bit-of x y) other)
                                          other2)
                       (svl::4vec-concat$ size
                                          (f2 (adder-sum (bit-of x y) other))
                                          other2))
                (equal (svl::4vec-concat$ size
                                          other2
                                          (adder-and (bit-of x y) other))
                       (svl::4vec-concat$ size
                                          other2
                                          (f2 (adder-sum (bit-of x y) other))))))
  :hints (("goal"
           :cases ((bitp (bit-of x y)))
           :in-theory (e/d (bitp)
                           ((:type-prescription bit-of)
                            (:rewrite bitp-of-bit-of))))))

(def-rp-rule :disabled t
  4vec-concat$-1-of-binary-and
  (equal (svl::4vec-concat$ 1 (and$ x y) z)
         (svl::4vec-concat$ 1 (s-spec (list (and$ x y))) z))
  :hints (("goal"
           :in-theory (e/d (and$) ()))))

(encapsulate
  nil
  (local
   (use-arithmetic-5 t))
  (defthmd insert-redundant-loghead-to-bits
    (implies (and (integerp a)
                  (natp x)
                  (natp y))
             (equal (svl::bits a x y)
                    (svl::bits (loghead (+ x y) a) x y)))
    :hints (("goal"
             :in-theory (e/d (svl::bits
                              sum
                              sv::4vec->upper
                              sv::4vec-shift-core
                              sv::4vec->lower
                              sv::4vec-rsh
                              sv::4vec-concat
                              sv::4vec-part-select)
                             (+-is-sum)))))
  ;; since there is a meta rule now that rewrites the * symbol. this lemma is
  ;; likely never used.
  (def-rp-rule bits-of-*
    (implies (and (integerp a)
                  (integerp b)
                  (natp x)
                  (natp y))
             (equal (svl::bits (* a b) x y)
                    (svl::bits (loghead (+ x y) (* a b)) x y)))
    :hints (("goal"
             :use ((:instance insert-redundant-loghead-to-bits
                              (a (* a b))))
             :in-theory (e/d () ())))))

(def-rp-rule bits-of---=of-bitp
  (implies (and (natp start)
                (bitp x))
           (equal (svl::bits (-- x) start 1)
                  x))
  :hints (("goal"
           :in-theory (e/d (svl::bits
                            bitp)
                           ()))))

(def-rp-rule bit-of-of-bits
  (implies (and (natp index)
                (natp start)
                (natp size)
                (integerp x))
           (equal (bit-of (svl::bits x start size) index)
                  (svl::bits (svl::bits x start size) index 1)))
  :hints (("goal"
           :use ((:instance bits-is-bit-of
                            (num (svl::bits x start size))
                            (start index)))
           :in-theory (e/d (bits-is-bit-of)
                           (
                            +-is-sum
                            svl::bits-of-bits-1)))))

;; -------------------------------------------------------------------------------
;; -------------------------------------------------------------------------------

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For when definitions of ha and fa modules are replaced with + sign:

;; it is necessary  to create this rewrite mechanism because  when output of an
;; ha becomes and input of another ha, it messes up with the system somehow and
;; some full-adders are not simplified as they  are supposed to. So I looked at
;; the   rw    stack   for    svl::bits-of-4vec-plus-is-4vec-plus-start=0   and
;; svl::bits-of-4vec-plus-is-4vec-plus  to  figure  out  what  fa  and  ha  are
;; rewritten to. And I decided to rewrite summation of single bit SV::4VEC-PLUS
;; to  temp-ha-spec. If  it is  added with  another SV::4VEC-PLUS,  then it  is
;; probably a part  of a full-adder, so  I convert that to fa  spec.  For other
;; adder types, other rewrite rules might be necessary.

;;;;;;;

;; First catch that strange case of 4vec-plus-chains

(local
 (defthm integerp-4vec-adder
   (implies (and (natp size)
                 (integerp x)
                 (integerp y)
                 (integerp carry-in))
            (integerp (4vec-adder x y carry-in size)))
   :rule-classes (:rewrite :type-prescription)
   :hints (("Goal"
            :in-theory (e/d (4VEC-ADDER) ())))))

(local
 (defthm integerp-bits
   (implies (and (natp start)
                 (natp size)
                 (integerp x))
            (integerp (svl::bits x start size)))
   :rule-classes (:type-prescription :rewrite)))

(local
 (defthm 4vec-part-select-start=0-for-integers-is-loghead
   (implies (and (natp size)
                 (integerp x))
            (equal (sv::4vec-part-select 0 size x)
                   (loghead size x)))
   :hints (("Goal"
            :in-theory (e/d (sv::4vec-part-select
                             SV::4VEC-CONCAT
                             ACL2::|arith (* 0 x)|
                             SV::4VEC->UPPER
                             SV::4VEC->lower)
                            ())))))

(encapsulate
  nil
  (local
   (use-arithmetic-5 t))

  (def-rp-rule :disabled-for-acl2 t
    unsigned-byte-p-redefined-with-loghead
    (implies (natp size)
             (equal (unsigned-byte-p size x)
                    (and (integerp x)
                         (equal x (loghead size x)))
                    #|(and (hide (unsigned-byte-p size x))
                    (integerp x) ; ; ; ;
                    (equal (ash x (- size)) 0))|#))
    :hints (("Goal"
             :expand ((hide (unsigned-byte-p size x)))
             :in-theory (e/d ((:REWRITE ACL2::ASH-TO-FLOOR)
                              (:REWRITE ACL2::FLOOR-ZERO . 1)
                              (:REWRITE MINUS-OF-MINUS)
                              (:REWRITE ACL2::REMOVE-WEAK-INEQUALITIES)
                              (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)
                              (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE)
                              (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE)
                              (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                             ()))))

  (defthmd unsigned-byte-p-redefined-with-loghead-for-atom
    (implies (and (natp size)
                  (syntaxp (atom x)))
             (equal (unsigned-byte-p size x)
                    (and (integerp x)
                         (equal x (loghead size x)))
                    #|(and (hide (unsigned-byte-p size x))
                    (integerp x) ; ; ;
                    (equal (ash x (- size)) 0))|#))
    :hints (("Goal"
             :expand ((hide (unsigned-byte-p size x)))
             :in-theory (e/d ((:REWRITE ACL2::ASH-TO-FLOOR)
                              (:REWRITE ACL2::FLOOR-ZERO . 1)
                              (:REWRITE MINUS-OF-MINUS)
                              (:REWRITE ACL2::REMOVE-WEAK-INEQUALITIES)
                              (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)
                              (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE)
                              (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE)
                              (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                             ()))))

  (def-rp-rule ash-implies-unsigned-byte-p
    (implies (and (integerp x)
                  (natp size)
                  (equal (ash x (- size)) 0))
             (unsigned-byte-p size x))
    :hints (("Goal"
             :in-theory (e/d ((:REWRITE ACL2::ASH-TO-FLOOR)
                              (:REWRITE ACL2::FLOOR-ZERO . 1)
                              (:REWRITE MINUS-OF-MINUS)
                              (:REWRITE ACL2::REMOVE-WEAK-INEQUALITIES)
                              (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)
                              (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE)
                              (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE)
                              (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
                             ())))))

(local
 (encapsulate
   nil

   (local
    (defthmd insert-loghead-to-plusp-lemma-1
      (implies (and (integerp x)
                    (<= x max1)
                    (integerp y)
                    (<= y max2)
                    (integerp z)
                    (<= z max3)
                    )
               (<= (+ x y z) (+ max1 max2 max3)))
      :otf-flg t
      :hints (("Goal"
               :in-theory (e/d* ()
                                (+-is-sum))))))

   (local
    (defthmd <=-to-<-for-integers
      (implies (and (integerp x)
                    (integerp y))
               (equal (<= x y)
                      (< x (1+ y))))
      :rule-classes (:rewrite)
      :hints (("Goal"
               :in-theory (e/d ()
                               (+-is-sum))))))

   (local
    (defthmd insert-loghead-to-plusp-lemma-2
      (implies (natp size)
               (equal (+ (EXPT 2 SIZE) (EXPT 2 SIZE))
                      (EXPT 2 (1+ SIZE))))
      :hints (("Goal"
               :in-theory (e/d () (+-is-sum))))))

   (local
    (defthmd insert-loghead-to-plusp-lemma-3
      (implies (natp size)
               (equal (* 2 (EXPT 2 SIZE))
                      (EXPT 2 (1+ SIZE))))
      :hints (("Goal"
               :in-theory (e/d () (+-is-sum))))))

   (local
    (use-arithmetic-5 t))

   (defthmd insert-loghead-to-plusp-lemma
     (implies (and (unsigned-byte-p size x)
                   (unsigned-byte-p size y)
                   (unsigned-byte-p 1 z))
              (unsigned-byte-p (1+ size)
                               (+ x y z)))
     :otf-flg t
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance unsigned-byte-p-of-+
                               (size1 size)
                               (size2 size)))
              :in-theory (e/d (bitp)
                              (unsigned-byte-p-of-+)))))

   (defthmd remove-loghead
     (implies (unsigned-byte-p size x)
              (equal (loghead size x)
                     x)))

   (defthmd remove-loghead-from-plus
     (implies (and (unsigned-byte-p size x)
                   (unsigned-byte-p size y)
                   (unsigned-byte-p 1 z))
              (equal (loghead (1+ size) (+ x y z))
                     (+ x y z)))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance remove-loghead
                               (x (+ x y z))
                               (size (1+ size)))
                    (:instance insert-loghead-to-plusp-lemma))
              :in-theory (e/d ()
                              (+-is-sum)))))))

(local
 (defthmd
   4vec-adder-is-2vec-adder
   (implies (and (integerp x)
                 (integerp y)
                 (integerp carry-in)
                 (natp size))
            (equal (4vec-adder x y carry-in size)
                   (2vec-adder x y carry-in size)))
   :hints
   (("goal" :in-theory (e/d (2vec-adder-is-4vec-adder) nil)))))

(def-rp-rule :disabled-for-acl2 t
  4vec-plus-is-+
  (implies (and (integerp x)
                (integerp y))
           (equal (sv::4vec-plus x y)
                  (+ x y)))
  :hints (("goal"
           :in-theory (e/d (sv::4vec-plus
                            sv::4vec->upper
                            sv::4vec->lower) ()))))

(def-rp-rule 4vec-plus-chain-1
  (implies
   (and (> size 2) ;; if it is a full-adder pattern, then it should be caught
        ;; with the rules below so size=2 is not allowed here.
        (integerp size)

        (bitp carry-in)
        (unsigned-byte-p (1- size) x)
        (unsigned-byte-p (1- size) y))
   (and (equal (sv::4vec-plus (sv::4vec-concat
                               size
                               (sv::4vec-part-select 0 size (sv::4vec-plus x y))
                               0)
                              carry-in)
               (svl::4vec-plus++ x y carry-in size))
        (equal (sv::4vec-plus (sv::4vec-concat
                               size
                               (sv::4vec-plus x y)
                               0)
                              carry-in)
               (svl::4vec-plus++ x y carry-in size))
        (equal (sv::4vec-plus (sv::4vec-part-select 0 size (sv::4vec-plus x y))
                              carry-in)
               (svl::4vec-plus++ x y carry-in size))
        ))
  :otf-flg t
  :hints (("Goal"
           :use ((:instance remove-loghead-from-plus
                            (size (1- size))
                            (z 0))
                 (:instance remove-loghead-from-plus
                            (size (1- size))
                            (z carry-in))
                 (:instance loghead-of-+-is-2vec-adder-lemma
                            (carry carry-in)))
           :do-not-induct t
           ;;:induct (2VEC-ADDER X Y carry-in SIZE)
           :in-theory (e/d (SVL::4VEC-CONCAT$-OF-TERM2=0

                            4VEC-ADDER-IS-2VEC-ADDER

                            SV::4VEC-PLUS
                            BITOPS::LOGHEAD-OF-LOGHEAD-2
                            SV::2VEC
                            ;;loghead
                            ;;(:induction 2VEC-ADDER)
                            SVL::BITS
                            ;;bitp
                            SV::4VEC
                            ;;SV::4VEC-PART-SELECT
                            2VEC-ADDER
                            SV::4VEC->UPPER
                            SV::4VEC->LOWER)
                           (4vec-adder-opener-size>0
                            ACL2::POSP-REDEFINITION
                            unsigned-byte-p-redefined-with-loghead
                            ;; UNSIGNED-BYTE-P-TO-ASH-FORM
                            2vec-adder-is-4vec-adder
                            unsigned-byte-p
                            ash
                            loghead
                            f2
                            m2
                            bit-of
                            ;;ACL2::LIFIX$INLINE
                            +-is-sum
                            LOGHEAD-OF-+-IS-2VEC-ADDER-WITHOUT-CARRY
                            loghead-of-+-is-2vec-adder-lemma
                            loghead-of-+-is-2vec-adder
                            2vec-adder-is-4vec-adder
                            )))))

(rp::add-rp-rule rp::4vec-plus-chain-1 :outside-in :both)

(progn
  ;; Find Full and Half adder patterns from SVEX when defined with the + sign


  (defund tertiaryp (x)
    (or (= x 0)
        (= x 1)
        (= x 2)))

  (encapsulate
    nil
    (local
     (use-arithmetic-5 t))
    (def-rp-rule :disabled t
      4vec-plus-to-HA-FA-helper-1
      (implies (and (tertiaryp (svl::4vec-list x y))
                    (integerp n)
                    (>= n 2))
               (and (equal (sv::4vec-part-select 0 n (svl::4vec-list x y))
                           (svl::4vec-list x y))
                    (equal (svl::bits (svl::4vec-list x y) 0 n)
                           (svl::4vec-list x y))))
      :hints (("Goal"
               :in-theory (e/d (tertiaryp
                                svl::bits)
                               (+-is-sum))))))

  (defthm 4vec-plus-to-HA-FA-helper-1-side-cond
    (implies (tertiaryp (svl::4vec-list x y))
             (tertiaryp (svl::4vec-list x y)))
    :rule-classes nil)

  (rp-attach-sc 4vec-plus-to-HA-FA-helper-1
                4vec-plus-to-HA-FA-helper-1-side-cond)

  (def-rp-rule 4vec-plus-pattern-to-FA-1
    (implies (and (tertiaryp x)
                  (bitp y))
             (equal (sv::4vec-plus y x)
                    (svl::4vec-list (s-spec (list y
                                                  (acl2::logcar x)
                                                  (acl2::logcdr x)
                                                  (acl2::logcdr x)))
                                    (c-spec (list y
                                                  (acl2::logcar x)
                                                  (acl2::logcdr x)
                                                  (acl2::logcdr x))))))
    :hints (("Goal"
             :in-theory (e/d (tertiaryp bitp) ()))))

  (def-rp-rule 4vec-plus-pattern-to-FA-2
    (implies (and (tertiaryp x)
                  (bitp y))
             (equal (sv::4vec-plus x y)
                    (svl::4vec-list (s-spec (list y
                                                  (acl2::logcar x)
                                                  (acl2::logcdr x)
                                                  (acl2::logcdr x)))
                                    (c-spec (list y
                                                  (acl2::logcar x)
                                                  (acl2::logcdr x)
                                                  (acl2::logcdr x))))))
    :hints (("Goal"
             :in-theory (e/d (tertiaryp bitp) ()))))

  (defthmd 4vec-plus-pattern-to-FA-side-cond
    (implies (and (tertiaryp x)
                  (bitp y))
             (and (bitp (s-spec (list y
                                      (acl2::logcar x)
                                      (acl2::logcdr x)
                                      (acl2::logcdr x))))
                  (bitp (c-spec (list y
                                      (acl2::logcar x)
                                      (acl2::logcdr x)
                                      (acl2::logcdr x))))))
    :hints (("Goal"
             :in-theory (e/d (bitp tertiaryp) ()))))

  (rp-attach-sc 4vec-plus-pattern-to-FA-1
                4vec-plus-pattern-to-FA-side-cond)
  (rp-attach-sc 4vec-plus-pattern-to-FA-2
                4vec-plus-pattern-to-FA-side-cond)

  ;; These should have priority because if x is a constant, then
  ;; 4vec-plus-pattern-to-FA-1 or 4vec-plus-pattern-to-FA-2 will apply but we
  ;; don't want that.
  (def-rp-rule 4vec-plus-when-bitp
    (implies (and (bitp x)
		  (bitp y))
	     (equal (sv::4vec-plus x y)
		    (svl::4vec-list (s-spec (list x y))
				    (c-spec (list x y)))))
    :hints (("Goal"
	     :in-theory (e/d (bitp) ()))))

  (defthmd 4vec-plus-when-bitp-side-cond
    (implies (and (bitp x)
		  (bitp y))
	     (and (tertiaryp (svl::4vec-list (s-spec (list x y))
				             (c-spec (list x y))))
                  (bitp (s-spec (list x y)))
                  (bitp (c-spec (list x y)))))
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (rp-attach-sc 4vec-plus-when-bitp
                4vec-plus-when-bitp-side-cond))

#|(progn
  (def-rp-rule HA-patterned-4vec-plus
    (implies (and (bitp x)
		  (bitp y))
	     (equal (sv::4vec-plus x y)
		    (svl::4vec-list (s-spec (list x y))
				    (c-spec (list x y)))))
    :hints (("Goal"
	     :in-theory (e/d (bitp) ()))))

  (add-rp-rule HA-patterned-4vec-plus :outside-in :both)

  (def-rp-rule FA-patterned-4vec-plus
    (implies (and (bitp x)
		  (bitp y)
		  (bitp z))
	     (equal (sv::4vec-plus (sv::4vec-part-select 0 2 (sv::4vec-plus x y))
				   z)
		    (svl::4vec-list (s-spec (list x y z))
				    (c-spec (list x y z)))))
    :hints (("Goal"
	     :in-theory (e/d (bitp) ()))))

  (add-rp-rule FA-patterned-4vec-plus :outside-in :both))|#


(progn
  (def-rp-rule pull-out-dumb-twos-complement
    (implies (and (bitp test)
                  (integerp t1)
                  (integerp else)
                  (natp start)
                  (natp size))
	     (equal (sv::4vec-? test
                                (sv::4vec-part-select start size
                                                      (sv::4vec-plus t1 1))
                                else)
                    (progn$
                     (cw "(:rewrite pull-out-dumb-twos-complement) applied ~%")
                     (sv::4vec-bitor
                      (sv::4vec-? test 0 else)
                      (sv::4vec-part-select
                       start size
                       (sv::4vec-plus (sv::4vec-? test t1 0)
                                      test))))))
    :hints (("Goal"
             :expand ((:free (x)
                             (sv::4vec-plus 0 x)))
             :in-theory (e/d (bitp
                              SV::4VEC->UPPER
                              SV::4VEC->lower)
                             (RP::4VEC-PLUS++-IS-4VEC-ADDER)))))
  (add-rp-rule pull-out-dumb-twos-complement
               :outside-in :both))

(def-rp-rule 4vec-reduction-and-of---bitp
  (implies (bitp x)
           (equal (sv::4vec-reduction-and (-- x))
                  (- x)))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

(bump-all-meta-rules)

(bump-rule 4vec-plus-to-HA-FA-helper-1)

;;(bump-down-rp-rule (:META medw-compress-meta . equal))
;;(bump-down-rp-rule (:META make-sc-fgl-ready-meta-main . equal))

#|(bump-rules ;;(:meta hons-acons-meta . hons-acons)
;;(:meta fast-alist-free-meta . fast-alist-free)
;;(:meta hons-get-meta . hons-get)
;;(:meta assoc-eq-vals-meta . assoc-eq-vals)
;;(:meta rp-equal-meta . equal)
;;(:meta rp-equal-cnt-meta . equal)
;;(:meta mv-nth-meta . mv-nth)
;;(:meta implies-meta . implies)
;;(:meta cons-to-list-meta . cons-to-list)
;;(:meta list-to-cons-meta . list-to-cons)
(:meta svl::bits-of-meta-fn
. sv::4vec-part-select)
(:meta svl::bits-of-meta-fn . svl::bits)
(:meta svl::concat-meta . svl::4vec-concat$)
(:meta svl::concat-meta . sv::4vec-concat)
(:meta svl::svexl-node-eval-wog-meta-main
. svl::svexl-node-eval-wog)
(:meta svl::svex-eval-wog-meta-main
. svl::svex-eval-wog)
(:meta svl::svex-alist-eval-meta
. sv::svex-alist-eval)
(:meta svl::4vec-rsh-of-meta . sv::4vec-rsh)
(:meta rp-equal-iter-pp+-meta . equal)
(:meta resolve-adder-and-order
. merge-adder-and)
(:meta resolve-adder-sum-order
. merge-adder-b+)
(:meta adder-mux-meta . adder-mux)
(:meta sort-sum-meta . sort-sum)
(:meta s-c-spec-meta . s-spec)
(:meta s-c-spec-meta . c-spec)
(:meta s-c-spec-meta . s-c-spec)
(:meta s-c-spec-meta . c-s-spec)
(:meta unpack-booth-meta . unpack-booth))|#
