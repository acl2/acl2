
; Copyright (C) 2023 Intel Corporation
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Mertcan Temel <mert.temel@intel.com>

(in-package "SVL")

(include-book "base")

(include-book "projects/rp-rewriter/top" :dir :system)

(include-book "../fnc-defs")

(local
 (include-book "projects/rp-rewriter/proofs/rp-rw-lemmas" :dir :system)) ;; need rp::rp-check-context-is-correct-iff
(local
 (include-book "../4vec-lemmas"))
(local
 (include-book "../bits-sbits"))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/ihs-extensions" :dir :system)
  use-ihs-extensions))

(local
 (rp::fetch-new-events
  (include-book "ihs/logops-lemmas" :dir :system)
  use-ihs-logops-lemmas))

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

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(define width-of-svex ((x sv::svex-p))
  :returns (width acl2::maybe-natp)
  :measure (sv::Svex-count x)
  (sv::svex-case
   x
   :var nil
   :quote (cond ((natp x)
                 (integer-length x))
                ((4vec-p x)
                 (b* (((4vec x)))
                   (and (natp x.upper)
                        (natp x.lower)
                        (max (integer-length x.upper)
                             (integer-length x.lower))))))
   :call
   (cond ((and* (equal x.fn 'sv::bitand)
                (equal-len x.args 2))
          (b* ((w1 (width-of-svex (first x.args)))
               (w2 (width-of-svex (second x.args)))
               ((Unless w1) w2)
               ((unless w2) w1))
            (min w1 w2)))
         ((and* (or (equal x.fn 'sv::bitor)
                    (equal x.fn 'sv::bitxor)
                    (equal x.fn 'sv::res))
                (equal-len x.args 2))
          (b* ((w1 (width-of-svex (first x.args)))
               ((Unless w1) nil)
               (w2 (width-of-svex (second x.args)))
               ((Unless w2) nil))
            (max w1 w2)))
         ((and* (equal x.fn 'sv::partsel)
                (equal-len x.args 3))
          ;; TODO: An option to do further search here can be implemented to see if
          ;; the argument of partsel is even narrower than its size indicates..
          (b* ((start (first x.args))
               (size (second x.args)))
            (and (natp start)
                 (natp size)
                 size)))
         ((and* (equal x.fn 'sv::concat)
                (equal-len x.args 3))
          (b* ((size (first x.args))
               ((Unless (natp size)) nil)
               (term1 (second x.args))
               (term2 (third x.args))
               (term2-width (width-of-svex term2))
               ((Unless term2-width)
                nil)
               ((unless (equal term2-width 0))
                (+ size term2-width))
               (term1-size (width-of-svex term1)))
            (if term1-size
                (min size term1-size)
              size)))

         ((and* (equal x.fn 'sv::zerox)
                (equal-len x.args 2))
          (b* ((size (first x.args))
               ((Unless (natp size)) nil)
               (term1 (second x.args))
               (term1-size (width-of-svex term1)))
            (if term1-size
                (min size (width-of-svex term1))
              size)))

         ((and* (or (equal x.fn 'sv::unfloat)
                    (equal x.fn 'sv::id))
                (equal-len x.args 1))
          (width-of-svex (first x.args)))

         ((and* (equal x.fn 'sv::lsh)
                (equal-len x.args 2))
          (b* ((size (first x.args))
               ((Unless (natp size)) nil)
               (term1 (second x.args))
               (term1-size (width-of-svex term1)))
            (and term1-size
                 (+ term1-size size))))

         ((and* (equal x.fn 'sv::rsh)
                (equal-len x.args 2))
          (b* ((size (first x.args))
               ((Unless (natp size)) nil)
               (term1 (second x.args))
               (term1-size (width-of-svex term1)))
            (and term1-size
                 (nfix (+ term1-size (- size))))))

         ((and* (or (equal x.fn 'sv::?!)
                    (equal x.fn 'sv::?)
                    (equal x.fn 'sv::?*)
                    (equal x.fn 'sv::bit?!)
                    (equal x.fn 'sv::bit?))
                (equal-len x.args 3))
          (b* (
               (w1 (width-of-svex (second x.args)))
               ((Unless w1) nil)
               (w2 (width-of-svex (third x.args)))
               ((Unless w2) nil))
            (max w1 w2)))

         #|((and* (equal x.fn 'sv::partinst)
         (equal-len x.args 4)) ;
         ;; I don't expect to get partinst here for my use case. So I am not ;
         going to try to prove this here. ;
; ; ;
         ;; TODO: there  could be made  a slight improvement here  by checking ;
         ;; new-val's acutal size as well. (+ start new-val-size) can be added ;
         ;; into  the  final  calculation.  If  (+  start  size)  is  >=  than ;
         ;; old-val-width,  then   min  of  (+   start  size)  and   (+  start ;
         ;; new-val-size) can be picked. ;
         (b* ((start (first x.args)) ;
         (size (second x.args)) ;
         ((unless (and (natp start) ;
         (natp size))) ;
         nil) ;
         (old-val (third x.args)) ;
         (?new-val (fourth x.args)) ;
         (old-val-width (width-of-svex old-val)) ;
         ((unless old-val-width) ;
         nil)) ;
         (max (+ start size) old-val-width)))|#

         )))

;; maybe better to memoize for only a handful of svex functions..
(memoize 'width-of-svex
         :condition '(and (equal (svex-kind x) :call)
                          (member-equal (svex-call->fn x)
                                        '(sv::bitor
                                          sv::concat
                                          sv::bitxor
                                          sv::bitand
                                          sv::?!
                                          sv::?
                                          sv::?*
                                          sv::bit?!
                                          sv::bit?
                                          sv::rsh
                                          sv::lsh)))
         )

(local
 (defthm logapp-of-integer-length
   (implies (and (natp x)
                 (integerp width)
                 (>= width (integer-length x)))
            (and (equal (logapp width x 0) x)
                 (equal (loghead width x) x)))
   :hints (("Goal"
            :in-theory (e/d* (bitops::ihsext-inductions
                              bitops::ihsext-recursive-redefs)
                             ())))))

(Local
 (svex-eval-lemma-tmpl
  (defret svex-eval-<fn>-is-correct-when-quoted
    (implies (and width
                  (equal (svex-kind x) :quote))
             (equal (4vec-part-select 0 width (svex-eval x env))
                    (svex-eval x env)))
    :fn width-of-svex
    :hints (("goal"
             :in-theory (e/d (4vec-concat
                              4vec-part-select
                              4vec-p
                              sv::svex-quote->val
                              width-of-svex)
                             (loghead logapp)))))))

(local
 (defthm 4vec-part-select-lemma-1
   (implies (and (natp w1)
                 (natp w2)
                 (<= w1 w2)
                 (equal (4vec-part-select 0 w1 x) x))
            (equal (4vec-part-select 0 w2 x) x))
   :hints (("Goal"
            :in-theory (e/d (4vec-part-select
                             4vec-concat)
                            ())))))

(local
 (defthmd logand-of-single-loghead-2
   (and (equal (logand x (Loghead size y))
               (loghead size (logand x y)))
        (equal (logand (Loghead size y) x)
               (loghead size (logand x y))))
   :hints (("Goal"
            :use ((:instance LOGAND-OF-SINGLE-LOGHEAD))
            :in-theory (e/d* (bitops::ihsext-recursive-redefs
                              bitops::ihsext-inductions)
                             ()) ))))

(local
 (defthm 4vec-part-select-lemma-2-for-bitand
   (implies (and (natp w1)
                 (natp w2)
                 (<= w1 w2)
                 (equal (4vec-part-select 0 w1 x) x)
                 (equal (4vec-part-select 0 w2 y) y))
            (equal (4vec-bitand x (4vec-part-select 0 w1 y))
                   (4vec-bitand x y)))
   :hints (("Goal"
            :in-theory (e/d* (logand-of-single-loghead-2
                              4VEC-BITAND
                              3VEC-BITAND
                              SV::3VEC-FIX
                              4vec-part-select
                              4vec-concat)
                             (BITOPS::LOGHEAD-OF-LOGAND))))))

(local
 (defthm 4vec-part-select-lemma-3-for-bitand
   (implies (and (natp w1)
                 (equal (4vec-part-select 0 w1 x) x))
            (equal (4vec-bitand x (4vec-part-select 0 w1 y))
                   (4vec-bitand x y)))
   :hints (("Goal"
            :in-theory (e/d* (logand-of-single-loghead-2
                              4VEC-BITAND
                              3VEC-BITAND
                              SV::3VEC-FIX
                              4vec-part-select
                              4vec-concat)
                             (BITOPS::LOGHEAD-OF-LOGAND))))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-when-svex-is-natp
   (implies (natp x)
            (equal (svex-eval x env) x))
   :hints (("Goal"
            :in-theory (e/d (svex-eval svex-kind SV::SVEX-QUOTE->VAL) ()))))))

(local
 (defthm 4vec-concat-of-0-is-4vec-part-select
   (equal (4vec-concat size term 0)
          (4vec-part-select 0 size term))
   :hints (("goal"
            :in-theory (e/d (4vec-concat
                             4vec-part-select)
                            ())))))

(local
 (defthmd 4vec-part-select-of-4vec-bit?!-2
   (implies (and (natp size))
            (equal (4vec-part-select 0 size
                                     (sv::4vec-bit?! test then else))
                   (sv::4vec-bit?! test
                                   (4vec-part-select 0 size then)
                                   (4vec-part-select 0 size else))))
   ;;:otf-flg t
   :hints (("Goal"
            :do-not-induct t
            :do-not '(preprocess)
            :in-theory (e/d (SV::4VEC-BIT?!
                             4VEC-CONCAT
                             4VEC-RSH
                             4VEC-SHIFT-CORE
                             4VEC-PART-SELECT)
                            (4VEC-CONCAT-OF-0-IS-4VEC-PART-SELECT)))
           (and stable-under-simplificationp
                '(:in-theory (e/d (SV::4VEC-BIT?!
                                   LOGNOT-OF-LOGTAIL
                                   logand-of-single-loghead-2
                                   4VEC-CONCAT
                                   4VEC-RSH
                                   4VEC-SHIFT-CORE
                                   4VEC-PART-SELECT
                                   LOGAND-OF-LOGTAIL)
                                  (BITOPS::LOGHEAD-OF-LOGAND
                                   BITOPS::LOGTAIL-OF-LOGNOT
                                   BITOPS::LOGTAIL-OF-LOGand
                                   4VEC-CONCAT-OF-0-IS-4VEC-PART-SELECT)))))))

(local
 (encapsulate
   nil
   (local
    (use-equal-by-logbitp t))

   (local
    (in-theory (e/d (acl2::bool->bit)
                    ((:linear bitops::logior-<-0-linear-2)
                     (:rewrite logapp-of-integer-length)
                     (:rewrite acl2::natp-when-integerp)
                     (:linear bitops::logand->=-0-linear-2)
                     (:linear acl2::logand-upper-bound . 2)
                     (:linear bitops::upper-bound-of-logand . 2)))))

   (defthmd 4vec-part-select-of-4vec-bit?-2
     (implies (and (natp size))
              (equal (4vec-part-select 0 size
                                       (sv::4vec-bit? test then else))
                     (sv::4vec-bit? test
                                    (4vec-part-select 0 size then)
                                    (4vec-part-select 0 size else))))
     ;;:otf-flg t
     :hints (("goal"
              :do-not-induct t
              :do-not '(preprocess)
              :in-theory (e/d (sv::4vec-bit?
                               sv::3vec-bit?
                               sv::3vec-fix
                               4vec-concat
                               4vec-rsh
                               4vec-shift-core
                               4vec-part-select)
                              (4vec-concat-of-0-is-4vec-part-select)))
             (bitops::logbitp-reasoning)
             ))))

(local
 (defthm expand-equal-of-part-select
   (implies (and (natp lsb)
                 (natp width))
            (equal (equal x (4vec-part-install lsb width in val))
                   (equal x (4VEC-CONCAT
                             lsb in
                             (4VEC-CONCAT
                              width val
                              (4VEC-RSH (+ lsb width) in))))))
   :hints (("Goal"
            :in-theory (e/d (2VEC
                             4VEC
                             4vec-part-install) ())))))

(local
 (in-theory (disable sv::svex-apply$-is-svex-apply)))

(svex-eval-lemma-tmpl
 (defret svex-eval-<fn>-is-correct-1
  (implies (and width
                (sv::Svex-p x))
           (equal (4vec-part-select 0 width (svex-eval x env))
                  (svex-eval x env)))
  :fn width-of-svex
  :hints (("goal"
           :expand ((:free (fn x y)
                           (svex-apply fn (cons x y)))
                    (svexlist-eval (svex-call->args x)
                                   env)
                    (svexlist-eval (cdr (svex-call->args x))
                                   env)
                    (svexlist-eval (cddr (svex-call->args x))
                                   env)
                    (svexlist-eval (cdddr (svex-call->args x))
                                   env))
           :in-theory (e/d (svex-p
                            nfix
                            ;;4vec-part-install
                            4vec-concat$
                            width-of-svex
                            4vec-part-select-of-4vec-bitxor-better
                            4vec-part-select-of-4vec-bitor-better
                            4vec-part-select-of-4vec-bitand-better
                            svexlist-eval
                            4vec-part-select-of-4vec-bit?!-2
                            4vec-part-select-of-4vec-bit?-2)
                           (loghead
                            logapp
                            4vec-part-select-of-4vec-bit?!
                            4vec-part-select-of-4vec-bit?)))
          (and stable-under-simplificationp
               '(:use ((:instance svex-eval-<fn>-is-correct-when-quoted)))))))

(svex-eval-lemma-tmpl
 (defret svex-eval-<fn>-is-correct
  (implies (and width
                (equal free-var-width width)
                (sv::Svex-p x))
           (equal (4vec-part-select 0 free-var-width (svex-eval x env))
                  (svex-eval x env)))
  :fn width-of-svex))
