
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

(defines width-of-svex
  :flag-local nil
  (define width-of-svex ((x sv::svex-p)
                         &key
                         ((config svex-reduce-config-p)
                          'config))
    :returns (width acl2::maybe-natp)
    :measure (sv::svex-count x)
    :verify-guards nil
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
           ((and* (or* (equal x.fn 'sv::bitor)
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

           ((and* (or* (equal x.fn 'sv::unfloat)
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

           ((and* (or* (equal x.fn 'sv::?!)
                       (equal x.fn 'sv::?)
                       (equal x.fn 'sv::?*)
                       (equal x.fn 'sv::bit?!)
                       (equal x.fn 'sv::bit?))
                  (equal-len x.args 3))
            (b* ((w1 (width-of-svex (second x.args)))
                 ((Unless w1) nil)
                 (w2 (width-of-svex (third x.args)))
                 ((Unless w2) nil))
              (max w1 w2)))

           (t (b* (((svex-reduce-config config) config)
                   (obj (assoc-equal x.fn config.width-extns))
                   ((unless obj) nil)
                   ((width-of-svex-extn obj) obj)
                   ((unless (equal (len x.args) obj.arg-len))
                    nil)
                   ((Unless (mbt (posp obj.arg-len))) nil) ;; for measure
                   ((Unless (mbt (width-of-svex-extn-p obj)))
                    nil) ;; for proofs without this hyp.
                   (widths (widths-of-svexlist x.args))
                   (res (width-of-svex-extn-formula-eval obj.formula x.args widths)))
                (and (natp res)
                     res)))

           #|((and* (equal x.fn 'sv::partinst)
           (equal-len x.args 4)) ; ; ;
           ;; I don't expect to get partinst here for my use case. So I am not ; ; ;
           going to try to prove this here. ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
           ;; TODO: there  could be made  a slight improvement here  by checking ; ; ;
           ;; new-val's acutal size as well. (+ start new-val-size) can be added ; ; ;
           ;; into  the  final  calculation.  If  (+  start  size)  is  >=  than ; ; ;
           ;; old-val-width,  then   min  of  (+   start  size)  and   (+  start ; ; ;
           ;; new-val-size) can be picked. ; ; ;
           (b* ((start (first x.args)) ; ; ;
           (size (second x.args)) ; ; ;
           ((unless (and (natp start) ; ; ;
           (natp size))) ; ; ;
           nil) ; ; ;
           (old-val (third x.args)) ; ; ;
           (?new-val (fourth x.args)) ; ; ;
           (old-val-width (width-of-svex old-val)) ; ; ;
           ((unless old-val-width) ; ; ;
           nil)) ; ; ;
           (max (+ start size) old-val-width)))|#

           )))
  (define widths-of-svexlist ((lst sv::svexlist-p)
                              &key
                              ((config svex-reduce-config-p)
                               'config))
    :returns (widths)
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        nil
      (cons (width-of-svex (car lst))
            (widths-of-svexlist (cdr lst))))))

(local
 (defthm width-of-svex-extn-p-of-assoc-equal
   (implies (and (assoc-equal fn WIDTH-EXTNS)
                 (WIDTH-OF-SVEX-EXTN-list-P WIDTH-EXTNS))
            (width-of-svex-extn-p (ASSOC-EQUAL fn WIDTH-EXTNS)))))

(local
 (defthm alistp-of-WIDTH-OF-SVEX-EXTN-list-P
   (implies (width-of-svex-extn-list-p x)
            (alistp x))))

(verify-guards width-of-svex-fn)

;; maybe better to memoize for only a handful of svex functions..
(memoize 'width-of-svex
         :condition '(and (equal (svex-kind x) :call)
                          #|(member-equal (svex-call->fn x)
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
                          sv::lsh))|#)
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

(defthm 4vec-correct-width-p-of-4vec-bitxor
  (implies (and ;;(natp w1)
            ;;(natp w2)
            (4vec-correct-width-p w1 a1)
            (4vec-correct-width-p w2 a2)
            (equal w (safe-max w1 w2)))
           (4vec-correct-width-p w (sv::4vec-bitxor a1 a2)))
  :hints (("goal"
           :in-theory (e/d (natp
                            4vec-correct-width-p
                            4vec-part-select-of-4vec-bitxor-better
                            safe-max)
                           ()))))

(defthm 4vec-correct-width-p-of-4vec-bitor
  (implies (and ;;(natp w1)
            ;;(natp w2)
            (4vec-correct-width-p w1 a1)
            (4vec-correct-width-p w2 a2)
            (equal w (safe-max w1 w2)))
           (4vec-correct-width-p w (sv::4vec-bitor a1 a2)))
  :hints (("goal"
           :in-theory (e/d (4vec-correct-width-p
                            4vec-part-select-of-4vec-bitor-better
                            safe-max)
                           ()))))

(defthm 4vec-correct-width-p-of-4vec-bitand
  (implies (and ;;(natp w1)
            ;;(natp w2)
            (4vec-correct-width-p w1 a1)
            (4vec-correct-width-p w2 a2)
            (equal w (safe-min w1 w2)))
           (4vec-correct-width-p w (sv::4vec-bitand a1 a2)))
  :hints (("goal"
           :in-theory (e/d (4vec-correct-width-p
                            4vec-part-select-of-4vec-bitand-better
                            safe-min)
                           ()))))

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
                             sv::4vec-bitmux
                             sv::4vec-1mask
                             acl2::logite
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
                   (equal x (4vec-concat
                             lsb in
                             (4vec-concat
                              width val
                              (4vec-rsh (+ lsb width) in))))))
   :hints (("goal"
            :in-theory (e/d (2vec
                             4vec
                             4vec-part-install) ())))))

(local
 (in-theory (disable sv::svex-apply$-is-svex-apply)))

(local
 (defthm car-of-assoc-equal
   (implies (assoc-equal fn alist)
            (equal (car (assoc-equal fn alist))
                   fn))))

(defthm width-of-svex-extn-p-of-assoc-equal-of-svex-functions
  (implies (assoc-equal fn sv::*svex-op-table*)
           (not (width-of-svex-extn-p (assoc-equal fn extensions))))
  :hints (("goal"
           :cases ((assoc-equal fn extensions))
           :in-theory (e/d
                       (svex-foreign-fnsym-p
                        width-of-svex-extn-p)
                       (assoc-equal)))))

(local
 (defthm 4vec-correct-width-p-of-not-natp
   (implies (not (natp width))
            (4vec-correct-width-p width x))
   :hints (("goal"
            :in-theory (e/d (4vec-correct-width-p) ())))))



(local
 (defthm 4vec-correct-width-p-expand
   (implies (syntaxp (and (consp term)
                          (assoc-equal (car term)
                                       (strip-cdrs sv::*svex-op-table*))))
            (equal (4vec-correct-width-p width term)
                   (implies (natp width)
                            (equal (4vec-part-select 0 width term)
                                   term))))
   :hints (("goal"
            :in-theory (e/d (4vec-correct-width-p) ())))))

(local
 (defthm 4vec-correct-width-p-of-and
   (equal (4vec-correct-width-p (and x y) val)
          (implies x
                   (4vec-correct-width-p y val)))))

(local
 (defthm width-of-svex-extn-correct$-of-assoc
   (implies (and (assoc-equal fn extns)
                 (width-of-svex-extn-correct$-lst extns))
            (width-of-svex-extn-correct$
             (assoc-equal fn extns)))
   :hints (("goal"
            :in-theory (e/d () (width-of-svex-extn-correct$))))))

(defret len-of-widths-of-svexlist
  (equal (len widths)
         (len lst))
  :fn widths-of-svexlist
  :hints (("goal"
           :induct (len lst)
           :in-theory (e/d (widths-of-svexlist) ()))))

(local
 (defthm width-of-svex-extn->fn-of-assoc-equal
   (implies (and (width-of-svex-extn-p (assoc-equal fn lst)))
            (equal (width-of-svex-extn->fn (assoc-equal fn lst))
                   fn))
   :hints (("goal"
            :in-theory (e/d (width-of-svex-extn-p
                             width-of-svex-extn->fn) ())))))

(local
 (defthm 4vec-correct-width-p-of-width-of-svex-extn-formula-eval
   (implies (and (width-of-svex-extn-correct$ extn)
                 (4vec-correct-widths-p arg-widths (svexlist-eval$ args env))
                 (equal (len args)
                        (width-of-svex-extn->arg-len extn))
                 (equal (len args) (len arg-widths))
                 (equal fn (width-of-svex-extn->fn extn))
                 (width-of-svex-extn-p extn)
                 ;;(not (member-equal fn (strip-cars sv::*svex-op-table*)))
                 )
            (4vec-correct-width-p
             (width-of-svex-extn-formula-eval
              (width-of-svex-extn->formula extn)
              args
              arg-widths)
             (svex-apply$ fn (svexlist-eval$ args env))))
   :hints (("goal"
            :do-not-induct t
            :use ((:instance width-of-svex-extn-correct$-necc
                             (widths arg-widths)
                             (obj extn)))
            :in-theory (e/d ()
                            (width-of-svex-extn-correct$
                             width-of-svex-extn-correct$-necc))))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-apply-opener-for-known-functions
    (implies (not (svex-foreign-fnsym-p fn))
             (equal (svex-apply fn args)
                    (let* ((fn (fnsym-fix fn))
                           (args (sv::4veclist-fix args)))
                      (svex-apply-cases fn args))))
    :hints (("goal"
             :in-theory (e/d (svex-apply) ()))))))

(local
 (in-theory (disable SV::SVEXLIST-EVAL$-IS-SVEXLIST-EVAL)))

(defret-mutual integerp-of-<fn>
   (defret return-val-of-<fn>
     (implies width
              (and (natp width)
                   (integerp width)
                   (rationalp width)))
     :fn width-of-svex)
   (defret return-val-of-<fn>
     t
     :fn widths-of-svexlist
     :rule-classes nil)
   ;;:otf-flg t
   :mutual-recursion width-of-svex
   :hints (("Goal"
            :in-theory (e/d (width-of-svex
                             widths-of-svexlist)
                            ()))))

(svex-eval-lemma-tmpl
 (defret-mutual svex-eval-width-is-correct-1
   (defret svex-eval-<fn>-is-correct-1
     (implies (and ;;width
               (sv::Svex-p x)
               (:@ :dollar-eval
                   (width-of-svex-extn-correct<$>-lst
                    (svex-reduce-config->width-extns config)))
               (:@ :normal-eval
                   (equal (svex-reduce-config->width-extns config) nil)))
              (4vec-correct-width-p width (svex-eval x env))
              #|(equal (4vec-part-select 0 width (svex-eval x env))
              (svex-eval x env))|#)
     :fn width-of-svex)
   (defret svexlist-eval-<fn>-is-correct-1
     (implies (and ;;widths
               (sv::Svexlist-p lst)
               (:@ :dollar-eval
                   (width-of-svex-extn-correct<$>-lst
                    (svex-reduce-config->width-extns config)))
               (:@ :normal-eval
                   (equal (svex-reduce-config->width-extns config) nil)))
              (and
               ;;(equal (len lst) (len widths))
               (4vec-correct-widths-p widths
                                      (svexlist-eval lst env))))
     :fn widths-of-svexlist)
   ;;:otf-flg t
   :hints (("goal"
            :do-not-induct t
            :expand ((:free (x y z)
                            (4VEC-CORRECT-WIDTHS-P (cons x y) z))
                     (:free (x y)
                            (len (cons x y)))
                     (4vec-correct-width-p (width-of-svex (car (svex-call->args x)))
                                           (svex-eval (car (svex-call->args x))
                                                      env))
                     (4vec-correct-width-p (width-of-svex (cadr (svex-call->args x)))
                                           (svex-eval (cadr (svex-call->args x))
                                                      env))
                     (4vec-correct-width-p (width-of-svex (caddr (svex-call->args x)))
                                           (svex-eval (caddr (svex-call->args x))
                                                      env))
                     (4vec-correct-width-p 0
                                           (svex-eval (caddr (svex-call->args x))
                                                      env))
                     (4vec-correct-width-p (integer-length x)
                                           x)

                     (widths-of-svexlist nil)
                     (widths-of-svexlist lst)

                     #|(:free (fn x y)
                     (svex-apply fn (cons x y)))|#
                     ;; (svexlist-eval (svex-call->args x)
                     ;;                env)
                     ;; (svexlist-eval (cdr (svex-call->args x))
                     ;;                env)
                     ;; (svexlist-eval (cddr (svex-call->args x))
                     ;;                env)
                     ;; (svexlist-eval (cdddr (svex-call->args x))
                     ;;                env)
                     )
            :in-theory (e/d (;;4vec-correct-widths-p
                             ;;4vec-correct-width-p
                             or*
                             len
                             svex-p
                             nfix
                             ;;4vec-part-install
                             4vec-concat$
                             width-of-svex
                             ;;widths-of-svexlist
                             4vec-part-select-of-4vec-bitxor-better
                             4vec-part-select-of-4vec-bitor-better
                             4vec-part-select-of-4vec-bitand-better
                             svexlist-eval
                             4vec-part-select-of-4vec-bit?!-2
                             4vec-part-select-of-4vec-bit?-2

                             )
                            (
                             (:definition svex-p)
                             (:rewrite default-<-1)
                             (:rewrite default-<-2)

                             svex-apply
                             (:rewrite default-cdr)
                             (:rewrite default-car)
                             ;;(:definition assoc-equal)
                             (:meta
                              rp::binary-or**/and**-guard-meta-correct)
                             ;;(:rewrite dummy-lemma-1)

                             (:type-prescription
                              posp-of-width-of-svex-extn->arg-len)
                             (:type-prescription len)
                             ;;(:definition len)
                             (:definition member-equal)
                             width-of-svex-extn-correct$
                             rp::len-cons
                             acl2::equal-len-1
                             rp::dummy-len-equiv
                             loghead
                             logapp
                             4vec-part-select-of-4vec-bit?!
                             4vec-part-select-of-4vec-bit?)))
           (and stable-under-simplificationp
                '(:expand ((svexlist-eval (svex-call->args x)
                                          env)
                           (svexlist-eval (cdr (svex-call->args x))
                                          env)
                           (svexlist-eval (cddr (svex-call->args x))
                                          env)
                           (svexlist-eval (cdddr (svex-call->args x))
                                          env))
                          :use ((:instance svex-eval-width-of-svex-is-correct-when-quoted)))))))

(svex-eval-lemma-tmpl
 (defret svex-eval-<fn>-is-correct
   (implies (and width
                 (equal free-var-width width)
                 (sv::svex-p x)
                 (:@ :dollar-eval
                     (width-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->width-extns config)))
                 (:@ :normal-eval
                     (equal (svex-reduce-config->width-extns config) nil)))
            (and (equal (4vec-part-select 0 free-var-width (svex-eval x env))
                        (svex-eval x env))
                 (4vec-correct-width-p free-var-width (svex-eval x env))))
   :fn width-of-svex
   :hints (("goal"
            :use ((:instance svex-eval-width-of-svex-is-correct-1))
            :in-theory (e/d (4vec-correct-width-p) ())))))

;; (width-of-svex '(ha-s (partsel 0 2 a) (partsel 0 3 a))
;;                :config (make-svex-reduce-config
;;                         :width-extns (list
;;                                       (make-width-of-svex-extn
;;                                        :fn 'ha-s
;;                                        :arg-len 2
;;                                        :formula '(safe-max (nth '0 widths)
;;                                                            (nth '1 widths))))))
;; returns
;; 3.


(progn
  (defthmd 4vec-correct-width-p-of-not-natp
    (implies (not (natp width))
             (4vec-correct-width-p width x))
    :hints (("goal"
             :in-theory (e/d (4vec-correct-width-p) ()))))

  (defmacro create-width-of-svex-extn (&key
                                       formula
                                       fn
                                       prepwork
                                       extra-hints)
    `(make-event
      (b* ((arg-len (len (acl2::formals ',fn (w state))))
           (- (or (width-of-svex-extn-formula-p ',formula)
                  (hard-error 'create-width-of-svex-extn
                              "Given formula does not satisfy ~
  svl::width-of-svex-extn-formula-p: ~p0~%"
                              (list (cons #\0 ',formula))))))
        (acl2::template-subst
         '(defsection width-of-svex-extn-correct-of-<fn>
            ,@prepwork
            
            (defthm width-of-svex-extn-correct-of-<fn>
              (b* ((obj (svl::make-width-of-svex-extn
                         :fn '<fn>
                         :arg-len <arg-len>
                         :formula ',formula)))
                (implies (apply$-warrant-<fn>)
                         (svl::width-of-svex-extn-correct$ obj)))
              :hints (("Goal"
                       :expand ((:free (args)
                                       (sv::svex-apply$ '<fn> args)))
                       :in-theory (e/d (FTY::EQUAL-OF-PLUS-ONE
                                        FTY::EQUAL-OF-LEN
                                        4VEC-CORRECT-WIDTHS-P
                                        safe-min
                                        safe-max
                                        sv::svex-eval$-when-fncall
                                        svl::width-of-svex-extn-formula-eval
                                        svl::4vec-correct-width-p-of-not-natp
                                        <fn>)
                                       ()))
                      ,@extra-hints))

            (table width-of-svex-extns (svl::make-width-of-svex-extn
                                        :fn '<fn>
                                        :arg-len <arg-len>
                                        :formula ',formula)
                   'width-of-svex-extn-correct-of-<fn>))
         :atom-alist `((<arg-len> . ,arg-len)
                       (<fn> . ,',fn))
         :str-alist '(("<FN>" . ,(symbol-name fn)))
         :pkg-sym ',fn)))))
