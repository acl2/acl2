
; Copyright (C) 2022 Intel Corporation
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

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(local
 (defthm svex-p-lemmas
   (implies (and (sv::Svex-p x)
                 (equal (sv::Svex-kind x) :call))
            (and (implies (equal-len (cdr x) 1)
                          (sv::Svex-p (cadr x)))
                 (implies (equal-len (cdr x) 2)
                          (and (sv::Svex-p (cadr x))
                               (sv::Svex-p (caddr x))))
                 (implies (equal-len (cdr x) 3)
                          (and (sv::Svex-p (cadr x))
                               (sv::Svex-p (caddr x))
                               (sv::Svex-p (cadddr x))))
                 (implies (equal-len (cdr x) 4)
                          (and (sv::Svex-p (cadr x))
                               (sv::Svex-p (caddr x))
                               (sv::Svex-p (cadddr x))
                               (sv::Svex-p (caddr (cddr x)))))))
   :hints (("Goal"
            :in-theory (e/d (sv::Svex-p
                             SVEX-KIND)
                            ())))))

(local
 (defthm svex-p-lemma2
   (IMPLIES (AND (SVEX-P X)
                 (EQUAL (SVEX-KIND X) :CALL)
                 (NOT (CONSP X)))
            (NOT X))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (sv::Svex-p
                             SVEX-KIND)
                            ())))))

(define has-integerp-rp (term)
  :prepwork ((local
              (in-theory
               (enable rp::is-rp-loose))))
  (or (and (rp::is-rp-loose term)
           (or (equal (cadr term) ''integerp)
               (equal (cadr term) ''bitp)
               (has-integerp-rp (caddr term))))
      ;; (case-match term ;; needs formula checks...
      ;;   (('bits x ('quote start) ('quote size))
      ;;    (and (natp start)
      ;;         (natp size)
      ;;         (has-integerp-rp x))))
      )
  ///
  (local
   (defthm rp-evlt-of-rp-call
     (implies (and (consp x)
                   (equal (car x) 'rp))
              (equal (rp-evlt x a)
                     (rp (rp-evlt (cadr x) a)
                         (rp-evlt (caddr x) a))))))
  (local
   (defthm rp-evlt-of-integerp-call
     (implies (and (consp x)
                   (equal (car x) 'integerp))
              (equal (rp-evlt x a)
                     (integerp (rp-evlt (cadr x) a))))))
  (local
   (defthm rp-evlt-of-bitp-call
     (implies (and (consp x)
                   (equal (car x) 'bitp))
              (equal (rp-evlt x a)
                     (bitp (rp-evlt (cadr x) a))))))
  (defthm has-integerp-rp-is-correct
    (implies (and (rp::valid-sc term a)
                  (has-integerp-rp term))
             (and (integerp (rp-evlt term a))))
    :hints (("goal"
             :do-not-induct t
             :expand ((rp::valid-sc term a))
             :induct (has-integerp-rp term)
             :in-theory (e/d (rp::context-from-rp
                              rp::valid-sc rp::is-rp rp::is-if)
                             (rp::rp-trans
                              rp::rp-evl-and-side-cond-consistent-rp-rw-relieve-hyp
                              rp::rp-term-listp
                              rp::valid-sc-subterms
                              rp::eval-and-all-context-from-when-valid-sc
                              rp::valid-sc-cons
                              rp::rp-evl-of-trans-list-lemma))))))

(define has-natp-rp (term)
  :prepwork ((local
              (in-theory
               (enable rp::is-rp-loose))))
  (and (rp::is-rp-loose term)
       (or (equal (cadr term) ''natp)
           (has-natp-rp (caddr term))))
  ///
  (local
   (defthm rp-evlt-of-rp-call
     (implies (and (consp x)
                   (equal (car x) 'rp))
              (equal (rp-evlt x a)
                     (rp (rp-evlt (cadr x) a)
                         (rp-evlt (caddr x) a))))))
  (local
   (defthm rp-evlt-of-natp-call
     (implies (and (consp x)
                   (equal (car x) 'natp))
              (equal (rp-evlt x a)
                     (natp (rp-evlt (cadr x) a))))))
  (defthm has-natp-rp-is-correct
    (implies (and (rp::valid-sc term a)
                  (has-natp-rp term))
             (and (natp (rp-evlt term a))))
    :hints (("goal"
             :do-not-induct t
             :expand ((rp::valid-sc term a))
             :induct (has-natp-rp term)
             :in-theory (e/d (rp::context-from-rp
                              rp::valid-sc rp::is-rp rp::is-if)
                             (rp::rp-trans
                              rp::rp-evl-and-side-cond-consistent-rp-rw-relieve-hyp
                              rp::rp-term-listp
                              rp::valid-sc-subterms
                              rp::eval-and-all-context-from-when-valid-sc
                              rp::valid-sc-cons
                              rp::rp-evl-of-trans-list-lemma))))))

(define bit?!-test-is-dont-care-p ((x sv::svex-p)
                                   &key
                                   ((env) 'env)
                                   ((config svex-reduce-config-p) 'config))

  :returns res
  (and (not (svex-reduce-config->keep-missing-env-vars config))
       (case-match x
         (('sv::bit?! ('sv::partsel & & var1)
                      &
                      &)
          (and (sv::svar-p var1)
               (not (hons-get (sv::svar-fix var1) env)))))))

(defines integerp-of-svex
  :flag-local nil
  :hints (("Goal"
           :in-theory (e/d (rp::measure-lemmas)
                           ())))
  (define integerp-of-svex ((x sv::svex-p)
                            &key
                            ((env) 'env)
                            ((context rp::rp-term-listp) 'context)
                            ((config svex-reduce-config-p) 'config))
    :measure (rp::cons-count x)

    :verify-guards nil
    :returns (res )

    (let* ((kind (sv::Svex-kind x)))
      (case kind
        (:var (b* ((val (hons-get x env))
                   ((unless (consp val))
                    nil)
                   (val (cdr val))
                   ((when (and (quotep val)
                               (consp (cdr val))))
                    (integerp (unquote val)))
                   (- (and (4vec-p val)
                           (acl2::raise "Constants are expected to be quoted in the  given env. But given instead:~p0"
                                        (cons x val))))

                   ((when (has-integerp-rp val)) t)

                   ((unless (rp::rp-termp val)) ;; this may be taken out with guards on env
                    nil)

                   ((mv res &)
                    (rp::rp-check-context `(integerp ,val) nil context
                                          :iff-flg t))
                   ((when (equal res ''t)) t)
                   ((mv res &)
                    (rp::rp-check-context `(bitp ,val) nil context
                                          :iff-flg t))
                   ((when (equal res ''t)) t))
                nil))
        (:quote (integerp x))
        (:call
         (b* ((x.fn (car x))
              (x.args (cdr x)))
           (cond ((and* (equal-len x.args 1)
                        (or* (equal x.fn 'sv::id)
                             (equal x.fn 'sv::unfloat)
                             (equal x.fn 'sv::bitnot)
                             (equal x.fn 'sv::onp)
                             (equal x.fn 'sv::offp)
                             (equal x.fn 'sv::uand)
                             (equal x.fn 'sv::uor)
                             ;;(equal x.fn 'sv::uxor) same as sv::onehot0, expect natp
                             (equal x.fn 'sv::u-)
                             ;;(equal x.fn 'sv::countones) same as sv::onehot0, expect natp
                             ;; (equal x.fn 'sv::onehot) expects a natp
                             ;;(equal x.fn 'sv::onehot0) expects a natp, since there is not natp-of-svex, I am avoiding it here.
                             (equal x.fn 'sv::xdet)
                             ;; (equal x.fn 'sv::clog2) same as sv::onehot0, expect natp
                             ))
                  (integerp-of-svex (car x.args)))

                 ((and* (equal-len x.args 1)
                        (or* (equal x.fn 'sv::uxor) ;; same as sv::onehot0, expect natp
                             (equal x.fn 'sv::countones) ;; same as sv::onehot0, expect natp
                             (equal x.fn 'sv::onehot)    ;; expects a natp
                             (equal x.fn 'sv::onehot0) ;; expects a natp, since there is not natp-of-svex, I am avoiding it here.
                             (equal x.fn 'sv::clog2) ;;same as sv::onehot0, expect natp
                             ))
                  (natp-of-svex (car x.args)))

                 ((and* (equal-len x.args 2)
                        (or* (equal x.fn 'sv::bitand)
                             (equal x.fn 'sv::bitor)
                             (equal x.fn 'sv::bitxor)

                             ;;(equal x.fn 'sv::res) ;; can return don't care even when two are integer.
                             (equal x.fn 'sv::resand)
                             (equal x.fn 'sv::resor)
                             (equal x.fn 'sv::override)

                             (equal x.fn 'sv::lsh)
                             (equal x.fn 'sv::rsh)

                             (equal x.fn 'sv::+)
                             (equal x.fn 'sv::*)
                             ;;(equal x.fn 'sv::pow) ;; pow likely to get constants

                             (equal x.fn 'sv::b-)

                             (equal x.fn 'sv::<)
                             (equal x.fn 'sv::==)
                             (equal x.fn 'sv::===)
                             (equal x.fn 'sv::===*)
                             (equal x.fn 'sv::==?)
                             (equal x.fn 'sv::==??)
                             (equal x.fn 'sv::safer-==?)
                             ))
                  (and (integerp-of-svex (first x.args))
                       (integerp-of-svex (second x.args))))

                 ((and* (equal-len x.args 2)
                        (equal x.fn 'sv::===))
                  t)

                 ((and* (equal-len x.args 2)
                        (or* (equal x.fn 'sv::%)
                             (equal x.fn 'sv::/)))
                  (and (and (integerp (second x.args))
                            (not (equal (second x.args) 0)))
                       (integerp-of-svex (first x.args))))

                 ((and* (equal-len x.args 2)
                        (equal x.fn 'sv::signx))
                  (and (posp (first x.args))
                       (integerp-of-svex (second x.args))))

                 ((and* (equal-len x.args 2)
                        (or* (equal x.fn 'sv::bitsel)
                             (equal x.fn 'sv::zerox)))
                  (and (natp (first x.args))
                       (integerp-of-svex (second x.args))))

                 ((and* (equal-len x.args 3)
                        (or* (equal x.fn 'sv::?)
                             (equal x.fn 'sv::?*)
                             (equal x.fn 'sv::bit?)
                             (equal x.fn 'sv::bit?!)
                             (equal x.fn 'sv::?!)))
                  (if (bit?!-test-is-dont-care-p x)
                      (integerp-of-svex (third x.args))
                    (and (integerp-of-svex (first x.args))
                         (integerp-of-svex (second x.args))
                         (integerp-of-svex (third x.args)))))

                 ((and* (equal-len x.args 3)
                        (equal x.fn 'sv::partsel))
                  (and (natp (first x.args))
                       (natp (second x.args))
                       (integerp-of-svex (third x.args))))

                 ((and* (equal-len x.args 3)
                        (equal x.fn 'sv::concat))
                  (and (natp (first x.args))
                       (integerp-of-svex (second x.args))
                       (integerp-of-svex (third x.args))))

                 ((and* (equal-len x.args 3)
                        (equal x.fn 'sv::blkrev))
                  (and (natp (first x.args))
                       (posp (second x.args))
                       (integerp-of-svex (third x.args))))

                 ((and* (equal-len x.args 4)
                        (equal x.fn 'sv::partinst))
                  (and (natp (first x.args))
                       (natp (second x.args))
                       (integerp-of-svex (third x.args))
                       (integerp-of-svex (fourth x.args))))
                 (t (b* (((svex-reduce-config config))

                         (extension-obj (assoc-equal x.fn config.integerp-extns))
                         ((unless extension-obj) nil)
                         ((integerp-of-svex-extn obj) extension-obj)
                         ((unless (equal (len x.args) obj.arg-len))
                          nil)
                         ((Unless (mbt (posp obj.arg-len))) nil) ;; for measure
                         ((Unless (mbt (integerp-of-svex-extn-p extension-obj)))
                          nil) ;; for proofs without this hyp.
                         )
                      (integer-listp-of-svexlist x.args)))))))))

  (define natp-of-svex ((x sv::svex-p)
                        &key
                        ((env) 'env)
                        ((context rp::rp-term-listp) 'context)
                        ((config svex-reduce-config-p) 'config))
    :measure (rp::cons-count x)

    :verify-guards nil
    :returns (res )

    (let* ((kind (sv::Svex-kind x)))
      (case kind
        (:var (b* ((val (hons-get x env))
                   ((unless (consp val))
                    nil)
                   (val (cdr val))
                   ((when (and (quotep val)
                               (consp (cdr val))))
                    (natp (unquote val)))
                   (- (and (4vec-p val)
                           (acl2::raise "Constants are expected to be quoted in the  given env. But given instead:~p0"
                                        (cons x val))))

                   ((when (has-natp-rp val)) t)

                   ((unless (rp::rp-termp val)) ;; this may be taken out with guards on env
                    nil)

                   ((mv res &)
                    (rp::rp-check-context `(natp ,val) nil context
                                          :iff-flg t)))
                (equal res ''t)))
        (:quote (natp x))
        (:call
         (b* ((x.fn (car x))
              (x.args (cdr x)))
           (cond ((and* (equal-len x.args 1)
                        (or* (equal x.fn 'sv::id)
                             (equal x.fn 'sv::unfloat)
                             (equal x.fn 'sv::onp)
                             (equal x.fn 'sv::xdet)
                             (equal x.fn 'sv::countones) ;; returns natp, when given natp
                             (equal x.fn 'sv::onehot) ;; returns natp, when given natp
                             (equal x.fn 'sv::onehot0) ;; same as above.
                             (equal x.fn 'sv::clog2) ;; same as sv::onehot0, expect natp

                             ;;(equal x.fn 'sv::uand) ;; either 0 or -1,
                             ;;(equal x.fn 'sv::uor) ;; either 0 or -1
                             ;;(equal x.fn 'sv::uxor) ;; returns 0 or -1

                             ;;below 3 requires negative-svex-p; probably will never be necessary.
                             ;;(equal x.fn 'sv::bitnot) ;; special: to be natp, arg should be integerp but not natp
                             ;;(equal x.fn 'sv::offp) ;; same as sv::bitnot
                             ;;(equal x.fn 'sv::u-) ;; 0 returns 0. Otherwise negates, so like sv::bitnot

                             ))
                  (natp-of-svex (car x.args)))

                 ((and* (equal-len x.args 2)
                        (or* (equal x.fn 'sv::bitand) ;; at least one natp
                             (equal x.fn 'sv::resand) ;; same as bitand

                             ;;(equal x.fn 'sv::res) ;; can return don't care even when two are integer.

                             ;;(equal x.fn 'sv::pow) ;; pow likely to get constants

                             ;;(equal x.fn 'sv::b-) ;; conservatively, first natp, second negp

                             ;;(equal x.fn 'sv::<) ;; returns 0 or -1
                             ;;(equal x.fn 'sv::==) ;; returns 0 or -1
                             ;;(equal x.fn 'sv::===) ;; returns 0 or -1
                             ;;(equal x.fn 'sv::===*) ;; returns 0 or -1
                             ;;(equal x.fn 'sv::==?) ;; returns 0 or -1
                             ;;(equal x.fn 'sv::==??) ;; returns 0 or -1
                             ;;(equal x.fn 'sv::safer-==?) ;; returns 0 or -1
                             ;;(equal x.fn 'sv::===) ;; same
                             ))
                  (b* ((n1 (natp-of-svex (first x.args)))
                       (n2 (natp-of-svex (second x.args))))
                    (cond ((and n1 n2) t)
                          (n1 (integerp-of-svex (second x.args)))
                          (n2 (integerp-of-svex (first x.args))))))
                 ((and* (equal-len x.args 2)
                        (or* (equal x.fn 'sv::bitor) ;; both natp
                             (equal x.fn 'sv::resor) ;; same as bitor
                             (equal x.fn 'sv::bitxor) ;; either both negp or both natp
                             (equal x.fn 'sv::+)      ;; both natp
                             (equal x.fn 'sv::*) ;; either both natp or both negp
                             ))
                  (and (natp-of-svex (first x.args))
                       (natp-of-svex (second x.args))))

                 ((and* (equal-len x.args 2)
                        (or* ;; first integerp, second natp
                         (equal x.fn 'sv::lsh)
                         (equal x.fn 'sv::rsh)))
                  (and (integerp-of-svex (first x.args))
                       (natp-of-svex (second x.args))))

                 ((and* (equal-len x.args 2)
                        (or* ;; second integerp, first natp
                         (equal x.fn 'sv::override)))
                  (and (natp-of-svex (first x.args))
                       (integerp-of-svex (second x.args))))

                 ((and* (equal-len x.args 2)
                        ;; Will likely have constants..
                        (or* (equal x.fn 'sv::%) ;; first natp, second integer
                             (equal x.fn 'sv::/) ;; like xor
                             ))
                  (and (and (natp (second x.args))
                            (not (equal (second x.args) 0)))
                       (natp-of-svex (first x.args))))

                 ;; (equal x.fn 'sv::signx): could be anything.

                 ((and* (equal-len x.args 2)
                        (or* ;; always natp if args are integer
                         (equal x.fn 'sv::bitsel)
                         (equal x.fn 'sv::zerox)
                         ))
                  (and (natp (first x.args))
                       (integerp-of-svex (second x.args))))

                 ((and* (equal-len x.args 3)
                        (or* (equal x.fn 'sv::?)
                             (equal x.fn 'sv::?*)
                             (equal x.fn 'sv::bit?)
                             (equal x.fn 'sv::bit?!)
                             (equal x.fn 'sv::?!)))
                  (if (bit?!-test-is-dont-care-p x)
                      (natp-of-svex (third x.args))
                    (and (integerp-of-svex (first x.args))
                         (natp-of-svex (second x.args))
                         (natp-of-svex (third x.args)))))

                 ((and* (equal-len x.args 3)
                        (equal x.fn 'sv::partsel))
                  ;; always natp when arg is integer
                  (and (natp (first x.args))
                       (natp (second x.args))
                       (integerp-of-svex (third x.args))))

                 ((and* (equal-len x.args 3)
                        (equal x.fn 'sv::concat))
                  (and (natp (first x.args))
                       (integerp-of-svex (second x.args))
                       (natp-of-svex (third x.args))))

                 ((and* (equal-len x.args 3)
                        (equal x.fn 'sv::blkrev))
                  (and (natp (first x.args))
                       (posp (second x.args))
                       ;; logheads and concat repeatedly.
                       (integerp-of-svex (third x.args))))

                 ((and* (equal-len x.args 4)
                        (equal x.fn 'sv::partinst))
                  (and (natp (first x.args))
                       (natp (second x.args))
                       (natp-of-svex (third x.args))
                       ;; old value should be natp
                       (integerp-of-svex (fourth x.args))))
                 (t ;; maybe configs can be supplied later
                  nil)))))))

  (define integer-listp-of-svexlist ((lst sv::svexlist-p)
                                     &key
                                     ((env) 'env)
                                     ((context rp::rp-term-listp) 'context)
                                     ((config svex-reduce-config-p)
                                      'config))
    :measure (rp::cons-count lst)
    :returns (res )
    (or (atom lst)
        (and (integerp-of-svex (car lst))
             (integer-listp-of-svexlist (cdr lst))))))

(local
 (defthm svexlist-p-of-args-when-cdr
   (implies (and (equal (svex-kind x) :call)
                 (svex-p x))
            (svexlist-p (cdr x)))
   :hints (("goal"
            :in-theory (e/d (svex-kind svex-p ) ())))))

(local
 (defthm integerp-of-svex-extn-list-p-lemma-1
   (implies (and (integerp-of-svex-extn-list-p extensions)
                 (assoc-equal fn extensions))
            (> (cdr (assoc-equal fn extensions))
               0))
   :rule-classes :linear
   :hints (("goal"
            :in-theory (e/d
                        (integerp-of-svex-extn-p
                         integerp-of-svex-extn-list-p)
                        ())))))

(local
 (defthm integerp-of-svex-extn-p-of-assoc-equal
   (implies (and (integerp-of-svex-extn-list-p extensions)
                 (assoc-equal fn extensions))
            (integerp-of-svex-extn-p (assoc-equal fn extensions)))
   :hints (("goal"
            :in-theory (e/d (integerp-of-svex-extn-list-p) ())))))

(with-output :off :all :on (error summary)
  (verify-guards integerp-of-svex-fn
    :hints (("goal"
             :expand ((:free (x) (rp::rp-termp (cons 'integerp x)))
                      (:free (x) (rp::rp-termp (cons 'bitp x)))
                      (:free (x) (rp::rp-termp (cons 'natp x)))
                      (:free (x y) (rp::rp-term-listp (cons x y))))
             :in-theory (e/d ()
                             ((:definition acl2::apply$-badgep)
                              (:rewrite acl2::apply$-badgep-properties . 1)
                              (:definition subsetp-equal)
                              (:definition member-equal)
                              (:rewrite rp::rp-term-listp-is-true-listp)
                              (:meta rp::binary-or**/and**-guard-meta-correct)
                              rp::dummy-len-equiv
                              rp::rp-term-listp
                              rp::rp-termp
                              (:e tau-system)
                              ))))))

(memoize 'integerp-of-svex-fn
         :condition '(not (equal (svex-kind x) :quote))
         ;;:aokp t
         )

(memoize 'natp-of-svex-fn
         :condition '(not (equal (svex-kind x) :quote))
         ;;:aokp t
         )

#|(define integer-listp-of-svexlist ((lst sv::svexlist-p)
&optional
((env) 'env)
((context rp::rp-term-listp) 'context))
:returns res
(if (atom lst)
(equal lst nil)
(and (integerp-of-svex (car lst))
(integer-listp-of-svexlist (cdr lst)))))|#

;;;;;;;;;;;;;;;;;;;;

(progn

  (local
   (defthm integerp-of-4vec
     (integerp (4vec x x))
     :hints (("goal"
              :in-theory (e/d (4vec) ())))))

  (defthm integerp-of-4vec-concat
    (implies (and (force (natp a1))
                  (integerp a2)
                  (integerp a3))
             (integerp (4vec-concat a1 a2 a3)))
    :hints (("goal"
             :in-theory (e/d (4vec-concat 4vec) ()))))

  (defthm integerp-of-4vec-rsh
    (implies (and (integerp a1)
                  (integerp a2))
             (integerp (4vec-rsh a1 a2)))
    :hints (("goal"
             :in-theory (e/d (4vec-shift-core
                              4vec
                              4vec-rsh)
                             ()))))

  (defthm integerp-of-4vec-part-install
    (implies (and (force (natp a1))
                  (force (natp a2))
                  (integerp a3)
                  (integerp a4))
             (integerp (4vec-part-install a1 a2 a3 a4)))
    :hints (("goal"
             :in-theory (e/d (2vec 4vec 4vec-part-install) ()))))

  (defthm integerp-of-4vec-rev-blocks
    (implies (and (force (natp a1))
                  (force (posp a2))
                  (integerp a3))
             (integerp (sv::4vec-rev-blocks a1 a2 a3)))
    :hints (("goal"
             :in-theory (e/d (sv::4vec-rev-blocks) ()))))

  (defthm integerp-of-4vec-part-selectr
    (implies (and (force (natp a1))
                  (force (natp a2))
                  (integerp a3))
             (integerp (sv::4vec-part-select a1 a2 a3)))
    :hints (("goal"
             :in-theory (e/d (sv::4vec-part-select) ()))))

  (defthm integerp-of-4vec-bit-extract
    (implies (and (force (natp a1))
                  (integerp a2))
             (integerp (sv::4vec-bit-extract a1 a2)))
    :hints (("goal"
             :in-theory (e/d (sv::4vec-bit-extract sv::4vec-bit-index) ()))))

  (defthm integerp-of-4vec-<
    (implies (and (integerp a1)
                  (integerp a2))
             (integerp (sv::4vec-< a1 a2)))
    :hints (("goal"
             :in-theory (e/d (sv::4vec-<
                              2vec)
                             ()))))

  (defthm integerp-of-4vec-resor
    (implies (and (integerp a1)
                  (integerp a2))
             (integerp (sv::4vec-resor a1 a2)))
    :hints (("goal"
             :in-theory (e/d (sv::4vec-resor
                              4vec
                              2vec)
                             (logior logand)))))

  (defthm integerp-of-4vec-resand
    (implies (and (integerp a1)
                  (integerp a2))
             (integerp (sv::4vec-resand a1 a2)))
    :hints (("goal"
             :in-theory (e/d* (bitops::logior-of-self
                               bitops::logand-of-logand-self-1
                               sv::4vec-resand
                               acl2::logand-logior
                               acl2::commutativity-of-logand
                               bitops::commutativity-2-of-logand
                               4vec
                               2vec)
                              (logior logand)))))

  (defthm integerp-of-4vec-lsh
    (implies (and (integerp a1)
                  (integerp a2))
             (integerp (sv::4vec-lsh a1 a2)))
    :hints (("goal"
             :in-theory (e/d* (4vec-shift-core
                               sv::4vec-lsh 2vec)
                              ()))))

  (local
   (use-ihs-logops-lemmas t))

  (local
   (use-ihs-extensions t))

  (defthm integerp-of-4vec-===*
    (implies (and (integerp a1)
                  (integerp a2))
             (integerp (sv::4vec-===* a1 a2)))
    :hints (("goal"
             :in-theory (e/d* (acl2::logand-logxor
                               sv::4vec-===*
                               bitops::logior-of-self
                               bitops::logand-of-logand-self-1
                               acl2::logand-logior
                               acl2::commutativity-of-logand
                               bitops::commutativity-2-of-logand
                               4vec
                               2vec)
                              (logxor lognot logior logand)))
            ))

  (defthm integerp-of-4vec-times
    (implies (and (integerp a1)
                  (integerp a2))
             (integerp (sv::4vec-times a1 a2)))
    :hints (("goal"
             :in-theory (e/d* (2vec sv::4vec-times)
                              (logxor lognot logior logand)))
            ))

  (defthm integerp-of-4vec-remainder
    (implies (and (integerp a1)
                  (integerp a2)
                  (force (not (equal a2 0))))
             (integerp (sv::4vec-remainder a1 a2)))
    :hints (("goal"
             :in-theory (e/d* (2vec sv::4vec-remainder)
                              (logxor lognot logior logand)))
            ))

  (defthm integerp-of-4vec-quotient
    (implies (and (integerp a1)
                  (integerp a2)
                  (force (not (equal a2 0))))
             (integerp (sv::4vec-quotient a1 a2)))
    :hints (("goal"
             :in-theory (e/d* (2vec sv::4vec-quotient)
                              (logxor lognot logior logand)))
            ))

  (defthm integerp-of-4vec-wildeq
    (implies (and (integerp a1)
                  (integerp a2))
             (integerp (sv::4vec-wildeq a1 a2)))
    :hints (("goal"
             :do-not-induct t
             :in-theory (e/d* (4vec
                               sv::3vec-bitor
                               2vec sv::4vec-wildeq
                               sv::3vec-reduction-and
                               sv::3vec-bitnot
                               sv::4vec-bitxor
                               sv::4vec->lower)
                              (logxor lognot logior logand)))
            ))

  (defthm integerp-of-4vec-wildeq-safe
    (implies (and (integerp a1)
                  (integerp a2))
             (integerp (sv::4vec-wildeq-safe a1 a2)))
    :hints (("goal"
             :do-not-induct t
             :in-theory (e/d* (4vec
                               sv::3vec-bitor
                               2vec sv::4vec-wildeq-safe
                               sv::3vec-reduction-and
                               sv::3vec-bitnot
                               sv::4vec-bitxor
                               sv::4vec->lower)
                              (logxor lognot logior logand)))
            ))

  (defthm integerp-of-4vec-reduction-and
    (implies (and (integerp a1))
             (integerp (sv::4vec-reduction-and a1)))
    :hints (("goal"
             :do-not-induct t
             :in-theory (e/d* (4vec
                               sv::4vec-reduction-and
                               sv::3vec-bitor
                               2vec sv::4vec-wildeq-safe
                               sv::3vec-reduction-and
                               sv::3vec-bitnot
                               sv::4vec-bitxor
                               sv::4vec->lower)
                              (logxor lognot logior logand)))
            ))

  (defthm integerp-of-4vec-reduction-or
    (implies (and (integerp a1))
             (integerp (sv::4vec-reduction-or a1)))
    :hints (("goal"
             :do-not-induct t
             :in-theory (e/d* (4vec
                               sv::3vec-reduction-or
                               sv::4vec-reduction-or
                               sv::3vec-bitor
                               2vec sv::4vec-wildeq-safe
                               sv::3vec-reduction-and
                               sv::3vec-bitnot
                               sv::4vec-bitxor
                               sv::4vec->lower)
                              (logxor lognot logior logand)))
            ))

  (defthm integerp-of-4vec-===
    (implies t
             (integerp (sv::4vec-=== a1 a2)))
    :hints (("goal"
             :in-theory (e/d* (
                               sv::4vec-===
                               4vec
                               2vec)
                              (logxor lognot logior logand)))
            ))

  (defthm integerp-of-4vec-minus
    (implies (and (integerp a1)
                  (integerp a2))
             (integerp (sv::4vec-minus a1 a2)))
    :hints (("goal"
             :in-theory (e/d* (
                               sv::4vec-minus
                               4vec
                               2vec)
                              (logxor lognot logior logand)))
            ))

  (defthm integerp-of-4vec-onset
    (implies (and (integerp a1))
             (integerp (sv::4vec-onset a1)))
    :hints (("goal"
             :in-theory (e/d* (
                               sv::4vec-onset
                               4vec
                               2vec)
                              (logxor lognot logior logand)))
            ))

  (defthm integerp-of-4vec-offset
    (implies (and (integerp a1))
             (integerp (sv::4vec-offset a1)))
    :hints (("goal"
             :in-theory (e/d* (
                               sv::4vec-offset
                               4vec
                               2vec)
                              (logxor lognot logior logand)))
            ))

  (defthm integerp-of-4vec-uminus
    (implies (and (integerp a1))
             (integerp (sv::4vec-uminus a1)))
    :hints (("goal"
             :in-theory (e/d* (
                               sv::4vec-uminus
                               4vec
                               2vec)
                              (logxor lognot logior logand)))
            ))


  (defthm integerp-of-4vec-parity
    (implies (and (natp a1))
             (integerp (sv::4vec-parity a1)))
    :hints (("goal"
             :in-theory (e/d* (sv::4vec-parity
                               4vec
                               2vec)
                              ()))
            ))


  (defthm integerp-of-4vec-clog2
    (implies (natp x)
             (and (integerp (sv::4vec-clog2 x))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (sv::4vec-clog2 4vec
                              2VEC)
                             ()))))

  (defthm integerp-of-4vec-COUNTONES
    (implies (natp x)
             (and (integerp (sv::4vec-COUNTONES x))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (sv::4vec-COUNTONES 4vec
                              2VEC)
                             ()))))

  (defthm integerp-of-4vec-onehot
    (implies (natp x)
             (and (integerp (sv::4vec-onehot x))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (sv::4vec-onehot 4vec
                              2VEC)
                             ()))))

  (defthm integerp-of-4vec-onehot0
    (implies (natp x)
             (and (integerp (sv::4vec-onehot0 x))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (sv::4vec-onehot0 4vec
                              2VEC)
                             ()))))

  

  )

(progn

  (defthm natp-of-4vec-concat
    (implies (and (force (natp a1))
                  (integerp a2)
                  (natp a3))
             (natp (4vec-concat a1 a2 a3)))
    :hints (("goal"
             :in-theory (e/d (4vec-concat 4vec) ()))))

  
  (defthm natp-of-4vec-times
    (implies (and
              (or (and (natp a1)
                       (natp a2))
                  (and (not (posp a1))
                       (not (posp a2)))
                  (equal a1 0)
                  (equal a2 0))
              (integerp a1)
              (integerp a2))
             (natp (sv::4vec-times a1 a2)))
    :hints (("goal"
             :cases ((equal a1 0)
                     (equal a2 0))
             :in-theory (e/d (sv::4vec-times 2vec 4vec) ()))))

  (defthm natp-of-4vec-plus-conservative
    (implies (and
              (natp a1)
              (natp a2))
             (natp (sv::4vec-plus a1 a2)))
    :hints (("goal"
             :in-theory (e/d (sv::4vec-plus 2vec 4vec) ()))))

  (defthm natpp-of-4vec-rsh
    (implies (and (integerp a1)
                  (natp a2))
             (natp (4vec-rsh a1 a2)))
    :hints (("goal"
             :in-theory (e/d (4vec-shift-core
                              4vec
                              4vec-rsh)
                             ()))))

  (defthm natp-of-4vec-part-install
    (implies (and (force (natp a1))
                  (force (natp a2))
                  (natp a3)
                  (integerp a4))
             (natp (4vec-part-install a1 a2 a3 a4)))
    :hints (("goal"
             :in-theory (e/d (2vec 4vec 4vec-part-install) ()))))

  (defthm natpp-of-4vec-rev-blocks
    (implies (and (force (natp a1))
                  (force (posp a2))
                  (integerp a3))
             (natp (sv::4vec-rev-blocks a1 a2 a3)))
    :hints (("goal"
             :in-theory (e/d (sv::4vec
                              sv::4vec-rev-blocks
                              SV::REV-BLOCKS)
                             ()))))

  (defthm natp-of-4vec-part-selectr
    (implies (and (force (natp a1))
                  (force (natp a2))
                  (integerp a3))
             (natp (sv::4vec-part-select a1 a2 a3)))
    :hints (("goal"
             :in-theory (e/d (sv::4vec-part-select) ()))))

  (defthm natp-of-4vec-bit-extract
    (implies (and (force (natp a1))
                  (integerp a2))
             (natp (sv::4vec-bit-extract a1 a2)))
    :hints (("goal"
             :in-theory (e/d (sv::4vec sv::4vec-bit-extract sv::4vec-bit-index) ()))))

  (defthm natp-of-4vec-resor
    (implies (and (natp a1)
                  (natp a2))
             (natp (sv::4vec-resor a1 a2)))
    :hints (("goal"
             :in-theory (e/d (sv::4vec-resor
                              4vec
                              2vec)
                             (logior logand)))))

  (defthm natp-of-4vec-resand
    (implies (and (or (natp a1)
                      (natp a2))
                  (integerp a1)
                  (integerp a2))
             (natp (sv::4vec-resand a1 a2)))
    :hints (("goal"
             :in-theory (e/d* (bitops::logior-of-self
                               bitops::logand-of-logand-self-1
                               sv::4vec-resand
                               acl2::logand-logior
                               acl2::commutativity-of-logand
                               bitops::commutativity-2-of-logand
                               4vec
                               2vec)
                              (logior logand)))))

  (defthm natp-of-4vec-lsh
    (implies (and (integerp a1)
                  (natp a2))
             (natp (sv::4vec-lsh a1 a2)))
    :hints (("goal"
             :in-theory (e/d* (4vec-shift-core
                               4VEC
                               sv::4vec-lsh 2vec)
                              ()))))

  (local
   (use-ihs-logops-lemmas t))

  (local
   (use-ihs-extensions t))

  (local
   (use-arithmetic-5 t))

  (defthm natp-of-4vec-remainder
    (implies (and (natp a1)
                  (integerp a2)
                  (force (not (equal a2 0))))
             (natp (sv::4vec-remainder a1 a2)))
    :hints (("goal"
             :in-theory (e/d* (2vec 4vec sv::4vec-remainder)
                              (logxor lognot logior logand)))
            ))

  (local
   (use-arithmetic-5 nil))

  ;; or if both are neg, that would work too..
  (defthm natp-of-4vec-quotient
    (implies (and (or (and (natp a1)
                           (natp a2))
                      (and (not (natp a1))
                           (not (natp a2))))
                  (integerp a1)
                  (integerp a2)
                  (force (not (equal a2 0))))
             (natp (sv::4vec-quotient a1 a2)))
    :hints (("goal"
             :in-theory (e/d* (4vec 2vec sv::4vec-quotient)
                              (logxor lognot logior logand)))
            ))

  (defthm natp-of-4vec-onset
    (implies (and (natp a1))
             (natp (sv::4vec-onset a1)))
    :hints (("goal"
             :in-theory (e/d* (
                               sv::4vec-onset
                               4vec
                               2vec)
                              (logxor lognot logior logand)))
            ))

  (defthm natp-of-4vec-offset
    (implies (and (not (natp a1))
                  (integerp a1))
             (natp (sv::4vec-offset a1)))
    :hints (("goal"
             :in-theory (e/d* (
                               sv::4vec-offset
                               4vec
                               2vec)
                              (logxor lognot logior logand)))
            ))

  (defthm natp-of-4vec-uminus
    (implies (and (integerp a1)
                  (not (posp a1)))
             (natp (sv::4vec-uminus a1)))
    :hints (("goal"
             :in-theory (e/d* (
                               sv::4vec-uminus
                               4vec
                               2vec)
                              (logxor lognot logior logand)))
            ))

  (defthm natp-of-4VEC-?
    (implies (and (integerp test)
                  (natp then)
                  (natp else))
             (and (natp (sv::4vec-? test then else))))
    :hints (("Goal"
             :in-theory (e/d (sv::4vec-?
                              SV::3VEC-?)
                             ()))))

  (local
   (use-arithmetic-5 t))
  (defthm natp-of-4VEC-bit?
    (implies (and (integerp test)
                  (natp then)
                  (natp else))
             (and (natp (sv::4vec-bit? test then else))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (4vec
                              sv::4vec-bit?
                              SV::3VEC-bit?)
                             ()))))

  (defthm natp-of-4VEC-bit?!
    (implies (and (integerp test)
                  (natp then)
                  (natp else))
             (and (natp (sv::4vec-bit?! test then else))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (4vec
                              sv::4vec-bit?!
                              sv::4vec-bitmux
                              acl2::logite
                              )
                             ()))))

  (defthm natp-of-4VEC-?*
    (implies (and (integerp test)
                  (natp then)
                  (natp else))
             (and (natp (sv::4vec-?* test then else))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (4vec
                              sv::4vec-?*
                              SV::3VEC-?*)
                             ()))))

  (defthm natp-of-4VEC-?!
    (implies (and (integerp test)
                  (natp then)
                  (natp else))
             (and (natp (sv::4vec-?! test then else))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (4vec
                              sv::4vec-?!
                              )
                             ()))))

  (local
   (use-arithmetic-5 nil))

  (defthm natp-of-4vec-clog2
    (implies (natp x)
             (and (natp (sv::4vec-clog2 x))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (sv::4vec-clog2 4vec
                              2VEC)
                             ()))))

  (defthm natp-of-4vec-COUNTONES
    (implies (natp x)
             (and (natp (sv::4vec-COUNTONES x))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (sv::4vec-COUNTONES 4vec
                              2VEC)
                             ()))))

  (defthm natp-of-4vec-onehot
    (implies (natp x)
             (and (natp (sv::4vec-onehot x))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (sv::4vec-onehot 4vec
                              2VEC)
                             ()))))

  (defthm natp-of-4vec-onehot0
    (implies (natp x)
             (and (natp (sv::4vec-onehot0 x))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (sv::4vec-onehot0 4vec
                              2VEC)
                             ()))))

  (defthm natp-of-4vec-fix
    (implies (natp x)
             (and (natp (sv::4vec-fix x))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (sv::4vec-fix 4vec
                              2VEC)
                             ()))))

  (defthm natp-of-3vec-fix
    (implies (natp x)
             (and (natp (sv::3vec-fix x))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (sv::3vec-fix 4vec
                              2VEC)
                             ()))))

  )

(local
 (svex-eval-lemma-tmpl
  (progn
    (defthm posp-of-svex-implies-for-svex-eval
      (implies (posp x)
               (posp (svex-eval x env)))
      :hints (("goal"
               :expand ((svex-eval x env))
               :in-theory (e/d (svex-eval
                                sv::svex-quote->val
                                sv::svex-kind)
                               ()))))

    (defthm natp-of-svex-implies-for-svex-eval
      (implies (natp x)
               (natp (svex-eval x env)))
      :hints (("goal"
               :expand ((svex-eval x env))
               :in-theory (e/d (svex-eval
                                sv::svex-quote->val
                                sv::svex-kind)
                               ()))))

    (defthm integerp-of-svex-implies-for-svex-eval
      (implies (integerp x)
               (integerp (svex-eval x env)))
      :hints (("goal"
               :expand ((svex-eval x env))
               :in-theory (e/d (svex-eval
                                sv::svex-quote->val
                                sv::svex-kind)
                               ()))))

    (defthm nonzero-of-svex-implies-for-svex-eval
      (implies (and (integerp x)
                    (not (equal x 0)))
               (not (equal (svex-eval x env) 0)))
      :hints (("goal"
               :expand ((svex-eval x env))
               :in-theory (e/d (svex-eval
                                sv::svex-quote->val
                                sv::svex-kind)
                               ())))))))

(local
 (defthm remove-consp-hons-assoc-equal
   (iff (consp (hons-assoc-equal svex env))
        (hons-assoc-equal svex env))))

(progn
  (defun-sk sub-alistp (alist1 alist2)
    (forall key
            (implies (hons-assoc-equal key alist1)
                     (equal (hons-assoc-equal key alist1)
                            (hons-assoc-equal key alist2)))))

  (defthm sub-alistp-of-self
    (sub-alistp x x)
    :rule-classes (:rewrite :type-prescription))

  (defthm sub-alistp-of-with-nil
    (sub-alistp nil x))

  (defthm hons-assoc-equal-and-sub-alistp-lemma
    (implies (and (sub-alistp alist1 alist2)
                  (hons-assoc-equal key alist1))
             (equal (hons-assoc-equal key alist2)
                    (hons-assoc-equal key alist1)))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance sub-alistp-necc))
             :in-theory (e/d ()
                             (sub-alistp)))))

  (in-theory (disable sub-alistp)))

(local
 (defthm rp::falist-consistent-aux-lemma1
   (implies (and (rp::falist-consistent-aux env-falist term)
                 (hons-assoc-equal x env-falist))
            (equal (cdr (hons-assoc-equal x (rp-evlt term a)))
                   (rp-evlt (cdr (hons-assoc-equal x env-falist))
                            a)))
   :hints (("Goal"
            :in-theory (e/d ()
                            (sub-alistp))))))

(local
 (defthm rp::falist-consistent-aux-lemma
   (implies (and (rp::falist-consistent-aux big-env-falist term)
                 (hons-assoc-equal x env-falist)
                 (sub-alistp env-falist big-env-falist))
            (equal (cdr (hons-assoc-equal x (rp-evlt term a)))
                   (rp-evlt (cdr (hons-assoc-equal x big-env-falist))
                            a)))
   :hints (("Goal"
            :do-not-induct T
            :in-theory (e/d ()
                            (sub-alistp))))))

(local
 (defthm rp::falist-consistent-aux-lemma-2
   (implies (and (rp::falist-consistent-aux env-falist term))
            (iff (hons-assoc-equal x (rp-evlt term a))
                 (hons-assoc-equal x env-falist)))))

(local
 (defthm falist-consistent-aux-lemma
   (implies (and (rp::falist-consistent-aux big-env env-term)
                 (sub-alistp env big-env)
                 (hons-assoc-equal svex env)
                 (equal (svex-kind svex) :var)
                 (sv::svex-p svex))
            (equal (sv::svex-env-lookup svex
                                        (rp-evlt env-term a))
                   (4vec-fix (rp-evlt (cdr (hons-assoc-equal svex big-env))
                                      a))))
   :hints (("goal"
            ;;:induct (rp::falist-consistent-aux env env-term)
            :do-not-induct t
            :in-theory (e/d (svex-kind
                             svex-p
                             ;;sv::svar-fix
                             rp::falist-consistent-aux
                             hons-assoc-equal
                             sv::svex-env-lookup)
                            (sub-alistp))))))

(local
 (defthm falist-consistent-aux-valid-sc-lemma-1
   (implies (and (rp::falist-consistent-aux env env-term)
                 (rp::valid-sc env-term a)
                 (hons-assoc-equal svex env))
            (rp::valid-sc (cdr (hons-assoc-equal svex env))
                          a))
   :hints (("Goal"
            ;;:induct (hons-assoc-equal svex env)
            ;;:do-not-induct t
            :in-theory (e/d (rp::falist-consistent-aux
                             rp::valid-sc
                             rp::is-rp
                             rp::is-if)
                            ((:rewrite rp::valid-sc-cons)
                             (:definition rp::rp-termp)
                             (:definition rp::rp-term-listp)

                             (:linear acl2::apply$-badgep-properties . 1)
                             (:definition acl2::apply$-badgep)
                             (:rewrite
                              rp::rp-evl-and-side-cond-consistent-rp-rw-relieve-hyp)
                             (:rewrite rp::valid-sc-caddr)))))))

(local
 (defthm falist-consistent-aux-valid-sc-lemma-2
   (implies (and (rp::falist-consistent-aux big-env env-term)
                 (rp::valid-sc env-term a)
                 (sub-alistp env big-env)
                 (hons-assoc-equal svex env))
            (rp::valid-sc (cdr (hons-assoc-equal svex env))
                          a))
   :hints (("Goal"
            :use ((:instance falist-consistent-aux-valid-sc-lemma-1
                             (env big-env)))
            ;;:induct (hons-assoc-equal svex env)
            ;;:do-not-induct t
            :in-theory (e/d ()
                            (falist-consistent-aux-valid-sc-lemma-1))))))

(local
 (in-theory (disable sv::svex-apply$-is-svex-apply
                     sv::svex-eval$-is-svex-eval
                     sv::svexlist-eval$-is-svexlist-eval)))

(Local
 (defthm integerp-of-4vec-fix
   (implies (integerp x)
            (integerp (4vec-fix x)))))

(local
 (defthm rp-evlt-of-quoted
   (implies (and (consp x)
                 (equal (car x) 'quote))
            (equal (rp-evlt x a)
                   (unquote x)))))

(local
 (defthm rp-evlt-of-integerp-call
   (implies (and (consp x)
                 (equal (car x) 'integerp))
            (equal (rp-evlt x a)
                   (integerp (rp-evlt (cadr x) a))))))

(Local
 (defthm integerp-of-4VECLIST-NTH-SAFE-lemma
   (implies (and (> (len x) 0)
                 (natp index)
                 (< index (len x))
                 (integer-listp x))
            (integerp (4veclist-nth-safe index x)))
   :hints (("Goal"
            :in-theory (e/d (integer-listp
                             4veclist-nth-safe)
                            ())))))

(local
 (defthm has-integerp-rp-implies
   (implies (has-integerp-rp x)
            (case-match x
              (('rp & &) t)))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (RP::IS-RP-LOOSE
                             has-integerp-rp)
                            ())))))

(local
 (defthm has-natp-rp-implies
   (implies (has-natp-rp x)
            (case-match x
              (('rp & &) t)))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (RP::IS-RP-LOOSE
                             has-natp-rp)
                            ())))))

(local
 (defthm car-of-assoc-equal
   (implies (assoc-equal fn alist)
            (equal (car (assoc-equal fn alist))
                   fn))))

(defthm integerp-of-svex-extn-p-of-assoc-equal-of-svex-functions
  (implies (assoc-equal fn sv::*svex-op-table*)
           (not (integerp-of-svex-extn-p (assoc-equal fn extensions))))
  :hints (("goal"
           :cases ((assoc-equal fn extensions))
           :in-theory (e/d
                       (svex-foreign-fnsym-p integerp-of-svex-extn-p)
                       (assoc-equal)))))

(local
 (defthm integerp-of-svex-extn-correct$-lemma
   (implies (and (integerp-of-svex-extn-p extension-obj)
                 extension-obj
                 (equal fn (car extension-obj))
                 (equal arg-len (integerp-of-svex-extn->arg-len extension-obj))
                 (equal (len args) arg-len)
                 (not (member-equal fn (strip-cars sv::*svex-op-table*)))
                 (integerp-of-svex-extn-correct$ extension-obj)
                 (integer-listp (svexlist-eval$ args env)))
            (integerp (apply$ fn
                              (svexlist-eval$ args env))))
   :hints (("goal"
            :do-not-induct t
            :expand ((:free (fn args)
                            (svex-eval$ (cons fn args) env)))
            :use ((:instance integerp-of-svex-extn-correct$-necc
                             (obj extension-obj)
                             (args args)
                             (env env)))
            :in-theory (e/d (integerp-of-svex-extn->arg-len
                             integerp-of-svex-extn->fn
                             svex-apply$
                             integerp-of-svex-extn-p
                             svex-kind
                             svex-call->fn
                             svex-call->args
                             svex-foreign-fnsym-p)
                            (4vec-reduction-and-to-4vec-bitand
                             integerp-of-svex-extn-correct$-necc
                             integerp-of-svex-extn-correct$
                             ))))))

(local
 (defthm fnsym-fix-car-of-svex-call
   (implies (and (svex-p x)
                 (equal (svex-kind x) :call))
            (equal (fnsym-fix (car x))
                   (car x)))
   :hints (("goal"
            :in-theory (e/d (fnsym-fix svex-p svex-kind) ())))))

(local
 (defthm integerp-of-svex-extn-correct$-of-assoc-equal-lemma
   (implies (and (integerp-of-svex-extn-correct$-lst extensions)
                 (or (integerp-of-svex-extn-p (assoc-equal fn extensions))
                     (assoc-equal fn extensions)))
            (integerp-of-svex-extn-correct$ (assoc-equal fn extensions)))
   :hints (("goal"
            :in-theory (e/d (integerp-of-svex-extn-correct$-lst)
                            (integerp-of-svex-extn-correct$))))))

(local
 (defthm assoc-equal-of-nil
   (equal (ASSOC-EQUAL (CAR X) NIL)
          nil)))

(local
 (defret bit?!-test-is-dont-care-p-implies
   (implies res
            (and (equal (car x) 'sv::bit?!)
                 (NOT (SVEX-REDUCE-CONFIG->KEEP-MISSING-ENV-VARS CONFIG))))
   :fn bit?!-test-is-dont-care-p
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (bit?!-test-is-dont-care-p) ())))))

(local
 (defthm svex-eval-of-bit?!-test-is-dont-care-p-correct-lemma
   (b* (((sv::4vec x) (4VEC-PART-SELECT start size '(-1 . 0))))
     (and (equal (logand x.upper x.lower) 0)
          (equal (logand x.lower x.upper) 0)))
   :hints (("Goal"
            :in-theory (e/d (4VEC-SHIFT-CORE
                             4VEC-RSH
                             4VEC-CONCAT
                             4VEC-PART-SELECT)
                            ())))))

(local
 (defthm SV::4VEC-BIT?!-when-test-doesnt-have-1
   (implies (equal (logand (sV::4vec->lower test) (sV::4vec->upper test)) 0)
            (equal (sv::4vec-bit?! test then else)
                   (sv::4vec-fix else)))
   :hints (("Goal"
            :in-theory (e/d (sv::4vec-bit?! sv::4vec-bitmux sV::4vec-1mask) ())))))

(svex-eval-lemma-tmpl
 (local
  (defret svex-eval-of-bit?!-test-is-dont-care-p-correct
    (implies (and res
                  (rp::falist-consistent-aux env env-term)
                  )
             (equal (sv::svex-eval x (rp-evlt env-term a))
                    (sv::svex-eval (third (cdr x)) (rp-evlt env-term a))))
    :fn bit?!-test-is-dont-care-p
    :hints (("Goal"
             :do-not-induct t

             :expand ((SVEX-EVAL X (RP-EVLT ENV-TERM A))
                      (SVEXLIST-EVAL (CDDDR (CADR X))
                                     (RP-EVLT ENV-TERM A))
                      (SVEXLIST-EVAL (CDDR (CADR X))
                                     (RP-EVLT ENV-TERM A))
                      (SVEXLIST-EVAL (CDR (CADR X))
                                     (RP-EVLT ENV-TERM A))
                      (svex-eval (cadddr (cadr x))
                                 (rp-evlt env-term a))
                      (svexlist-eval (cddr (cadr x))
                                     (rp-evlt env-term a))
                      (svexlist-eval (cdr (cadr x))
                                     (rp-evlt env-term a))
                      (svex-eval (cadddr (cadr x)) env-term)
                      (svexlist-eval (cdr x)
                                     (rp-evlt env-term a))
                      (svex-eval (cadr x)
                                 (rp-evlt env-term a)))
             :in-theory (e/d (;;4VEC-PART-SELECT
                              ;;SV::4VEC-BIT?!
                              ;;SVEXLIST-EVAL
                              SV::SVAR-P
                              SVEX-KIND-WOG-IS-SVEX-KIND
                              SV::SVEX-QUOTE->VAL
                              SV::SVEX-ENV-LOOKUP
                              ;;SV::SVAR-FIX
                              SVEX-VAR->NAME
                              SVEX-KIND
                              SV::4VEC-FIX-UNDER-4VEC-EQUIV

                              SVEX-APPLY
                              SVEX-CALL->FN
                              SVEX-CALL->args
                              bit?!-test-is-dont-care-p)
                             ((:definition rp::rp-termp)
                              (:definition rp::rp-term-listp)
                              (:rewrite rp::is-if-rp-termp))))))))

(local
 (defthm rp-evlt-of-natp
   (equal (rp-evlt `(natp ,x) a)
          (natp (rp-evlt x a)))))

(local
 (defthm rp-evlt-of-bitp
   (equal (rp-evlt `(bitp ,x) a)
          (bitp (rp-evlt x a)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; main lemma.
(with-output
  :off :all
  :gag-mode nil
  :on (error summary)
  (svex-eval-lemma-tmpl
   (defret-mutual svex-eval-of-integerp-of-svex-is-correct
     (defret svex-eval-of-<fn>-is-correct
       (and (implies (and ;;(equal (svex-kind svex) :var)
                      (sub-alistp env big-env)
                      (sv::svex-p x)
                      (rp::rp-term-listp context)
                      res
                      (rp::valid-sc env-term a)
                      (rp::eval-and-all context a)
                      (rp::falist-consistent-aux big-env env-term)
                      (:@ :dollar-eval
                          (integerp-of-svex-extn-correct<$>-lst
                           (svex-reduce-config->integerp-extns config)))
                      (:@ :normal-eval
                          (equal (svex-reduce-config->integerp-extns config)
                                 nil))
                      (or* (svex-reduce-config->keep-missing-env-vars config)
                           (equal big-env env)))
                     (integerp (sv::svex-eval x (rp-evlt env-term a))))
            )
       :fn integerp-of-svex)
     (defret svex-eval-of-<fn>-is-correct
       (and (implies (and ;;(equal (svex-kind svex) :var)
                      (sub-alistp env big-env)
                      (sv::svex-p x)
                      (rp::rp-term-listp context)
                      res
                      (rp::valid-sc env-term a)
                      (rp::eval-and-all context a)
                      (rp::falist-consistent-aux big-env env-term)
                      (:@ :dollar-eval
                          (integerp-of-svex-extn-correct<$>-lst
                           (svex-reduce-config->integerp-extns config)))
                      (:@ :normal-eval
                          (equal (svex-reduce-config->integerp-extns config)
                                 nil))
                      (or* (svex-reduce-config->keep-missing-env-vars config)
                           (equal big-env env)))
                     (natp (sv::svex-eval x (rp-evlt env-term a))))
            )
       :fn natp-of-svex)
     (defret svexlist-eval-of-<fn>-is-correct
       (and (implies (and ;;(equal (svex-kind svex) :var)
                      (sub-alistp env big-env)
                      (sv::svexlist-p lst)
                      (rp::rp-term-listp context)
                      res
                      (rp::valid-sc env-term a)
                      (rp::eval-and-all context a)
                      (rp::falist-consistent-aux big-env env-term)
                      (:@ :dollar-eval
                          (integerp-of-svex-extn-correct<$>-lst
                           (svex-reduce-config->integerp-extns config)))
                      (:@ :normal-eval
                          (equal (svex-reduce-config->integerp-extns config) nil))
                      (or* (svex-reduce-config->keep-missing-env-vars config)
                           (equal big-env env)))
                     (integer-listp (sv::svexlist-eval lst (rp-evlt env-term a))))
            )
       :fn integer-listp-of-svexlist)

     :hints (
             ("goal"
              :do-not-induct t
              ;;:induct (integerp-of-svex svex env context)
              :expand ((svex-eval x (rp-evlt env-term a))
                       (INTEGERP-OF-SVEX X)
                       (natp-of-svex X)
                       (:free (lst) (member-equal (car x) lst)))
              :in-theory (e/d (or*

                               ;;bit?!-test-is-dont-care-p

                               sv::svex-quote->val
                               svex-apply
                               svexlist-eval
                               svex-call->fn
                               svex-var->name
                               ;;sv::svex-env-lookup
                               ;;sv::svar-fix
                               sv::svex-call->args
                               integerp-of-svex
                               natp-of-svex
                               integer-listp-of-svexlist
                               hons-assoc-equal

                               )
                              (natp
                               ACL2::NATP-WHEN-INTEGERP
                               svex-eval-of-bit?!-test-is-dont-care-p-correct
                               (:META
                                RP::BINARY-OR**/AND**-GUARD-META-CORRECT)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE DEFAULT-CAR)
                               (:REWRITE ACL2::OR*-TRUE-FIRST)
                               (:REWRITE ACL2::NATP-WHEN-GTE-0)
                               (:REWRITE ACL2::OR*-TRUE-SECOND)
                               (:DEFINITION ASSOC-EQUAL)
                               INTEGERP-OF-SVEX-EXTN-CORRECT$
                               (:definition acl2::apply$-badgep)
                               (:rewrite acl2::apply$-badgep-properties . 1)
                               (:definition rp::eval-and-all)
                               (:rewrite rp::rp-evl-and-side-cond-consistent-rp-rw-relieve-hyp)
                               (:definition subsetp-equal)
                               (:definition member-equal)
                               rp-trans
                               rp::rp-trans-is-term-when-list-is-absent
                               rp::valid-sc
                               loghead
                               4vec-reduction-and-to-4vec-bitand
                               expt floor logapp
                               posp natp
                               sub-alistp
                               rp::rp-evl-of-variable
                               4VEC-PARITY-TO-BITXOR
                               rp::rp-check-context-is-correct-iff)))
             (and stable-under-simplificationp
                  '(:use ((:instance rp::rp-check-context-is-correct-iff
                                     (rp::iff-flg t)
                                     (rp::dont-rw nil)
                                     (rp::context context)
                                     (rp::a a)
                                     (rp::term (list 'integerp
                                                     (cdr (hons-assoc-equal x big-env))))
                                     (rp::attach-sc nil)
                                     (rp::rw-context-flg nil))
                          (:instance rp::rp-check-context-is-correct-iff
                                     (rp::iff-flg t)
                                     (rp::dont-rw nil)
                                     (rp::context context)
                                     (rp::a a)
                                     (rp::term (list 'bitp
                                                     (cdr (hons-assoc-equal x big-env))))
                                     (rp::attach-sc nil)
                                     (rp::rw-context-flg nil))
                          (:instance rp::rp-check-context-is-correct-iff
                                     (rp::iff-flg t)
                                     (rp::dont-rw nil)
                                     (rp::context context)
                                     (rp::a a)
                                     (rp::term (list 'natp
                                                     (cdr (hons-assoc-equal x big-env))))
                                     (rp::attach-sc nil)
                                     (rp::rw-context-flg nil))
                          (:instance svex-eval-of-bit?!-test-is-dont-care-p-correct
                                     (env big-env))
                          )))))))

(with-output
  :off :all
  :gag-mode nil
  :on (error summary)
  (svex-eval-lemma-tmpl
   (defret-mutual svex-eval-of-integerp-of-svex-is-correct-env=nil
     (defret svex-eval-of-<fn>-is-correct-env=nil
       (implies (and (equal env nil)
                     (sv::svex-p x)
                     res

                     (:@ :dollar-eval
                         (integerp-of-svex-extn-correct<$>-lst
                          (svex-reduce-config->integerp-extns config)))
                     (:@ :normal-eval
                         (equal (svex-reduce-config->integerp-extns config) nil))
                     (svex-reduce-config->keep-missing-env-vars config))
                (integerp (sv::svex-eval x svex-env)))
       :fn integerp-of-svex)
     (defret svex-eval-of-<fn>-is-correct-env=nil
       (implies (and (equal env nil)
                     (sv::svex-p x)
                     res

                     (:@ :dollar-eval
                         (integerp-of-svex-extn-correct<$>-lst
                          (svex-reduce-config->integerp-extns config)))
                     (:@ :normal-eval
                         (equal (svex-reduce-config->integerp-extns config) nil))
                     (svex-reduce-config->keep-missing-env-vars config))
                (natp (sv::svex-eval x svex-env)))
       :fn natp-of-svex)
     (defret svexlist-eval-of-<fn>-is-correct-env=nil
       (implies (and (equal env nil)
                     (sv::svexlist-p lst)
                     res
                     (:@ :dollar-eval
                         (integerp-of-svex-extn-correct<$>-lst
                          (svex-reduce-config->integerp-extns config)))
                     (:@ :normal-eval
                         (equal (svex-reduce-config->integerp-extns config) nil))
                     (svex-reduce-config->keep-missing-env-vars config))
                (integer-listp (sv::svexlist-eval lst svex-env)))
       :fn integer-listp-of-svexlist)
     :hints (("goal"
              :do-not-induct t
              :expand ((:free (lst) (member-equal (car x) lst)))
              ;;:induct (integerp-of-svex svex nil context)
              :in-theory (e/d (SVEXLIST-EVAL
                               INTEGER-LISTP-OF-SVEXLIST
                               sv::svex-quote->val
                               svex-apply
                               svexlist-eval
                               svex-call->fn
                               svex-var->name
                               sv::svex-call->args
                               integerp-of-svex
                               natp-of-svex
                               hons-assoc-equal)
                              (svex-eval-of-bit?!-test-is-dont-care-p-correct
                               (:definition acl2::apply$-badgep)
                               (:rewrite acl2::apply$-badgep-properties . 1)
                               (:rewrite acl2::apply$-badgep-properties . 2)
                               (:rewrite rp::rp-term-listp-is-true-listp)
                               (:definition subsetp-equal)
                               (:definition true-listp)
                               (:definition member-equal)
                               (:definition rp::rp-term-listp)
                               (:rewrite default-cdr)
                               (:rewrite acl2::or*-true-second)
                               (:definition assoc-equal)
                               (:meta
                                rp::binary-or**/and**-guard-meta-correct)
                               (:rewrite
                                acl2::member-equal-newvar-components-1)
                               (:definition rp::rp-termp)
                               (:rewrite rp::rp-termp-implies-cdr-listp)

                               4VEC-PARITY-TO-BITXOR
                               loghead
                               4vec-reduction-and-to-4vec-bitand
                               expt floor logapp
                               posp natp
                               sub-alistp
                               rp::rp-evl-of-variable
                               rp::rp-check-context-is-correct-iff)))

             ))))

#|(svex-eval-lemma-tmpl
(defret svexlist-eval-of-integer-listp-of-svexlist-is-correct
(and (implies (and
(sub-alistp env big-env)
(sv::svexlist-p lst)
(rp::rp-term-listp context)
(integer-listp-of-svexlist lst env context)
(rp::valid-sc env-term a)
(rp::eval-and-all context a)
(rp::falist-consistent-aux big-env env-term))
(integer-listp (sv::svexlist-eval lst (rp-evlt env-term a))))
(implies (and
(sv::svexlist-p lst)
(integer-listp-of-svexlist lst nil context))
(integer-listp (sv::svexlist-eval lst svex-env))))
:fn integer-listp-of-svexlist
:hints (("goal"
:in-theory (e/d (integer-listp-of-svexlist
sv::svexlist-eval)
(sub-alistp
rp::falist-consistent-aux
rp::eval-and-all
svex-eval))))))|#

(defmacro create-integerp-of-svex-extn (&key fn
                                             prepwork)
  `(make-event
    (b* ((arg-len (len (acl2::formals ',fn (w state)))))
      (acl2::template-subst
       '(defsection integerp-of-svex-extn-correct-of-<fn>
          ,@prepwork
          (defthm integerp-of-svex-extn-correct-of-<fn>
            (b* ((obj (make-integerp-of-svex-extn
                       :fn '<fn>
                       :arg-len <arg-len>)))
              (implies (apply$-warrant-<fn>)
                       (svl::integerp-of-svex-extn-correct$ obj)))
            :hints (("Goal"
                     ;;:do-not '(preprocess fertilize generalize)
                     :expand ((:free (args)
                                     (sv::svex-apply$ '<fn> args))
                              (:free (y)
                                     (sv::svex-call->fn (cons '<fn> y)))
                              (:free (y)
                                     (sv::svex-call->args (cons '<fn> y)))
                              (:free (y env)
                                     (sv::svex-eval$ (cons '<fn> y) env))
                              (:free (y)
                                     (sv::svex-kind (cons '<fn> y))))
                     :in-theory (e/d (fty::equal-of-plus-one
                                      fty::equal-of-len
                                      sv::svex-eval$-when-fncall
                                      <fn>)
                                     (sv::svexlist-eval$
                                      sv::svex-eval$
                                      sv::svex-kind)))))
          (table integerp-of-svex-extns (make-integerp-of-svex-extn
                                         :fn '<fn>
                                         :arg-len <arg-len>)
                 'integerp-of-svex-extn-correct-of-<fn>))
       :atom-alist `((<arg-len> . ,arg-len)
                     (<fn> . ,',fn))
       :str-alist '(("<FN>" . ,(symbol-name fn)))
       :pkg-sym ',fn))))
