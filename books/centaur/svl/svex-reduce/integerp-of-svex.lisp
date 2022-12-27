
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

(include-book "centaur/sv/svex/eval" :dir :system)

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



(define integerp-of-svex ((x sv::svex-p)
                          &optional
                          ((env) 'env)
                          ((context rp::rp-term-listp) 'context))
  :measure (rp::cons-count x)
  :hints (("Goal"
           :in-theory (e/d (SVEX-CALL->ARGS
                            rp::measure-lemmas)
                           ())))
  :verify-guards nil
  :returns (res booleanp)

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

                 ((unless (rp::rp-termp val)) ;; this may be taken out with guards on env
                  nil)

                 ((mv res &)
                  (rp::rp-check-context `(integerp ,val) nil context
                                        :iff-flg t)))
              (equal res ''t)))
      (:quote (integerp x))
      (:call
       (b* ((x.fn (car x))
            (x.args (cdr x)))
         (cond ((and (equal-len x.args 1)
                     (or (equal x.fn 'sv::id)
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

               
               ((and (equal-len x.args 2)
                     (or (equal x.fn 'sv::bitand)
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

               ((and (equal-len x.args 2)
                     (equal x.fn 'sv::===))
                t)

               ((and (equal-len x.args 2)
                     (or (equal x.fn 'sv::%)
                         (equal x.fn 'sv::/)))
                (and (and (integerp (second x.args))
                          (not (equal (second x.args) 0)))    
                     (integerp-of-svex (first x.args))))
               
               ((and (equal-len x.args 2)
                     (or (equal x.fn 'sv::signx)))
                (and (posp (first x.args))
                     (integerp-of-svex (second x.args))))

               ((and (equal-len x.args 2)
                     (or (equal x.fn 'sv::bitsel)
                         (equal x.fn 'sv::zerox)))
                (and (natp (first x.args))
                     (integerp-of-svex (second x.args))))

               ((and (equal-len x.args 3)
                     (or (equal x.fn 'sv::?)
                         (equal x.fn 'sv::?*)
                         (equal x.fn 'sv::bit?)
                         (equal x.fn 'sv::bit?!)
                         (equal x.fn 'sv::?!)))
                (and (integerp-of-svex (first x.args))
                     (integerp-of-svex (second x.args))
                     (integerp-of-svex (third x.args))))

               ((and (equal-len x.args 3)
                     (equal x.fn 'sv::partsel))
                (and (natp (first x.args))
                     (natp (second x.args))
                     (integerp-of-svex (third x.args))))

               ((and (equal-len x.args 3)
                     (equal x.fn 'sv::concat))
                (and (natp (first x.args))
                     (integerp-of-svex (second x.args))
                     (integerp-of-svex (third x.args))))

               ((and (equal-len x.args 3)
                     (equal x.fn 'sv::blkrev))
                (and (natp (first x.args))
                     (posp (second x.args))
                     (integerp-of-svex (third x.args))))

               ((and (equal-len x.args 4)
                     (equal x.fn 'sv::partinst))
                (and (natp (first x.args))
                     (natp (second x.args))
                     (integerp-of-svex (third x.args))
                     (integerp-of-svex (fourth x.args))))
               (t nil)))))))

(with-output :off :all :on (error summary)
  (verify-guards integerp-of-svex-fn
    :hints (("Goal"
             :in-theory (e/d () ((:e tau-system)))))))


(memoize 'integerp-of-svex-fn
         :condition '(equal (svex-kind x) :call)
         ;;:aokp t
         )

(progn

  (defthm integerp-of-4vec
    (integerp (4vec x x))
    :hints (("goal"
             :in-theory (e/d (4vec) ()))))

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
    
  )

(progn
  (local
   (defthm posp-of-svex-implies
     (implies (posp x)
              (posp (svex-eval x env)))
     :hints (("goal"
              :expand ((svex-eval x env))
              :in-theory (e/d (svex-eval
                               sv::svex-quote->val
                               sv::svex-kind)
                              ())))))

  (local
   (defthm natp-of-svex-implies
     (implies (natp x)
              (natp (svex-eval x env)))
     :hints (("goal"
              :expand ((svex-eval x env))
              :in-theory (e/d (svex-eval
                               sv::svex-quote->val
                               sv::svex-kind)
                              ())))))

  (local
   (defthm integerp-of-svex-implies
     (implies (integerp x)
              (integerp (svex-eval x env)))
     :hints (("goal"
              :expand ((svex-eval x env))
              :in-theory (e/d (svex-eval
                               sv::svex-quote->val
                               sv::svex-kind)
                              ())))))

  (local
   (defthm nonzero-of-svex-implies
     (implies (and (integerp x)
                   (not (equal x 0)))
              (not (equal (svex-eval x env) 0)))
     :hints (("goal"
              :expand ((svex-eval x env))
              :in-theory (e/d (svex-eval
                               sv::svex-quote->val
                               sv::svex-kind)
                              ()))))))


(local
 (defthm remove-consp-hons-assoc-equal
   (iff (consp (hons-assoc-equal svex env))
        (hons-assoc-equal svex env))))

(local
 (defthm rp::falist-consistent-aux-lemma
   (implies (and (rp::falist-consistent-aux env-falist term)
                 (hons-assoc-equal x env-falist))
            (equal (cdr (hons-assoc-equal x (rp-evlt term a)))
                   (rp-evlt (cdr (hons-assoc-equal x env-falist))
                            a)))))
(local
 (defthm rp::falist-consistent-aux-lemma-2
   (implies (and (rp::falist-consistent-aux env-falist term))
            (iff (hons-assoc-equal x (rp-evlt term a))
                 (hons-assoc-equal x env-falist)))))

(local
 (defthm falist-consistent-aux-lemma
   (implies (and (rp::falist-consistent-aux env env-term)
                 (hons-assoc-equal svex env)
                 (equal (svex-kind svex) :var)
                 (sv::svex-p svex))
            (equal (sv::svex-env-lookup svex
                                        (rp-evlt env-term a))
                   (4vec-fix (rp-evlt (cdr (hons-assoc-equal svex env))
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
                            ())))))
   

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; main lemma.

(defret integerp-of-svex-is-correct
  (implies (and ;;(equal (svex-kind svex) :var)

                (sv::svex-p svex)
                (rp::rp-term-listp context)
                (integerp-of-svex svex env context)
                (rp::eval-and-all context a)
                (rp::falist-consistent-aux env env-term))
           (integerp (sv::svex-eval svex (rp-evlt env-term a))))
  :fn integerp-of-svex
  :hints (("goal"
           :do-not-induct t
           :induct (integerp-of-svex svex env context)
           :expand ((svex-eval svex (rp-evlt env-term a)))
           :in-theory (e/d (sv::svex-quote->val
                            svex-apply
                            svexlist-eval
                            svex-call->fn
                            svex-var->name
                            ;;sv::svex-env-lookup
                            ;;sv::svar-fix
                            sv::svex-call->args
                            integerp-of-svex

                            hons-assoc-equal)
                           (loghead
                            4vec-reduction-and-to-4vec-bitand
                            expt floor logapp
                            posp natp
                            
                            rp::rp-evl-of-variable
                            rp::rp-check-context-is-correct-iff)))
          (and stable-under-simplificationp
               '(:use ((:instance rp::rp-check-context-is-correct-iff
                                  (rp::iff-flg t)
                                  (rp::dont-rw nil)
                                  (rp::context context)
                                  (rp::a a)
                                  (rp::term (list 'integerp
                                                  (cdr (hons-assoc-equal svex env))))
                                  (rp::attach-sc nil)
                                  (rp::rw-context-flg nil)))))))
