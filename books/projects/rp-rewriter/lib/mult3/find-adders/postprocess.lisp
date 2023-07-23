
; Multiplier verification

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

(in-package "RP")

(include-book "../fnc-defs")
(include-book "centaur/svl/top" :dir :system)
(include-book "centaur/sv/svex/lists" :dir :system)
(include-book "centaur/misc/sneaky-load" :dir :system)
(include-book "centaur/fgl/portcullis" :dir :system)

(include-book "heuristics")
(include-book "adder-patterns")
(include-book "macros")
(include-book "misc")
(include-book "quick-search")


(local
 (include-book "centaur/bitops/ihs-extensions" :dir :system))

(local
 (include-book "ihs/logops-lemmas" :dir :system))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (defthm svexlist-p-of-remove-duplicates
   (implies (sv::Svexlist-p x)
            (sv::Svexlist-p (remove-duplicates-equal x)))))

(local
 (in-theory (disable acl2::merge-sort-lexorder
                     acl2::merge-lexorder)))

(local
 (in-theory (e/d (acl2::maybe-integerp
                  sv::svex-kind)
                 ((:e tau-system)))))

(defines svex-has-bitxor-0
  (define svex-has-bitxor-0 ((x sv::svex-p))
    :measure (sv::svex-count x)
    (sv::Svex-case
     x
     :var nil
     :quote nil
     :call (case-match x
             (('sv::bitxor 0 &) t)
             (('sv::bitxor & 0) t)
             (& (svexlist-has-bitxor-0 x.args)))))
  (define svexlist-has-bitxor-0 ((lst sv::svexlist-p))
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        nil
      (or (svex-has-bitxor-0 (car lst))
          (svexlist-has-bitxor-0 (cdr lst)))))
  ///
  (memoize 'svex-has-bitxor-0))

(local
 ;; some more lemmas first.
 (defsection 4vec-lemmas

   (defthm 4vec-concat$-to-logapp
     (implies (and (natp size)
                   (integerp x)
                   (integerp y))
              (equal (svl::4vec-concat$ size x y)
                     (logapp size x y)))
     :hints (("goal"
              :in-theory (e/d (svl::4vec-concat$
                               svl::logapp-to-4vec-concat)
                              ()))))

   (defthm sv::4vec-bitops-to-logops
     (and (implies (and (integerp x)
                        (integerp y))
                   (and (equal (sv::4vec-bitxor x y)
                               (logxor x y))
                        (equal (sv::4vec-bitand x y)
                               (logand x y))
                        (equal (sv::4vec-bitor x y)
                               (logior x y))))
          (implies (integerp x)
                   (equal (sv::4vec-bitnot x)
                          (lognot x))))
     :hints (("goal"
              :do-not-induct t
              :in-theory (e/d* (sv::4vec
                                sv::4vec-bitand
                                sv::3vec-bitand
                                sv::3vec-bitor
                                sv::4vec-bitor
                                sv::3vec-bitnot
                                sv::4vec-bitnot
                                bitops::ihsext-inductions
                                bitops::ihsext-recursive-redefs
                                sv::4vec-bitxor
                                sv::4vec->lower
                                sv::4vec->upper
                                sv::4vec-rsh
                                sv::4vec-shift-core
                                svl::bits
                                sv::4vec-part-select
                                sv::4vec-concat)
                               (floor
                                svl::equal-of-4vec-concat-with-size=1
                                logand)))))

   (defthm sv::svexlist-eval$-when-consp
     (implies (consp lst)
              (equal (sv::svexlist-eval$ lst env)
                     (cons (sv::svex-eval$ (car lst) env)
                           (sv::svexlist-eval$ (cdr lst) env)))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defines collect-ha-args-under-gates
  ;; collects to a fast-alist. Keys are args in any order.
  :verify-guards nil
  (define collect-ha-args-under-gates ((svex sv::svex-p)
                                       (underadder booleanp)
                                       (undergate booleanp)
                                       (collected alistp)
                                       (parsed-svexes alistp))
    :measure (sv::Svex-count svex)
    :Returns (mv (res-collected alistp :hyp (alistp collected))
                 (res-parsed-svexes alistp :hyp (alistp parsed-svexes)))
    (sv::svex-case
     svex
     :quote (mv collected parsed-svexes)
     :var (mv collected parsed-svexes)
     :call (b* (;; what if parsed under different context? This may need to be improved...
                (parse-key (list* svex underadder undergate))
                (parsed? (hons-get parse-key parsed-svexes))
                ((when parsed?) (mv collected parsed-svexes))
                (adder-p (or (equal svex.fn 'fa-c-chain)
                             (equal svex.fn 'fa-s-chain)
                             (equal svex.fn 'ha-c-chain)
                             (equal svex.fn 'ha-s-chain)
                             (equal svex.fn 'ha+1-c-chain)
                             (equal svex.fn 'ha+1-s-chain)))

                (ha-undergate? (and ;;underadder
                                undergate
                                (or (equal svex.fn 'ha-c-chain)
                                    (equal svex.fn 'ha-s-chain)
                                    (equal svex.fn 'ha+1-c-chain)
                                    (equal svex.fn 'ha+1-s-chain))))

                (collected (if ha-undergate?
                               ;; arguments should be ordered beforehand so not
                               ;; putting the args only one way.
                               (hons-acons (if (equal svex.fn 'ha+1-s-chain) (cdr svex.args) svex.args)
                                           nil
                                           collected)
                             collected))

                (parsed-svexes (hons-acons parse-key nil parsed-svexes)))
             (collect-ha-args-under-gates-list svex.args
                                               (or adder-p
                                                   (and
                                                    ;; carry on underadder only
                                                    ;; through these gates.
                                                    underadder
                                                    #|(member-equal
                                                    svex.fn
                                                    (list 'sv::bitand
                                                    'sv::unfloat
                                                    'sv::id 'sv::?* 'sv::?
                                                    'sv::bitor
                                                    'sv::uor
                                                    'SV::uand
                                                    'sv::bitxor))|#))
                                               (or (equal svex.fn 'sv::bitand)
                                                   (equal svex.fn 'sv::bitor)
                                                   (equal svex.fn 'sv::uor)
                                                   (equal svex.fn 'sv::uand)
                                                   (and (or (equal svex.fn 'sv::unfloat)
                                                            (equal svex.fn 'sv::id))
                                                        undergate)
                                                   (and underadder
                                                        (equal svex.fn 'sv::bitxor)
                                                        (or undergate
                                                            ;; If it is undergate move it through
                                                            ;; when bitxor is used for negation.
                                                            (not (member-equal 1 svex.args)))))
                                               collected
                                               parsed-svexes))))
  (define collect-ha-args-under-gates-list ((svexlist sv::svexlist-p)
                                            (underadder booleanp)
                                            (undergate booleanp)
                                            (collected alistp)
                                            (parsed-svexes alistp))
    :measure (sv::svexlist-count svexlist)
    :Returns (mv (res-collected alistp :hyp (alistp collected))
                 (res-parsed-svexes alistp :hyp (alistp parsed-svexes)))
    (if (atom svexlist)
        (mv collected parsed-svexes)
      (b* (((mv collected parsed-svexes)
            (collect-ha-args-under-gates (car svexlist)
                                         underadder undergate
                                         collected parsed-svexes))
           ((mv collected parsed-svexes)
            (collect-ha-args-under-gates-list (cdr svexlist)
                                              underadder undergate
                                              collected parsed-svexes)))
        (mv collected parsed-svexes))))
  ///
  (verify-guards collect-ha-args-under-gates)

  (define collect-ha-args-under-gates-alist ((x sv::svex-alist-p)
                                             &key
                                             ((collected alistp) 'nil)
                                             ((parsed-svexes alistp) 'nil))
    :Returns (mv (res-collected alistp :hyp (alistp collected))
                 (res-parsed-svexes alistp :hyp (alistp parsed-svexes)))
    (if (atom x)
        (mv (fast-alist-clean collected)
            (fast-alist-free parsed-svexes))
      (b* (((mv collected parsed-svexes)
            (collect-ha-args-under-gates (cdar x)
                                         nil nil
                                         collected parsed-svexes))
           ((mv collected parsed-svexes)
            (collect-ha-args-under-gates-alist (cdr x)
                                               :collected collected
                                               :parsed-svexes parsed-svexes)))
        (mv collected parsed-svexes)))))

(define shuffle-gates-after-removing-ha-under-gates ((svex.fn sv::fnsym-p)
                                                     (svex.args sv::svexlist-p)
                                                     (orig-svex.args sv::svexlist-p))

  ;; After an  half-adder is removed,  this function makes a  slight shuffle so  that we
  ;; don't match the exact same adder right away and possibly let other variations to be matched

  :prepwork ((local
              (in-theory (disable subsetp-equal
                                  member-equal
                                  symbol-listp
                                  default-car))))

  :returns (res-svex sv::svex-p :hyp (and (sv::fnsym-p svex.fn)
                                          (sv::svexlist-p svex.args))
                     :hints (("Goal"
                              :expand ((sv::svex-kind (car svex.args))
                                       (sv::svex-kind (cadr svex.args)))
                              :in-theory (e/d () (sv::svex-kind$inline)))))
  :guard-debug t
  :guard-hints (("Goal"
                 :expand ((sv::svex-kind (car svex.args))
                          (sv::svex-kind (cadr svex.args)))
                 :in-theory (e/d (and*
                                  SVL::EQUAL-LEN)
                                 (sv::svex-kind$inline))))

  (b* (((unless (or (equal svex.fn 'sv::bitxor)
                    (equal svex.fn 'sv::bitand)))
        (sv::Svex-call svex.fn svex.args))
       (no-orig (not orig-svex.args))
       ((unless (and*-exec (svl::equal-len svex.args 2)
                           (or no-orig
                               (svl::equal-len orig-svex.args 2))))
        (sv::Svex-call svex.fn svex.args))
       ((mv x1 x2) (mv (first svex.args) (second svex.args)))

       ((mv o1 o2) (mv (or no-orig (first orig-svex.args))
                       (or no-orig (second orig-svex.args))))

       ((list x1.fn x1.args) (and*-exec (equal (sv::svex-kind x1) :call)
                                        (list (sv::svex-call->fn x1)
                                              (sv::svex-call->args x1))))
       ((list x2.fn x2.args) (and*-exec (equal (sv::svex-kind x2) :call)
                                        (list (sv::svex-call->fn x2)
                                              (sv::svex-call->args x2))))
       (o1.fn (and*-exec orig-svex.args
                         (equal (sv::svex-kind o1) :call)
                         (sv::svex-call->fn o1)))
       (o2.fn (and*-exec orig-svex.args
                         (equal (sv::svex-kind o2) :call)
                         (sv::svex-call->fn o2)))

       ((when (or no-orig
                  (and*-exec (equal x1.fn o1.fn)
                             (equal x2.fn o2.fn))))
        (sv::Svex-call svex.fn svex.args)))
    (cond ((and*-exec (or no-orig (not (equal x1.fn o1.fn)))
                      (equal x1.fn svex.fn)
                      (svl::equal-len x1.args 2))
           (sv::Svex-call svex.fn
                          (hons-list (first x1.args)
                                     (sv::Svex-call svex.fn
                                                    (hons-list (second x1.args)
                                                               x2)))))
          ((and*-exec (or no-orig (not (equal x2.fn o2.fn)))
                      (equal x2.fn svex.fn)
                      (svl::equal-len x2.args 2))
           (sv::Svex-call svex.fn
                          (hons-list (sv::Svex-call svex.fn
                                                    (hons-list (second x2.args)
                                                               x1))
                                     (first x2.args))))
          (t  (sv::Svex-call svex.fn svex.args))))

  ///

  (defret <fn>-is-correct
    (implies t
             (equal (sv::Svex-eval$ res-svex env)
                    (sv::Svex-eval$ (sv::Svex-call svex.fn svex.args) env)))
    :fn shuffle-gates-after-removing-ha-under-gates
    :hints (("Goal"
             :expand ((sv::svex-kind (car svex.args))
                      (sv::svex-kind (cadr svex.args)))
             :in-theory (e/d (sv::svex-apply)
                             (sv::svex-kind$inline))))))

;; (shuffle-gates-after-removing-ha-under-gates 'sv::bitand
;;                                              (list 'z '(sv::bitand x y))
;;                                              (list 'z '(ha-c-chain x y)))

(defines remove-ha-under-gates
  :verify-guards nil
  :hints (("Goal"
           :in-theory (e/d (sv::SVEX-COUNT
                            SV::SVEX-CALL->FN
                            SV::SVEX-CALL->args)
                           ())))

  (define remove-ha-under-gates ((svex sv::Svex-p)
                                 &key
                                 ((wrap-with-id booleanp) 'wrap-with-id)
                                 ((collected alistp) 'collected))
    :measure (sv::svex-count svex)
    :Returns (res-svex sv::svex-p :hyp (sv::svex-p svex))

    (sv::svex-case
     svex
     :var svex
     :quote svex
     :call
     (b* ((adder-p (or (equal svex.fn 'ha-c-chain)
                       (equal svex.fn 'ha-s-chain)
                       (equal svex.fn 'ha+1-c-chain)
                       (equal svex.fn 'ha+1-s-chain)))
          (to-remove (and adder-p
                          (if (equal svex.fn 'ha+1-s-chain)
                              (hons-get (cdr svex.args) collected)
                            (hons-get svex.args collected))))
          ((unless to-remove)

           (shuffle-gates-after-removing-ha-under-gates
            svex.fn
            (remove-ha-under-gates-lst svex.args)
            svex.args)

           #|(sv::Svex-call svex.fn
           (remove-ha-under-gates-lst svex.args))|#)
          (res
           (cond
            ((ha-c-chain-self-pattern-p svex)
             (ha-c-chain-self-pattern-body
              svex
              (shuffle-gates-after-removing-ha-under-gates
               'sv::bitand
               (hons-list (remove-ha-under-gates x)
                          (remove-ha-under-gates y))
               nil)))
            ((ha-s-chain-self-pattern-p svex)
             (ha-s-chain-self-pattern-body
              svex
              (shuffle-gates-after-removing-ha-under-gates
               'sv::bitxor
               (hons-list (remove-ha-under-gates x)
                          (remove-ha-under-gates y))
               nil)))
            ((ha+1-s-chain-self-pattern-p svex)
             (ha+1-s-chain-self-pattern-body
              svex
              (cond
               ((equal m 0)
                (sv::Svex-call
                 'sv::bitnot
                 (hons-list
                  (sv::svex-call 'sv::bitxor
                                 (hons-list (remove-ha-under-gates x)
                                            (remove-ha-under-gates y))))))
               ((equal m 1)
                (sv::Svex-call
                 'sv::bitxor
                 (hons-list
                  1
                  (sv::svex-call 'sv::bitxor
                                 (hons-list (remove-ha-under-gates x)
                                            (remove-ha-under-gates y))))))
               ((equal m 10)
                (sv::svex-call 'sv::bitxor
                               (hons-list (remove-ha-under-gates x)
                                          (remove-ha-under-gates y))))
               (t
                (sv::Svex-call svex.fn
                               (remove-ha-under-gates-lst svex.args))))))
            ((ha+1-c-chain-self-pattern-p svex)
             (ha+1-c-chain-self-pattern-body
              svex
              (sv::Svex-call 'sv::bitor (hons-list (remove-ha-under-gates x)
                                                   (remove-ha-under-gates y)))))
            (t (sv::Svex-call svex.fn
                              (remove-ha-under-gates-lst svex.args)) ;; should never come here..
               )))
          (res (if wrap-with-id (sv::svex-call 'sv::id (hons-list res)) res)))
       res)))

  (define remove-ha-under-gates-lst ((lst sv::svexlist-p)
                                     &key
                                     ((wrap-with-id booleanp) 'wrap-with-id)
                                     ((collected alistp) 'collected))
    :measure (sv::svexlist-count lst)
    :Returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
    (if (atom lst)
        nil
      (hons (remove-ha-under-gates (car lst))
            (remove-ha-under-gates-lst (cdr lst)))))
  ///

  (verify-guards remove-ha-under-gates-lst-fn
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d () ()))))

  (memoize 'remove-ha-under-gates
           ;; :condition '(eq (sv::svex-kind svex) :call)
           )

  (defret-mutual correctness
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::Svex-eval$ res-svex env)
                      (sv::Svex-eval$ svex env)))
      :fn remove-ha-under-gates)
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::Svexlist-eval$ res-lst env)
                      (sv::Svexlist-eval$ lst env)))
      :fn remove-ha-under-gates-lst)
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (sv::svex-apply$
                              sv::svex-apply
                              sv::svex-call->fn
                              ha-c-chain
                              ha-s-chain
                              sv::svex-call->args
                              ha+1-s-chain
                              ha+1-c-chain)
                             ()))))

  (define remove-ha-under-gates-alist ((lst sv::svex-alist-p)
                                       &key
                                       ((wrap-with-id booleanp) 'wrap-with-id)
                                       ((collected alistp) 'collected))
    :Returns (res sv::svex-alist-p :hyp (sv::svex-alist-p lst))
    (if (atom lst)
        nil
      (acons (caar lst)
             (remove-ha-under-gates (cdar lst))
             (remove-ha-under-gates-alist (cdr lst))))
    ///
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::Svex-alist-eval$ res env)
                      (sv::Svex-alist-eval$ lst env)))
      :hints (("Goal"
               :expand ((sv::svex-alist-eval nil env))
               :in-theory (e/d (sv::svex-alist-eval$) ()))))))

(define remove-ha-pairs-under-gates-alist ((svex-alist sv::svex-alist-p)
                                           &key
                                           ((wrap-with-id booleanp) 'nil))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
  (b* ((- (cw "--- Now removing misidentified half-adders.~%"))
       ((mv collected &)
        (collect-ha-args-under-gates-alist svex-alist))
       (found-num (len collected))
       ((when (equal found-num 0))
        (progn$ (cw "- Could not find any misidentified half-adder.~%")
                (fast-alist-free collected)
                svex-alist))
       (- (cw "- Removing ~p0 half-adders that are suspected to be misidentified.~%" found-num))
       (svex-alist (remove-ha-under-gates-alist svex-alist))
       (- (fast-alist-free collected)))
    svex-alist)
  ///
  (defret <fn>-is-correct
    (implies (warrants-for-adder-pattern-match)
             (equal (sv::svex-alist-eval$ res env)
                    (sv::svex-alist-eval$ svex-alist env)))
    :hints (("goal"
             :do-not-induct t
             :in-theory (e/d ()
                             ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Remove unpaired fa-s

;; gather-adder-patterns-in-svex-alist adder-type='fa-self

(local
 (in-theory (enable SV::SVEX-QUOTE->VAL)))

(define remove-unpaired-fa-s---clean-pattern-alist ((pattern-alist pattern-alist-p)
                                                    (acc pattern-alist-p))
  :returns (res pattern-alist-p :hyp (and (pattern-alist-p acc)
                                          (pattern-alist-p pattern-alist)))
  (if (atom pattern-alist)
      acc
    (b* (((cons key value) (car pattern-alist))
         ((when (equal value '(fa-s-chain)))
          (remove-unpaired-fa-s---clean-pattern-alist
           (cdr pattern-alist)
           (hons-acons key value acc))))
      (remove-unpaired-fa-s---clean-pattern-alist (cdr pattern-alist)
                                                  acc))))

(defines remove-unpaired-fa-s-aux
  :hints (("Goal"
           :expand ((SV::SVEX-COUNT SVEX)
                    (SV::SVEX-COUNT (LIST 'FA-S-CHAIN SVEX3 SVEX5 SVEX7)))
           :in-theory (e/d (SV::SVEX-CALL->ARGS
                            FA-S-CHAIN-ITSELF-PATTERN-P)
                           ())))
  :verify-guards nil
  (define remove-unpaired-fa-s-aux ((svex sv::svex-p)
                                    &optional
                                    ((pattern-alist pattern-alist-p) 'pattern-alist))
    :returns (res sv::Svex-p :hyp (sv::svex-p svex))
    :measure (sv::Svex-count svex)
    (sv::Svex-case
     svex
     :var svex
     :quote svex
     :call (cond ((fa-s-chain-itself-pattern-p svex)
                  (fa-s-chain-itself-pattern-body
                   svex
                   (b* ((args (acl2::merge-sort-lexorder (list x y z)))
                        (found (hons-get args pattern-alist))
                        ((when found)
                         (hons-list 'sv::bitxor (remove-unpaired-fa-s-aux x)
                                    (hons-list 'sv::bitxor
                                               (remove-unpaired-fa-s-aux y)
                                               (remove-unpaired-fa-s-aux z)))))
                     (sv::svex-call svex.fn
                                    (remove-unpaired-fa-s-aux-lst svex.args)))))
                 (t (sv::svex-call svex.fn
                                   (remove-unpaired-fa-s-aux-lst svex.args))))))
  (define remove-unpaired-fa-s-aux-lst ((lst sv::svexlist-p)
                                        &optional
                                        ((pattern-alist pattern-alist-p) 'pattern-alist))
    :measure (sv::Svexlist-count lst)
    :returns (res sv::Svexlist-p :hyp (sv::svexlist-p lst))
    (if (atom lst)
        nil
      (hons (remove-unpaired-fa-s-aux (car lst))
            (remove-unpaired-fa-s-aux-lst (cdr lst)))))
  ///
  (verify-guards remove-unpaired-fa-s-aux-fn)
  (memoize 'remove-unpaired-fa-s-aux-fn
           ;; :condition '(eq (sv::svex-kind svex) :call)
           )

  (defret-mutual correctness
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::svex-eval$ res env)
                      (sv::svex-eval$ svex env)))
      :fn remove-unpaired-fa-s-aux)
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::svexlist-eval$ res env)
                      (sv::svexlist-eval$ lst env)))
      :fn remove-unpaired-fa-s-aux-lst)
    :hints (("Goal"
             :do-not-induct t
             :expand ((:free (args)
                             (sv::Svex-apply$ 'fa-s-chain args))
                      (:free (args)
                             (sv::Svex-apply 'SV::BItXOR args)))
             :in-theory (e/d (;;SV::SVEX-APPLY$
                              fa-s-chain
                              SV::SVEX-CALL->FN
                              SV::SVEX-CALL->args)
                             ())))))

(define remove-unpaired-fa-s-alist-aux ((x sv::svex-alist-p)
                                        &optional
                                        ((pattern-alist pattern-alist-p) 'pattern-alist))
  :returns (res sv::Svex-alist-p :hyp (sv::svex-alist-p x))
  (if (atom x)
      x
    (acons (caar x)
           (remove-unpaired-fa-s-aux (cdar x))
           (remove-unpaired-fa-s-alist-aux (cdr x))))
  ///
  (defret <fn>-is-correct
    (implies (warrants-for-adder-pattern-match)
             (equal (sv::svex-alist-eval$ res env)
                    (sv::svex-alist-eval$ x env)))
    :hints (("goal"
             :in-theory (e/d (SV::SVEX-ALIST-EVAL$)
                             ())))))

(define remove-unpaired-fa-s-alist ((svex-alist sv::svex-alist-p)
                                    &key
                                    ((env) 'env)
                                    ((context rp-term-listp) 'context)
                                    ((config svl::svex-reduce-config-p) 'config))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
  :guard-debug t
  (b* ((- (cw "--- Now looking for unpaired full-adder-s~%"))
       ((mv pattern-alist &)
        (gather-adder-patterns-in-svex-alist svex-alist :adder-type 'fa-self :track-column? nil))
       (pattern-alist (fast-alist-clean pattern-alist))
       (pattern-alist (fast-alist-free pattern-alist))
       (pattern-alist (remove-unpaired-fa-s---clean-pattern-alist pattern-alist
                                                                  'remove-unpaired-fa-s---clean-pattern-alist))
       (found-num (len pattern-alist))
       ((when (equal found-num 0))
        (progn$ (cw "- Could not find any unpaired full-adder.~%")
                (fast-alist-free pattern-alist)
                svex-alist))
       (- (cw "- Removing ~p0 unpaired full-adder-s patterns.~%" found-num))

       (svex-alist (remove-unpaired-fa-s-alist-aux svex-alist pattern-alist))

       (- (fast-alist-free pattern-alist)))
    svex-alist)
  ///
  (defret <fn>-is-correct
    (implies (warrants-for-adder-pattern-match)
             (equal (sv::svex-alist-eval$ res free-env)
                    (sv::svex-alist-eval$ svex-alist free-env)))
    :hints (("goal"
             :do-not-induct t
             :in-theory (e/d ()
                             ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines merge-fa-s-c-chains
  :verify-guards nil

  (define merge-fa-s-c-chains ((x sv::svex-p)
                               &key
                               ((env) 'env)
                               ((context rp::rp-term-listp) 'context)
                               ((config svl::svex-reduce-config-p) 'config))

    :returns (res-svex sv::svex-p :hyp (sv::svex-p x))
    :measure (sv::Svex-count x)
    (sv::Svex-case
     x
     :var x
     :quote x
     :call (b* ((args (merge-fa-s-c-chains-lst x.args)))
             (cond ((and (eq x.fn 'fa-s-chain)
                         (svl::equal-len x.args 3)
                         (and* (svl::bitp-of-svex (first x.args))
                               (svl::bitp-of-svex (second x.args))
                               (svl::bitp-of-svex (third x.args))))
                    (sv::svex-call 'sv::partsel
                                   (hons-list 0 1
                                              (sv::svex-call 'full-adder args))))
                   ((and (eq x.fn 'fa-c-chain)
                         (svl::equal-len x.args 4)
                         (and* (valid-fa-c-chain-args-p (first x.args)
                                                        (second x.args))
                               (svl::bitp-of-svex (second x.args))
                               (svl::bitp-of-svex (third x.args))
                               (svl::bitp-of-svex (fourth x.args))))
                    (sv::svex-call 'sv::partsel
                                   (hons-list 1 1
                                              (sv::svex-call 'full-adder (cdr args)))))

                   ((and (eq x.fn 'ha-s-chain)
                         (svl::equal-len x.args 2)
                         (and* (svl::bitp-of-svex (first x.args))
                               (svl::bitp-of-svex (second x.args))))
                    (sv::svex-call 'sv::partsel
                                   (hons-list 0 1
                                              (sv::svex-call 'half-adder args))))
                   ((and (eq x.fn 'ha-c-chain)
                         (svl::equal-len x.args 2)
                         (and* (svl::bitp-of-svex (first x.args))
                               (svl::bitp-of-svex (second x.args))))
                    (sv::svex-call 'sv::partsel
                                   (hons-list 1 1
                                              (sv::svex-call 'half-adder args))))

                   ((and (eq x.fn 'ha+1-s-chain)
                         (svl::equal-len x.args 3)
                         (and* (integerp (first x.args))
                               (not (equal (first x.args) 0))  ;; the 0 case is
                               ;; defined   with
                               ;; bitnot. Expected
                               ;; to  never  use
                               ;; that.
                               (svl::bitp-of-svex (second x.args))
                               (svl::bitp-of-svex (third x.args))))
                    (b* ((base (sv::svex-call 'sv::partsel
                                              (hons-list 0 1
                                                         (sv::svex-call 'full-adder
                                                                        (hons 1 (cdr args)))))))
                      (if (equal (first x.args) 10) ;; when this is 10, it means it was matched with carry+1
                          (sv::Svex-call 'sv::bitxor (hons-list 1 base))
                        base)))
                   ((and (eq x.fn 'ha+1-c-chain)
                         (svl::equal-len x.args 2)
                         (and* (svl::bitp-of-svex (first x.args))
                               (svl::bitp-of-svex (second x.args))))
                    (sv::svex-call 'sv::partsel
                                   (hons-list 1 1
                                              (sv::svex-call 'full-adder (hons 1 args)))))

                   (t (sv::svex-call x.fn args))))))

  (define merge-fa-s-c-chains-lst ((lst sv::svexlist-p)
                                   &key
                                   ((env) 'env)
                                   ((context rp::rp-term-listp) 'context)
                                   ((config svl::svex-reduce-config-p) 'config))
    :returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
    :measure (sv::Svexlist-count lst)
    (if (atom lst)
        nil
      (hons (merge-fa-s-c-chains (car lst))
            (merge-fa-s-c-chains-lst (cdr lst)))))
  ///

  (verify-guards merge-fa-s-c-chains-fn)

  (memoize 'merge-fa-s-c-chains
           ;; :condition '(eq (sv::svex-kind x) :call)
           )

  (local
   (defthm sv::4vec-part-select-of-fa-chains/s-c-spec-lemma
     (implies (and (bitp x) (bitp y) (bitp z))
              (and (equal (sv::4vec-part-select 0 1 (fa-c-chain 0 x y z))
                          (fa-c-chain 0 x y z))
                   (equal (sv::4vec-part-select 0 1 (c-spec (list x y z)))
                          (c-spec (list x y z)))
                   (equal (sv::4vec-part-select 0 1 (s-spec (list x y z)))
                          (s-spec (list x y z)))))
     :hints (("Goal"
              :in-theory (e/d (bitp
                               FA-C-CHAIN)
                              ())))))

  (local
   (defthm sv::4vec-part-select-of-fa-chains/s-c-spec-lemma-2
     (implies (and (bitp x) (bitp y))
              (and (equal (sv::4vec-part-select 0 1 (c-spec (list x y)))
                          (c-spec (list x y)))
                   (equal (sv::4vec-part-select 0 1 (s-spec (list x y)))
                          (s-spec (list x y)))))
     :hints (("Goal"
              :in-theory (e/d (bitp
                               FA-C-CHAIN)
                              ())))))

  (local
   (defthm ha+1-s-chain-to-s-spec-lemma
     (implies (and (bitp x) (bitp y) (not (equal m 0)))
              (and (equal (ha+1-s-chain m x y)
                          (if (equal m 10)
                              (s-spec (list x y))
                            (s-spec (list 1 x y))))))
     :hints (("Goal"
              :in-theory (e/d (BITP ha+1-s-chain)
                              ())))))

  (local
   (defthm negate-of-s-spec-with-1
     (implies (and (bitp x)
                   (bitp y))
              (equal (LOGXOR 1 (S-SPEC (LIST 1 x y)))
                     (S-SPEC (LIST x y))))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthm s/c-spec-move-consts
     (and (equal (c-spec (list x y 1))
                 (c-spec (list 1 x y)))
          (equal (s-spec (list x y 1))
                 (s-spec (list 1 x y)))

          (equal (s-spec (list 0 x y))
                 (s-spec (list x y)))
          (equal (c-spec (list 0 x y))
                 (c-spec (list x y))))
     :hints (("Goal"
              :in-theory (e/d (c-spec s-spec SUM-LIST sum) ())))))

  (local
   (in-theory (disable svl::width-of-svex-extn-correct$-lst
                       svl::width-of-svex-extn-correct$
                       ;;svexlist-p-implies-true-listp
                       (:rewrite acl2::apply$-badgep-properties . 1)
                       (:definition pattern-alist-p)
                       (:definition integer-listp)
                       member-equal
                       DEFAULT-CDR
                       DEFAULT-CAR
                       RP-TRANS)))

  (defret-mutual <fn>-is-correct
    (defret <fn>-is-correct
      (implies (and (sv::svex-p x)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (warrants-for-adder-pattern-match))
               (equal (sv::svex-eval$ res-svex (rp-evlt env-term a))
                      (sv::svex-eval$ x (rp-evlt env-term a))))
      :fn merge-fa-s-c-chains)
    (defret <fn>-is-correct
      (implies (and (sv::svexlist-p lst)
                    (warrants-for-adder-pattern-match)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    )
               (equal (sv::svexlist-eval$ res-lst (rp-evlt env-term a))
                      (sv::svexlist-eval$ lst (rp-evlt env-term a))))
      :fn merge-fa-s-c-chains-lst)
    :hints (("Goal"
             :do-not-induct t
             :expand ((merge-fa-s-c-chains x)
                      (merge-fa-s-c-chains-lst lst))
             :in-theory (e/d (SVL::LOGAPP-TO-4VEC-CONCAT
                              S-C-SPEC
                              SVL::4VEC-CONCAT$
                              SV::SVEXLIST-EVAL$
                              SV::SVEX-APPLY
                              sv::svex-apply$
                              full-adder half-adder)
                             ()))))

  (define merge-fa-s-c-chains-alist ((alist sv::svex-alist-p)
                                     &key
                                     ((env) 'env)
                                     ((context rp::rp-term-listp) 'context)
                                     ((config svl::svex-reduce-config-p) 'config))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
    (if (atom alist)
        nil
      (acons (caar alist)
             (merge-fa-s-c-chains (cdar alist))
             (merge-fa-s-c-chains-alist (cdr alist))))
    ///
    (defret <fn>-is-correct
      (implies (and (sv::svex-alist-p alist)
                    (warrants-for-adder-pattern-match)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config)))
               (equal (sv::svex-alist-eval$ res (rp-evlt env-term a))
                      (sv::svex-alist-eval$ alist (rp-evlt env-term a))))
      :hints (("goal"
               :do-not-induct t
               :induct (merge-fa-s-c-chains-alist alist)
               :in-theory (e/d (sv::svex-alist-eval$)
                               (merge-fa-s-c-chains))))))

  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define missed-adder-warning--adder-p (term
                                       nodes
                                       (limit natp))
  :measure (nfix limit)
  (if (zp limit)
      nil
    (case-match term
      (('sv::Bitxor 1 x)
       (missed-adder-warning--adder-p x nodes (1- limit)))
      (('id x)
       (missed-adder-warning--adder-p x nodes (1- limit)))
      (('sv::Bitxor x 1)
       (missed-adder-warning--adder-p x nodes (1- limit)))
      ((':node num)
       (b* ((x (hons-get num nodes)))
         (and (consp x)
              (missed-adder-warning--adder-p (cdr x) nodes (1- limit)))))
      ((fn . &)
       (or (equal fn 'fa-c-chain)
           (equal fn 'fa-s-chain)
           (equal fn 'full-adder)
           (equal fn 'half-adder)
           (equal fn 'ha-s-chain)
           (equal fn 'ha-c-chain)
           (equal fn 'ha+1-s-chain)
           (equal fn 'ha+1-c-chain))))))

(defines missed-adder-warning--traverse-node
  (define missed-adder-warning--traverse-node (node-term
                                               node-num
                                               nodes
                                               under-gate
                                               (limit natp))
    (b* (((when (zp limit))
          nil)
         (found (and under-gate
                     (missed-adder-warning--adder-p node-term nodes *large-number*)
                     (Not
                      (cwe "(:node ~p0). Node-term: ~p1 under ~p2.~%"
                           node-num node-term under-gate))))
         ((Unless (and (equal (svl::svexl-node-kind-wog node-term) :call)
                       (consp node-term)))
          found)
         (under-gate (or (and (equal (car node-term) 'sv::bitor) 'sv::bitor)
                         (and (equal (car node-term) 'sv::bitand) 'sv::bitand)
                         (and* (equal (car node-term) 'sv::bitxor)
                               (not (equal (nth 1 (true-list-fix node-term)) 1))
                               (not (equal (nth 2 (true-list-fix node-term)) 1))
                               'sv::bitxor)
                         (and (equal (car node-term) 'sv::partsel) under-gate))))
      (or*
       (missed-adder-warning--traverse-node-lst (cdr node-term)
                                                node-num
                                                nodes
                                                under-gate
                                                (1- limit))
       found)))

  (define missed-adder-warning--traverse-node-lst (node-lst
                                                   node-num
                                                   nodes
                                                   under-gate
                                                   (limit natp))
    (if (or (zp limit)
            (atom node-lst))
        nil
      (or* (missed-adder-warning--traverse-node (car node-lst)
                                                node-num
                                                nodes
                                                under-gate
                                                (1- limit))
           (missed-adder-warning--traverse-node-lst (cdr node-lst)
                                                    node-num
                                                    nodes
                                                    under-gate
                                                    (1- limit))))))

(define missed-adder-warning--iter ((term-alist alistp)
                                    nodes)
  (if (atom term-alist)
      nil
    (b* ((node-num (caar term-alist))
         (node-term (cdar term-alist)))
      (or* (missed-adder-warning--traverse-node node-term
                                                node-num
                                                nodes
                                                nil
                                                *large-number*)
           (missed-adder-warning--iter (cdr term-alist) nodes)))))

;;(include-book "books/centaur/misc/hons-extra" :dir :system)

(define missed-adder-warning ((svexl-alist svl::svexl-alist-p))
  (b* (((svl::svexl-alist x) svexl-alist)
       (x.node-array (make-fast-alist x.node-array)) ;;((with-fast x.node-array))
       ((Unless (and (alistp x.top-node-alist) ;; for guards
                     (alistp x.node-array)))
        nil)

       (- (cw "- Checking if any adders are nested in other gates...~%"))

       (found1 (missed-adder-warning--iter x.top-node-alist
                                           x.node-array))
       (found2 (missed-adder-warning--iter x.node-array
                                           x.node-array))

       (- (if (or found1 found2)
              (cw "- Some adders are nested within or/and/xor gates. This may cause problems...~%")
            (cw "-> Could not find any adders nested within gates. That's good.~%")))
       )
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Try to add ha-c-chain for shifted outputs

(defines add-ha-c-for-shifted-search
  :verify-guards nil
  (define add-ha-c-for-shifted-search ((x sv::svex-p)
                                       (under-adder))
    :returns (mv (collected true-listp)
                 (good-args integerp))
    :measure (sv::Svex-count x)
    (sv::svex-case
     x
     :var (mv nil 1)
     :quote (mv nil 1)
     :call
     (cond ((or* (equal x.fn 'ha-c-chain)
                 (equal x.fn 'ha-s-chain)
                 (equal x.fn 'fa-c-chain)
                 (equal x.fn 'fa-s-chain)
                 (equal x.fn 'ha+1-s-chain)
                 (equal x.fn 'ha+1-c-chain))
            (b* (((mv collected &)
                  (add-ha-c-for-shifted-search-lst x.args t)))
              (mv collected 3)))
           ((and* (svl::equal-len x.args 2)
                  (equal x.fn 'sv::bitand))
            (b* (((mv collected good-args)
                  (add-ha-c-for-shifted-search-lst x.args under-adder))
                 ((when (and under-adder
                             (equal good-args 3)))
                  (mv (cons x collected) 3)))
              (mv collected 0)))
           ((or* (equal x.fn 'sv::?*)
                 (equal x.fn 'sv::?))
            (mv nil 3))
           (t (add-ha-c-for-shifted-search-lst x.args nil)))))

  (define add-ha-c-for-shifted-search-lst ((lst sv::Svexlist-p)
                                           (under-adder))
    :returns (mv (collected true-listp)
                 (good-args integerp))
    :measure (sv::Svexlist-count lst)
    (if (atom lst)
        (mv nil 0)
      (b* (((mv c1 g1) (add-ha-c-for-shifted-search (car lst)
                                                    under-adder))
           ((mv c2 g2) (add-ha-c-for-shifted-search-lst (cdr lst)
                                                        under-adder)))
        (mv (append c1 c2)
            (logior g1 g2)))))
  ///
  (verify-guards add-ha-c-for-shifted-search)
  (memoize 'add-ha-c-for-shifted-search
           ;; :condition '(eq (sv::svex-kind x) :call)
           )
  ;; no need to verify anything.

  (define add-ha-c-for-shifted-search-main ((x sv::svex-p))
    :Returns (collected-lst true-listp)
    (case-match x
      (('sv::concat size a b)
       (cond ((not (natp size))
              nil)
             ((= size 1)
              (b* (((mv c &)
                    (add-ha-c-for-shifted-search a nil)))
                ;; ((Unless c) nil)
                ;; (c (make-fast-alist (pairlis$ c nil)))
                ;; (c (fast-alist-clean c)))
                c))
             ((> size 1)
              (add-ha-c-for-shifted-search-main a))
             (t
              (add-ha-c-for-shifted-search-main b))))
      (& (b* (((mv c &)
               (add-ha-c-for-shifted-search x nil)))
           c))))

  (define add-ha-c-for-shifted-search-alist ((x sv::svex-alist-p))
    :Returns (collected-lst true-listp)
    (if (atom x)
        nil
      (append (add-ha-c-for-shifted-search-main (cdar x))
              (add-ha-c-for-shifted-search-alist (cdr x))))))

(defines add-ha-c-for-shifted
  :verify-guards nil
  (define add-ha-c-for-shifted  ((x sv::svex-p)
                                 (collected))
    :returns (res-svex sv::svex-p :hyp (sv::svex-p x))
    :measure (sv::Svex-count x)
    (sv::svex-case
     x
     :var x
     :quote x
     :call
     (cond ((and*-exec
             (equal x.fn 'sv::bitand)
             (svl::equal-len x.args 2)
             (hons-get x collected))
            (sv::Svex-call 'ha-c-chain
                           (add-ha-c-for-shifted-lst x.args collected)))
           (t (sv::Svex-call x.fn
                             (add-ha-c-for-shifted-lst x.args collected))))))

  (define add-ha-c-for-shifted-lst ((lst sv::Svexlist-p)
                                    (collected))
    :returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
    :measure (sv::Svexlist-count lst)
    (if (atom lst)
        nil
      (hons (add-ha-c-for-shifted (car lst) collected)
            (add-ha-c-for-shifted-lst (cdr lst) collected))))
  ///
  (verify-guards add-ha-c-for-shifted)
  (memoize 'add-ha-c-for-shifted
           ;; :condition '(eq (sv::svex-kind x) :call)
           )

  (defret-mutual <fn>-is-correct
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::svex-eval$ res-svex env)
                      (sv::svex-eval$ x env)))
      :fn add-ha-c-for-shifted)
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::svexlist-eval$ res-lst env)
                      (sv::svexlist-eval$ lst env)))
      :fn add-ha-c-for-shifted-lst)
    :hints (("Goal"
             :do-not-induct t
             :expand ()
             :in-theory (e/d (sv::svex-apply$
                              sv::svex-apply
                              ha-c-chain)
                             ()))))

  (define add-ha-c-for-shifted-alist ((x sv::Svex-alist-p)
                                      (collected))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p x))
    (if (atom x)
        nil
      (acons (caar x)
             (add-ha-c-for-shifted (cdar x) collected)
             (add-ha-c-for-shifted-alist (cdr x) collected)))
    ///
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::svex-alist-eval$ res env)
                      (sv::svex-alist-eval$ x env)))
      :hints (("Goal"
               :in-theory (e/d (sv::svex-alist-eval$
                                sv::svex-alist-eval)
                               ()))))))

(define search-and-add-ha-c-for-shifted ((x sv::Svex-alist-p))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p x))
  :prepwork
  ()

  (b* (((unless (search-and-add-ha-c-for-shifted-enabled))
        x)
       (collected-lst (add-ha-c-for-shifted-search-alist x))
       ((Unless collected-lst) x)
       (c (make-fast-alist (pairlis$ collected-lst nil)))
       (c (fast-alist-clean c))
       (- (and c
               (cw "- Marking ~p0 half-adder carry patterns that are suspected to ~
        come from a shifted data output result. If the proof fails and this is ~
        not a shifted multiplier/adder, then try disabling this heuristic by ~
        calling: ~p1~%~%" (len c) '(enable-search-and-add-ha-c-for-shifted
                                    nil))))
       ((Unless c) x)
       (x (add-ha-c-for-shifted-alist x c))
       (- (fast-alist-free c)))
    x)
  ///
  (defret <fn>-is-correct
    (implies (warrants-for-adder-pattern-match)
             (equal (sv::svex-alist-eval$ res env)
                    (sv::svex-alist-eval$ x env)))
    :hints (("Goal"
             :in-theory (e/d (sv::svex-alist-eval$
                              sv::svex-alist-eval)
                             ())))))



(defines adders-under-gates?
  (define adders-under-gates? ((x sv::Svex-p)
                               (under-gate?))
    :measure (sv::Svex-count x)
    (sv::svex-case
     x
     :var nil
     :quote nil
     :call
     (b* ((under-gate? (or under-gate?
                           (equal x.fn 'sv::bitand)
                           (equal x.fn 'sv::bitor)))
          ((when (and under-gate?
                      (member-eq x.fn '(fa-c-chain fa-s-chain
                                                   ha-s-chain ha-c-chain
                                                   ha+1-s-chain ha+1-c-chain
                                                   +))))
           t))
       (adders-under-gates?-lst x.args under-gate?))))

  (define adders-under-gates?-lst ((lst sv::Svexlist-p)
                                   (under-gate?))
    :measure (sv::Svexlist-count lst)
    (if (atom lst)
        nil
      (or (adders-under-gates? (car lst) under-gate?)
          (adders-under-gates?-lst (cdr lst) under-gate?))))
  ///
  (memoize 'adders-under-gates?)
  (define adders-under-gates?-alist ((alist sv::svex-alist-p))
    (if (atom alist)
        (progn$ (clear-memoize-table 'adders-under-gates?)
                nil)
      (or (adders-under-gates? (cdar alist) nil)
          (adders-under-gates?-alist (cdr alist))))))
