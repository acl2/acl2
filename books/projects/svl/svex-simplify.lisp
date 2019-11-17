; SVL - Listener-based Hierachical Verilog Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

;; A tool to apply existing rewrite rules about 4vec functions to simplify sv
;; expresions by wrappaing them with "svex-eval" and an environment with all
;; the variables in svex pointing to some automatically created free variables.

(in-package "SVL")

(include-book "meta/top")
(include-book "xdoc/topics" :dir :system)

(include-book "svex-simplify-rule-list")

(in-theory (disable bitp natp))

(in-theory (disable acl2::natp-when-gte-0
                    acl2::natp-when-integerp))

(defrec svex-simplify-preloaded
  (enabled-exec-rules rules . meta-rules)
  t)

(progn
  (define svex-simplify-preload (&key (runes '(let ((world (w state))) (current-theory :here)))
                                      (state 'state))
    (declare (xargs :guard-hints (("Goal"
                                   :in-theory (e/d () (table-alist))))
                    :stobjs (state)))
    (b* ((world (w state))
         (- (rp::check-if-clause-processor-up-to-date world))
         ;;(runes (if runes runes (current-theory :here)))
         (enabled-exec-rules (rp::get-enabled-exec-rules runes))
         (rules-alist (rp::get-rules runes state))
         (meta-rules-entry (hons-assoc-equal 'rp::meta-rules-list
                                             (table-alist 'rp::rp-rw world)))
         (meta-rules (if (consp meta-rules-entry)
                         (make-fast-alist
                          (cdr meta-rules-entry))
                       nil)))
      (make svex-simplify-preloaded :enabled-exec-rules enabled-exec-rules
            :meta-rules meta-rules
            :rules rules-alist)))

  (define svex-simplify-preloaded-guard (svex-simplify-preloaded state)
    (declare (xargs :stobjs (state)))
    :enabled t
    (or (not svex-simplify-preloaded)
        (and (weak-svex-simplify-preloaded-p svex-simplify-preloaded)
             (rp::rules-alistp (access svex-simplify-preloaded
                                       svex-simplify-preloaded
                                       :rules))
             (symbol-alistp (access svex-simplify-preloaded
                                    svex-simplify-preloaded
                                    :enabled-exec-rules))
             (rp::rp-meta-rule-recs-p (access svex-simplify-preloaded
                                              svex-simplify-preloaded
                                              :meta-rules)
                                      state))))

  (define svex-rw-free-preload (svex-simplify-preloaded state)
    (declare (xargs :stobjs (state)
                    :guard (svex-simplify-preloaded-guard
                            svex-simplify-preloaded state))
             (ignorable state))
    (if svex-simplify-preloaded
        (progn$
         (fast-alist-free (access svex-simplify-preloaded
                                  svex-simplify-preloaded
                                  :meta-rules))
         (fast-alist-free (access svex-simplify-preloaded
                                  svex-simplify-preloaded
                                  :rules))
         (fast-alist-free (access svex-simplify-preloaded
                                  svex-simplify-preloaded
                                  :enabled-exec-rules))
         nil)
      nil)))

(local
 (defthm rp-statep-update-not-simplified-action
   (implies (and (force (rp::rp-statep rp::rp-state))
                 (force (symbolp flg)))
            (rp::rp-statep
             (rp::update-not-simplified-action flg rp::rp-state)))
   :hints (("Goal"
            :in-theory (e/d (rp::rp-statep) ())))))

(local
 (defthm rp-statep-rp-state-new-run
   (implies (and (force (rp::rp-statep rp::rp-state)))
            (rp::rp-statep
             (rp::rp-state-new-run rp::rp-state)))
   :hints (("goal"
            :in-theory (e/d (rp::rp-state-new-run
                             rp::rp-statep) ())))))

(local
 (defthm symbolp-not-simplified-action
   (implies (rp::rp-statep rp::rp-state)
            (symbolp (rp::not-simplified-action rp::rp-state)))
   :hints (("Goal"
            :in-theory (e/d (rp::rp-statep) ())))))

(define to-svex-fnc (term)
  :prepwork
  ((local
    (in-theory (enable svex-p
                       svexl-node-p
                       svexl-nodelist-p
                       svexlist-p))))
  :returns (mv
            (err)
            (res svex-p :hyp (or (atom term) (svexlist-p (cdr term)))))
  (case-match term
    
    ;; (('svl::4vec-bitor$ size x y)   `(partsel 0 ,size (sv::bitor ,x ,y)))
    ;; (('svl::4vec-bitand$ size x y)  `(partsel 0 ,size (sv::bitand ,x ,y)))
    ;; (('svl::4vec-bitxor$ size x y)  `(partsel 0 ,size (sv::bitxor ,x ,y)))
    (('svl::4vec-bitnot$ size x)  (mv nil `(partsel 0 ,size (sv::bitnot ,x))))
    (('svl::4vec-plus$ size x y)  (mv nil `(partsel 0 ,size (+ ,x ,y))))
    (('svl::bits val s w)         (mv nil (list 'sv::partsel s w val)))
    (('svl::sbits s w new old)    (mv nil (list 'sv::partinst s w old new)))
    (('svl::4vec-concat$ & & &)   (mv nil (cons 'sv::concat   (cdr term))))
    (('sv::4vec-fix$inline &)     (mv nil (cons 'id            (cdr term))))
    (('svl::4vec-fix-wog &)       (mv nil (cons 'id           (cdr term))))
    (('sv::4vec-bit-extract & &)  (mv nil (cons 'sv::bitsel   (cdr term))))
    (('sv::3vec-fix &)            (mv nil (cons 'sv::unfloat  (cdr term))))
    (('4vec-bitnot &)             (mv nil (cons 'sv::bitnot   (cdr term))))
    (('4vec-bitand & &)           (mv nil (cons 'sv::bitand   (cdr term))))
    (('4vec-bitor & &)            (mv nil (cons 'sv::bitor    (cdr term))))
    (('sv::4vec-bitxor & &)       (mv nil (cons 'sv::bitxor   (cdr term))))
    (('sv::4vec-res & &)          (mv nil (cons 'sv::res      (cdr term))))
    (('sv::4vec-resand & &)       (mv nil (cons 'sv::resand   (cdr term))))
    (('sv::4vec-resor & &)        (mv nil (cons 'sv::resor    (cdr term))))
    (('sv::4vec-override & &)     (mv nil (cons 'sv::override (cdr term))))
    (('sv::4vec-onset &)          (mv nil (cons 'sv::onp      (cdr term))))
    (('sv::4vec-offset &)         (mv nil (cons 'sv::offp     (cdr term))))
    (('sv::4vec-reduction-and &)  (mv nil (cons 'sv::uand     (cdr term))))
    (('sv::4vec-reduction-or &)   (mv nil (cons 'sv::uor      (cdr term))))
    (('4vec-parity &)             (mv nil (cons 'sv::uxor     (cdr term))))
    (('4vec-zero-ext & &)         (mv nil (cons 'sv::zerox    (cdr term))))
    (('sv::4vec-sign-ext & &)     (mv nil (cons 'sv::signx    (cdr term))))
    (('4vec-concat & & &)         (mv nil (cons 'concat       (cdr term))))
    (('sv::4vec-rev-blocks & & &) (mv nil (cons 'sv::blkrev   (cdr term))))
    (('4vec-rsh & &)              (mv nil (cons 'sv::rsh      (cdr term))))
    (('4vec-lsh & &)              (mv nil (cons 'sv::lsh      (cdr term))))
    (('4vec-plus & &)             (mv nil (cons '+            (cdr term))))
    (('sv::4vec-minus & &)        (mv nil (cons 'sv::b-       (cdr term))))
    (('sv::4vec-uminus & &)       (mv nil (cons 'sv::u-       (cdr term))))
    (('sv::4vec-times & &)        (mv nil (cons '*            (cdr term))))
    (('sv::4vec-quotient & &)     (mv nil (cons '/            (cdr term))))
    (('sv::4vec-remainder & &)    (mv nil (cons 'sv::%        (cdr term))))
    (('sv::4vec-xdet &)           (mv nil (cons 'sv::xdet     (cdr term))))
    (('sv::4vec-countones &)      (mv nil (cons 'sv::countones(cdr term))))
    (('sv::4vec-onehot &)         (mv nil (cons 'sv::onehot   (cdr term))))
    (('sv::4vec-onehot0 &)        (mv nil (cons 'sv::onehot0  (cdr term))))
    (('sv::4vec-< & &)            (mv nil (cons '<            (cdr term))))
    (('4vec-== & &)               (mv nil (cons 'sv::==       (cdr term))))
    (('sv::4vec-=== & &)          (mv nil (cons 'sv::===      (cdr term))))
    (('sv::4vec-wildeq & &)       (mv nil (cons 'sv::==?      (cdr term))))
    (('sv::4vec-wildeq-safe & &)  (mv nil (cons 'sv::safer-==?(cdr term))))
    (('sv::4vec-symwildeq & &)    (mv nil (cons 'sv::==??     (cdr term))))
    (('sv::4vec-clog2 &)          (mv nil (cons 'sv::clog2    (cdr term))))
    (('sv::4vec-pow & &)          (mv nil (cons 'sv::pow      (cdr term))))
    (('4vec-? & & &)              (mv nil (cons 'sv::?        (cdr term))))
    (('4vec-?* & & &)             (mv nil (cons 'sv::?*       (cdr term))))
    (('sv::4vec-bit? & & &)       (mv nil (cons 'sv::bit?     (cdr term))))
    (('4vec-part-select & & &)    (mv nil (cons 'partsel      (cdr term))))
    (('4vec-part-install & & & &) (mv nil (cons 'sv::partinst (cdr term))))

    (& (progn$
        (cw "cannot match ~p0 with ~p1 arguments to any ~
  svex function. If you think this is a bug, consider changing ~
  svl::to-svex-fnc. ~%"
            (if (consp term) (car term) term) 
            (1- (len term)))
        (mv t '0))))
  ///
  (local
   (in-theory (disable svex-p-implies-svexl-node-p
                       svexlist-p-implies-svexl-nodelist-p)))
  (std::more-returns
   (res svexl-node-p :hyp (or (atom term) (svexl-nodelist-p (cdr term))))))

(acl2::defines
 4vec-to-svex
 :prepwork
 ((local
   (in-theory (e/d (svexl-node-p
                    svex-p
                    assoc-equal
                    sv::svar-p
                    sv::svex-kind
                    rp::measure-lemmas)
                   ((:rewrite rp::measure-lemma1)
                    (:rewrite rp::measure-lemma1-2)
                    (:rewrite sv::svexlist-p-when-subsetp-equal)
                    (:definition subsetp-equal)
                    (:rewrite
                     acl2::member-equal-newvar-components-1)
                    (:definition acl2::loop$-as)
                    (:definition member-equal)
                    (:rewrite
                     sv::svexlist-p-of-cdr-when-svexlist-p)
                    (:rewrite
                     acl2::symbolp-of-car-when-symbol-listp)
                    (:definition rp::rp-termp)))))

  (local
   (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

  (local
   (defthm ex-from-rp-is-nonnil
     (implies (and (rp::rp-termp rp::term))
              (rp::ex-from-rp rp::term))
     :hints (("goal"
              :induct (rp::ex-from-rp rp::term)
              :in-theory (e/d (rp::ex-from-rp
                               rp::is-rp) ())))))

  (local
   (defthm svex-p-to-svex-fnc-quote
     (svex-p
      (to-svex-fnc (cons 'quote x)))
     :hints (("goal"
              :in-theory (e/d (to-svex-fnc) ()))))))

 (define 4vec-to-svex (term svexl-node-flg memoize-flg)
   :guard t
   :measure (rp::cons-count term)
   :returns (mv (err)
                (res))
   (declare (ignorable memoize-flg))
   (b* ((term (rp::ex-from-rp term)))
     (cond ((atom term)
            (if (svex-p term)
                (mv nil term)
              (progn$ (cw "unexpected term ~p0 ~%" term)
                      (mv t 0))))
           ((and (quotep term)
                 (consp (cdr term)))
            (let ((ud (unquote term)))
              (cond ((and (atom ud)
                          (svexl-node-p ud))
                     (mv nil ud))
                    ((svex-p term)
                     (mv nil term))
                    (t
                     (progn$
                      (cw "unexpected term ~p0 ~%" term)
                      (mv t 0))))))
           ((case-match term
              (('svex-env-fastlookup-wog ('quote var) env)
               (and (sv::svar-p var)
                    (equal (rp::ex-from-rp env) 'svex-env)))
              (('sv::svex-env-fastlookup ('quote var) env)
               (and (sv::svar-p var)
                    (equal (rp::ex-from-rp env) 'svex-env))))
            (mv nil (unquote (cadr term))))
           ((and svexl-node-flg
                 (case-match term
                   (('svex-env-fastlookup-wog ('quote var) env)
                    (and (natp var)
                         (equal (rp::ex-from-rp env) 'node-env)))
                   (('sv::svex-env-fastlookup ('quote var) env)
                    (and (natp var)
                         (equal (rp::ex-from-rp env) 'node-env)))))
            (mv nil `(:node ,(unquote (cadr term)))))
           (t (b* ((fnc (car term))
                   ((mv err1 args) (4vec-to-svex-lst (cdr term) svexl-node-flg
                                                     memoize-flg))
                   ((mv err2 res) (to-svex-fnc (cons fnc args))))
                (mv (or err1 err2)
                    res))))))

 (define 4vec-to-svex-lst (lst svexl-node-flg memoize-flg)
   :measure (rp::cons-count lst)
   :returns (mv (err)
                (res-lst))
   (declare (ignorable memoize-flg))
   (if (atom lst)
       (mv nil nil)
     (b* (((mv err1 res1) (4vec-to-svex (car lst) svexl-node-flg memoize-flg))
          ((mv err2 res2) (4vec-to-svex-lst (cdr lst) svexl-node-flg memoize-flg)))
       (mv (or err1 err2)
           (cons res1 res2)))))

 ///

 (memoize '4vec-to-svex :condition 'memoize-flg)

 (std::defret-mutual
  svexl-node-p-of-4vec-to-svex
  (std::defret svexl-node-p-of-4vec-to-svex
               (and (svexl-node-p res)
                    (implies (not svexl-node-flg)
                             (svex-p res)))
               :fn 4vec-to-svex)
  (std::defret svexl-nodelist-p-of-4vec-to-svex-lst
               (and (svexl-nodelist-p res-lst)
                    (implies (not svexl-node-flg)
                             (svexlist-p res-lst)))
               :fn 4vec-to-svex-lst)
  :hints (("goal"
           :expand ((4vec-to-svex-lst lst svexl-node-flg memoize-flg)
                    (4vec-to-svex term svexl-node-flg memoize-flg)
                    (4vec-to-svex term nil memoize-flg))
           :in-theory
           (e/d (
                 )
                (4vec-to-svex-lst
                 4vec-to-svex
                 
                 (:rewrite default-cdr)
                 (:rewrite bitp-implies-natp)
                 (:type-prescription lognot)
                 (:type-prescription bitp)
                 (:rewrite default-<-2)
                 (:rewrite rp::atom-rp-termp-is-symbolp)
                 (:definition lognot)
                 (:rewrite rp::rp-termp-cadr)
                 (:type-prescription rp::rp-termp)
                 (:rewrite integerp-implies-4vecp)
                 (:rewrite rp::rp-termp-ex-from-rp)
                 (:rewrite sv::svar-p-of-car-when-svarlist-p)
                 (:rewrite natp-implies-integerp)
                 (:rewrite acl2::o-p-o-infp-car)
                 (:rewrite rp::rp-termp-extract-from-rp)
                 (:rewrite
                  acl2::booleanp-of-car-when-boolean-listp)
                 (:rewrite
                  acl2::boolean-listp-of-cdr-when-boolean-listp)
                 (:rewrite sv::4vec-p-of-car-when-4veclist-p)
                 (:rewrite
                  svexl-nodelist-p-of-cdr-when-svexl-nodelist-p)
                 (:rewrite
                  sv::4veclist-p-of-cdr-when-4veclist-p)
                 (:rewrite acl2::natp-of-car-when-nat-listp)
                 (:definition rp::ex-from-rp)
                 (:rewrite sv::svex-p-when-maybe-svex-p)
                 (:rewrite
                  acl2::nat-listp-of-cdr-when-nat-listp)
                 (:rewrite default-car)))))))

(progn
  (define svexl-node-simplify ((node svexl-node-p)
                               (preloaded-rules)
                               (hyp)
                               &key
                               (state 'state)
                               (rp::rp-state 'rp::rp-state))
    :guard (and preloaded-rules
                (svex-simplify-preloaded-guard preloaded-rules state))
    :returns (mv (node-new svexl-node-p)
                 (rp::rp-state-res rp::rp-statep :hyp (rp::rp-statep
                                                       rp::rp-state)))
    :prepwork
    ((local
      (in-theory (e/d () (rp::rp-statep
                          rp::rp-rw-aux))))
     (local
      (include-book "projects/rp-rewriter/proofs/rp-correct" :dir :system)))

    (b* ((rules preloaded-rules)
         ((mv enabled-exec-rules rules-alist meta-rules)
          (mv (access svex-simplify-preloaded rules
                      :enabled-exec-rules)
              (access svex-simplify-preloaded rules
                      :rules)
              (access svex-simplify-preloaded rules
                      :meta-rules)))
         (hyp `(if (sv::svex-env-p svex-env) ,hyp 'nil))
         (hyp `(if (node-env-p node-env) ,hyp 'nil))
         (term `(implies ,hyp (svexl-node-eval ',node node-env svex-env)))
         ((mv rw rp::rp-state) (rp::rp-rw-aux term rules-alist
                                              enabled-exec-rules
                                              meta-rules rp::rp-state
                                              state))
         (rw (case-match rw
               (('implies & x) x)
               (& rw)))
         ((mv err node-new) (4vec-to-svex rw t nil))
         (- (and err
                 (hard-error
                  'svexl-node-simplify
                  "4vec-to-svex returned an error for the term: ~p0 ~%"
                  (list (cons #\0 rw))))))
      (mv node-new rp::rp-state)))

  (define svex-simplify-linearize-aux ((svexl-node-alist svexl-node-alist-p)
                                       (preloaded-rules)
                                       (hyp)
                                       &key
                                       (state 'state)
                                       (rp::rp-state 'rp::rp-state))
    :returns (mv (svexl-new svexl-node-alist-p :hyp (svexl-node-alist-p svexl-node-alist))
                 (rp::rp-state-res rp::rp-statep :hyp (rp::rp-statep
                                                       rp::rp-state)))
    :verify-guards nil
    :guard (and preloaded-rules
                (svex-simplify-preloaded-guard preloaded-rules state))
    :prepwork
    ((local
      (in-theory (e/d (svexl-node-alist-p)
                      (rp::rp-statep
                       rp::rp-rw-aux)))))
    (if (atom svexl-node-alist)
        (mv nil rp::rp-state)
      (b* ((node (cdar svexl-node-alist))
           ((mv node rp::rp-state)
            (svexl-node-simplify node preloaded-rules hyp))
           ((mv rest rp::rp-state)
            (svex-simplify-linearize-aux (cdr svexl-node-alist) preloaded-rules hyp)))
        (mv (acons (caar svexl-node-alist) node rest)
            rp::rp-state)))
    ///
    (verify-guards svex-simplify-linearize-aux-fn))

  (define svex-simplify-linearize ((svex svex-p)
                                   (preloaded-rules)
                                   (hyp)
                                   &key
                                   (state 'state)
                                   (rp::rp-state 'rp::rp-state))
    :guard (and preloaded-rules
                (svex-simplify-preloaded-guard preloaded-rules state))
    :returns (mv (svexl-new svexl-node-alist-p :hyp (svex-p svex))
                 (rp::rp-state-res rp::rp-statep :hyp (rp::rp-statep
                                                       rp::rp-state)))
    (b* ((svexl-node-alist (svex-to-svexl svex)))
      (svex-simplify-linearize-aux svexl-node-alist preloaded-rules hyp))))

(define cons-count-compare ((term)
                            (cnt natp))
  (cond ((zp cnt) cnt)
        ((atom term)
         (- cnt 1))
        (t 
         (b* ((cnt (cons-count-compare (car term) cnt))
              ((when (zp cnt)) cnt)
              (cnt (cons-count-compare (cdr term) cnt)))
           cnt))))

(define svex-simplify-to-4vec ((svex svex-p)
                               &key
                               (state 'state)
                               (rp::rp-state 'rp::rp-state)
                               (hyp ''t)
                               (linearize ':auto)
                               (preloaded-rules 'nil)
                               (runes '(let ((world (w state))) (current-theory
                                                                 :here))))

  :stobjs (state rp::rp-state)
  :returns (mv (rw)
               (rp::rp-state-res rp::rp-statep :hyp (rp::rp-statep rp::rp-state)))
  :prepwork
  ((local
    (in-theory (e/d (svex-simplify-preload)
                    (rp::rules-alistp
                     state-p
                     rp::rp-statep
                     RP::NOT-SIMPLIFIED-ACTION
                     RP::UPDATE-NOT-SIMPLIFIED-ACTION
                     rp::rp-rw-aux
                     table-alist))))
   (local
    (include-book "projects/rp-rewriter/proofs/rp-correct" :dir :system))
   (local
    (include-book "projects/rp-rewriter/proofs/extract-formula-lemmas" :dir :system)))

  :guard (and (svex-simplify-preloaded-guard preloaded-rules state)
              (or (rp::rp-termp hyp)
                  (cw "Given hyp must satisfy rp::rp-termp ~%")))

  (b* ((world (w state))
       (linearize (if (eq linearize ':auto)
                      (zp (cons-count-compare svex 2048))
                    linearize))

       
       
       ;; do not let rp-rewriter complain when simplified term is not ''t
       (tmp-rp-not-simplified-action (rp::not-simplified-action rp::rp-state))
       (rp::rp-state (rp::update-not-simplified-action :none rp::rp-state))
       (rp::rp-state (rp::rp-state-new-run rp::rp-state))

       (rules (if preloaded-rules preloaded-rules
                (progn$
                 (rp::check-if-clause-processor-up-to-date world)
                 (svex-simplify-preload :runes runes))))

       (hyp `(if (sv::svex-env-p svex-env) ,hyp 'nil))

       (term `(implies ,hyp (svex-eval-wog ',svex svex-env)))

       ((unless (or preloaded-rules
                    (svex-simplify-preloaded-guard rules state)))
        (progn$
         (hard-error 'svex-simplify-to-4vec
                     "Something is wrong with the rules. ~%"
                     nil)
         (mv term rp::rp-state)))
       ((mv svexl-node-alist rp::rp-state)
        (if linearize
            (svex-simplify-linearize svex rules hyp)
          (mv nil rp::rp-state)))
       (term (if linearize
                 `(implies ,hyp (svexl-eval-wog ',svexl-node-alist svex-env))
               term))

       ((mv enabled-exec-rules rules-alist meta-rules)
        (mv (access svex-simplify-preloaded rules
                    :enabled-exec-rules)
            (access svex-simplify-preloaded rules
                    :rules)
            (access svex-simplify-preloaded rules
                    :meta-rules)))
       ((mv rw rp::rp-state) (rp::rp-rw-aux term rules-alist
                                            enabled-exec-rules
                                            meta-rules rp::rp-state
                                            state))

       ;; restore rp-state setting
       (rp::rp-state (rp::update-not-simplified-action
                      tmp-rp-not-simplified-action rp::rp-state))

       (- (and (not preloaded-rules)
               (svex-rw-free-preload rules state))))
    (mv rw rp::rp-state)))


         

(define svex-simplify ((svex svex-p)
                       &KEY
                       (state 'state)
                       (rp::rp-state 'rp::rp-state)
                       (hyp ''t) ;; "Have more context for variables."
                       (runes '(let ((world (w state)))
                                 (current-theory :here)))
                       ;; "if need to work with only certain rules other than current-theory"
                       (preloaded-rules 'nil) ;; Non-nil overrides rule
                       ;; structure  creation for the rewriter. This value
                       ;; can be created with (svex-simplify-preload)
                       (linearize ':auto)
                       )
  :stobjs (state rp::rp-state)
  :returns (mv (res svex-p)
               (rp::rp-state-res rp::rp-statep :hyp (rp::rp-statep
                                                     rp::rp-state)))
  :guard (and (svex-simplify-preloaded-guard preloaded-rules state)
              (or (rp::rp-termp hyp)
                  (cw "Given hyp must satisfy rp::rp-termp ~%")))
  (b* ((linearize (if (eq linearize ':auto)
                      (zp (cons-count-compare svex 2048))
                    linearize))
       ((mv rw rp::rp-state)
        (svex-simplify-to-4vec svex
                               :state state
                               :hyp hyp
                               :runes runes
                               :preloaded-rules preloaded-rules
                               :linearize linearize))
       ((mv err svex-res)
        (case-match rw
          (('implies & term) (4vec-to-svex term nil linearize))
          (& (4vec-to-svex rw nil linearize))))
       (- (and err
               (hard-error
                'svex-simplify
                "4vec-to-svex returned an error for the term: ~p0 ~%"
                (list (cons #\0 rw))))))
    (mv svex-res rp::rp-state)))

(acl2::defxdoc svex-simplify
               :parents (projects/svl)
               :short "Using proved rewrite rules for svex-eval and 4vec
  functions, rewrites an @('sv::svex')."
               :long "<p> SVEX-SIMPLIFY wraps an sv expression with an @('sv::svex-eval'),
  attaches some optional hypotheses for extra context and runs the main
  rp-rewriter function to perform rewriting, and then it converts the resulting
  term back to an equivalent sv expression. If you want to avoid converting back
  to svex expression but get the rewritten term you may use SVEX-SIMPLIFY-TO-4VEC
  </p>

<p> Example Use: </p>

@({
(defconst *test-svex*
   '(sv::partsel 0 3
     (sv::zerox 4
       (sv::concat 3 (sv::concat 2 (sv::concat 1 x y) z) k))))

;; This call will return an equivalent expression for *test-svex*
(svl::svex-simplify *test-svex*)

;; Returned value:
'(CONCAT 1 (PARTSEL 0 1 X)
         (CONCAT 1 (PARTSEL 0 1 Y)
                 (PARTSEL 0 1 Z)))

;; This call will what the term is rewritten to before trying to convert it
;; back to svex format.
(svl::svex-simplify-to-4vec *test-svex*)

;; Returned value
'(IMPLIES
  (IF (SVEX-ENV-P SVEX-ENV) T 'NIL)
  (4VEC-CONCAT$
      '1
      (BITS (SVEX-ENV-FASTLOOKUP-WOG 'X
                                     (RP 'SVEX-ENV-P SVEX-ENV))
            '0
            '1)
      (4VEC-CONCAT$ '1
                    (BITS (SVEX-ENV-FASTLOOKUP-WOG 'Y
                                                   (RP 'SVEX-ENV-P SVEX-ENV))
                          '0
                          '1)
                    (BITS (SVEX-ENV-FASTLOOKUP-WOG 'Z
                                                   (RP 'SVEX-ENV-P SVEX-ENV))
                          '0
                          '1))))
 })

<p> Users may also add more rewrite rules to have a different rewriting scheme than the
one that comes with this book. Should these new rewrite rules need more context
about the variables, you may pass an extra hyp argument (should be a translated term) to
SVEX-SIMPLIFY-TO-4VEC or SVEX-SIMPLIFY. Note: the functions assume that even without any
hypothesis, the functions assume the dummy svex environment satisfy SV::SVEX-ENV-P .</p>

<p> If you anticipate to call svl::svex-simplify or svl::rw-svex-to-4vec many
times for the same set of rules, you may want to use
(svl::svex-simplify-preload). This function call will return a structure and can
be passed to SVEX-SIMPLIFY. and SVEX-SIMPLIFY-TO-4VEC with the key
:preloded-rules. This avoids the repeated processing of rules from the
world. When you are finished, it is advisable to execute (svex-rw-free-preload
svex-rw-free-preloaded state) in order to free the fast-alists created. </p>

")

;; (trace$ (svex-simplify-linearize-fn :entry (car acl2::arglist)))

;; (svex-simplify  #!SV'(bitor (bitand (bitor a b) (bitor (bitor a b)
;;                                                        (bitor a b)))
;;                             (bitor (bitor a b)
;;                                    (bitor a b))))

;; (svex-simplify  #!SV'(bitor (bitand (bitor a b) (bitor (bitor a b)
;;                                                        (bitor a b)))
;;                             (bitor (bitor a b)
;;                                    (bitor a b)))
;;                 :linearize t)
