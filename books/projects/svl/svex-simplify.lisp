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
             (rp::update-not-simplified-action flg rp::rp-state)))))

(local
 (defthm rp-statep-rp-state-new-run
   (implies (and (force (rp::rp-statep rp::rp-state)))
            (rp::rp-statep
             (rp::rp-state-new-run rp::rp-state)))
   :hints (("goal"
            :in-theory (e/d (rp::rp-state-new-run) ())))))

(local
 (defthm symbolp-not-simplified-action
   (implies (rp::rp-statep rp::rp-state)
            (symbolp (rp::not-simplified-action rp::rp-state)))))


(progn
  (define to-svex-fnc (term)
    :prepwork
    ((local
      (in-theory (enable svexl-node-p
                         svexlist-p))))
    :returns (res svexl-node-p :hyp (or (atom term) (svexl-nodelist-p (cdr term))))
    (case-match term
      (('svl::4vec-bitnot$ size x)    `(partsel 0 ,size (sv::bitnot ,x)))
      (('svl::4vec-plus$ size x y)    `(partsel 0 ,size (+ ,x ,y)))
      ;; (('svl::4vec-bitor$ size x y)   `(partsel 0 ,size (sv::bitor ,x ,y)))
      ;; (('svl::4vec-bitand$ size x y)  `(partsel 0 ,size (sv::bitand ,x ,y)))
      ;; (('svl::4vec-bitxor$ size x y)  `(partsel 0 ,size (sv::bitxor ,x ,y)))

      (('svl::bits val s w)        (list 'sv::partsel s w val))
      (('svl::sbits s w new old)   (list 'sv::partinst s w old new))
      (('svl::4vec-concat$ & & &)  (cons 'sv::concat   (cdr term)))

      (('sv::4vec-fix$inline &)    (cons 'id            (cdr term)))
      (('svl::4vec-fix-wog &)      (cons 'id           (cdr term)))
      (('sv::4vec-bit-extract & &) (cons 'sv::bitsel   (cdr term)))
      (('sv::3vec-fix &)           (cons 'sv::unfloat  (cdr term)))
      (('4vec-bitnot &)            (cons 'sv::bitnot   (cdr term)))
      (('4vec-bitand & &)          (cons 'sv::bitand   (cdr term)))
      (('4vec-bitor & &)           (cons 'sv::bitor    (cdr term)))
      (('sv::4vec-bitxor & &)      (cons 'sv::bitxor   (cdr term)))
      (('sv::4vec-res & &)         (cons 'sv::res      (cdr term)))
      (('sv::4vec-resand & &)      (cons 'sv::resand   (cdr term)))
      (('sv::4vec-resor & &)       (cons 'sv::resor    (cdr term)))
      (('sv::4vec-override & &)    (cons 'sv::override (cdr term)))
      (('sv::4vec-onset &)         (cons 'sv::onp      (cdr term)))
      (('sv::4vec-offset &)        (cons 'sv::offp     (cdr term)))
      (('sv::4vec-reduction-and &) (cons 'sv::uand     (cdr term)))
      (('sv::4vec-reduction-or &)  (cons 'sv::uor      (cdr term)))
      (('4vec-parity &)            (cons 'sv::uxor     (cdr term)))
      (('4vec-zero-ext & &)        (cons 'sv::zerox    (cdr term)))
      (('sv::4vec-sign-ext & &)    (cons 'sv::signx    (cdr term)))
      (('4vec-concat & & &)        (cons 'concat       (cdr term)))
      (('sv::4vec-rev-blocks & & &)(cons 'sv::blkrev   (cdr term)))
      (('4vec-rsh & &)             (cons 'sv::rsh      (cdr term)))
      (('4vec-lsh & &)             (cons 'sv::lsh      (cdr term)))
      (('4vec-plus & &)            (cons '+            (cdr term)))
      (('sv::4vec-minus & &)       (cons 'sv::b-       (cdr term)))
      (('sv::4vec-uminus & &)      (cons 'sv::u-       (cdr term)))
      (('sv::4vec-times & &)       (cons '*            (cdr term)))
      (('sv::4vec-quotient & &)    (cons '/            (cdr term)))
      (('sv::4vec-remainder & &)   (cons 'sv::%        (cdr term)))
      (('sv::4vec-xdet &)          (cons 'sv::xdet     (cdr term)))
      (('sv::4vec-countones &)     (cons 'sv::countones(cdr term)))
      (('sv::4vec-onehot &)        (cons 'sv::onehot   (cdr term)))
      (('sv::4vec-onehot0 &)       (cons 'sv::onehot0  (cdr term)))
      (('sv::4vec-< & &)           (cons '<            (cdr term)))
      (('4vec-== & &)              (cons 'sv::==       (cdr term)))
      (('sv::4vec-=== & &)         (cons 'sv::===      (cdr term)))
      (('sv::4vec-wildeq & &)      (cons 'sv::==?      (cdr term)))
      (('sv::4vec-wildeq-safe & &) (cons 'sv::safer-==?(cdr term)))
      (('sv::4vec-symwildeq & &)   (cons 'sv::==??     (cdr term)))
      (('sv::4vec-clog2 &)         (cons 'sv::clog2    (cdr term)))
      (('sv::4vec-pow & &)         (cons 'sv::pow      (cdr term)))
      (('4vec-? & & &)             (cons 'sv::?        (cdr term)))
      (('4vec-?* & & &)            (cons 'sv::?*       (cdr term)))
      (('sv::4vec-bit? & & &)      (cons 'sv::bit?     (cdr term)))
      (('4vec-part-select & & &)   (cons 'partsel      (cdr term)))
      (('4vec-part-install & & & &)(cons 'sv::partinst (cdr term)))

      (& (progn$
          (hard-error '4vec-to-svex "cannot match ~p0 with ~p1 arguments to any ~
  svex function. If you think this is a bug, consider changing ~
  svl::to-svex-fnc. ~%"
                      (list (cons #\0 (if (consp term) (car term) term))
                            (cons #\1 (1- (len term)))))
          '0))))


  (acl2::defines
   4vec-to-svex
   :prepwork ((local
               (in-theory (e/d (svexl-node-p
                                assoc-equal
                                sv::svar-p
                                sv::svex-kind
                                rp::measure-lemmas)
                               ((:REWRITE RP::MEASURE-LEMMA1)
                                (:REWRITE RP::MEASURE-LEMMA1-2)
                                (:REWRITE SV::SVEXLIST-P-WHEN-SUBSETP-EQUAL)
                                (:DEFINITION SUBSETP-EQUAL)
                                (:REWRITE
                                 ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                                (:DEFINITION ACL2::LOOP$-AS)
                                (:DEFINITION MEMBER-EQUAL)
                                (:REWRITE
                                 SV::SVEXLIST-P-OF-CDR-WHEN-SVEXLIST-P)
                                (:REWRITE
                                 ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP)
                                (:DEFINITION RP::RP-TERMP)))))

              (local
               (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

              (local
               (DEFTHM EX-FROM-RP-is-nonnil
                 (IMPLIES (AND (RP::RP-TERMP RP::TERM))
                          (RP::EX-FROM-RP RP::TERM))
                 :hints (("Goal"
                          :induct (RP::EX-FROM-RP RP::TERM)
                          :in-theory (e/d (RP::EX-FROM-RP
                                           rp::is-rp) ())))))

              (local
               (defthm SVEX-P-to-svex-fnc-quote
                 (svex-p
                  (to-svex-fnc (cons 'quote x)))
                 :hints (("Goal"
                          :in-theory (e/d (to-svex-fnc) ()))))))
   (define 4vec-to-svex (term memoize-flg)
     :guard t
     :measure (rp::cons-count term)
     :returns (res svexl-node-p)
     (declare (ignorable memoize-flg))
     (b* ((term (rp::ex-from-rp term)))
       (cond ((atom term)
              (if (svexl-node-p term)
                  term
                (progn$ (hard-error '4vec-to-svex
                                    "Unexpected term ~p0 ~%"
                                    (list (cons #\0 term)))
                        0)))
             ((and (quotep term)
                   (consp (cdr term)))
              (let ((ud (unquote term)))
                (cond ((and (atom ud)
                            (svexl-node-p ud))
                       ud)
                      ((svexl-node-p term)
                       term)
                      (t
                       (progn$ (hard-error '4vec-to-svex
                                           "Unexpected term ~p0 ~%"
                                           (list (cons #\0 term)))
                               0)))))
             ((case-match term
                (('svex-env-fastlookup-wog ('quote var) env)
                 (and (sv::svar-p var)
                      (equal (rp::ex-from-rp env) 'svex-env)))
                (('sv::svex-env-fastlookup ('quote var) env)
                 (and (sv::svar-p var)
                      (equal (rp::ex-from-rp env) 'svex-env))))
              (unquote (cadr term)))
             ((case-match term
                (('svex-env-fastlookup-wog ('quote var) env)
                 (and (natp var)
                      (equal (rp::ex-from-rp env) 'node-env)))
                (('sv::svex-env-fastlookup ('quote var) env)
                 (and (natp var)
                      (equal (rp::ex-from-rp env) 'node-env))))
              `(:node ,(unquote (cadr term))))
             (t (b* ((fnc (car term))
                     (args (4vec-to-svex-lst (cdr term) memoize-flg)))
                  (to-svex-fnc (cons fnc args)))))))

   (define 4vec-to-svex-lst (lst memoize-flg)
     :measure (rp::cons-count lst)
     :returns (res-lst svexl-nodelist-p)
     (declare (ignorable memoize-flg))
     (if (atom lst)
         nil
       (cons (4vec-to-svex (car lst) memoize-flg)
             (4vec-to-svex-lst (cdr lst) memoize-flg)))))

  (memoize '4vec-to-svex :condition 'memoize-flg))


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
         (node-new (4vec-to-svex rw nil)))
      (mv node-new rp::rp-state)))


  (define svex-simplify-linearize-aux ((svexl svexl-p)
                                       (preloaded-rules)
                                       (hyp)
                                       &key
                                       (state 'state)
                                       (rp::rp-state 'rp::rp-state))
    :returns (mv (svexl-new svexl-p :hyp (svexl-p svexl))
                 (rp::rp-state-res rp::rp-statep :hyp (rp::rp-statep
                                                       rp::rp-state)))
    :verify-guards nil
    :guard (and preloaded-rules
                (svex-simplify-preloaded-guard preloaded-rules state))
    :prepwork
    ((local
      (in-theory (e/d (svexl-p)
                      (rp::rp-statep
                       rp::rp-rw-aux)))))
    (if (atom svexl)
        (mv nil rp::rp-state)
      (b* ((node (cdar svexl))
           ((mv node rp::rp-state)
            (svexl-node-simplify node preloaded-rules hyp))
           ((mv rest rp::rp-state)
            (svex-simplify-linearize-aux (cdr svexl) preloaded-rules hyp)))
        (mv (acons (caar svexl) node rest)
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
    :returns (mv (svexl-new svexl-p :hyp (svex-p svex))
                 (rp::rp-state-res rp::rp-statep :hyp (rp::rp-statep
                                                       rp::rp-state)))
    (b* ((svexl (svex-to-svexl svex)))
      (svex-simplify-linearize-aux svexl preloaded-rules hyp))))
       
  
                        

(define svex-simplify-to-4vec ((svex svex-p)
                               &key
                               (state 'state)
                               (rp::rp-state 'rp::rp-state)
                               (hyp ''t)
                               (linearize 'nil)
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

  :guard (svex-simplify-preloaded-guard preloaded-rules state)

  (b* ((world (w state))
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
       ((mv svexl rp::rp-state)
        (if linearize
            (svex-simplify-linearize svex rules hyp)
          (mv nil rp::rp-state)))
       (term (if linearize
                 `(implies ,hyp (svexl-eval-wog ',svexl svex-env))
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
                       (runes '(let ((world (w state))) (current-theory
                                                         :here)))
                       ;; "if need to work with only certain rules other than current-theory"
                       (preloaded-rules 'nil) ;; Non-nil overrides rule
                       ;; structure  creation for the rewriter. This value
                       ;; can be created with (svex-simplify-preload)
                       (linearize 'nil)
                       )
  :stobjs (state rp::rp-state)
  :returns (mv (res svexl-node-p)
               (rp::rp-state-res rp::rp-statep :hyp (rp::rp-statep
                                                     rp::rp-state)))
  :guard (svex-simplify-preloaded-guard preloaded-rules state)
  (b* (((mv rw rp::rp-state)
        (svex-simplify-to-4vec svex
                               :state state
                               :hyp hyp
                               :runes runes
                               :preloaded-rules preloaded-rules
                               :linearize linearize))
       (svex-res (case-match rw
                   (('implies & term) (4vec-to-svex term linearize))
                   (& (4vec-to-svex rw linearize)))))
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
