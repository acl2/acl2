

; Functions for quick search of adder patterns.


; Multiplier verification

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

(in-package "RP")

(include-book "../fnc-defs")
(include-book "centaur/svl/top" :dir :system)
(include-book "centaur/sv/svex/lists" :dir :system)

(include-book "heuristics")
(include-book "adder-patterns")
(include-book "macros")

(local
 (include-book "centaur/bitops/ihs-extensions" :dir :system))

(local
 (include-book "ihs/logops-lemmas" :dir :system))

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


(local
 (defthm sv::svexlist-eval$-when-consp
   (implies (consp lst)
            (equal (sv::svexlist-eval$ lst env)
                   (cons (sv::svex-eval$ (car lst) env)
                         (sv::svexlist-eval$ (cdr lst) env))))))



;; For simple, quick pattern finding.

;; 1. Gather applicable patterns and create a "pattern-alist"
(acl2::defines gather-adder-patterns-in-svex
  :prepwork
  ((define register-found-adder-patterns ((pattern-fn-call-list pattern-fn-call-list-p)
                                          (pattern-alist pattern-alist-p)
                                          (column acl2::maybe-integerp))
     :returns (res pattern-alist-p :hyp (and (pattern-alist-p pattern-alist)
                                             (acl2::maybe-integerp column)))
     ;;:inline t
     ;; when a matching pattern  is found, it should be saved  in a fast-alist whose
     ;; keys are arguments, and value should be a list of all the pattern names.
     (b* (((when (atom pattern-fn-call-list)) pattern-alist)
          ((pattern-fn-call x) (car pattern-fn-call-list))

          ;;((unless (and key value)) pattern-alist)
          (entry (hons-get x.args pattern-alist))

          ;; when column is tracked, the function name is saved as a cons pair instead..
          (new-fn (if column
                      (cons x.fn
                            (if (member x.fn '(fa-c-chain ha-c-chain ha+1-c-chain))
                                (1- column)
                              column))
                    x.fn))
          (new-entry (cons new-fn (cdr entry)))
          (new-entry (if (and x.new-p (not (member :new new-entry)))
                         (list* :new new-entry)
                       new-entry))
          (key x.args)
          (pattern-alist (hons-acons key new-entry pattern-alist)))
       (register-found-adder-patterns (cdr pattern-fn-call-list)
                                      pattern-alist
                                      column))
     ///
     (defret alistp-of-<fn>
       (implies (alistp pattern-alist)
                (alistp res)))))

  :verify-guards nil

  (define gather-adder-patterns-in-svex ((x sv::svex-p)
                                         &key
                                         ((pattern-alist pattern-alist-p) 'pattern-alist)
                                         (parsed-svexes 'parsed-svexes)
                                         (adder-type 'adder-type)
                                         ((column acl2::maybe-integerp) 'column)

                                         ((env) 'env)
                                         ((context rp-term-listp) 'context)
                                         ((config svl::svex-reduce-config-p) 'config))
    :measure (sv::svex-count x)
    :returns (mv (res-pattern-alist pattern-alist-p :hyp (and (pattern-alist-p pattern-alist)
                                                              (acl2::maybe-integerp column)))
                 res-parsed-svexes)
    (sv::svex-case
     x
     :quote (mv pattern-alist parsed-svexes)
     :var   (mv pattern-alist parsed-svexes)
     :call (b* ((already-parsed (hons-get x parsed-svexes))
                ((when already-parsed) (mv pattern-alist parsed-svexes))
                (parsed-svexes (hons-acons x nil parsed-svexes))
                ;; get a list of matching patterns.
                (matching-pattern-fn-call-list (adder-pattern-match x adder-type))
                (pattern-alist
                 (register-found-adder-patterns matching-pattern-fn-call-list pattern-alist column))
                ((unless column)
                 (gather-adder-patterns-in-svexlist x.args)))
             (cond 
              ((and*-exec (eq x.fn 'sv::concat)
                          (svl::equal-len x.args 3)
                          (natp (first x.args)))
               (b* (((mv pattern-alist parsed-svexes)
                     (gather-adder-patterns-in-svex (second x.args))))
                 (gather-adder-patterns-in-svex (third x.args)
                                                :column (+ column (first x.args)))))
              (t
               (b*  (;;  bitand and  bitor  is  likely  a part  of  carry
                     ;; logic. This will mess  up with column calculation.
                     ;; So let's  just increase  column a  lot so  it gets
                     ;; thrown away.
                     ((when (member-eq x.fn '(sv::bitand sv::bitor)))
                      (mv pattern-alist parsed-svexes))
                     
                     (column (+ column
                                (- (acl2::bool->bit
                                    (member-eq x.fn '(ha-c-chain fa-c-chain ha+1-c-chain)))))))
                 (gather-adder-patterns-in-svexlist x.args)))))))
  
  (define gather-adder-patterns-in-svexlist ((lst sv::svexlist-p)
                                             &key
                                             ((pattern-alist pattern-alist-p) 'pattern-alist)
                                             (parsed-svexes 'parsed-svexes)
                                             (adder-type 'adder-type)
                                             ((column acl2::maybe-integerp) 'column)

                                             ((env) 'env)
                                             ((context rp-term-listp) 'context)
                                             ((config svl::svex-reduce-config-p) 'config))
    :returns (mv (res-pattern-alist pattern-alist-p :hyp (and (pattern-alist-p pattern-alist)
                                                              (acl2::maybe-integerp column)))
                 res-parsed-svexes)
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        (mv pattern-alist parsed-svexes)
      (b* (((mv pattern-alist parsed-svexes)
            (gather-adder-patterns-in-svex (car lst)))
           ((mv pattern-alist parsed-svexes)
            (gather-adder-patterns-in-svexlist (cdr lst))))
        (mv pattern-alist parsed-svexes))))
  ///

  (verify-guards gather-adder-patterns-in-svex-fn)

  (defret-mutual alistp-of-<fn>
    (defret alistp-of-<fn>
      (implies (alistp pattern-alist)
               (alistp res-pattern-alist))
      :fn gather-adder-patterns-in-svex)
    (defret alistp-of-<fn>
      (implies (alistp pattern-alist)
               (alistp res-pattern-alist))
      :fn gather-adder-patterns-in-svexlist)
    :hints (("Goal"
             :expand ((gather-adder-patterns-in-svexlist lst)
                      (gather-adder-patterns-in-svex nil)
                      (gather-adder-patterns-in-svex x))
             :in-theory (e/d () ())))))

(define gather-adder-patterns-in-svex-alist ((alist sv::svex-alist-p)
                                             &key
                                             ((pattern-alist pattern-alist-p) ''gather-adder-patterns-in-svex-alist)
                                             (parsed-svexes ''gather-adder-patterns-in-svex-alist-parsed-svexes)
                                             (adder-type 'adder-type)
                                             (track-column? 'track-column?)
                                             ((env) 'env)
                                             ((context rp-term-listp) 'context)
                                             ((config svl::svex-reduce-config-p) 'config))
  :returns (mv (res-pattern-alist pattern-alist-p :hyp (pattern-alist-p pattern-alist))
               res-parsed-svexes)
  (if (atom alist)
      (progn$ (fast-alist-free parsed-svexes)
              (mv pattern-alist parsed-svexes))
    (b* (((mv pattern-alist parsed-svexes)
          (gather-adder-patterns-in-svex (cdar alist)
                                         :column (and track-column? 0)))
         ((mv pattern-alist parsed-svexes)
          (gather-adder-patterns-in-svex-alist (cdr alist)
                                               :pattern-alist pattern-alist
                                               :parsed-svexes parsed-svexes)))
      (mv pattern-alist parsed-svexes)))
  ///
  (defret alistp-of-<fn>
    (implies (alistp pattern-alist)
             (alistp res-pattern-alist))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; now apply foind patterns.

(define run-pattern-rule ((rule symbol-listp)
                          (source.fn)
                          (found-patterns true-listp)
                          (track-column?))
  :prepwork
  ((define run-pattern-rule-aux-when-track-column (source.fn other.fn
                                                             found-patterns
                                                             (all-found-patterns true-listp))
     (if (atom found-patterns)
         nil
       (b* ((first (car found-patterns))
            (column (and (consp first) (cdr first)))
            (matched-fn? (and (consp first) (equal (car first) source.fn)))
            ((when (and matched-fn?
                        (member-equal (cons other.fn column)
                                      all-found-patterns)))
             t))
         (run-pattern-rule-aux-when-track-column
          source.fn other.fn (cdr found-patterns) all-found-patterns)))))

  (b* (((when (atom rule)) nil)
       (first-fn (car rule)))
    (or (cond ((equal first-fn t)
               t)
              (track-column?
               (run-pattern-rule-aux-when-track-column source.fn first-fn found-patterns found-patterns))
              (t (member-eq first-fn found-patterns)))
        (run-pattern-rule (cdr rule) source.fn found-patterns track-column?))))


(define pull-the-first-applicable-adder-pattern ((pattern-alist pattern-alist-p)
                                                 (pattern-fn-call-list pattern-fn-call-list-p)
                                                 (track-column?))
  :prepwork ((in-theory (e/d ()
                             (assoc-equal
                              (:e tau-system)))))
  :returns (pattern-fn-call (implies pattern-fn-call
                                     (pattern-fn-call-p pattern-fn-call))
                            :hyp (pattern-fn-call-list-p pattern-fn-call-list))
  (if (atom pattern-fn-call-list)
      nil
    (b* (((pattern-fn-call x) (car pattern-fn-call-list))
         ((when (equal x.rule '(t))) x)
         (found-patterns (cdr (hons-get x.args pattern-alist)))
         (should-rewrite (and x.rule (run-pattern-rule x.rule x.fn found-patterns track-column?)))
         ((when should-rewrite)
          (car pattern-fn-call-list)))
      (pull-the-first-applicable-adder-pattern pattern-alist
                                               (cdr pattern-fn-call-list)
                                               track-column?)))
  ///

  (defret <fn>-returns-a-member-of-pattern-fn-call-list
    (implies pattern-fn-call
             (and (member-equal pattern-fn-call pattern-fn-call-list)
                  (pattern-fn-call->rule pattern-fn-call)))))



(local
 (defthm replace-adder-patterns-in-svex-measure-lemma
   (implies
    (and (pull-the-first-applicable-adder-pattern
          pattern-alist
          (adder-pattern-match (sv::svex-fix x) adder-type)
          track-column?))
    (<
     (sv::svexlist-count
      (pattern-fn-call->args (pull-the-first-applicable-adder-pattern
                              pattern-alist
                              (adder-pattern-match (sv::svex-fix x) adder-type)
                              track-column?)))
     (sv::svex-count x)))
   :hints (("Goal"
            :use ((:instance
                   pattern-fn-call-list-provide-good-measure-p-and-member
                   (x (sv::svex-fix x))
                   (lst (adder-pattern-match (sv::svex-fix x) adder-type))
                   (e (pull-the-first-applicable-adder-pattern
                       pattern-alist
                       (adder-pattern-match (sv::svex-fix x) adder-type)
                       track-column?)))

                  (:instance adder-pattern-match-good-measure
                             (svex (sv::svex-fix x))))
            :in-theory (e/d (pattern-fn-call-provide-good-measure-p)
                            (pattern-fn-call-list-provide-good-measure-p-and-member
                             adder-pattern-match-good-measure))))))



(acl2::defines replace-adder-patterns-in-svex

  :flag-local nil

  :prepwork ((local
              (in-theory (e/d ()
                              (pattern-fn-call->args)))))

  (define replace-adder-patterns-in-svex ((x sv::Svex-p)
                                          &key
                                          ((pattern-alist pattern-alist-p) 'pattern-alist)
                                          (adder-type 'adder-type)
                                          (track-column? 'track-column?)
                                          ((env) 'env)
                                          ((context rp-term-listp) 'context)
                                          ((config svl::svex-reduce-config-p) 'config)
                                          )
    :measure (sv::svex-count x)
    :returns res
    :verify-guards nil
    (sv::svex-case
     x
     :quote x
     :var   x
     :call
     (b* ((x (sv::svex-fix x))
          (pattern-fn-call-list (adder-pattern-match x adder-type))
          (pattern-fn-call (pull-the-first-applicable-adder-pattern
                            pattern-alist pattern-fn-call-list track-column?)))
       (cond
        (pattern-fn-call
         (b* (((pattern-fn-call x) pattern-fn-call))
           (pattern-call x
                         (replace-adder-patterns-in-svexlist x.args))))
        (t
         (sv::svex-call x.fn
                        (replace-adder-patterns-in-svexlist x.args)))))))

  (define replace-adder-patterns-in-svexlist ((lst sv::svexlist-p)
                                              &key
                                              ((pattern-alist pattern-alist-p) 'pattern-alist)
                                              (adder-type 'adder-type)
                                              (track-column? 'track-column?)
                                              ((env) 'env)
                                              ((context rp-term-listp) 'context)
                                              ((config svl::svex-reduce-config-p) 'config))
    :returns res
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        nil
      (hons (replace-adder-patterns-in-svex (car lst))
            (replace-adder-patterns-in-svexlist (cdr lst)))))

  ///

  (defthm svex-p-pattern-call
    (implies (and (pattern-fn-call-p x)
                  (or (not optional-args)
                      (sv::svexlist-p optional-args)))
             (sv::svex-p (PATTERN-CALL x optional-args)))
    :hints (("Goal"
             :in-theory (e/d (PATTERN-CALL
                              SV::SVEX-P
                              PATTERN-FN-CALL->FN
                              PATTERN-FN-CALL-P)
                             ()))))

  (defret-mutual svex-p-of-<fn>
    (defret svex-p-of-<fn>
      (implies (sv::Svex-p x)
               (sv::Svex-p res))
      :fn replace-adder-patterns-in-svex)
    (defret Svexlist-p-of-<fn>
      (implies (sv::Svexlist-p lst)
               (sv::Svexlist-p res))
      :fn replace-adder-patterns-in-svexlist))

  (verify-guards replace-adder-patterns-in-svex-fn)

  (memoize 'replace-adder-patterns-in-svex ;; :condition '(eq (sv::svex-kind x) :call)
           )

  (defret-mutual replace-adder-patterns-in-svex-is-correct
    (defret <fn>-is-correct
      (implies (and (force (sv::svex-p x))
                    (force (warrants-for-adder-pattern-match))

                    (force (rp::rp-term-listp context))
                    (force (rp::valid-sc env-term a))
                    (force (rp::eval-and-all context a))
                    (force (rp::falist-consistent-aux env env-term))
                    (force (svl::width-of-svex-extn-correct$-lst
                            (svl::svex-reduce-config->width-extns config)))
                    (force
                     (svl::integerp-of-svex-extn-correct$-lst
                      (svl::svex-reduce-config->integerp-extns config))))
               (equal (sv::svex-eval$ res (rp-evlt env-term a))
                      (sv::svex-eval$ x (rp-evlt env-term a))))
      :fn replace-adder-patterns-in-svex)
    (defret <fn>-is-correct
      (implies (and (force (sv::Svexlist-p lst))
                    (force (warrants-for-adder-pattern-match))
                    (force (rp::rp-term-listp context))
                    (force (rp::valid-sc env-term a))
                    (force (rp::eval-and-all context a))
                    (force (rp::falist-consistent-aux env env-term))
                    (force (svl::width-of-svex-extn-correct$-lst
                            (svl::svex-reduce-config->width-extns config)))
                    (force
                     (svl::integerp-of-svex-extn-correct$-lst
                      (svl::svex-reduce-config->integerp-extns config))))
               (equal (sv::svexlist-eval$ res (rp-evlt env-term a))
                      (sv::svexlist-eval$ lst (rp-evlt env-term a))))
      :fn replace-adder-patterns-in-svexlist)
    :hints (("Goal"
             :do-not-induct t
             :expand ((replace-adder-patterns-in-svex x )
                      (replace-adder-patterns-in-svexlist lst )
                      (:free (x y env)
                             (sv::Svex-eval$ (cons x y) env)))
             :in-theory (e/d (SV::SVEX-EVAL$
                              SV::SVEXlist-EVAL$
                              SV::FNSYM-FIX
                              sv::svex-kind
                              SV::SVEX-P
                              PATTERN-CALL
                              SV::SVEX-CALL->ARGS
                              SV::SVEX-CALL->fn
                              )
                             (adder-pattern-match-correct-pattern)))
            (and STABLE-UNDER-SIMPLIFICATIONP
                 '(:use ((:instance
                          adder-pattern-match-correct-pattern
                          (pattern (pull-the-first-applicable-adder-pattern
                                    pattern-alist (adder-pattern-match x adder-type)
                                    track-column?))
                          (svex x))))
                 ))))

(define replace-adder-patterns-in-svex-alist ((alist sv::svex-alist-p)
                                              &key
                                              ((pattern-alist pattern-alist-p) 'pattern-alist)
                                              (adder-type 'adder-type)
                                              (track-column? 'track-column?)

                                              ((env) 'env)
                                              ((context rp-term-listp) 'context)
                                              ((config svl::svex-reduce-config-p) 'config)
                                              )
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
  (if (atom alist)
      (progn$ (clear-memoize-table 'replace-adder-patterns-in-svex)
              nil)
    (acons (caar alist)
           (replace-adder-patterns-in-svex (cdar alist))
           (replace-adder-patterns-in-svex-alist (cdr alist))))
  ///
  (defret <fn>-is-correct
    (implies (and (force (sv::Svex-alist-p alist))
                  (force (warrants-for-adder-pattern-match))
                  (force (rp::rp-term-listp context))
                  (force (rp::valid-sc env-term a))
                  (force (rp::eval-and-all context a))
                  (force (rp::falist-consistent-aux env env-term))
                  (force (svl::width-of-svex-extn-correct$-lst
                          (svl::svex-reduce-config->width-extns config)))
                  (force
                   (svl::integerp-of-svex-extn-correct$-lst
                    (svl::svex-reduce-config->integerp-extns config))))
             (equal (sv::svex-alist-eval$ res (rp-evlt env-term a))
                    (sv::svex-alist-eval$ alist (rp-evlt env-term a))))
    :fn replace-adder-patterns-in-svex-alist
    :hints (("Goal"
             :in-theory (e/d (SV::SVEX-ALIST-EVAL$) ())))))

