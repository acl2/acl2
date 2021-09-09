
; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
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

(in-package "SVL")

(include-book "svexl")

;; a function to help with induction and be a bridge between functions.
(local
 (mutual-recursion
  (defun svex-induct1 (svex reuse-stats nodesdb node-env svexl-node-array env)
    (declare (xargs :measure (sv::svex-count svex)))
    (sv::svex-case
     svex
     :quote (mv svex.val svex nodesdb node-env svexl-node-array)
     :var (mv (sv::svex-env-fastlookup  svex.name env) svex nodesdb node-env svexl-node-array)
     :call (b* ((nodesdb-entry (hons-get svex nodesdb))
                ((when nodesdb-entry)
                 (mv
                  (svex-env-fastlookup-wog (cdr nodesdb-entry) node-env)
                  (make-svexl-node-node :node-id (cdr nodesdb-entry))
                  nodesdb
                  node-env
                  svexl-node-array))
                ((mv rest-result rest-node nodesdb node-env svexl-node-array)
                 (svexlist-induct1 svex.args reuse-stats nodesdb node-env svexl-node-array
                                   env))
                (cnt (len node-env))
                (new-node (make-svexl-node-call
                           :fn svex.fn
                           :args rest-node))
                (result (sv::svex-apply svex.fn rest-result)))

             (if (should-be-an-svexl-node reuse-stats svex)
                 (mv result
                     (make-svexl-node-node :node-id cnt)
                     (hons-acons svex cnt nodesdb)
                     (hons-acons cnt result node-env)
                     (hons-acons cnt new-node svexl-node-array))
               (mv result new-node nodesdb node-env svexl-node-array)))))

  (defun svexlist-induct1 (lst reuse-stats nodesdb node-env svexl-node-array env)
    (declare (xargs :measure (sv::svexlist-count lst)))
    (if (atom lst)
        (mv nil nil nodesdb node-env svexl-node-array)
      (b* (((mv new-car-lst new-car-node-lst nodesdb node-env svexl-node-array)
            (svex-induct1
             (car lst) reuse-stats nodesdb node-env svexl-node-array env))
           ((mv new-cdr-lst new-cdr-node-lst nodesdb node-env svexl-node-array)
            (svexlist-induct1
             (cdr lst) reuse-stats nodesdb node-env svexl-node-array env)))
        (mv (cons new-car-lst new-cdr-lst)
            (cons new-car-node-lst new-cdr-node-lst)
            nodesdb
            node-env
            svexl-node-array))))))

(local
 (make-flag svex-induct1 :defthm-macro-name defthm-svex-induct1))

;; an invariant; nodesdb and node-env is consistent.
(local
 (defun node-env-nodesdb-inv (nodesdb node-env env)
   (if (or (atom nodesdb)
           (atom node-env))
       (and (eq nodesdb nil)
            (eq node-env nil))
     (b* ((n1 (car nodesdb))
          (s1 (car node-env)))
       (and (consp n1)
            (consp s1)
            (equal (car s1) (cdr n1))
            (equal (car s1) (1- (len node-env)))
            (equal (svex-eval (car n1) env)
                   (cdr s1))
            (node-env-nodesdb-inv (cdr nodesdb)
                                  (cdr node-env)
                                  env))))))

(progn
  (local
   (defthmd svexl-induct1-inv1-lemma0
     (implies (and (node-env-nodesdb-inv nodesdb node-env env)
                   (hons-assoc-equal svex nodesdb)
                   (not (equal svex (caar nodesdb))))
              (> (cdar nodesdb)
                 (cdr (hons-assoc-equal svex nodesdb))))))

  (local
   (defthm svexl-induct1-inv1-lemma1
     (implies (and (node-env-nodesdb-inv nodesdb node-env env)
                   (not (equal svex (caar nodesdb)))
                   (consp nodesdb)
                   (hons-assoc-equal svex (cdr nodesdb)))
              (equal
               (equal (cdr (hons-assoc-equal svex (cdr nodesdb)))
                      (caar node-env))
               nil))
     :hints (("Goal"
              :do-not-induct t
              :expand ((node-env-nodesdb-inv NODESDB NODE-ENV ENV))
              :use ((:instance svexl-induct1-inv1-lemma0))
              :in-theory (e/d () ())))))

  (local
   (defthmd svexl-induct1-inv1-lemma
     (implies (and (node-env-nodesdb-inv nodesdb node-env env)
                   (svex-p svex)
                   (hons-assoc-equal svex nodesdb)
                   ;;(svex-env-p env)
                   )
              (equal (svex-eval svex env)
                     (svex-env-fastlookup-wog (cdr (hons-assoc-equal svex nodesdb))
                                              node-env)))
     :otf-flg t
     :hints (("Goal"
              :do-not-induct t
              :induct (node-env-nodesdb-inv nodesdb node-env env)
              :in-theory (e/d (svex-env-fastlookup-wog)
                              (svex-eval-is-svex-eval-wog)))
             ("Subgoal *1/3"
              :use ((:instance svexl-induct1-inv1-lemma1))))))

  #|(local
   (defthmd svexl-induct1-inv1-lemma-2
     (implies (and (node-env-nodesdb-inv nodesdb node-env env)
                   (svex-p svex)
                   (hons-assoc-equal svex nodesdb))
              (equal (svex-eval svex env)
                     (sv::svex-env-fastlookup (cdr (hons-assoc-equal svex nodesdb))
                                              node-env)))
     :otf-flg t
     :hints (("Goal"
              :do-not-induct t
              :induct (node-env-nodesdb-inv nodesdb node-env env)
              :in-theory (e/d (svex-env-fastlookup-wog
                               sv::svex-env-fastlookup)
                              (svex-eval-is-svex-eval-wog)))
             ("Subgoal *1/3"
              :use ((:instance svexl-induct1-inv1-lemma1))))))|#

  (local
   (defthm-svex-induct1
     (defthm svex-induct1-inv1
       (implies (and (svex-p svex)
                     ;;(svex-env-p env)
                     (node-env-nodesdb-inv nodesdb node-env env))
                (b* (((mv res ?node-res nodesdb-res node-env-res ?svexl-res)
                      (svex-induct1 svex reuse-stats nodesdb node-env svexl-node-array env)))
                  (and (node-env-nodesdb-inv nodesdb-res node-env-res env)
                       (equal res (svex-eval svex env)))))
       :flag svex-induct1)

     (defthm svexlist-induct1-inv1
       (implies (and (svexlist-p lst)
                     ;;(svex-env-p env)
                     (node-env-nodesdb-inv nodesdb node-env env))
                (b* (((mv res ?node-res nodesdb-res node-env-res ?svexl-res)
                      (svexlist-induct1 lst reuse-stats nodesdb node-env svexl-node-array env)))
                  (and (node-env-nodesdb-inv nodesdb-res node-env-res env)
                       (equal res (svexlist-eval lst env)))))
       :flag svexlist-induct1)
     :hints (("Goal"
              :in-theory (e/d (svex-eval
                               svexlist-eval
                               svexl-induct1-inv1-lemma
                               svex-env-lookup-is-svex-env-fastlookup-wog
                               )
                              (svex-eval-is-svex-eval-wog)))))))

(local
 (progn
   (defthm svex-to-svexl-aux-of-cnt
     (implies (syntaxp (equal cnt 'cnt))
              (equal (svex-to-svexl-aux svex reuse-stats nodesdb svexl-node-array cnt)
                     (svex-to-svexl-aux svex reuse-stats nodesdb svexl-node-array (len
                                                                                   svexl-node-array))))
     :hints (("Goal"
              :expand ((svex-to-svexl-aux svex reuse-stats nodesdb svexl-node-array cnt)
                       (svex-to-svexl-aux svex reuse-stats nodesdb svexl-node-array (len
                                                                                     svexl-node-array)))
              :in-theory (e/d () ()))))

   (defthm svex-to-svexl-aux-lst-of-cnt
     (implies (and (syntaxp (equal cnt 'cnt)))
              (equal (svex-to-svexl-aux-lst lst reuse-stats nodesdb svexl-node-array cnt)
                     (svex-to-svexl-aux-lst lst reuse-stats nodesdb svexl-node-array (len
                                                                                      svexl-node-array))))
     :hints (("Goal"
              :do-not-induct t
              :expand ((svex-to-svexl-aux-lst lst reuse-stats nodesdb svexl-node-array cnt)
                       (SVEX-TO-SVEXL-AUX-LST LST
                                              REUSE-STATS NODESDB svexl-node-array (LEN svexl-node-array)))
              :in-theory (e/d () ()))))))

(local
 (defthm-svex-induct1
   (defthm svex-to-svexl-aux--svex-induct-1
     (implies (and (svex-p svex)
                   ;;(svex-env-p env)
                   (equal (len node-env)
                          (len svexl-node-array))
                   (node-env-nodesdb-inv nodesdb node-env env))
              (b* (((mv new-node nodesdb-res svexl-res ?cnt-res)
                    (svex-to-svexl-aux svex reuse-stats nodesdb svexl-node-array cnt))
                   ((mv ?res-i new-node-i nodesdb-res-i node-env-res-i svexl-res-i)
                    (svex-induct1 svex reuse-stats nodesdb node-env svexl-node-array env)))
                (and (equal (len svexl-res-i)
                            (len node-env-res-i))
                     (equal cnt-res (len node-env-res-i))
                     (equal svexl-res svexl-res-i)
                     (equal nodesdb-res nodesdb-res-i)
                     (equal new-node new-node-i))))
     :flag svex-induct1)

   (defthm svex-to-svexl-aux-lst--svexlist-induct1
     (implies (and (svexlist-p lst)
                   ;;(svex-env-p env)
                   (equal (len node-env)
                          (len svexl-node-array))
                   (node-env-nodesdb-inv nodesdb node-env env))
              (b* (((mv new-node-lst nodesdb-res svexl-res ?cnt-res)
                    (svex-to-svexl-aux-lst lst reuse-stats nodesdb svexl-node-array cnt))
                   ((mv ?res-i new-node-lst-i nodesdb-res-i node-env-res-i svexl-res-i)
                    (svexlist-induct1 lst reuse-stats nodesdb node-env svexl-node-array env)))
                (and (equal (len svexl-res-i)
                            (len node-env-res-i))
                     (equal cnt-res (len node-env-res-i))
                     (equal svexl-res svexl-res-i)
                     (equal nodesdb-res nodesdb-res-i)
                     (equal new-node-lst new-node-lst-i))))
     :flag svexlist-induct1)

   :hints (("goal"
            :expand ((svex-to-svexl-aux-lst nil reuse-stats
                                            nodesdb svexl-node-array (len node-env))
                     (SVEX-TO-SVEXL-AUX-LST LST REUSE-STATS
                                            NODESDB svexl-node-array (LEN NODE-ENV))
                     (svex-to-svexl-aux svex reuse-stats
                                        nodesdb svexl-node-array (len node-env)))
            :in-theory (e/d () ()))
           ("Subgoal *1/6"
            :use ((:instance svex-induct1-inv1
                             (svex (car lst))))
            :in-theory (e/d () (svex-induct1-inv1))))))

(local
 (defun svexl-node-env-inv (svexl-node-array node-env env)
   (if (or (atom svexl-node-array)
           (atom node-env))
       (and (eq svexl-node-array nil)
            (eq node-env nil))
     (b* ((s (car svexl-node-array))
          (n (car node-env)))
       (and (consp s)
            (consp n)
            (equal (car s) (car n))
            (equal (car s) (1- (len svexl-node-array)))
            (equal (svexl-node-eval (cdr s) (cdr node-env) env)
                   (cdr n))
            (svexl-node-env-inv (cdr svexl-node-array) (cdr node-env) env))))))

(local
 (defthm svexl-and-node-env-inv-implies-lens
   (implies (svexl-node-env-inv svexl-node-array node-env env)
            (equal (len svexl-node-array)
                   (len node-env)))
   :rule-classes :forward-chaining))

(local
 (defthmd svex-fncs-to-svexl-node-fncs
   (implies (svex-p svex)
            (and (equal (svex-kind svex)
                        (svexl-node-kind svex))
                 (equal (svex-call->args svex)
                        (svexl-node-call->args svex))
                 (equal (svex-call->fn svex)
                        (svexl-node-call->fn svex))
                 (equal (sv::svex-quote->val svex)
                        (svexl-node-quote->val svex))
                 (equal (svex-var->name svex)
                        (svexl-node-var->name svex))))
   :hints (("Goal"
            :in-theory (e/d (svex-call->fn
                             SV::SVEX-QUOTE->VAL
                             SVEXL-NODE-QUOTE->VAL
                             svex-var->name
                             svexl-node-var->name
                             svexl-node-call->fn
                             svexl-node-call->args
                             svex-call->args
                             SVEX-KIND
                             SVEXL-NODE-KIND
                             svex-p) ())))))

(local
 (defthm svex-fncs-to-svexl-node-fncs-reverse
   (implies (svex-p svex)
            (and (equal (svexl-node-kind svex)
                        (svex-kind svex))
                 (equal (svexl-node-call->args svex)
                        (svex-call->args svex))
                 (equal (svexl-node-call->fn svex)
                        (svex-call->fn svex))
                 (equal (svexl-node-quote->val svex)
                        (sv::svex-quote->val svex))
                 (equal (svexl-node-var->name svex)
                        (svex-var->name svex))))
   :hints (("Goal"
            :in-theory (e/d (svex-fncs-to-svexl-node-fncs) ())))))

(local
 (defthm types-of-nodesdb-var
   (implies (node-env-nodesdb-inv nodesdb node-env env)
            (and (integer-listp (strip-cdrs nodesdb))
                 (nat-listp (strip-cdrs nodesdb))
                 (alistp nodesdb)))
   :rule-classes :forward-chaining))

(local
 (defthm integerp-of-integer-valued-alist
   (implies (and (nat-listp (strip-cdrs alist))
                 (hons-assoc-equal x alist))
            (and (integerp (cdr (hons-assoc-equal x alist)))
                 (<= 0 (integerp (cdr (hons-assoc-equal x alist))))
                 (natp (cdr (hons-assoc-equal x alist)))
                 (equal (nfix (cdr (hons-assoc-equal x alist)))
                        (cdr (hons-assoc-equal x alist)))))))

(local
 (defthm-svex-induct1
   (defthm return-type-of-svex-induct1
     (b* (((mv ?res ?new-node nodesdb-res ?node-env-res svexl-res)
           (svex-induct1 svex reuse-stats nodesdb node-env svexl-node-array env)))
       (and (implies (and (svex-p svex)
                          (svexl-node-array-p svexl-node-array)
                          (nodesdb-p nodesdb))
                     (svexl-node-array-p svexl-res))
            (implies (and (svex-p svex)
                          (nodesdb-p nodesdb))
                     (nodesdb-p nodesdb-res))
            (implies (and (svex-p svex)
                          (nodesdb-p nodesdb))
                     (svexl-node-p new-node))))
     :flag svex-induct1)

   (defthm return-type-of-svexlist-induct1
     (b* (((mv ?res ?new-node-lst ?nodesdb-res ?node-env-res svexl-res)
           (svexlist-induct1 lst reuse-stats nodesdb node-env svexl-node-array env)))
       (and (implies (and (svexlist-p lst)
                          (svexl-node-array-p svexl-node-array)
                          (nodesdb-p nodesdb))
                     (svexl-node-array-p svexl-res))
            (implies (and (svexlist-p lst)
                          (nodesdb-p nodesdb))
                     (nodesdb-p nodesdb-res))
            (implies (and (svexlist-p lst)
                          (nodesdb-p nodesdb))
                     (svexl-nodelist-p new-node-lst))))
     :flag svexlist-induct1)

   :hints (("goal"
            :in-theory (e/d ()
                            ())))))

(local
 (defthm nfix-of-len
   (equal (nfix (len x))
          (len x))))

(local
 (defthm svex-env-fastlookup-wog-lemma
   (equal (svex-env-fastlookup-wog id (cons (cons id val) rest))
          val)
   :hints (("goal"
            :in-theory (e/d (svex-env-fastlookup-wog) ())))))

(local
 (mutual-recursion
  (defun all-nodes-covered (x node-env)
    (declare (xargs :measure (svexl-node-count x)))
    (svexl-node-case x
                     :var t
                     :quote t
                     :node (and (hons-assoc-equal x.node-id node-env)
                                t)
                     :call
                     (all-nodes-covered-lst x.args node-env)))

  (defun all-nodes-covered-lst (lst node-env)
    (declare (xargs :measure (svexl-nodelist-count lst)))
    (if (atom lst)
        t
      (and (all-nodes-covered (car lst) node-env)
           (all-nodes-covered-lst (cdr lst) node-env))))))

(local
 (defun well-numbered-list-p (x)
   (if (atom x)
       (eq x nil)
     (and (equal (car x) (1- (len x)))
          (well-numbered-list-p (cdr x))))))

(local
 (defthm suffixp-lemma1
   (implies (and (suffixp small big)
                 (hons-assoc-equal x small))
            (hons-assoc-equal x big))
   :hints (("Goal"
            :in-theory (e/d (suffixp) ())))))

(local
 (defthm len-strip-cars/cdr
   (and (equal (len (strip-cars x))
               (len x))
        (equal (len (strip-cdrs x))
               (len x)))))

(local
 (defthm well-numbered-list-p-lemma1
   (implies (and (well-numbered-list-p (strip-cars big))
                 (<= (len big) size))
            (not (hons-assoc-equal size big)))
   :hints (("Goal"
            :in-theory (e/d () ())))))

(local
 (defthm all-nodes-covered-subsetp-equal-svexl-node-eval-lemma1
   (IMPLIES (AND ;;(SVEX-ENV-P ENV)
                 (HONS-ASSOC-EQUAL x NODE-ENV)
                 (suffixp NODE-ENV BIG)
                 (well-numbered-list-P (STRIP-CARS BIG)))
            (EQUAL (hons-assoc-equal x node-env)
                   (hons-assoc-equal x BIG)))
   :otf-flg t
   :hints (("Goal"
            :induct (STRIP-CARS BIG)
            :do-not-induct t
            :in-theory (e/d (suffixp
                             suffixp-lemma1
                             svex-env-fastlookup-wog) ())))))

(local
 (defthm all-nodes-covered-subsetp-equal-svexl-node-eval-lemma
   (implies (and ;;(svex-env-p env)
                 (hons-assoc-equal x node-env)
                 (suffixp node-env big)
                 (well-numbered-list-p (strip-cars big)))
            (equal (svex-env-fastlookup-wog x node-env)
                   (svex-env-fastlookup-wog x big)))
   :otf-flg t
   :hints (("goal"
            :do-not-induct t
            :in-theory (e/d (suffixp
                             suffixp-lemma1
                             svex-env-fastlookup-wog) ())))))

(local
 (defthm-svexl-node-eval
   (defthm all-nodes-covered-subsetp-equal-svexl-node-eval
     (implies (and (svexl-node-p x)
                   ;;(svex-env-p env)
                   (all-nodes-covered x node-env)
                   (suffixp node-env big)
                   (well-numbered-list-p (strip-cars big)))
              (equal (svexl-node-eval x node-env env)
                     (svexl-node-eval x big env)))
     :flag svexl-node-eval)
   (defthm all-nodes-covered-subsetp-equal-svexl-nodelist-eval
     (implies (and (svexl-nodelist-p lst)
                   ;;(svex-env-p env)
                   (all-nodes-covered-lst lst node-env)
                   (suffixp node-env big)
                   (well-numbered-list-p (strip-cars big)))
              (equal (svexl-nodelist-eval lst node-env env)
                     (svexl-nodelist-eval lst big env)))
     :flag svexl-nodelist-eval)
   :hints (("goal"
            :in-theory (e/d (svexl-nodelist-eval
                             svexl-node-eval)
                            (svexl-nodelist-eval-is-svexl-nodelist-eval-wog
                             svexl-node-eval-is-svexl-node-eval-wog))))))


(local
 (defthm-svexl-node-eval
   (defthm suffixp-all-nodes-covered
     (implies (and (svexl-node-p x)
                   (all-nodes-covered x node-env)
                   (suffixp node-env big))
              (all-nodes-covered x big))
     :flag svexl-node-eval)
   (defthm suffixp-all-nodes-covered-lst
     (implies (and (svexl-nodelist-p lst)
                   (all-nodes-covered-lst lst node-env)
                   (suffixp node-env big))
              (all-nodes-covered-lst lst big))
     :flag svexl-nodelist-eval)
   :hints (("goal"
            :in-theory (e/d (svexl-nodelist-eval
                             svexl-node-eval)
                            (svexl-nodelist-eval-is-svexl-nodelist-eval-wog
                             svexl-node-eval-is-svexl-node-eval-wog))))))

(local
 (defthm lemma1
   (implies (and (hons-assoc-equal svex nodesdb)
                 (svex-p svex)
                 ;;(svex-env-p env)
                 (nodesdb-p nodesdb)
                 (svexl-node-array-p svexl-node-array)
                 (svexl-node-env-inv svexl-node-array node-env env)
                 (well-numbered-list-p (strip-cars node-env))
                 (node-env-nodesdb-inv nodesdb node-env env))
            (hons-assoc-equal (cdr (hons-assoc-equal svex nodesdb))
                              node-env))))

(local
 (defthm-svex-induct1
   (defthm suffix-p-svex-to-svexl-aux-node-env
     (implies (and (svex-p svex)
                   ;;(svex-env-p env)
                   (nodesdb-p nodesdb)
                   (svexl-node-array-p svexl-node-array))
              (b* (((mv ?res ?new-node ?nodesdb-res node-env-res ?svexl-res)
                    (svex-induct1 svex reuse-stats nodesdb node-env svexl-node-array env)))
                (and (suffixp node-env node-env-res))))
     :flag svex-induct1)

   (defthm suffix-p-svex-to-svexl-aux-lst-node-env
     (implies (and (svexlist-p lst)
                   ;;(svex-env-p env)
                   (svexl-node-array-p svexl-node-array)
                   (nodesdb-p nodesdb))
              (b* (((mv ?res ?new-node-lst ?nodesdb-res node-env-res ?svexl-res)
                    (svexlist-induct1 lst reuse-stats nodesdb node-env svexl-node-array env)))
                (and (suffixp node-env node-env-res))))
     :flag svexlist-induct1)
   :otf-flg t
   :hints (("goal"
            :in-theory (e/d (svexl-nodelist-eval
                             suffixp
                             svexl-node-eval
                             svex-to-svexl-aux
                             svex-to-svexl-aux-lst)
                            (svexl-node-eval-is-svexl-node-eval-wog
                             svex-eval-is-svex-eval-wog
                             all-nodes-covered-subsetp-equal-svexl-nodelist-eval
                             nfix
                             natp
                             nodesdb-p
                             svexl-nodelist-eval-is-svexl-nodelist-eval-wog))))))

(local
 (defthm-svex-induct1
   (defthm svex-to-svexl-aux--svex-meval--svexl
     (implies (and (svex-p svex)
                   ;;(svex-env-p env)
                   (nodesdb-p nodesdb)
                   (svexl-node-array-p svexl-node-array)
                   (svexl-node-env-inv svexl-node-array node-env env)
                   (well-numbered-list-p (strip-cars node-env))
                   (node-env-nodesdb-inv nodesdb node-env env))
              (b* (((mv res new-node ?nodesdb-res node-env-res svexl-res)
                    (svex-induct1 svex reuse-stats nodesdb node-env svexl-node-array env)))
                (and (svexl-node-env-inv svexl-res node-env-res env)
                     (all-nodes-covered new-node node-env-res)
                     (well-numbered-list-p (strip-cars node-env-res))
                     (equal (svexl-node-eval new-node node-env-res env)
                            res))))
     :flag svex-induct1)

   (defthm svex-to-svexl-aux-lst--svexlist-meval--svexl
     (implies (and (svexlist-p lst)
                   ;;(svex-env-p env)
                   (svexl-node-array-p svexl-node-array)
                   (nodesdb-p nodesdb)
                   (svexl-node-env-inv svexl-node-array node-env env)
                   (well-numbered-list-p (strip-cars node-env))
                   (node-env-nodesdb-inv nodesdb node-env env))
              (b* (((mv res new-node-lst ?nodesdb-res node-env-res svexl-res)
                    (svexlist-induct1 lst reuse-stats nodesdb node-env svexl-node-array env)))
                (and (svexl-node-env-inv svexl-res node-env-res env)
                     (well-numbered-list-p (strip-cars node-env-res))
                     (all-nodes-covered-lst new-node-lst node-env-res)
                     (equal (svexl-nodelist-eval new-node-lst node-env-res env)
                            res))))
     :flag svexlist-induct1)
   :otf-flg t
   :hints (("goal"
            :in-theory (e/d (svexl-nodelist-eval
                             svexl-node-eval
                             svex-to-svexl-aux
                             svex-to-svexl-aux-lst)
                            (svexl-node-eval-is-svexl-node-eval-wog
                             svex-eval-is-svex-eval-wog
                             nfix
                             all-nodes-covered-subsetp-equal-svexl-node-eval
                             natp
                             nodesdb-p
                             svexl-nodelist-eval-is-svexl-nodelist-eval-wog)))
           ("subgoal *1/6"
            :use ((:instance all-nodes-covered-subsetp-equal-svexl-node-eval
                             (x (mv-nth 1
                                        (svex-induct1 (car lst)
                                                      reuse-stats nodesdb
                                                      node-env svexl-node-array env)))
                             (node-env (mv-nth 3
                                               (svex-induct1 (car lst)
                                                             reuse-stats nodesdb node-env svexl-node-array env)))
                             (big (mv-nth
                                   3
                                   (svexlist-induct1
                                    (cdr lst)
                                    reuse-stats
                                    (mv-nth 2
                                            (svex-induct1 (car lst)
                                                          reuse-stats nodesdb node-env svexl-node-array env))
                                    (mv-nth 3
                                            (svex-induct1 (car lst)
                                                          reuse-stats nodesdb node-env svexl-node-array env))
                                    (mv-nth 4
                                            (svex-induct1 (car lst)
                                                          reuse-stats nodesdb node-env svexl-node-array env))
                                    env)))))))))

(local
 (defthmd equal-cons-1
   (and (implies (consp x)
                 (equal (equal (cons a (cdr x)) x)
                        (equal a (car x))))
        (implies (consp x)
                 (equal (equal (cons (car x) y) x)
                        (equal y (cdr x)))))))

(local
 (defthm svexl-eval-aux--svexl-and-node-env-inv
   (implies (and (svexl-node-array-p svexl-node-array)
                 ;;(svex-env-p env)
                 (svexl-node-env-inv svexl-node-array node-env env))
            (equal (svexl-eval-aux svexl-node-array env)
                   node-env))
   :hints (("Goal"
            :induct (svexl-node-env-inv svexl-node-array node-env env)
            :do-not-induct t
            :in-theory (e/d (svexl-eval-aux
                             equal-cons-1)
                            (svexl-node-eval-is-svexl-node-eval-wog
                             svexl-eval-aux-is-svexl-eval-aux-wog))))))

(defthmd svexl-correct
  (implies (and (force (svex-p svex))
                ;;(force (svex-env-p env))
                )
           (equal (svex-eval svex env)
                  (svexl-eval (svex-to-svexl svex) env)))
  :hints (("Goal"
           :do-not-induct t
           :expand ((svex-to-svexl svex)
                    (:free (x rest)
                           (svexl-eval-aux (cons x rest) env)))
           :use ((:instance svex-to-svexl-aux--svex-induct-1
                            (reuse-stats (svex-to-svexl-get-stats nil svex))
                            (svex svex)
                            (env env)
                            (node-env nil)
                            (svexl-node-array nil)
                            (nodesdb nil)
                            (cnt 0))
                 (:instance svexl-eval-aux--svexl-and-node-env-inv
                            (svexl-node-array (mv-nth 2
                                                      (svex-to-svexl-aux svex (svex-to-svexl-get-stats nil svex)
                                                                         nil nil 0)))
                            (env env)
                            (node-env (MV-NTH 3
                                              (SVEX-INDUCT1 SVEX (SVEX-TO-SVEXL-GET-STATS NIL SVEX)
                                                            NIL NIL NIL ENV)))))
           :in-theory (e/d (svexl-eval)
                           (svexl-eval-is-svexl-eval-wog
                            svex-to-svexl-aux--svex-induct-1
                            svexl-eval-aux--svexl-and-node-env-inv
                            svexl-node-eval-is-svexl-node-eval-wog
                            return-cnt-of-svex-to-svexl-aux
                            svexl-eval-aux-is-svexl-eval-aux-wog
                            svex-eval-is-svex-eval-wog)))))

(defthmd svexllist-correct
  (implies (and (force (svexlist-p lst))
                ;;(force (svex-env-p env))
                )
           (equal (svexlist-eval lst env)
                  (svexllist-eval (svexlist-to-svexllist lst) env)))
  :hints (("Goal"
           :do-not-induct t
           :expand ((svexlist-to-svexllist lst)
                    (:free (x rest)
                           (svexl-eval-aux (cons x rest) env)))
           :use ((:instance svex-to-svexl-aux-lst--svexlist-induct1
                            (reuse-stats (svex-to-svexl-get-stats-lst nil lst))
                            (lst lst)
                            (env env)
                            (node-env nil)
                            (svexl-node-array nil)
                            (nodesdb nil)
                            (cnt 0))
                 (:instance svexl-eval-aux--svexl-and-node-env-inv
                            (svexl-node-array (mv-nth 2
                                                      (svex-to-svexl-aux-lst lst (svex-to-svexl-get-stats-lst nil lst)
                                                                             nil nil 0)))
                            (env env)
                            (node-env (MV-NTH 3
                                              (svexlist-induct1 lst (svex-to-svexl-get-stats-lst nil lst)
                                                                nil nil nil env)))))
           :in-theory (e/d (svexl-eval
                            svexllist-eval)
                           (svexl-eval-is-svexl-eval-wog
                            svexl-nodelist-eval-is-svexl-nodelist-eval-wog
                            svex-to-svexl-aux--svex-induct-1
                            svex-to-svexl-aux-lst--svexlist-induct1
                            svexl-eval-aux--svexl-and-node-env-inv
                            svexl-node-eval-is-svexl-node-eval-wog
                            return-cnt-of-svex-to-svexl-aux
                            svexl-eval-aux-is-svexl-eval-aux-wog
                            svex-eval-is-svex-eval-wog)))))

(rp::add-rp-rule svexl-correct :disabled t)
(rp::add-rp-rule svexllist-correct :disabled t)

(encapsulate
  nil

  (local
   (defun svexl-node-alist-eval-alt (alist node-env env)
     (b* ((keys (strip-cars alist))
          (lst (strip-cdrs alist))
          (eval-lst (svexl-nodelist-eval lst node-env env)))
       (pairlis$ keys eval-lst))))

  (local
   (defthm svexl-node-alist-eval-redef
     (implies t
              (equal (svexl-node-alist-eval alist node-env env)
                     (svexl-node-alist-eval-alt alist node-env env)))
     :hints (("Goal"
              :in-theory (e/d (svexl-node-alist-eval
                               SVEXL-NODELIST-EVAL
                               SVEXL-NODE-ALIST-P)
                              (SVEXL-NODE-ALIST-EVAL-IS-SVEXL-NODE-ALIST-EVAL-WOG
                               SVEXL-NODELIST-EVAL-IS-SVEXL-NODELIST-EVAL-WOG))))))

  (local
   (defun svex-alist-eval-alt (alist env)
     (b* ((keys (strip-cars alist))
          (lst (strip-cdrs alist))
          (eval-lst (sv::svexlist-eval lst env)))
       (pairlis$ keys eval-lst))))

  (local
   (defthm svex-alist-eval-redef
     (implies (sv::svex-alist-p alist)
              (equal (sv::svex-alist-eval alist  env)
                     (svex-alist-eval-alt alist  env)))
     :hints (("Goal"
              :in-theory (e/d (svexl-node-alist-eval
                               SVEXLIST-EVAL
                               sv::svex-alist-eval)
                              ())))))

  (defthm svexl-node-alist-p-of-pairlis$
    (implies (and (equal (len x) (len y))
                  (sv::svarlist-p x)
                  (svexl-nodelist-p y))
             (svexl-node-alist-p (pairlis$ x y)))
    :hints (("Goal"
             :in-theory (e/d (svexl-node-alist-p
                              sv::svarlist-p
                              svexl-nodelist-p)
                             ()))))

  (local
   (defthm sv::svex-alist-p-and-strip-fncs
     (implies (SV::SVEX-ALIST-P alist)
              (and (sv::svarlist-p (strip-cars alist))
                   (svexlist-p (strip-cdrs alist))))))

  (local
   (defthm strip-cars/cdrs-of-pairlis$
     (and (implies (true-listp x)
                   (equal (strip-cars (pairlis$ x y))
                          x))
          (implies (and (equal (len x) (len y))
                        (true-listp y))
                   (equal (strip-cdrs (pairlis$ x y))
                          y)))))

  (defthmd svexl-alist-correct
    (implies (and (force (sv::svex-alist-p alist))
                  ;;(force (svex-env-p env))
                  )
             (equal (sv::svex-alist-eval alist env)
                    (svexl-alist-eval (svex-alist-to-svexl-alist alist) env)))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance svex-to-svexl-aux-lst--svexlist-induct1
                              (reuse-stats (svex-to-svexl-get-stats-lst nil (STRIP-CDRS ALIST)))
                              (lst (STRIP-CDRS ALIST))
                              (env env)
                              (node-env nil)
                              (svexl-node-array nil)
                              (nodesdb nil)
                              (cnt 0))
                   (:instance svexl-eval-aux--svexl-and-node-env-inv
                              (svexl-node-array (mv-nth 2
                                                        (svex-to-svexl-aux-lst
                                                         (STRIP-CDRS ALIST)
                                                         (svex-to-svexl-get-stats-lst nil (STRIP-CDRS ALIST))
                                                         nil nil 0)))
                              (env env)
                              (node-env (MV-NTH 3
                                                (svexlist-induct1 (STRIP-CDRS
                                                                   ALIST)
                                                                  (svex-to-svexl-get-stats-lst nil (STRIP-CDRS ALIST))
                                                                  nil nil nil env)))))
             :in-theory (e/d (sv::svex-alist-eval
                              sv::svex-alist-p
                              svexlist-eval
                              svexl-correct
                              SVEX-ALIST-TO-SVEXL-ALIST
                              svexl-alist-eval)
                             (svexl-eval-is-svexl-eval-wog
                              svexl-eval-aux--svexl-and-node-env-inv
                              svex-to-svexl-aux-lst--svexlist-induct1
                              svexllist-correct
                              svexl-nodelist-eval-is-svexl-nodelist-eval-wog
                              svex-to-svexl-aux--svex-induct-1
                              svex-to-svexl-aux-lst--svexlist-induct1
                              svexl-eval-aux--svexl-and-node-env-inv
                              svexl-node-eval-is-svexl-node-eval-wog
                              return-cnt-of-svex-to-svexl-aux
                              svexl-eval-aux-is-svexl-eval-aux-wog
                              svex-eval-is-svex-eval-wog)))))

  (rp::add-rp-rule svexl-alist-correct :disabled t))
