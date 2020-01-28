
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

(include-book "../svex-eval-wog")

(fty::deftypes
 svexl-node
 :prepwork ((local
             (defthm integerp-implies-4vecp
               (implies (integerp x)
                        (4vec-p x))
               :hints (("Goal"
                        :in-theory (e/d (4vec-p) ())))))
            (local (defthm car-of-svar-when-consp
                     (implies (and (sv::svar-p x)
                                   (consp x)
                                   (syntaxp (quotep v)))
                              (equal (equal (car x) v)
                                     (equal v :var)))
                     :hints(("Goal" :in-theory (enable sv::svar-p)))))
            (local (defthm 4vec-not-svar-p
                     (implies (sv::svar-p x)
                              (not (4vec-p x)))
                     :hints(("Goal" :in-theory (enable 4vec-p sv::svar-p)))))
            (local (defthm cons-fnsym-not-svar-p
                     (implies (not (eq x :var))
                              (not (sv::svar-p (cons x y))))
                     :hints(("Goal" :in-theory (enable fnsym-p sv::svar-p))))))
 (fty::defflexsum
  svexl-node
  (:var
   :short "A variable, which represents a @(see 4vec)."
   :cond (if (atom x)
             (or (stringp x)
                 (and x (symbolp x)))
           (eq (car x) :var))
   :fields ((name :acc-body x :type sv::svar-p))
   :ctor-body name)
  (:quote
   :short "A ``quoted constant'' @(see 4vec), which represents itself."
   :cond (or (atom x)
             (eq (car x) 'quote))
   :shape (or (atom x) (and (consp (cdr x))
                            (consp (cadr x))
                            (not (cddr x))))
   :fields ((val :acc-body (if (atom x) x (cadr x))
                 :type 4vec))
   :ctor-body (if (atom val) val (hons 'quote (hons val nil))))
  (:node
   :cond (and (consp x)
              (consp (cdr x))
              (not (cddr x))
              (eq (car x) ':node))
   :fields ((node-id :acc-body (cadr x) :type natp))
   :ctor-body  (hons ':node (hons node-id nil)))
  (:call
   :short "A function applied to some expressions."
   :cond t
   :fields ((fn :acc-body (car x)
                :type sv::fnsym)
            (args :acc-body (cdr x)
                  :type svexl-nodelist))
   :ctor-body (hons fn args)))

 (fty::deflist svexl-nodelist
               :elt-type svexl-node
               :true-listp t))

(fty::defalist svexl-node-alist
               :key-type natp
               :val-type svexl-node
               :true-listp t)

(fty::defprod
 svexl
 ((top-node svexl-node)
  (node-alist svexl-node-alist)))

(fty::defprod
 svexllist
 ((top-nodelist svexl-nodelist)
  (node-alist svexl-node-alist)))

(define reuse-statsp (x)
  :enabled t
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (natp (cdar x))
         (svex-p (caar x))
         (reuse-statsp (cdr x)))))

(define nodesdb-p (x)
  :enabled t
  (reuse-statsp x)
  ///
  (defthm nodesdb-p-implies-reuse-statsp
    (implies (nodesdb-p x)
             (reuse-statsp x))))

(define reverse-nodesdb-p (x)
  :enabled t
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (natp (caar x))
         (svex-p (cdar x))
         (reverse-nodesdb-p (cdr x)))))

(define node-env-p (x)
  :measure (acl2-count x)
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (natp (caar x))
         (4vec-p (cdar x))
         (node-env-p (cdr x)))))

(acl2::defines
 svex-to-svexl-get-stats
 :prepwork
 ((local
   (in-theory (e/d (sv::svex-kind
                    sv::svexlist-p
                    sv::svex-p)
                   ())))

  (local
   (defthm lemma1
     (implies (and (hons-assoc-equal svex acc)
                   (reuse-statsp acc))
              (and (natp (+ 1 (cdr (hons-assoc-equal svex acc))))
                   (natp (cdr (hons-assoc-equal svex acc))))))))

 (define svex-to-svexl-get-stats ((acc reuse-statsp)
                                  (svex svex-p))
   :measure (sv::svex-count svex)
   :verify-guards nil
   :returns (res-acc reuse-statsp :hyp (and (reuse-statsp acc)
                                            (svex-p svex)))
   (sv::svex-case
    svex
    :var acc
    :quote acc
    :call (b* ((entry (hons-get svex acc)))
            (if entry
                (hons-acons svex (1+ (cdr entry)) acc)
              (svex-to-svexl-get-stats-lst (hons-acons svex 1 acc)
                                           svex.args)))))

 (define svex-to-svexl-get-stats-lst ((acc reuse-statsp)
                                      (lst sv::svexlist-p))
   :returns (res-acc reuse-statsp :hyp (and (reuse-statsp acc)
                                            (sv::svexlist-p lst)))
   :measure (sv::svexlist-count lst)
   (if (atom lst)
       acc
     (b* ((acc (svex-to-svexl-get-stats acc (car lst)))
          (acc (svex-to-svexl-get-stats-lst acc (cdr lst))))
       acc)))
 ///

 (verify-guards svex-to-svexl-get-stats))

(define should-be-an-svexl-node ((reuse-stats reuse-statsp)
                                 (svex svex-p))
  :inline t
  (b* ((reuse-stats-entry (hons-get svex reuse-stats)))
    (and reuse-stats-entry
         (> (cdr reuse-stats-entry) 1))))

(acl2::defines
 svex-to-svexl-aux
 :flag-defthm-macro defthm-svex-to-svexl-aux
 :flag-local nil
 :prepwork
 ((local
   (in-theory (e/d (svex-kind
                    sv::svexlist-p
                    svexl-node-p
                    svexl-node-alist-p
                    sv::svex-p)
                   (natp))))
  (local
   (defthm lemma1
     (implies (and (hons-assoc-equal svex nodesdb)
                   (reuse-statsp nodesdb))
              (natp (cdr (hons-assoc-equal svex nodesdb)))))))
 (define svex-to-svexl-aux ((svex svex-p)
                            (reuse-stats reuse-statsp)
                            (nodesdb nodesdb-p)
                            (svexl-node-alist svexl-node-alist-p)
                            (cnt natp))
   :guard (equal cnt (len svexl-node-alist))
   :verify-guards nil ;;verified below.
   :measure (sv::svex-count svex)
   :returns (mv (res-svex svexl-node-p
                          :hyp (and (svex-p svex)
                                    (nodesdb-p nodesdb)
                                    #|(natp cnt)||#))
                (nodesdb-res nodesdb-p
                             :hyp (and (svex-p svex)
                                       #|(natp cnt)||#
                                       (nodesdb-p nodesdb)))
                (svexl-res svexl-node-alist-p
                           :hyp (and (svex-p svex)
                                     (svexl-node-alist-p svexl-node-alist)
                                     (nodesdb-p nodesdb)
                                     #|(natp cnt)||#))
                (cnt-res natp #|:hyp||# #|(natp cnt)||#))
   (b* ((cnt (mbe :exec cnt
                  :logic (len svexl-node-alist))))
     (sv::svex-case
      svex
      :quote (mv svex nodesdb svexl-node-alist cnt)
      :var (mv svex nodesdb svexl-node-alist cnt)
      :call (b* ((nodesdb-entry (hons-get svex nodesdb))
                 ((when nodesdb-entry)
                  (mv (make-svexl-node-node :node-id (cdr nodesdb-entry))
                      nodesdb svexl-node-alist cnt))
                 ((mv rest-node nodesdb svexl-node-alist cnt)
                  (svex-to-svexl-aux-lst svex.args reuse-stats nodesdb svexl-node-alist cnt))
                 (cnt (mbe :exec cnt :logic (len svexl-node-alist)))
                 (new-node (make-svexl-node-call
                            :fn svex.fn
                            :args rest-node)))
              (if (should-be-an-svexl-node reuse-stats svex)
                  (mv (make-svexl-node-node :node-id cnt)
                      (hons-acons svex cnt nodesdb)
                      (hons-acons cnt new-node svexl-node-alist)
                      (1+ cnt))
                (mv new-node nodesdb svexl-node-alist cnt))))))

 (define svex-to-svexl-aux-lst ((lst svexlist-p)
                                (reuse-stats reuse-statsp)
                                (nodesdb nodesdb-p)
                                (svexl-node-alist svexl-node-alist-p)
                                (cnt natp))
   :measure (sv::svexlist-count lst)
   :returns (mv (res-svexlst svexl-nodelist-p
                             :hyp (and (svexlist-p lst)
                                       (nodesdb-p nodesdb)
                                       (natp cnt)))
                (nodesdb-res nodesdb-p
                             :hyp (and (svexlist-p lst)
                                       (natp cnt)
                                       (nodesdb-p nodesdb)))
                (svexl-res svexl-node-alist-p
                           :hyp (and (svexlist-p lst)
                                     (nodesdb-p nodesdb)
                                     (svexl-node-alist-p svexl-node-alist)
                                     (natp cnt)))
                (cnt-res natp :hyp (natp cnt)))
   :guard (equal cnt (len svexl-node-alist))
   (b* ((cnt (mbe :exec cnt
                  :logic (len svexl-node-alist))))
     (if (atom lst)
         (mv nil nodesdb svexl-node-alist cnt)
       (b* (((mv new-car-lst nodesdb svexl-node-alist cnt)
             (svex-to-svexl-aux
              (car lst) reuse-stats nodesdb svexl-node-alist cnt))
            (cnt (mbe :exec cnt
                      :logic (len svexl-node-alist)))
            ((mv new-cdr-lst nodesdb svexl-node-alist cnt)
             (svex-to-svexl-aux-lst
              (cdr lst) reuse-stats nodesdb svexl-node-alist cnt))
            (cnt (mbe :exec cnt
                      :logic (len svexl-node-alist))))
         (mv (cons new-car-lst
                   new-cdr-lst)
             nodesdb svexl-node-alist cnt)))))

 ///

 (local
  (defthm lemma2
    (implies (natp x)
             (rationalp x))))

 (defthm-svex-to-svexl-aux
   (defthm return-cnt-of-svex-to-svexl-aux
     (implies (equal (len svexl-node-alist) cnt)
              (equal (mv-nth 3 (svex-to-svexl-aux
                                svex reuse-stats nodesdb svexl-node-alist cnt))
                     (len (mv-nth 2 (svex-to-svexl-aux
                                     svex reuse-stats nodesdb svexl-node-alist cnt)))))
     :flag svex-to-svexl-aux)
   (defthm return-cnt-of-svex-to-svexl-aux-lst
     (implies (equal (len svexl-node-alist) cnt)
              (equal (mv-nth 3 (svex-to-svexl-aux-lst
                                lst reuse-stats nodesdb svexl-node-alist cnt))
                     (len (mv-nth 2 (svex-to-svexl-aux-lst
                                     lst reuse-stats nodesdb svexl-node-alist cnt)))))
     :flag svex-to-svexl-aux-lst))

 (verify-guards svex-to-svexl-aux))

(define svex-to-svexl ((svex svex-p))
  :returns (svexl svexl-p :hyp (svex-p svex))
  (b* ((svex (hons-copy svex))
       (reuse-stats (svex-to-svexl-get-stats nil svex))
       ((mv new-node nodesdb svexl-node-alist ?cnt)
        (svex-to-svexl-aux svex reuse-stats nil
                           nil 0))
       (- (fast-alist-free nodesdb))
       (- (fast-alist-free svexl-node-alist))
       (- (fast-alist-free reuse-stats))
       (svexl (make-svexl
               :top-node new-node
               :node-alist svexl-node-alist)))
    svexl))

(define svexlist-to-svexllist ((svexlist svexlist-p))
  :returns (svexl svexllist-p :hyp (svexlist-p svexlist))
  (b* ((svexlist (hons-copy svexlist))
       (reuse-stats (svex-to-svexl-get-stats-lst nil svexlist))
       ((mv new-node-lst nodesdb svexl-node-alist ?cnt)
        (SVEX-TO-SVEXL-AUX-LST svexlist reuse-stats nil
                               nil 0))
       (- (fast-alist-free nodesdb))
       (- (fast-alist-free svexl-node-alist))
       (- (fast-alist-free reuse-stats))
       (svexllist (make-svexllist
                   :top-nodelist new-node-lst
                   :node-alist svexl-node-alist)))
    svexllist))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Svexl to Svex functions (convert back)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defines
 svexl-node-to-svex
 :flag-local nil
 :flag-defthm-macro defthm-svexl-node-to-svex
 :prepwork
 ((local
   (in-theory (e/d ( ;svexl-node-kind
                    sv::svexlist-p
                    svexl-node-p
                    reverse-nodesdb-p
                    svexl-node-alist-p
                    sv::svex-p)
                   ())))
  (local
   (defthm lemma1
     (implies (and

               (hons-assoc-equal x
                                 reverse-nodesdb)
               (reverse-nodesdb-p reverse-nodesdb))
              (svex-p (cdr (hons-assoc-equal x
                                             reverse-nodesdb))))
     :hints (("Goal"
              :induct (reverse-nodesdb-p reverse-nodesdb)
              :do-not-induct t
              :in-theory (e/d () ())))))

  (local
   (defthm lemma2
     (implies (and (equal (svexl-node-kind x) :var)
                   (svexl-node-p x))
              (svex-p x))
     :hints (("Goal"
              :in-theory (e/d (svexl-node-p svex-p svexl-node-kind) ())))))

  (local
   (defthm lemma3
     (implies (and (equal (svexl-node-kind x) :quote)
                   (svexl-node-p x))
              (svex-p x))
     :hints (("Goal"
              :in-theory (e/d (svexl-node-p svex-p svexl-node-kind) ()))))))

 (define svexl-node-to-svex ((x svexl-node-p)
                             (reverse-nodesdb reverse-nodesdb-p))
   :measure (svexl-node-count x)
   :verify-guards nil
   :returns (res sv::svex-p :hyp (and (svexl-node-p x)
                                      (reverse-nodesdb-p reverse-nodesdb)))
   (svexl-node-case
    x
    :var x
    :quote x
    :node (b* ((node (hons-get x.node-id reverse-nodesdb)))
            (if node
                (cdr node)
              (list 'quote (sv::4vec-x))))
    :call (cons
           x.fn
           (svexl-nodelist-to-svexlist x.args
                                       reverse-nodesdb))))

 (define svexl-nodelist-to-svexlist ((lst svexl-nodelist-p)
                                     (reverse-nodesdb reverse-nodesdb-p))
   :returns (res sv::svexlist-p :hyp (and (svexl-nodelist-p lst)
                                          (reverse-nodesdb-p reverse-nodesdb)))
   :measure (svexl-nodelist-count lst)
   (if (atom lst)
       nil
     (cons (svexl-node-to-svex (car lst) reverse-nodesdb)
           (svexl-nodelist-to-svexlist (cdr lst) reverse-nodesdb))))

 ///

 (verify-guards svexl-node-to-svex))

(define svexl-to-svex-aux ((x svexl-node-alist-p))
  :verify-guards nil
  :prepwork
  ((local
    (in-theory (e/d (svexl-node-alist-p
                     node-env-p)
                    ()))))
  :returns (reverse-nodesdb reverse-nodesdb-p :hyp (svexl-node-alist-p x))
  (if (atom x)
      nil
    (b* ((reverse-nodesdb (svexl-to-svex-aux (cdr x)))
         (node-id (caar x))
         (node (cdar x))
         (res (svexl-node-to-svex node reverse-nodesdb)))
      (hons-acons node-id res reverse-nodesdb)))
  ///
  (verify-guards svexl-to-svex-aux))

(define svexl-to-svex ((svexl svexl-p))
  :returns (svex svex-p :hyp (svexl-p svexl))
  (b* ((node (svexl->top-node svexl))
       (node-alist (svexl->node-alist svexl))
       (reverse-nodesdb (svexl-to-svex-aux node-alist))
       (res (svexl-node-to-svex node reverse-nodesdb))
       (- (fast-alist-free reverse-nodesdb)))
    res))

(define svexllist-to-svexlist ((svexllist svexllist-p))
  :returns (svexlist svexlist-p :hyp (svexllist-p svexllist))
  (b* ((top-nodelist (svexllist->top-nodelist svexllist))
       (node-alist (svexllist->node-alist svexllist))
       (reverse-nodesdb (svexl-to-svex-aux node-alist))
       (res (svexl-nodelist-to-svexlist top-nodelist reverse-nodesdb))
       (- (fast-alist-free reverse-nodesdb)))
    res))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Eval functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defines
 svexl-node-eval
 :flag-local nil
 :flag-defthm-macro defthm-svexl-node-eval
 :prepwork
 ((local
   (in-theory (e/d (svexl-node-kind
                    svex-env-fastlookup-wog
                    sv::svexlist-p
                    svexl-node-p
                    svexl-node-alist-p
                    sv::svex-p)
                   ())))
  (local
   (defthm lemma1
     (implies (and (node-env-p node-env)
                   (hons-assoc-equal x node-env))
              (4vec-p (cdr (hons-assoc-equal x node-env))))
     :hints (("goal"
              :in-theory (e/d (node-env-p) ()))))))

 (define svexl-node-eval ((x svexl-node-p)
                          (node-env node-env-p)
                          (env sv::svex-env-p))
   :measure (svexl-node-count x)
   :verify-guards nil
   :returns (res sv::4vec-p :hyp (and (svexl-node-p x)
                                      (node-env-p node-env)
                                      (sv::svex-env-p env)))
   (svexl-node-case
    x
    :var (svex-env-fastlookup-wog x.name env)
    :quote x.val
    :node (svex-env-fastlookup-wog x.node-id node-env)
    :call (sv::svex-apply
           x.fn
           (svexl-nodelist-eval x.args
                                node-env
                                env))))

 (define svexl-nodelist-eval ((lst svexl-nodelist-p)
                              (node-env node-env-p)
                              (env sv::svex-env-p))
   :returns (res sv::4veclist-p :hyp (and (svexl-nodelist-p lst)
                                          (node-env-p node-env)
                                          (sv::svex-env-p env)))
   :measure (svexl-nodelist-count lst)
   (if (atom lst)
       nil
     (cons (svexl-node-eval (car lst) node-env env)
           (svexl-nodelist-eval (cdr lst) node-env env))))

 ///

 (verify-guards svexl-node-eval))

(define svexl-eval-aux ((x svexl-node-alist-p)
                        (env sv::svex-env-p))
  :verify-guards nil
  :prepwork
  ((local
    (in-theory (e/d (svexl-node-alist-p
                     node-env-p)
                    ()))))
  :returns (res-node-env node-env-p :hyp (and (svexl-node-alist-p x)
                                              (sv::svex-env-p env)))
  (if (atom x)
      nil
    (b* ((node-env (svexl-eval-aux (cdr x) env))
         (node-id (caar x))
         (node (cdar x))
         (eval-res (svexl-node-eval node node-env env)))
      (hons-acons node-id eval-res node-env)))
  ///
  (verify-guards svexl-eval-aux))

(define svexl-eval ((x svexl-p)
                    (env sv::svex-env-p))
  :returns (res sv::4vec-p :hyp (and (svexl-p x)
                                     (sv::svex-env-p env)))
  (b* ((node (svexl->top-node x))
       (node-alist (svexl->node-alist x))
       (node-env (svexl-eval-aux node-alist env))
       (res (svexl-node-eval node node-env env))
       (- (fast-alist-free node-env)))
    res))

(define svexllist-eval ((x svexllist-p)
                        (env sv::svex-env-p))
  :returns (res sv::4veclist-p :hyp (and (svexllist-p x)
                                         (sv::svex-env-p env)))
  (b* ((node-lst (svexllist->top-nodelist x))
       (node-alist (svexllist->node-alist x))
       (node-env (svexl-eval-aux node-alist env))
       (res (svexl-nodelist-eval node-lst node-env env))
       (- (fast-alist-free node-env)))
    res))

;; Example:
#|(b* ((svex #!SV'(bitor (bitand (bitor a b) (bitor (bitor a b)
                                                  (bitor a b)))
                       (bitor (bitor a b)
                              (bitor a b))))
     (env (make-fast-alist #!SV`((a . 12312321) (b . 331312312))))
     (svexl (svex-to-svexl svex)))
  `(('svex-eval ,(svex-eval svex env))
    ('svexl-eval ,(svexl-eval svexl env))
    ('svexl ,svexl)))||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Eval functions without guards:

(define svexl-node-kind-wog (x)
  :returns kind
  :inline t
  :guard-hints
  (("goal" :in-theory
    (disable fty::open-member-equal-on-list-of-tags))
   (and stable-under-simplificationp
        '(:expand ((svex-p x)))))
  :progn t
  (cond ((if (atom x)
             (or (stringp x) (and x (symbolp x)))
           (eq (car x) :var))
         :var)
        ((or (atom x) (eq (car x) 'quote))
         :quote)
        ((and (consp x)
              (consp (cdr x))
              (not (cddr x))
              (eq (car x) ':node))
         :node)
        (t :call)))

(def-rp-rule$ t nil
  svexl-node-kind-is-svexl-node-kind-wog
  (equal (svexl-node-kind x)
         (svexl-node-kind-wog x))
  :hints (("Goal"
           :in-theory (e/d (svexl-node-kind-wog
                            svexl-node-kind) ()))))

(defthmd svexl-node-kind-wog-is-svexl-node-kind
  (equal (svexl-node-kind-wog x)
         (svexl-node-kind x))
  :hints (("Goal"
           :in-theory (e/d (svexl-node-kind-wog
                            svexl-node-kind) ()))))

(acl2::defines
 svexl-node-eval-wog
 :flag-local nil
 :flag-defthm-macro defthm-svexl-node-eval-wog
 :prepwork
 ((local
   (in-theory (e/d (svexl-node-kind
                    sv::svexlist-p
                    svexl-node-p
                    svexl-node-alist-p
                    svexl-node-kind-wog-is-svexl-node-kind
                    sv::svex-p)
                   ()))))
 (define svexl-node-eval-wog ((x)
                              (node-env)
                              (env))
   :measure (acl2-count x)
   :verify-guards nil
   (b* ((kind (svexl-node-kind-wog x)))
     (cond ((eq kind :var)
            (svex-env-fastlookup-wog x env))
           ((eq kind :quote)
            (cond ((atom x) x)
                  ((atom (cdr x)) (sv::4vec-x))
                  (t (cadr x))))
           ((eq kind :node)
            (svex-env-fastlookup-wog (cadr x) node-env))
           (t
            (b* ((x.fn (car x))
                 (x.args (cdr x)))
              (svex-apply-wog
               x.fn
               (svexl-nodelist-eval-wog x.args node-env env)))))))

 (define svexl-nodelist-eval-wog ((lst)
                                  (node-env)
                                  (env))
   :measure (acl2-count lst)
   (if (atom lst)
       nil
     (cons (svexl-node-eval-wog (car lst) node-env env)
           (svexl-nodelist-eval-wog (cdr lst) node-env env))))

 ///

 ;; openers:
 (def-rp-rule svexl-eval-node-of-var
   (implies (eq (svexl-node-kind-wog x) ':var)
            (equal (svexl-node-eval-wog x node-env env-wires)
                   (let ((entry (hons-get x env-wires)))
                     (if entry (cdr entry)
                       (sv::4vec-x)))))
   :hints (("goal"
            :expand (svexl-node-eval-wog x node-env env-wires)
            :in-theory (e/d (svex-env-fastlookup-wog) ()))))

 (def-rp-rule svexl-eval-node-of-node
   (implies (eq (svexl-node-kind-wog x) ':node)
            (equal (svexl-node-eval-wog x node-env env-wires)
                   (let ((entry (hons-get (cadr x) node-env)))
                     (if entry (cdr entry)
                       (sv::4vec-x)))))
   :hints (("goal"
            :expand (svexl-node-eval-wog x node-env env-wires)
            :in-theory (e/d (svex-env-fastlookup-wog) ()))))

 (def-rp-rule svexl-eval-node-of-quoted
   (implies (eq (svexl-node-kind-wog x) ':quote)
            (equal (svexl-node-eval-wog x node-env env-wires)
                   (cond ((atom x) x)
                         ((atom (cdr x)) (sv::4vec-x))
                         (t (cadr x)))))
   :hints (("goal"
            :expand (svexl-node-eval-wog x node-env env-wires)
            :in-theory (e/d (svex-env-fastlookup-wog) ()))))

 (def-rp-rule svexl-eval-node-of-call
   (implies (eq (svexl-node-kind-wog x) ':call)
            (equal (svexl-node-eval-wog x node-env env)
                   (svex-apply-wog
                    (car x)
                    (svexl-nodelist-eval-wog (cdr x) node-env env))))
   :hints (("goal"
            :expand (svexl-node-eval-wog x node-env env)
            :in-theory (e/d (svex-env-fastlookup-wog) ()))))

 (def-rp-rule svexl-nodelist-eval-wog-of-cons
   (equal (svexl-nodelist-eval-wog (cons x rest) node-env env)
          (cons (svexl-node-eval-wog x node-env env)
                (svexl-nodelist-eval-wog rest node-env env)))
   :hints (("Goal"
            :expand (svexl-nodelist-eval-wog (cons x rest) node-env env)
            :in-theory (e/d () ()))))

 (def-rp-rule svexl-nodelist-eval-wog-of-nil
   (equal (svexl-nodelist-eval-wog nil node-env env)
          nil)
   :hints (("Goal"
            :expand (svexl-nodelist-eval-wog nil node-env env)
            :in-theory (e/d () ()))))

 (verify-guards svexl-node-eval-wog))

(defthm-svexl-node-eval-wog
  (defthm svexl-node-eval-is-svexl-node-eval-wog
    (implies (svexl-node-p x)
             (equal (svexl-node-eval x node-env env)
                    (svexl-node-eval-wog x node-env env)))
    :flag svexl-node-eval-wog)
  (defthm svexl-nodelist-eval-is-svexl-nodelist-eval-wog
    (implies (svexl-nodelist-p lst)
             (equal (svexl-nodelist-eval lst node-env env)
                    (svexl-nodelist-eval-wog lst node-env env)))
    :flag svexl-nodelist-eval-wog)
  :hints (("goal"
           :expand ((svexl-node-eval x node-env env))
           :in-theory (e/d (svex-call->fn
                            svexl-nodelist-fix
                            svexl-node-var->name
                            svexl-node-quote->val
                            svexl-node-call->args
                            svexl-nodelist-p
                            svexl-node-call->fn
                            svexl-node-node->node-id
                            svexl-node-p
                            svex-kind
                            svex-env-fastlookup-wog
                            svex-eval-wog
                            SVEX-APPLY-IS-SVEX-APPLY-WOG
                            svex-env-lookup-is-svex-env-fastlookup-wog
                            svexl-node-kind-wog-is-svexl-node-kind
                            svexlist-eval-wog
                            svexl-node-eval
                            svexl-node-kind
                            svexl-node-eval-wog
                            svex-p
                            sv::svar-p
                            svex-eval
                            svex-var->name
                            sv::svex-quote->val
                            svex-call->args
                            svexl-nodelist-eval
                            svexl-nodelist-eval-wog)
                           ()))))

(rp::add-rp-rule svexl-node-eval-is-svexl-node-eval-wog)
(rp::add-rp-rule svexl-nodelist-eval-is-svexl-nodelist-eval-wog)

(define svexl-eval-aux-wog ((x alistp)
                            (env))
  :prepwork
  ((local
    (in-theory (e/d (svexl-node-alist-p
                     node-env-p)
                    ()))))
  (if (atom x)
      nil
    (b* ((node-env
          (svexl-eval-aux-wog (cdr x) env))
         (node-id (caar x))
         (node (cdar x))
         (eval-res (svexl-node-eval-wog node node-env env)))
      (hons-acons node-id eval-res node-env)))
  ///

  (def-rp-rule$ t nil
    svexl-eval-aux-is-svexl-eval-aux-wog
    (implies (svexl-node-alist-p x)
             (equal (svexl-eval-aux x env)
                    (svexl-eval-aux-wog x env)))
    :hints (("Goal"
             :in-theory (e/d (svexl-eval-aux
                              svexl-eval-aux-wog) ()))))

  (rp::defthm-lambda
   svexl-eval-aux-wog-cons
   (equal (svexl-eval-aux-wog (cons (cons node-id node) rest) env)
          (b* ((node-env (svexl-eval-aux-wog rest env))
               (eval-res (svexl-node-eval-wog node node-env env)))
            (hons-acons node-id eval-res node-env))))

  (def-rp-rule
    svexl-eval-aux-wog-nil
    (equal (svexl-eval-aux-wog nil env)
           nil)))

(define svexl-eval-wog ((x svexl-p)
                        (env))
  (b* ((node (svexl->top-node x))
       (node-alist (svexl->node-alist x))
       (node-env (svexl-eval-aux-wog node-alist env))
       (res (svexl-node-eval-wog node node-env env))
       (- (fast-alist-free node-env)))
    res)
  ///

  (def-rp-rule$ t nil
    svexl-eval-is-svexl-eval-wog
    (implies (svexl-p x)
             (equal (svexl-eval x env)
                    (svexl-eval-wog x env)))
    :hints (("Goal"
             :in-theory (e/d (svexl-eval
                              svexl-eval-wog
                              SVEXL-EVAL-AUX-IS-SVEXL-EVAL-AUX-WOG)
                             ()))))

  (rp::defthm-lambda
   svexl-eval-wog-opener
   (equal (svexl-eval-wog x env)
          (b* ((node (svexl->top-node x))
               (node-alist (svexl->node-alist x))
               (node-env (svexl-eval-aux-wog node-alist env))
               (res (svexl-node-eval-wog node node-env env))
               (- (fast-alist-free node-env)))
            res))))

(define svexllist-eval-wog ((x svexllist-p)
                            (env))
  (b* ((node-lst (svexllist->top-nodelist x))
       (node-alist (svexllist->node-alist x))
       (node-env (svexl-eval-aux-wog node-alist env))
       (res (svexl-nodelist-eval-wog node-lst node-env env))
       (- (fast-alist-free node-env)))
    res)
  ///
  (def-rp-rule$ t nil
    svexllist-eval-is-svexllist-eval-wog
    (implies (svexllist-p x)
             (equal (svexllist-eval x env)
                    (svexllist-eval-wog x env)))
    :hints (("Goal"
             :in-theory (e/d (svexllist-eval
                              svexllist-eval-wog
                              SVEXL-EVAL-AUX-IS-SVEXL-EVAL-AUX-WOG)
                             ()))))

  (rp::defthm-lambda
   svexllist-eval-wog-opener
   (equal (svexllist-eval-wog x env)
          (b* ((node-lst (svexllist->top-nodelist x))
               (node-alist (svexllist->node-alist x))
               (node-env (svexl-eval-aux-wog node-alist env))
               (res (svexl-nodelist-eval-wog node-lst node-env env))
               (- (fast-alist-free node-env)))
            res))))

(defthm-svexl-node-eval-wog
  (defthm svex-p-implies-svexl-node-p
    (implies (svex-p x)
             (svexl-node-p x))
    :flag svexl-node-eval-wog)
  (defthm svexlist-p-implies-svexl-nodelist-p
    (implies (svexlist-p lst)
             (svexl-nodelist-p lst))
    :flag svexl-nodelist-eval-wog)
  :rule-classes :type-prescription
  :hints (("Goal"
           :in-theory (e/d (svex-p
                            svexl-node-kind-wog-is-svexl-node-kind
                            svexlist-p
                            svexl-nodelist-p
                            svexl-node-p
                            svexl-node-kind
                            svex-kind) ()))))
