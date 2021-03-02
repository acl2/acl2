
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
                     :hints(("Goal" :in-theory (enable fnsym-p sv::svar-p)))))
            (local (defthm car-of-4vec-fix-integerp
                      (implies (consp (4vec-fix x))
                               (integerp (car (4vec-fix x))))
                      :hints(("Goal" :in-theory (enable 4vec-fix 4vec)))))
            (local (defthm car-of-4vec-fix-type
                      (or (integerp (car (4vec-fix x)))
                          (not (car (4vec-fix x))))
                      :hints(("Goal" :in-theory (enable 4vec-fix 4vec)))
                      :rule-classes ((:type-prescription :typed-term (car (4vec-fix x)))))))
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
             (integerp (car x)))
   :fields ((val :acc-body x
                 :type 4vec))
   :ctor-body val)
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

(fty::defalist svexl-node-array
               :key-type natp
               :val-type svexl-node
               :true-listp t)

(fty::defalist svexl-node-alist
               :key-type sv::svar-p
               :val-type svexl-node
               :true-listp t)

(fty::defprod
 svexl
 ((top-node svexl-node)
  (node-array svexl-node-array)))

(fty::defprod
 svexllist
 ((top-nodelist svexl-nodelist)
  (node-array svexl-node-array)))

(fty::defprod
 svexl-alist
 ((top-node-alist svexl-node-alist)
  (node-array svexl-node-array)))

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
                    svexl-node-array-p
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
                            (svexl-node-array svexl-node-array-p)
                            (cnt natp))
   :guard (equal cnt (len svexl-node-array))
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
                (svexl-res svexl-node-array-p
                           :hyp (and (svex-p svex)
                                     (svexl-node-array-p svexl-node-array)
                                     (nodesdb-p nodesdb)
                                     #|(natp cnt)||#))
                (cnt-res natp #|:hyp||# #|(natp cnt)||#))
   (b* ((cnt (mbe :exec cnt
                  :logic (len svexl-node-array))))
     (sv::svex-case
      svex
      :quote (mv svex nodesdb svexl-node-array cnt)
      :var (mv svex nodesdb svexl-node-array cnt)
      :call (b* ((nodesdb-entry (hons-get svex nodesdb))
                 ((when nodesdb-entry)
                  (mv (make-svexl-node-node :node-id (cdr nodesdb-entry))
                      nodesdb svexl-node-array cnt))
                 ((mv rest-node nodesdb svexl-node-array cnt)
                  (svex-to-svexl-aux-lst svex.args reuse-stats nodesdb svexl-node-array cnt))
                 (cnt (mbe :exec cnt :logic (len svexl-node-array)))
                 (new-node (make-svexl-node-call
                            :fn svex.fn
                            :args rest-node)))
              (if (should-be-an-svexl-node reuse-stats svex)
                  (mv (make-svexl-node-node :node-id cnt)
                      (hons-acons svex cnt nodesdb)
                      (hons-acons cnt new-node svexl-node-array)
                      (1+ cnt))
                (mv new-node nodesdb svexl-node-array cnt))))))

 (define svex-to-svexl-aux-lst ((lst svexlist-p)
                                (reuse-stats reuse-statsp)
                                (nodesdb nodesdb-p)
                                (svexl-node-array svexl-node-array-p)
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
                (svexl-res svexl-node-array-p
                           :hyp (and (svexlist-p lst)
                                     (nodesdb-p nodesdb)
                                     (svexl-node-array-p svexl-node-array)
                                     (natp cnt)))
                (cnt-res natp :hyp (natp cnt)))
   :guard (equal cnt (len svexl-node-array))
   (b* ((cnt (mbe :exec cnt
                  :logic (len svexl-node-array))))
     (if (atom lst)
         (mv nil nodesdb svexl-node-array cnt)
       (b* (((mv new-car-lst nodesdb svexl-node-array cnt)
             (svex-to-svexl-aux
              (car lst) reuse-stats nodesdb svexl-node-array cnt))
            (cnt (mbe :exec cnt
                      :logic (len svexl-node-array)))
            ((mv new-cdr-lst nodesdb svexl-node-array cnt)
             (svex-to-svexl-aux-lst
              (cdr lst) reuse-stats nodesdb svexl-node-array cnt))
            (cnt (mbe :exec cnt
                      :logic (len svexl-node-array))))
         (mv (cons new-car-lst
                   new-cdr-lst)
             nodesdb svexl-node-array cnt)))))

 ///

 (local
  (defthm lemma2
    (implies (natp x)
             (rationalp x))))

 (defthm-svex-to-svexl-aux
   (defthm return-cnt-of-svex-to-svexl-aux
     (implies (equal (len svexl-node-array) cnt)
              (equal (mv-nth 3 (svex-to-svexl-aux
                                svex reuse-stats nodesdb svexl-node-array cnt))
                     (len (mv-nth 2 (svex-to-svexl-aux
                                     svex reuse-stats nodesdb svexl-node-array cnt)))))
     :flag svex-to-svexl-aux)
   (defthm return-cnt-of-svex-to-svexl-aux-lst
     (and
      (true-listp (mv-nth 0 (svex-to-svexl-aux-lst
                             lst reuse-stats nodesdb svexl-node-array cnt)))
      (equal (len (mv-nth 0 (svex-to-svexl-aux-lst
                             lst reuse-stats nodesdb svexl-node-array cnt)))
             (len lst))
     (implies (equal (len svexl-node-array) cnt)
              (equal (mv-nth 3 (svex-to-svexl-aux-lst
                                lst reuse-stats nodesdb svexl-node-array cnt))
                     (len (mv-nth 2 (svex-to-svexl-aux-lst
                                     lst reuse-stats nodesdb svexl-node-array cnt))))))
     :flag svex-to-svexl-aux-lst))

 (verify-guards svex-to-svexl-aux))

(define svex-to-svexl ((svex svex-p))
  :returns (svexl svexl-p :hyp (svex-p svex))
  (b* ((svex (hons-copy svex))
       (reuse-stats (svex-to-svexl-get-stats nil svex))
       ((mv new-node nodesdb svexl-node-array ?cnt)
        (svex-to-svexl-aux svex reuse-stats nil
                           nil 0))
       (- (fast-alist-free nodesdb))
       (- (fast-alist-free svexl-node-array))
       (- (fast-alist-free reuse-stats))
       (svexl (make-svexl
               :top-node new-node
               :node-array svexl-node-array)))
    svexl))

(define svexlist-to-svexllist ((svexlist svexlist-p))
  :returns (svexl svexllist-p :hyp (svexlist-p svexlist))
  (b* ((svexlist (hons-copy svexlist))
       (reuse-stats (svex-to-svexl-get-stats-lst nil svexlist))
       ((mv new-node-lst nodesdb svexl-node-array ?cnt)
        (svex-to-svexl-aux-lst svexlist reuse-stats nil
                               nil 0))
       (- (fast-alist-free nodesdb))
       (- (fast-alist-free svexl-node-array))
       (- (fast-alist-free reuse-stats))
       (svexllist (make-svexllist
                   :top-nodelist new-node-lst
                   :node-array svexl-node-array)))
    svexllist))

(define svex-alist-to-svexl-alist ((svex-alist sv::svex-alist-p))

  :prepwork
  ((local
    (defthm lemma1
      (implies (and (sv::svarlist-p svarlist)
                    (svexl-nodelist-p nodelist)
                    (equal (len svarlist)
                           (len nodelist)))
               (svexl-node-alist-p (pairlis$ svarlist nodelist)))
      :hints (("Goal"
               :induct (pairlis$ svarlist nodelist)
               :in-theory (e/d (svexl-node-alist-p
                                svexl-nodelist-p
                                sv::svarlist-p)
                               ())))))
   (local
    (defthm lemma2
      (implies (SV::SVEX-ALIST-P SVEX-ALIST)
               (and (EQUAL (LEN (STRIP-CARS SVEX-ALIST))
                           (LEN (STRIP-CDRS SVEX-ALIST)))
                    (SV::SVARLIST-P (STRIP-CARS SVEX-ALIST))
                    (SVEXLIST-P (STRIP-CDRS SVEX-ALIST))))
      :hints (("Goal"
               :in-theory (e/d (SV::SVEX-ALIST-P
                                SVEXLIST-P
                                SV::SVARLIST-P)
                               ()))))))
  :guard-hints (("Goal"
                 :do-not-induct t
                 :in-theory (e/d () ())))
  :returns (svexl-alist svexl-alist-p :hyp (sv::svex-alist-p svex-alist))
  (b* ((keys (strip-cars svex-alist))
       (svexlist (strip-cdrs svex-alist))
       (svexlist (hons-copy svexlist))
       (reuse-stats (svex-to-svexl-get-stats-lst nil svexlist))
       ((mv new-node-lst nodesdb svexl-node-array ?cnt)
        (svex-to-svexl-aux-lst svexlist reuse-stats nil
                               nil 0))
       (top-node-alist (pairlis$ keys new-node-lst))
       (- (fast-alist-free nodesdb))
       (- (fast-alist-free svexl-node-array))
       (- (fast-alist-free reuse-stats))
       (svexl-alist (make-svexl-alist
                   :top-node-alist top-node-alist
                   :node-array svexl-node-array)))
    svexl-alist))

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
                    svexl-node-array-p
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
              (svex-p (svexl-node-quote->val x)))
     :hints (("Goal"
              :in-theory (e/d (svexl-node-p svex-p svexl-node-quote->val 4vec-p svexl-node-kind) ())))))
  )

 (define svexl-node-to-svex ((x svexl-node-p)
                             (reverse-nodesdb reverse-nodesdb-p))
   :measure (svexl-node-count x)
   :verify-guards nil
   :returns (res sv::svex-p :hyp (and (svexl-node-p x)
                                      (reverse-nodesdb-p reverse-nodesdb)))
   (svexl-node-case
    x
    :var x
    :quote x.val
    :node (b* ((node (hons-get x.node-id reverse-nodesdb)))
            (if node
                (cdr node)
              (sv::4vec-x)))
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

(define svexl-to-svex-aux ((x svexl-node-array-p))
  :verify-guards nil
  :prepwork
  ((local
    (in-theory (e/d (svexl-node-array-p
                     node-env-p)
                    ()))))
  :returns (reverse-nodesdb reverse-nodesdb-p :hyp (svexl-node-array-p x))
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
       (node-array (svexl->node-array svexl))
       (reverse-nodesdb (svexl-to-svex-aux node-array))
       (res (svexl-node-to-svex node reverse-nodesdb))
       (- (fast-alist-free reverse-nodesdb)))
    res))

(define svexllist-to-svexlist ((svexllist svexllist-p))
  :returns (svexlist svexlist-p :hyp (svexllist-p svexllist))
  (b* ((top-nodelist (svexllist->top-nodelist svexllist))
       (node-array (svexllist->node-array svexllist))
       (reverse-nodesdb (svexl-to-svex-aux node-array))
       (res (svexl-nodelist-to-svexlist top-nodelist reverse-nodesdb))
       (- (fast-alist-free reverse-nodesdb)))
    res))


(define svexl-alist-to-svex-alist ((svexl-alist svexl-alist-p))
  :returns (svex-alist sv::svex-alist-p :hyp (svexl-alist-p svexl-alist))
  :prepwork
  ((local
    (progn
      (defthm lemma1
        (IMPLIES
         (SVEXL-NODE-ALIST-P node-alist)
         (SVEXL-NODELIST-P (STRIP-CDRS node-alist)))
        :hints (("Goal"
                 :in-theory (e/d (SVEXL-NODE-ALIST-P SVEXL-NODELIST-P)
                                 ()))))
   
      (defthm lemma2
        (implies (svexl-node-alist-p alist)
                 (and (SV::SVARLIST-P (STRIP-CARS alist))
                      (SVEXL-NODELIST-P (STRIP-CDRS alist))))
        :hints (("Goal"
                 :in-theory (e/d (svexl-node-alist-p) ()))))
   
      (defthm len-of-svexl-nodelist-to-svexlist
        (equal (len (svexl-nodelist-to-svexlist lst r))
               (len lst))
        :hints (("Goal"
                 :induct (len lst)
                 :in-theory (e/d (svexl-nodelist-to-svexlist) ()))))

      (defthm len-of-strip-cars
        (equal (len (strip-cars x))
               (len x)))

      (defthm len-of-strip-cdrs
        (equal (len (strip-cdrs x))
               (len x))))))
   
  (b* ((top-node-alist (svexl-alist->top-node-alist svexl-alist))
       (node-array (svexl-alist->node-array svexl-alist))
       (reverse-nodesdb (svexl-to-svex-aux node-array))
       (top-nodelist (strip-cdrs top-node-alist))
       (keys (strip-cars top-node-alist))
       (res (svexl-nodelist-to-svexlist top-nodelist reverse-nodesdb))
       (- (fast-alist-free reverse-nodesdb)))
    (pairlis$ keys res)))

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
                    svexl-node-array-p
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

(define svexl-node-alist-eval ((alist svexl-node-alist-p)
                               (node-env node-env-p)
                               (env sv::svex-env-p))
  :returns (res sv::svex-env-p :hyp (and (svexl-node-alist-p alist)
                                         (node-env-p node-env)
                                         (sv::svex-env-p env)))
  (if (atom alist)
      nil
    (acons (caar alist)
           (svexl-node-eval (cdar alist)
                            node-env env)
           (svexl-node-alist-eval (cdr alist)
                                  node-env
                                  env))))

(define svexl-eval-aux ((x svexl-node-array-p)
                        (env sv::svex-env-p))
  :verify-guards nil
  :prepwork
  ((local
    (in-theory (e/d (svexl-node-array-p
                     node-env-p)
                    ()))))
  :returns (res-node-env node-env-p :hyp (and (svexl-node-array-p x)
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
       (node-array (svexl->node-array x))
       (node-env (svexl-eval-aux node-array env))
       (res (svexl-node-eval node node-env env))
       (- (fast-alist-free node-env)))
    res))

(define svexllist-eval ((x svexllist-p)
                        (env sv::svex-env-p))
  :returns (res sv::4veclist-p :hyp (and (svexllist-p x)
                                         (sv::svex-env-p env)))
  (b* ((node-lst (svexllist->top-nodelist x))
       (node-array (svexllist->node-array x))
       (node-env (svexl-eval-aux node-array env))
       (res (svexl-nodelist-eval node-lst node-env env))
       (- (fast-alist-free node-env)))
    res))

(define svexl-alist-eval ((x svexl-alist-p)
                          (env sv::svex-env-p))
  :returns (res sv::svex-env-p :hyp (and (svexl-alist-p x)
                                         (sv::svex-env-p env)))
  (b* ((top-node-alist (svexl-alist->top-node-alist x))
       (node-array (svexl-alist->node-array x))
       (node-env (svexl-eval-aux node-array env))
       (res (svexl-node-alist-eval top-node-alist node-env env))
       (- (fast-alist-free node-env)))
    res))

;; Example:
#|
(b* ((svex #!SV'(bitor (bitand (bitor a b) (bitor (bitor a b)
                                                  (bitor a b)))
                       (bitor (bitor a b)
                              (bitor a b))))
     (env (make-fast-alist #!SV`((a . 12312321) (b . 331312312))))
     (svexl (svex-to-svexl svex)))
  `((svex-eval ,(svex-eval svex env))
    (svexl-eval ,(svexl-eval svexl env))
    (svexl ,svexl)))||#

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
        ((or (atom x) (integerp (car x)))
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
                    svexl-node-array-p
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
           ((eq kind :quote) x)
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
                   x))
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


(define svexl-node-alist-eval-wog ((alist alistp)
                                  (node-env)
                                  (env))
   :measure (acl2-count alist)
   (if (atom alist)
       nil
     (acons
      (caar alist)
      (svexl-node-eval-wog (cdar alist) node-env env)
      (svexl-node-alist-eval-wog (cdr alist) node-env env)))
   ///
   (def-rp-rule svexl-node-alist-eval-wog-of-cons
     (equal (svexl-node-alist-eval-wog (cons x rest) node-env env)
            (acons
             (car x)
             (svexl-node-eval-wog (cdr x) node-env env)
             (svexl-node-alist-eval-wog rest node-env env)))
     :hints (("Goal"
              :expand (svexl-node-alist-eval-wog (cons x rest) node-env env)
              :in-theory (e/d () ()))))

   (def-rp-rule svexl-node-alist-eval-wog-of-nil
     (equal (svexl-node-alist-eval-wog nil node-env env)
            nil)
   :hints (("Goal"
            :expand (svexl-node-alist-eval-wog nil node-env env)
            :in-theory (e/d () ()))))
   )

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

(def-rp-rule svexl-node-alist-eval-is-svexl-node-alist-eval-wog
  (implies (svexl-node-alist-p alist)
           (equal (svexl-node-alist-eval alist node-env env)
                  (svexl-node-alist-eval-wog alist node-env env)))
  :hints (("Goal"
           :in-theory (e/d (svexl-node-alist-eval
                            svexl-node-alist-p
                            svexl-node-alist-eval-wog)
                           ()))))

(define svexl-eval-aux-wog ((x alistp)
                            (env))
  :prepwork
  ((local
    (in-theory (e/d (svexl-node-array-p
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
    (implies (svexl-node-array-p x)
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
       (node-array (svexl->node-array x))
       (node-env (svexl-eval-aux-wog node-array env))
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

  (set-ignore-ok t)
  (add-rp-rule svexl-eval-wog :beta-reduce t))


(define svexllist-eval-wog ((x svexllist-p)
                            (env))
  (b* ((node-lst (svexllist->top-nodelist x))
       (node-array (svexllist->node-array x))
       (node-env (svexl-eval-aux-wog node-array env))
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
  (set-ignore-ok t)
  (add-rp-rule svexllist-eval-wog :beta-reduce t))


(define svexl-alist-eval-wog ((x svexl-alist-p)
                              (env))
  (b* ((top-node-alist (svexl-alist->top-node-alist x))
       (node-array (svexl-alist->node-array x))
       (node-env (svexl-eval-aux-wog node-array env))
       (res (svexl-node-alist-eval-wog top-node-alist node-env env))
       (- (fast-alist-free node-env)))
    res)
  ///
  (def-rp-rule$ t nil
    svexl-alist-eval-is-svexl-alist-eval-wog
    (implies (svexl-alist-p x)
             (equal (svexl-alist-eval x env)
                    (svexl-alist-eval-wog x env)))
    :hints (("Goal"
             :in-theory (e/d (svexl-alist-eval
                              svexl-alist-eval-wog
                              svexl-node-alist-eval-is-svexl-node-alist-eval-wog
                              SVEXL-EVAL-AUX-IS-SVEXL-EVAL-AUX-WOG)
                             ()))))
  (set-ignore-ok t)
  (add-rp-rule svexl-alist-eval-wog :beta-reduce t))

(memoize 'svexl-alist-p)
(memoize 'svexllist-p)
(memoize 'svexl-p)


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
