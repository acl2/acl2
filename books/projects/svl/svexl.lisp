
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

(include-book "svex-eval-wog")

(fty::deftypes
 svexl
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
   :fields ((node-cnt :acc-body (cadr x) :type natp))
   :ctor-body `(:node ,node-cnt))
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

(fty::defalist svexl
               :key-type natp
               :val-type svexl-node
               :true-listp t)

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
   :measure (acl2-count svex)
   :verify-guards nil
   :returns (res-acc reuse-statsp :hyp (and (reuse-statsp acc)
                                            (svex-p svex)))
   (b* ((kind (sv::svex-kind svex)))
     (cond
      ((or (eq kind :var)
           (eq kind :quote))
       acc)
      (t
       (b* ((entry (hons-get svex acc)))
         (if entry
             (hons-acons svex (1+ (cdr entry)) acc)
           (svex-to-svexl-get-stats-lst (hons-acons svex 1 acc)
                                        (cdr svex))))))))
 (define svex-to-svexl-get-stats-lst ((acc reuse-statsp)
                                      (lst sv::svexlist-p))
   :returns (res-acc reuse-statsp :hyp (and (reuse-statsp acc)
                                            (sv::svexlist-p lst)))
   :measure (acl2-count lst)
   (if (atom lst)
       acc
     (b* ((acc (svex-to-svexl-get-stats acc (car lst)))
          (acc (svex-to-svexl-get-stats-lst acc (cdr lst))))
       acc)))
 ///

 (verify-guards svex-to-svexl-get-stats))

(acl2::defines
 svex-to-svexl-aux
 :prepwork
 ((local
   (in-theory (e/d (sv::svex-kind
                    sv::svexlist-p
                    SVEXL-NODE-P
                    svexl-p
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
                            (svexl svexl-p)
                            (cnt natp))
   :verify-guards nil
   :measure (acl2-count svex)
   :returns (mv (res-svex svexl-node-p
                          :hyp (and (svex-p svex)
                                    (nodesdb-p nodesdb)
                                    (natp cnt)))
                (nodesdb-res nodesdb-p
                             :hyp (and (svex-p svex)
                                       (natp cnt)
                                       (nodesdb-p nodesdb)))
                (svexl-res svexl-p
                           :hyp (and (svex-p svex)
                                     (svexl-p svexl)
                                     (nodesdb-p nodesdb)
                                     (natp cnt)))
                (cnt-res natp :hyp (natp cnt)))
   (b* ((kind (sv::svex-kind svex)))
     (cond
      ((or (eq kind :var)
           (eq kind :quote))
       (mv svex nodesdb svexl cnt))
      (t (b* ((nodesdb-entry (hons-get svex nodesdb))
              ((when nodesdb-entry)
               (mv `(:node ,(cdr nodesdb-entry))
                   nodesdb svexl cnt))
              (reuse-stats-entry (hons-get svex reuse-stats))
              (should-be-a-node (and reuse-stats-entry
                                     (> (cdr reuse-stats-entry) 1)))
              ((mv rest-svex nodesdb svexl cnt)
               (svex-to-svexl-aux-lst (cdr svex) reuse-stats nodesdb svexl
                                      cnt))
              (new-svex (cons (car svex) rest-svex)))
           (if should-be-a-node
               (mv `(:node ,cnt)
                   (hons-acons svex cnt nodesdb)
                   (hons-acons cnt new-svex svexl)
                   (1+ cnt))
             (mv new-svex
                 nodesdb
                 svexl
                 cnt)))))))

 (define svex-to-svexl-aux-lst ((lst svexlist-p)
                                (reuse-stats reuse-statsp)
                                (nodesdb nodesdb-p)
                                (svexl svexl-p)
                                (cnt natp))
   :measure (acl2-count lst)
   :returns (mv (res-svexlst svexl-nodelist-p
                             :hyp (and (svexlist-p lst)
                                       (nodesdb-p nodesdb)
                                       (natp cnt)))
                (nodesdb-res nodesdb-p
                             :hyp (and (svexlist-p lst)
                                       (natp cnt)
                                       (nodesdb-p nodesdb)))
                (svexl-res svexl-p
                           :hyp (and (svexlist-p lst)
                                     (nodesdb-p nodesdb)
                                     (svexl-p svexl)
                                     (natp cnt)))
                (cnt-res natp :hyp (natp cnt)))
   (if (atom lst)
       (mv lst nodesdb svexl cnt)
     (b* (((mv new-car-lst nodesdb svexl cnt)
           (svex-to-svexl-aux
            (car lst) reuse-stats nodesdb svexl cnt))
          ((mv new-cdr-lst nodesdb svexl cnt)
           (svex-to-svexl-aux-lst
            (cdr lst) reuse-stats nodesdb svexl cnt)))
       (mv (cons new-car-lst
                 new-cdr-lst)
           nodesdb svexl cnt))))

 ///

 (local
  (defthm lemma2
    (implies (natp x)
             (rationalp x))))

 (verify-guards svex-to-svexl-aux))

(define svex-to-svexl ((svex svex-p))
  :returns (svexl svexl-p :hyp (svex-p svex))
  (b* ((svex (hons-copy svex))
       (reuse-stats (svex-to-svexl-get-stats nil svex))
       ((mv new-svex nodesdb svexl cnt) (svex-to-svexl-aux svex reuse-stats nil
                                                           nil 0))
       (- (fast-alist-free nodesdb))
       (- (fast-alist-free svexl))
       (- (fast-alist-free reuse-stats))
       (svexl (acons cnt new-svex svexl)))
    svexl))


(define node-env-fastlookup
  ((var natp)
   (env node-env-p
        "must be a @(see fast-alist)."))
  :enabled t
  (let ((look (hons-get var env)))
    (if look (cdr look)
      (sv::4vec-x))))

(acl2::defines
 svexl-node-eval
 :prepwork
 ((local
   (in-theory (e/d (svexl-node-kind
                    sv::svexlist-p
                    SVEXL-NODE-P
                    svexl-p
                    sv::svex-p)
                   ())))
  (local
   (defthm lemma1
     (IMPLIES (AND (NODE-ENV-P NODE-ENV)
                   (HONS-ASSOC-EQUAL x NODE-ENV))
              (4VEC-P (CDR (HONS-ASSOC-EQUAL x NODE-ENV))))
     :hints (("Goal"
              :in-theory (e/d (NODE-ENV-P) ()))))))

 (define svexl-node-eval ((x svexl-node-p)
                          (node-env node-env-p)
                          (env sv::svex-env-p))
   :measure (acl2-count x)
   :verify-guards nil
   :returns (res sv::4vec-p :hyp (and (svexl-node-p x)
                                      (node-env-p node-env)
                                      (sv::svex-env-p env)))
   (b* ((kind (svexl-node-kind x)))
     (cond ((eq kind :var)
            (sv::svex-env-fastlookup x env))
           ((eq kind :quote)
            (cond ((atom x) x)
                  ((atom (cdr x)) (sv::4vec-x))
                  (t (cadr x))))
           ((eq kind :node)
            (node-env-fastlookup (cadr x) node-env))
           (t
            (b* ((x.fn (car x))
                 (x.args (cdr x)))
              (sv::svex-apply
               x.fn
               (svexl-node-eval-lst x.args
                                    node-env
                                    env)))))))
 (define svexl-node-eval-lst ((lst svexl-nodelist-p)
                              (node-env node-env-p)
                              (env sv::svex-env-p))
   :returns (res sv::4veclist-p :hyp (and (svexl-nodelist-p lst)
                                          (node-env-p node-env)
                                          (sv::svex-env-p env)))
   :measure (acl2-count lst)
   (if (atom lst)
       nil
     (cons (svexl-node-eval (car lst) node-env env)
           (svexl-node-eval-lst (cdr lst) node-env env))))

 ///

 (verify-guards svexl-node-eval))


(define svexl-eval-aux ((x svexl-p)
                    (env sv::svex-env-p))
  :verify-guards nil
  :prepwork
  ((local
    (in-theory (e/d (svexl-p
                     node-env-p)
                    ()))))
  :returns (mv (res-node-env node-env-p :hyp (and (svexl-p x)
                                                  (sv::svex-env-p env)))
               (res sv::4vec-p :hyp (and (svexl-p x)
                                         (sv::svex-env-p env))))
  (if (atom x)
      (mv nil (sv::4vec-x))
    (b* (((mv node-env &)
          (svexl-eval-aux (cdr x) env))
         (node-cnt (caar x))
         (node (cdar x))
         (eval-res (svexl-node-eval node node-env env)))
      (mv (hons-acons node-cnt eval-res node-env)
          eval-res)))
  ///
  (verify-guards svexl-eval-aux))


(define svexl-eval ((x svexl-p)
                         (env sv::svex-env-p))
  (b* (((mv node-env res)
        (svexl-eval-aux x env))
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


;; ;; Final theorem to be proved.
;; (skip-proofs
;;  (defthm svex-eval-is-svexl-eval
;;    (implies (and (sv::svex-p svex)
;;                  (sv::svex-env-p env))
;;             (equal (svex-eval svex env)
;;                    (svexl-eval (svex-to-svexl svex) env)))))
