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

(include-book "../svex-eval-wog-openers")
(include-book "../svexl/svexl")

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (in-theory (enable hons-get)))

(define nth-term (n argsvar)
  :guard (natp n)
  (if (atom argsvar)
      ''nil
    (if (zp n)
        (car argsvar)
        (nth-term (1- n) (cdr argsvar)))))

(define nth-4vec (n argsvar)
  :guard (natp n)
  (if (atom argsvar)
      (SV::4VEC-X)
      (if (zp n)
          (car argsvar)
          (nth-4vec (1- n) (cdr argsvar)))))


(define quoted-4vec-listp (lst)
  (if (atom lst)
      (equal lst nil)
      (and (consp (car lst))
           (consp (cdar lst))
           (acl2::fquotep (car lst))
           (sv::4vec-p (unquote (car lst)))
           (quoted-4vec-listp (cdr lst)))))

(local
 (defthm nth-term-opener
   (implies (natp n)
            (equal (nth-term n argsvar)
                   (if (atom argsvar)
                       ''nil
                       (if (zp n)
                           (car argsvar)
                           (nth-term (1- n) (cdr argsvar))))))
   :hints (("Goal"
            :in-theory (e/d (nth-term) ())))))

(local
 (defthm nth-opener
   (implies (natp n)
            (equal (nth n argsvar)
                   (if (atom argsvar)
                       nil
                       (if (zp n)
                           (car argsvar)
                           (nth (1- n) (cdr argsvar))))))
   :hints (("Goal"
            :in-theory (e/d (nth) ())))))

(local
 (defthm nth-4vec-opener
     (implies (natp n)
              (equal (nth-4vec n argsvar)
                     (if (atom argsvar)
                         (SV::4VEC-X)
                         (if (zp n)
                             (car argsvar)
                             (nth-4vec (1- n) (cdr argsvar))))))
   :hints (("Goal"
            :in-theory (e/d (nth-4vec) ())))))

(local
 (defthm QUOTED-4VEC-LISTP-lemma
     (implies (and (quoted-4vec-listp lst)
                   (consp lst))
              (and (consp (car lst))
                   (consp (cdar lst))
                   (acl2::fquotep (car lst))
                   (sv::4vec-p (unquote (car lst)))
                   (quoted-4vec-listp (cdr lst))
                   (4VEC-P (CAR (RP::UNQUOTE-ALL lst)))))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (quoted-4vec-listp
                             RP::UNQUOTE-ALL)
                            ())))))


(defund svex-apply-collect-args-wog-meta (n max argsvar args-dontrw)
  (declare (xargs :measure (nfix (- (nfix max) (nfix n)))))
  (let* ((n (nfix n)) (max (nfix max)))
    (if (zp (- max n))
        (mv nil nil nil)
      (b* (((mv rest1 rest2 rest-dontrw)
            (svex-apply-collect-args-wog-meta
             (+ 1 n) max argsvar args-dontrw)))
        (mv (cons `(nth-4vec ,n ,argsvar) rest1)
            (cons `(nth-term ,n ,argsvar) rest2)
            (cons `(nth-term ,n ,args-dontrw) rest-dontrw))))))

(defund svex-apply-cases-wog-fn-meta (argsvar args-dontrw optable)
  (b* (((when (atom optable))
        '((otherwise
           (mv (or (hard-error
                    'svex-apply-cases-wog-fn-meta
                    "attempting to apply unknown function ~x0~%"
                    (list (cons #\0 fn)))
                   (list 'quote (sv::4vec-x)))
            nil))))
       ((list sym fn args) (car optable))
       ((mv entry-for-quoted entry entry-dontrw)
        (svex-apply-collect-args-wog-meta 0 (len args) argsvar args-dontrw))
       (call
        `(if quoted
             (mv (list 'quote (,fn . ,entry-for-quoted)) t)
             (mv (list ',fn . ,entry)
                 (list 'nil . ,entry-dontrw)))))
    (cons (cons sym (cons call 'nil))
          (svex-apply-cases-wog-fn-meta argsvar args-dontrw (cdr optable)))))

(defmacro svex-apply-cases-wog-meta (fn args args-dontrw)
  `(b* ((quoted (quoted-4vec-listp args))
        (args (if quoted (rp::unquote-all args) args)))
   (case ,fn
     ,@(svex-apply-cases-wog-fn-meta args args-dontrw
                                     (cons '(ID sv::4VEC-FIX$INLINE (ACL2::X)
                                             "identity function") ;; had to
                                           ;; change this because 4vec-fix is
                                           ;; the only function that is inlined
                                           (cdr sv::*svex-op-table*))))))

(defund svex-apply-wog-meta (fn args args-dontrw)
    (declare (xargs :guard (and (true-listp args)
                                (true-listp args-dontrw))
                    :verify-guards nil))
    (let* ((fn (fnsym-fix fn)))
      (svex-apply-cases-wog-meta fn args args-dontrw)))


(local
 (defthm true-listp-of-unquote-all
     (implies (true-listp x)
              (true-listp (rp::unquote-all x)))))


(local
 (defthm QUOTED-4VEC-LISTP-implies-4vec-listp-when-unquoted
     (implies (and (QUOTED-4VEC-LISTP ARGS))
              (sv::4veclist-p (rp::unquote-all args)))
   :hints (("Goal"
            :in-theory (e/d (QUOTED-4VEC-LISTP) ())))))

(verify-guards svex-apply-wog-meta
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d () ()))))

(acl2::defines
 svex-eval-wog-meta
 :flag-defthm-macro defthm-svex-eval-wog-meta
 :flag-local nil
 :prepwork ((local
             (in-theory (enable svex-kind-wog))))
 (define svex-eval-wog-meta (x env-falist good-env-flg)
   :flag expr
   :measure (cons-count x)
   :hints (("Goal"
            :in-theory (e/d (svex-kind
                             measure-lemmas) ())))
   :verify-guards nil
   :returns (mv (result)
                (result-dont-rw rp::dont-rw-syntaxp))
   (let* ((x.kind (svex-kind-wog x)))
     (case
       x.kind
       (:quote (mv (list 'quote x)
                   t))
       (:var (if good-env-flg
                 (mv (let* ((val (hons-get x env-falist)))
                       (if val
                           (cdr val)
                         (list 'quote (sv::4vec-x))))
                     t)
               (mv `(svex-env-fastlookup-wog ',x ,env-falist)
                   (if (atom (rp::ex-from-rp env-falist))
                       t
                     `(nil t t)))))
       (otherwise
        (b* ((x.fn (car x))
             (x.args (cdr x))
             ((mv args args-dontrw)
              (svex-eval-wog-meta-lst x.args env-falist good-env-flg)))
          (svex-apply-wog-meta x.fn args args-dontrw))))))

 (define svex-eval-wog-meta-lst (lst env-falist good-env-flg)
   :flag list
   :measure (cons-count lst)
   :returns (mv (res true-listp)
                (res-dontrw rp::dont-rw-syntaxp))
   (if (atom lst)
       (mv nil nil)
     (b* (((mv car-term car-dontrw)
           (svex-eval-wog-meta (car lst) env-falist good-env-flg))
          ((mv rest rest-dontrw)
           (svex-eval-wog-meta-lst (cdr lst) env-falist good-env-flg)))
       (mv (cons car-term rest)
           (cons car-dontrw rest-dontrw)))))

 ///

 (acl2::more-returns
  svex-eval-wog-meta-lst
  (res-dontrw true-listp
              :hints (("Goal"
                       :induct (true-listp lst)
                       :in-theory (e/d () ())))))

 (verify-guards svex-eval-wog-meta
   :hints (("Goal"
            :in-theory (e/d (svex-kind) ())))))

(define svex-eval-wog-meta-main (term)
  (case-match term
    (('svex-eval-wog ('quote svex) env)
     (b* ((env-orig env)
          (env (rp::ex-from-rp env)))
       (case-match env
         (('falist ('quote env-falist) &)
          (svex-eval-wog-meta svex env-falist t))
         (''nil
          (svex-eval-wog-meta svex nil t))
         (&
          (svex-eval-wog-meta svex env-orig nil)))))
    (& (mv term nil))))

(acl2::defines
 svexl-node-eval-wog-meta
 :flag-defthm-macro defthm-svexl-node-eval-wog-meta
 :flag-local nil
 :prepwork ((local
             (in-theory (enable svexl-node-kind))))
 (define svexl-node-eval-wog-meta (x node-env-falist env-falist good-env-flg)
   :flag expr
   :measure (cons-count x)
   :hints (("Goal"
            :in-theory (e/d (svexl-node-kind-wog
                             measure-lemmas) ())))
   :verify-guards nil
   :returns (mv (result)
                (result-dont-rw rp::dont-rw-syntaxp))
   (let* ((x.kind (svexl-node-kind-wog x)))
     (case
       x.kind
       (:quote (mv (list 'quote x)
                   t))
       (:var (if good-env-flg
                 (mv (let* ((val (hons-get x env-falist)))
                       (if val
                           (cdr val)
                         (list 'quote (sv::4vec-x))))
                     t)
               (mv `(svex-env-fastlookup-wog ',x ,env-falist)
                   (if (atom (rp::ex-from-rp env-falist))
                       t
                     `(nil t t)))))
       (:node (if good-env-flg
                  (mv (let* ((val (hons-get (cadr x) node-env-falist)))
                        (if val
                            (cdr val)
                          (list 'quote (sv::4vec-x))))
                      t)
                (mv `(svex-env-fastlookup-wog ',(cadr x) ,node-env-falist)
                    (if (atom (rp::ex-from-rp node-env-falist))
                        t
                      `(nil t t)))))
       (otherwise
        (b* ((x.fn (car x))
             (x.args (cdr x))
             ((mv args args-dontrw)
              (svexl-nodelist-eval-wog-meta x.args node-env-falist env-falist good-env-flg)))
          (svex-apply-wog-meta x.fn args args-dontrw))))))

 (define svexl-nodelist-eval-wog-meta (lst node-env-falist env-falist good-env-flg)
   :flag list
   :measure (cons-count lst)
   :returns (mv (res true-listp)
                (res-dontrw rp::dont-rw-syntaxp))
   (if (atom lst)
       (mv nil nil)
     (b* (((mv car-term car-dontrw)
           (svexl-node-eval-wog-meta (car lst) node-env-falist env-falist good-env-flg))
          ((mv rest rest-dontrw)
           (svexl-nodelist-eval-wog-meta (cdr lst) node-env-falist env-falist good-env-flg)))
       (mv (cons car-term rest)
           (cons car-dontrw rest-dontrw)))))

 ///

 (acl2::more-returns
  svexl-nodelist-eval-wog-meta
  (res-dontrw true-listp
              :hints (("Goal"
                       :induct (true-listp lst)
                       :in-theory (e/d () ())))))

 (verify-guards svexl-node-eval-wog-meta
   :hints (("Goal"
            :in-theory (e/d (svexl-node-kind-wog) ())))))

(define svexl-node-eval-wog-meta-main (term)
  (case-match term
    (('svexl-node-eval-wog ('quote svex) node-env env)
     (b* ((env-orig env)
          (env (rp::ex-from-rp env))
          (node-env-orig node-env)
          (node-env (rp::ex-from-rp node-env)))
       (case-match env
         (('falist ('quote env-falist) &)
          (case-match node-env
            (('falist ('quote node-env-falist) &)
             (svexl-node-eval-wog-meta svex node-env-falist env-falist t))
            (''nil
             (svexl-node-eval-wog-meta svex nil env-falist t))
            (& (svexl-node-eval-wog-meta svex node-env-orig env-orig nil))))
         (''nil
          (case-match node-env
            (('falist ('quote node-env-falist) &)
             (svexl-node-eval-wog-meta svex node-env-falist nil t))
            (''nil
             (svexl-node-eval-wog-meta svex nil nil t))
            (& (svexl-node-eval-wog-meta svex node-env-orig env-orig nil))))
         (&
          (svexl-node-eval-wog-meta svex node-env-orig env-orig nil)))))
    (& (mv term nil))))


;; (svex-eval-wog-meta '(partsel '0 '1 (bitand x y))
;;                  (make-fast-alist
;;                   '((x . (rp 'bitp a))
;;                     (y . b)))
;;                  'expr)

;; (svex-eval-wog-meta-main `(svex-eval-wog '(partsel '0 '1 (bitand x y))
;;                                    (falist ',(make-fast-alist
;;                                               '((x . (rp 'bitp a))
;;                                                 (y . b)))
;;                                            corres)))

(rp::def-formula-checks-default-evl
 rp::rp-evl
 (strip-cars rp::*small-evl-fncs*))

(encapsulate
  nil
  (local
   (in-theory (e/d (the-check
                    eql
                    hons-get
                    svex-env-fastlookup-wog)
                   (svex-kind-wog-is-svex-kind
                    4vec-fix-wog-is-4vec-fix
                    hons-assoc-equal
                    svex-apply-is-svex-apply-wog
                    svexl-node-kind-wog-is-svexl-node-kind
                    sv::4vec-equal))))

  (local
   (defthm the-check-def
     (equal (the-check x y z)
            z)))

  (local
   (defthm svex-env-fastlookup-wog-def-local
     (equal (svex-env-fastlookup-wog var env)
            (let* ((look (hons-get var env)))
              (if look (cdr look) (sv::4vec-x))))
     :hints (("goal"
              :in-theory (e/d (svex-env-fastlookup-wog) ())))))

  (local
   (defthm hons-get-is-assoc-equal
     (equal (hons-get x y)
            (hons-assoc-equal x y))))

  (with-output
    :off :all
    :gag-mode nil
    (rp::def-formula-checks
     svex-eval-wog-formula-checks
     (;;svex-eval-wog-meta-main
      sv::4vec-fix$inline
      svex-env-fastlookup-wog
      ;;svexl-node-eval-wog-meta-main
      svexl-node-eval-wog
      svex-eval-wog))))

(local
 (defthmd svex-eval-wog-eval
   (implies (and (rp-evl-meta-extract-global-facts)
                 (svex-eval-wog-formula-checks state)
                 (consp x)
                 (equal (car x) 'svex-eval-wog)
                 (consp (cdr x))
                 (consp (cddr x))
                 (not (cdddr x)))
            (and (equal (rp-evl x a)
                        (svex-eval-wog (rp-evl (cadr x) a)
                                       (rp-evl (caddr x) a)))
                 (equal (rp-evlt x a)
                        (svex-eval-wog (rp-evlt (cadr x) a)
                                       (rp-evlt (caddr x) a)))))))

(local
 (defthmd svexl-node-eval-wog-eval
   (implies (and (rp-evl-meta-extract-global-facts)
                 (svex-eval-wog-formula-checks state)
                 (consp x)
                 (equal (car x) 'svexl-node-eval-wog)
                 (consp (cdr x))
                 (consp (cddr x))
                 (consp (cdddr x))
                 (not (cddddr x)))
            (and (equal (rp-evl x a)
                        (svexl-node-eval-wog (rp-evl (cadr x) a)
                                             (rp-evl (caddr x) a)
                                             (rp-evl (cadddr x) a)))
                 (equal (rp-evlt x a)
                        (svexl-node-eval-wog (rp-evlt (cadr x) a)
                                             (rp-evlt (caddr x) a)
                                             (rp-evlt (cadddr x) a)))))))

(local
 (defthmd svex-env-fastlookup-wog-eval
   (implies (and (rp-evl-meta-extract-global-facts)
                 (svex-eval-wog-formula-checks state)
                 (consp x)
                 (equal (car x) 'svex-env-fastlookup-wog)
                 (consp (cdr x))
                 (consp (cddr x))
                 (not (cdddr x)))
            (and (equal (rp-evlt x a)
                   (svex-env-fastlookup-wog (rp-evlt (cadr x) a)
                                            (rp-evlt (caddr x) a)))
                 (equal (rp-evl x a)
                   (svex-env-fastlookup-wog (rp-evl (cadr x) a)
                                            (rp-evl (caddr x) a)))))))

(local
 (defthmd rp-evl-of-ex-from-rp-reverse
   (implies (syntaxp (atom term))
            (and (equal (rp-evl term a)
                        (rp-evl (rp::ex-from-rp term) a))
                 (equal (rp-evlt term a)
                        (rp-evlt (rp::ex-from-rp term) a))))
   :hints (("Goal"
            :in-theory (e/d (rp::is-rp) ())))))

(local
 (defthmd falist-eval
   (implies (and (rp-evl-meta-extract-global-facts)
                 (svex-eval-wog-formula-checks state)
                 (consp x)
                 (equal (car x) 'falist)
                 (consp (cdr x))
                 (consp (cddr x))
                 (not (cdddr x)))
            (and (equal (rp-evl x a)
                        (rp-evl (caddr x) a))
                 (equal (rp-evlt x a)
                        (rp-evlt (caddr x) a))))))

(local
 (defthmd falist-eval2
   (implies (and (rp-evl-meta-extract-global-facts)
                 (svex-eval-wog-formula-checks state)
                 (consp (rp::ex-from-rp x))
                 (equal (car (rp::ex-from-rp x)) 'falist)
                 (consp (cdr (rp::ex-from-rp x)))
                 (consp (cddr (rp::ex-from-rp x)))
                 (not (cdddr (rp::ex-from-rp x))))
            (and (equal (rp-evl x a)
                        (rp-evl (caddr (rp::ex-from-rp x)) a))
                 (equal (rp-evlt x a)
                        (rp-evlt (caddr (rp::ex-from-rp x)) a))))
   :hints (("Goal"
            :in-theory (e/d (rp-evl-of-ex-from-rp-reverse) ())))))

(local
 (defthm rp::falist-consistent-aux-lemma
   (implies (and (rp::falist-consistent-aux env-falist term)
                 (hons-assoc-equal x env-falist)
                 (hons-assoc-equal x (rp-evlt term a)))
            (equal (rp-evlt (cdr (hons-assoc-equal x env-falist))
                           a)
                   (cdr (hons-assoc-equal x (rp-evlt term a)))))))

(local
 (defthm rp::falist-consistent-aux-lemma-2
   (implies (and (rp::falist-consistent-aux env-falist term)
                 (hons-assoc-equal x env-falist))
            (hons-assoc-equal x (rp-evlt term a)))))

(local
 (defthm rp::falist-consistent-aux-lemma-3
   (implies (and (rp::falist-consistent-aux env-falist term)
                 (hons-assoc-equal x (rp-evlt term a)))
            (hons-assoc-equal x env-falist))))

#|(local
 (defthm lemma1
   (implies (not (rp-evl term a))
            (equal (equal (4vec-fix (rp-evl (car term) a)) '(-1 . 0))
                   t))
   :hints (("Goal"
            :in-theory (e/d (4vec-fix) ())))))||#

(local
 (encapsulate
   nil

   (local
    (defthm 4vec-fix-of-4vec-fix
      (equal (4vec-fix (4vec-fix term))
             (4vec-fix term))
      :hints (("goal"
               :in-theory (e/d (4vec-fix) ())))))

   (defthm 4vec-fncs-and-fix
     (and (equal (sv::4vec-onehot (4vec-fix x))
                 (sv::4vec-onehot x))
          (equal (sv::4vec-onehot0 (4vec-fix x))
                 (sv::4vec-onehot0 x))
          (equal (4vec-part-select (4vec-fix x) y z)
                 (4vec-part-select x y z))
          (equal (4vec-part-select x (4vec-fix y) z)
                 (4vec-part-select x y z))
          (equal (4vec-part-select x y (4vec-fix z))
                 (4vec-part-select x y z))
          (equal (4vec-part-install m (4vec-fix x) y z)
                 (4vec-part-install m x y z))
          (equal (4vec-part-install m x (4vec-fix y) z)
                 (4vec-part-install m x y z))
          (equal (4vec-part-install m x y (4vec-fix z))
                 (4vec-part-install m x y z))
          (equal (4vec-part-install (4vec-fix m) x y z)
                 (4vec-part-install m x y z)))
     :hints (("goal"
              :in-theory (e/d (sv::4vec-onehot0
                               4vec-part-install
                               4vec-part-select) ()))))
   (local
    (defthm lemma1
      (and (equal (4vec-part-select x y nil)
                  (4vec-part-select x y '(-1 . 0)))
           (equal (4vec-part-select x nil z)
                  (4vec-part-select x '(-1 . 0) z))
           (equal (4vec-part-select nil y z)
                  (4vec-part-select '(-1 . 0) y z))
           (equal (4vec-part-install m x y nil)
                  (4vec-part-install m x y '(-1 . 0)))
           (equal (4vec-part-install m x nil z)
                  (4vec-part-install m x '(-1 . 0) z))
           (equal (4vec-part-install m nil y z)
                  (4vec-part-install m '(-1 . 0) y z))
           (equal (4vec-part-install nil x y z)
                  (4vec-part-install '(-1 . 0) x y z)))
      :hints (("goal"
               :in-theory (e/d (4vec-part-select
                                4vec-part-install) ())))))


   (local
    (defthm QUOTED-4VEC-LISTP-and-unquote-all-correct
        (implies (QUOTED-4VEC-LISTP ARGS)
                 (equal (RP::UNQUOTE-ALL ARGS)
                        (RP-EVLT-LST ARGS A)))
      :hints (("Goal"
               :induct (QUOTED-4VEC-LISTP ARGS)
               :in-theory (e/d (QUOTED-4VEC-LISTP) ())))))
   
   (defthm rp-evl-of-svex-apply-wog-meta
     (implies (and (rp-evl-meta-extract-global-facts)
                   (svex-eval-wog-formula-checks state))
              (equal (rp-evlt (mv-nth 0 (svex-apply-wog-meta call args args-dontrw)) a)
                     (svex-apply-wog call
                                     (rp-evlt-lst args a))))
     :hints (("goal"
              :do-not-induct t
              :do-not '(preprocess)
              :expand ((:free (x y)
                              (nth x y))
                       (:free (x y)
                              (nth-term x y)))
              :in-theory (e/d (svex-apply-wog
                               svex-apply-wog-meta)
                              (svex-apply-is-svex-apply-wog
                               (:definition nth)
                               (:rewrite default-cdr)
                               (:rewrite default-car)
                               (:rewrite sv::4vec-fix-of-4vec)
                               (:rewrite acl2::o-p-o-infp-car)
                               (:forward-chaining
                                acl2::|a <= b & ~(a = b)  =>  a < b|)
                               (:rewrite sv::fnsym-fix-when-fnsym-p)
                               (:rewrite
                                rp::rp-evl-of-rp-equal-cnt-subterms-call)
                               (:rewrite rp::rp-evl-of-lambda)
                               (:rewrite rp::rp-evl-of-unary-/-call)
                               (:rewrite rp::rp-evl-of-unary---call)

                               (:type-prescription fnsym-fix)
                               (:rewrite sv::4vec-p-when-maybe-4vec-p)
                               (:type-prescription 4vec-p)
                               (:type-prescription sv::maybe-4vec-p)
                               (:rewrite
                                sv::4vec-p-when-member-equal-of-4veclist-p)
                               (:rewrite sv::maybe-4vec-p-when-4vec-p)
                               (:rewrite sv::4vec-p-of-nth-when-4veclist-p)
                               (:type-prescription svex-eval-wog-formula-checks)
                               (:type-prescription o<)
                               (:type-prescription sv::fnsym-equiv$inline)
                               (:type-prescription 4vec-part-install)
                               (:rewrite rp::rp-evl-of-typespec-check-call)
                               (:rewrite rp::rp-evl-of-synp-call)
                               (:rewrite rp::rp-evl-of-symbolp-call)
                               (:rewrite
                                rp::rp-evl-of-symbol-package-name-call)
                               (:rewrite rp::rp-evl-of-symbol-name-call)
                               (:rewrite rp::rp-evl-of-stringp-call)
                               (:rewrite
                                rp::rp-evl-of-rp-equal-subterms-call)
                               (:rewrite rp::rp-evl-of-rp-equal-cnt-call)
                               (:rewrite rp::rp-evl-of-rp-equal-call)
                               (:rewrite rp::rp-evl-of-rp-call)
                               (:rewrite rp::rp-evl-of-return-last-call)
                               (:rewrite rp::rp-evl-of-realpart-call)
                               (:rewrite rp::rp-evl-of-rationalp-call)
                               (:rewrite rp::rp-evl-of-numerator-call)
                               (:rewrite rp::rp-evl-of-not-call)
                               (:rewrite
                                rp::rp-evl-of-intern-in-package-of-symbol-call)
                               (:rewrite rp::rp-evl-of-integerp-call)
                               (:rewrite rp::rp-evl-of-implies-call)
                               (:rewrite rp::rp-evl-of-imagpart-call)
                               (:rewrite rp::rp-evl-of-iff-call)
                               (:rewrite rp::rp-evl-of-if-call)
                               (:rewrite rp::rp-evl-of-hide-call)
                               (:rewrite rp::rp-evl-of-falist-call)
                               (:rewrite rp::rp-evl-of-equal-call)
                               (:rewrite rp::rp-evl-of-denominator-call)
                               (:rewrite rp::rp-evl-of-consp-call)
                               (:rewrite rp::rp-evl-of-cons-call)
                               (:rewrite
                                rp::rp-evl-of-complex-rationalp-call)
                               (:rewrite rp::rp-evl-of-coerce-call)
                               (:rewrite rp::rp-evl-of-code-char-call)
                               (:rewrite rp::rp-evl-of-characterp-call)
                               (:rewrite rp::rp-evl-of-char-code-call)
                               (:rewrite rp::rp-evl-of-cdr-call)
                               (:rewrite rp::rp-evl-of-car-call)
                               (:rewrite rp::rp-evl-of-binary-+-call)
                               (:rewrite rp::rp-evl-of-binary-*-call)
                               (:rewrite rp::rp-evl-of-bad-atom<=-call)
                               (:rewrite rp::rp-evl-of-acl2-numberp-call)
                               (:rewrite rp::rp-evl-of-<-call)
                               (:rewrite acl2::symbol-listp-implies-symbolp)
                               (:meta acl2::mv-nth-cons-meta))))))

   (defthm-svex-eval-wog-meta
     (defthmd rp-evl-of-svex-eval-wog-meta
       (implies (and (rp-evl-meta-extract-global-facts)
                     (svex-eval-wog-formula-checks state)
                     (if good-env-flg
                         (rp::falist-consistent-aux env-falist term)
                       (equal term env-falist)))
                (equal (rp-evlt (mv-nth 0 (svex-eval-wog-meta x env-falist good-env-flg)) a)
                       (rp-evlt `(svex-eval-wog ,(list 'quote x) ,term) a)))
       :flag expr)

     (defthmd rp-evl-of-svex-eval-wog-meta-lst
       (implies (and (rp-evl-meta-extract-global-facts)
                     (svex-eval-wog-formula-checks state)
                     (if good-env-flg
                         (rp::falist-consistent-aux env-falist term)
                       (equal term env-falist)))
                (equal (rp-evlt-lst
                        (mv-nth 0 (svex-eval-wog-meta-lst lst env-falist good-env-flg))
                        a)
                       (rp-evlt `(svexlist-eval-wog ,(list 'quote lst) ,term) a)))
       :flag list)
     :hints (("goal"
               :expand ((:free (lst term) (RP-TRANS (LIST 'SVEXLIST-EVAL-WOG
                                                          (LIST 'QUOTE LST)
                                                          TERM)))
                        (:free (x y) (rp-trans-lst (cons x y))))
              :in-theory (e/d (svex-eval-wog-meta-lst
                               SVEX-ENV-FASTLOOKUP-WOG
                               svex-eval-wog
                               svexlist-eval-wog
                               svex-eval-wog-eval
                               svexl-node-eval-wog-eval
                               svex-env-fastlookup-wog-eval
                               svex-eval-wog-meta)
                              (svex-apply-is-svex-apply-wog
                               rp-trans
                               rp-trans-lst)))))

   (local
    (defthm all-falist-consistent-lemma
      (implies (and (rp::rp-termp term)
                    (equal (car (rp::ex-from-rp term)) 'falist)
                    (consp (rp::ex-from-rp term))
                    (consp (cdr (rp::ex-from-rp term)))
                    (consp (cddr (rp::ex-from-rp term)))
                    (not (cdddr (rp::ex-from-rp term)))
                    (quotep (cadr (rp::ex-from-rp term))))
               (rp::falist-consistent-aux (cadr (cadr (rp::ex-from-rp term)))
                                          (caddr (rp::ex-from-rp term))))
      :hints (("goal"
               :in-theory (e/d (rp::is-rp) ())))))


   (local
    (DEFTHMd
        RP::RP-EVLT-OF-EX-FROM-RP-reverse
        (implies (syntaxp (not (rp::include-fnc rp::term 'rp::ex-from-rp)))
                 (EQUAL 
                  (RP-EVL (RP-TRANS RP::TERM) RP::A)
                  (RP-EVL (RP-TRANS (RP::EX-FROM-RP RP::TERM))
                          RP::A)))
      :HINTS
      (("Goal" :IN-THEORY (E/D (RP::EX-FROM-RP RP::IS-RP) NIL)))))

   (local
    (defthm dummy-lemma-for-nil
        (implies (and (EQUAL (RP::EX-FROM-RP (CADDR TERM))
                             ''NIL))
                 (equal (RP-EVLT (CADDR TERM) A) nil))
      :hints (("Goal"
               :in-theory (e/d (rp::rp-evlt-of-ex-from-rp-reverse)
                               (rp::rp-evlt-of-ex-from-rp))))))
   
   (defthm rp-evl-of-svex-eval-wog-meta-main
     (implies (and (rp-evl-meta-extract-global-facts)
                   (rp::rp-termp term)
                   (svex-eval-wog-formula-checks state))
              (equal (rp-evlt (mv-nth 0 (svex-eval-wog-meta-main term)) a)
                     (rp-evlt term a)))
     :hints (("goal"
              :use ((:instance rp-evl-of-svex-eval-wog-meta
                               (env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                                        term)))))
                               (a a)
                               (good-env-flg t)
                               (x (cadr (cadr term)))
                               (term (caddr (rp::ex-from-rp (caddr
                                                             term)))))
                    (:instance rp-evl-of-svex-eval-wog-meta
                               (env-falist nil)
                               (a a)
                               (good-env-flg t)
                               (x (cadr (cadr term)))
                               (term ''nil))
                    (:instance rp-evl-of-svex-eval-wog-meta
                               (good-env-flg nil)
                               (a a)
                               (x (cadr (cadr term)))
                               (term (CADDR TERM))
                               (env-falist (CADDR TERM))))
              :in-theory (e/d (svex-eval-wog-meta-main
                               falist-eval
                               rp-trans
                               rp-trans-lst
                               rp::rp-evl-of-ex-from-rp
                               falist-eval2
                               svex-eval-wog-eval)
                              (RP::RP-EVL-OF-VARIABLE)))))))

(local
 (encapsulate
   nil

   (defthm-svexl-node-eval-wog-meta
     (defthmd rp-evl-of-svexl-node-eval-wog-meta
       (implies (and (rp-evl-meta-extract-global-facts)
                     (svex-eval-wog-formula-checks state)
                     (if good-env-flg
                         (and (rp::falist-consistent-aux env-falist env-term)
                              (rp::falist-consistent-aux node-env-falist node-env-term))
                       (and (equal env-term env-falist)
                            (equal node-env-term node-env-falist))))
                (equal (rp-evlt (mv-nth 0 (svexl-node-eval-wog-meta
                                          x node-env-falist env-falist good-env-flg))
                               a)
                       (rp-evlt `(svexl-node-eval-wog
                                 ,(list 'quote x) ,node-env-term ,env-term)
                               a)))
       :flag expr)

     (defthmd rp-evl-of-svexl-node-eval-wog-meta-lst
       (implies (and (rp-evl-meta-extract-global-facts)
                     (svex-eval-wog-formula-checks state)
                     (if good-env-flg
                         (and (rp::falist-consistent-aux env-falist env-term)
                              (rp::falist-consistent-aux node-env-falist node-env-term))
                       (and (equal env-term env-falist)
                            (equal node-env-term node-env-falist))))
                (equal (rp-evlt-lst
                        (mv-nth 0 (svexl-nodelist-eval-wog-meta
                                   lst node-env-falist env-falist good-env-flg))
                        a)
                       (rp-evlt `(svexl-nodelist-eval-wog
                                 ,(list 'quote lst) ,node-env-term ,env-term)
                               a)))
       :flag list)
     :hints (("goal"
              :in-theory (e/d (svex-eval-wog-meta-lst
                               svex-env-fastlookup-wog
                               svexl-nodelist-eval-wog-meta
                               svex-eval-wog-meta
                               svexl-nodelist-eval-wog
                               SVEXL-NODE-KIND-WOG
                               SVEX-KIND
                               svexl-node-eval-wog-meta
                               svex-kind-wog
                               svexl-node-eval-wog)
                              (svex-apply-is-svex-apply-wog)))))

   (local
    (defthm all-falist-consistent-lemma
      (implies (and (rp::rp-termp term)
                    (equal (car (rp::ex-from-rp term)) 'falist)
                    (consp (rp::ex-from-rp term))
                    (consp (cdr (rp::ex-from-rp term)))
                    (consp (cddr (rp::ex-from-rp term)))
                    (not (cdddr (rp::ex-from-rp term)))
                    (quotep (cadr (rp::ex-from-rp term))))
               (rp::falist-consistent-aux (cadr (cadr (rp::ex-from-rp term)))
                                          (caddr (rp::ex-from-rp term))))
      :hints (("goal"
               :in-theory (e/d (rp::is-rp) ())))))


   (local
    (DEFTHMd
        RP::RP-EVLT-OF-EX-FROM-RP-reverse
        (implies (syntaxp (not (rp::include-fnc rp::term 'rp::ex-from-rp)))
                 (EQUAL 
                  (RP-EVL (RP-TRANS RP::TERM) RP::A)
                  (RP-EVL (RP-TRANS (RP::EX-FROM-RP RP::TERM))
                          RP::A)))
      :HINTS
      (("Goal" :IN-THEORY (E/D (RP::EX-FROM-RP RP::IS-RP) NIL)))))
   
   (local
    (defthm dummy-lemma-for-nil
        (and (implies (and (EQUAL (RP::EX-FROM-RP (CADDR TERM))
                                  ''NIL))
                      (equal (RP-EVLT (CADDR TERM) A) nil))
             (implies (and (EQUAL (RP::EX-FROM-RP (CADDdR TERM))
                                  ''NIL))
                      (equal (RP-EVLT (CADdDR TERM) A) nil)))
      :hints (("Goal"
               :in-theory (e/d (rp::rp-evlt-of-ex-from-rp-reverse)
                               (rp::rp-evlt-of-ex-from-rp))))))

   (defthm rp-evl-of-svexl-node-eval-wog-meta-main
     (implies (and (rp-evl-meta-extract-global-facts)
                   (rp::rp-termp term)
                   (svex-eval-wog-formula-checks state))
              (equal (rp-evlt (mv-nth 0 (svexl-node-eval-wog-meta-main term)) a)
                     (rp-evlt term a)))
     :hints (("goal"
              :use ((:instance rp-evl-of-svexl-node-eval-wog-meta
                               (env-falist (cadr (cadr (rp::ex-from-rp (cadddr
                                                                        term)))))
                               (node-env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                                             term)))))
                               (a a)
                               (good-env-flg t)
                               (x (cadr (cadr term)))
                               (node-env-term (caddr (rp::ex-from-rp (caddr
                                                                      term))))
                               (env-term (caddr (rp::ex-from-rp (cadddr
                                                                 term)))))
                    (:instance rp-evl-of-svexl-node-eval-wog-meta
                               (env-falist (cadr (cadr (rp::ex-from-rp (cadddr
                                                                        term)))))
                               (node-env-falist nil)
                               (a a)
                               (good-env-flg t)
                               (x (cadr (cadr term)))
                               (node-env-term ''nil)
                               (env-term (caddr (rp::ex-from-rp (cadddr
                                                                 term)))))
                    (:instance rp-evl-of-svexl-node-eval-wog-meta
                               (env-falist nil)
                               (node-env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                                             term)))))
                               (a a)
                               (good-env-flg t)
                               (x (cadr (cadr term)))
                               (node-env-term (caddr (rp::ex-from-rp (caddr
                                                                      term))))
                               (env-term ''nil))
                    (:instance rp-evl-of-svexl-node-eval-wog-meta
                               (env-falist nil)
                               (node-env-falist nil)
                               (a a)
                               (good-env-flg t)
                               (x (cadr (cadr term)))
                               (node-env-term ''nil)
                               (env-term ''nil))
                    (:instance rp-evl-of-svexl-node-eval-wog-meta
                               (good-env-flg nil)
                               (a a)
                               (x (cadr (cadr term)))
                               (env-term (CADdDR TERM))
                               (node-env-term (CADDR TERM))
                               (env-falist (CAdDDR TERM))
                               (node-env-falist (CADDR TERM))))
              :do-not-induct t
              :do-not '(preprocess fertilize generalize)
              :in-theory (e/d (svexl-node-eval-wog-meta-main
                               falist-eval
                               rp::rp-evl-of-ex-from-rp
                               falist-eval2
                               svex-eval-wog-eval)
                              (rp::rp-evl-of-variable
                               (:type-prescription rp::rp-termp)
                               (:type-prescription o<)
                               (:type-prescription rp::rp-term-listp)
                               (:type-prescription rp::is-rp$inline)
                               (:type-prescription rp::falist-consistent-aux)
                               (:type-prescription o-p)
                               (:rewrite svex-eval-wog-eval)
                               (:forward-chaining
                                acl2::|a <= b & ~(a = b)  =>  a < b|)
                               (:rewrite rp::rp-evl-of-unary-/-call)
                               (:rewrite rp::rp-termp-caddr)
                               (:rewrite default-car)
                               (:rewrite rp::rp-termp-cadddr)
                               (:definition rp::ex-from-rp)
                               (:rewrite default-cdr)
                               (:rewrite rp::rp-termp-cadr)
                               (:rewrite rp::rp-termp-implies-cdr-listp)
                               (:type-prescription
                                svex-eval-wog-formula-checks)
                               (:type-prescription rp::falist-consistent)
                               (:definition rp::falist-consistent-aux)
                               (:type-prescription
                                svexl-node-kind-wog$inline)
                               (:definition eq)
                               (:rewrite acl2::o-p-o-infp-car)
                               (:definition rp::falist-consistent))))))))

(local
 (encapsulate
   nil

   (defthm rp-termp-svex-apply-wog-meta
     (implies (rp::rp-term-listp args)
              (rp::rp-termp
               (mv-nth 0 (svex-apply-wog-meta call args args-dontrw))))
     :hints (("goal"
              :do-not-induct t
              :expand ((:free (x y)
                              (nth x y))
                       (:free (x y)
                              (nth-term x y)))
              :in-theory (e/d (svex-apply-wog-meta)
                              ((:definition rp::falist-consistent)
                               (:rewrite default-cdr)
                               (:rewrite default-car)
                               (:rewrite acl2::o-p-o-infp-car)
                               (:rewrite acl2::o-p-def-o-finp-1)
                               (:rewrite rp::rp-termp-implies-cdr-listp)
                               (:definition acl2::apply$-badgep)
                               (:rewrite acl2::apply$-badgep-properties . 3)
                               (:definition true-listp)
                               (:definition subsetp-equal)
                               (:definition member-equal)
                               (:rewrite
                                acl2::member-equal-newvar-components-1)
                               (:type-prescription rp::rp-termp))))))

   (local
    (defthm lemma1
      (implies (and (rp::falist-consistent-aux env-falist term)
                    (rp::rp-termp term)
                    (hons-assoc-equal x env-falist))
               (rp::rp-termp (cdr (hons-assoc-equal x env-falist))))))


   (defthm-svex-eval-wog-meta
     (defthmd rp-termp-svex-eval-wog-meta
       (implies (and (if good-env-flg
                         (rp::falist-consistent-aux env-falist term)
                       (equal term env-falist))
                     (rp::rp-termp term))
                (rp::rp-termp
                 (mv-nth 0 (svex-eval-wog-meta x env-falist good-env-flg))))
       :flag expr)

     (defthmd rp::rp-termp-svex-eval-wog-meta-lst
       (implies (and (if good-env-flg
                         (rp::falist-consistent-aux env-falist term)
                       (equal term env-falist))
                     (rp::rp-termp term))
                (rp::rp-term-listp
                 (mv-nth 0 (svex-eval-wog-meta-lst lst env-falist good-env-flg))))
       :flag list)
     :hints (("goal"
              :in-theory (e/d (svex-kind
                               svex-eval-wog-meta
                               svex-eval-wog-meta-lst
                               rp::is-falist)
                              ()))))

   (defthm-svexl-node-eval-wog-meta
     (defthmd rp-termp-svexl-node-eval-wog-meta
       (implies (and (if good-env-flg
                         (and (rp::falist-consistent-aux env-falist env-term)
                              (rp::falist-consistent-aux node-env-falist node-env-term))
                       (and (equal env-term env-falist)
                            (equal node-env-term node-env-falist)))
                     (rp::rp-termp node-env-term)
                     (rp::rp-termp env-term))
                (rp::rp-termp
                 (mv-nth 0 (svexl-node-eval-wog-meta x node-env-falist env-falist good-env-flg))))
       :flag expr)

     (defthmd rp-termp-svexl-node-eval-wog-meta-lst
       (implies (and (if good-env-flg
                         (and (rp::falist-consistent-aux env-falist env-term)
                              (rp::falist-consistent-aux node-env-falist node-env-term))
                       (and (equal env-term env-falist)
                            (equal node-env-term node-env-falist)))
                     (rp::rp-termp env-term)
                     (rp::rp-termp node-env-term))
                (rp::rp-term-listp
                 (mv-nth 0 (svexl-nodelist-eval-wog-meta lst node-env-falist env-falist good-env-flg))))
       :flag list)
     :hints (("goal"
              :in-theory (e/d (svexl-node-kind
                               svexl-node-kind-wog
                               svexl-nodelist-eval-wog-meta
                               svexl-node-eval-wog-meta
                               rp::is-falist)
                              ()))))



   (local
    (defthm lemma2
      (implies (and (rp::rp-termp term))
               (and (rp::rp-termp (rp::ex-from-rp term))))
      :hints (("goal"
               :in-theory (e/d (rp::ex-from-rp rp::is-rp) ())))))

   (local
    (defthm lemma3
      (implies (and (rp::rp-termp term)
                    (consp term)
                    (not (equal (car term) 'quote))
                    (consp (cdr term))
                    (consp (cddr term)))
               (rp::rp-termp (caddr term)))))

   (local
    (defthm rp-termp-implies-ex-from-rp
      (implies (rp::rp-termp x)
               (rp::rp-termp (rp::ex-from-rp x)))
      :rule-classes :forward-chaining))

   (local
    (defthm rp-termp-and-falist-consistent-aux
      (implies (and (rp::rp-termp term)
                    (equal (car term) 'falist)
                    (consp (cdr term))
                    (consp (cddr term))
                    (not (cdddr term))
                    (quotep (cadr term)))
               (rp::falist-consistent-aux (cadr (cadr term))
                                          (caddr term)))))

   (defthm rp-termp-svex-eval-wog-meta-main
     (implies (and (rp::rp-termp term))
              (rp::rp-termp (mv-nth 0 (svex-eval-wog-meta-main term))))
     :hints (("goal"
              :do-not-induct t
              :do-not '(preprocess)
              :use ((:instance
                     rp-termp-svex-eval-wog-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                              term)))))
                     (good-env-flg t)
                     (x (cadr (cadr term)))
                     (term (caddr (rp::ex-from-rp (caddr term)))))
                    (:instance
                     rp-termp-svex-eval-wog-meta
                     (env-falist nil)
                     (good-env-flg t)
                     (x (cadr (cadr term)))
                     (term ''nil))
                    (:instance
                     rp-termp-svex-eval-wog-meta
                     (env-falist (CADDR TERM))
                     (term (CADDR TERM))
                     (good-env-flg nil)
                     (x (CADR (CADR TERM)))
                     ))
              :in-theory (e/d (svex-eval-wog-meta-main
                               rp::is-falist)
                              ((:definition rp::falist-consistent)
                               rp-termp-svex-eval-wog-meta
                               RP::RP-TERM-LISTP
                               RP::RP-TERMP
                               (:type-prescription rp::falist-consistent)
                               #|rp-termp-svex-eval-wog-meta||#)))))

   (defthm rp-termp-svexl-node-eval-wog-meta-main
     (implies (and (rp::rp-termp term))
              (rp::rp-termp (mv-nth 0 (svexl-node-eval-wog-meta-main term))))
     :hints (("goal"
              :do-not-induct t
              :do-not '(preprocess)
              :use ((:instance
                     rp-termp-svexl-node-eval-wog-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (cadddr
                                                              term)))))
                     (node-env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                              term)))))
                     (good-env-flg t)
                     (x (cadr (cadr term)))
                     (env-term (caddr (rp::ex-from-rp (cadddr term))))
                     (node-env-term (caddr (rp::ex-from-rp (caddr term)))))
                    (:instance
                     rp-termp-svexl-node-eval-wog-meta
                     (env-falist nil)
                     (node-env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                              term)))))
                     (good-env-flg t)
                     (x (cadr (cadr term)))
                     (env-term ''nil)
                     (node-env-term (caddr (rp::ex-from-rp (caddr term)))))
                    (:instance
                     rp-termp-svexl-node-eval-wog-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (cadddr
                                                              term)))))
                     (node-env-falist nil)
                     (good-env-flg t)
                     (x (cadr (cadr term)))
                     (env-term (caddr (rp::ex-from-rp (cadddr term))))
                     (node-env-term ''nil))
                    (:instance
                     rp-termp-svexl-node-eval-wog-meta
                     (env-falist nil)
                     (node-env-falist nil)
                     (good-env-flg t)
                     (x (cadr (cadr term)))
                     (env-term ''nil)
                     (node-env-term ''nil))
                    (:instance
                     rp-termp-svexl-node-eval-wog-meta
                     (env-falist (CADdDR TERM))
                     (node-env-falist (CADDR TERM))
                     (env-term (CAdDDR TERM))
                     (node-env-term (CADDR TERM))
                     (good-env-flg nil)
                     (x (CADR (CADR TERM)))
                     ))
              :in-theory (e/d (SVEXL-NODE-EVAL-WOG-META-MAIN
                               rp::is-falist)
                              ((:definition rp::falist-consistent)
                               rp-termp-svex-eval-wog-meta
                               RP::RP-TERM-LISTP
                               RP::RP-TERMP
                               (:type-prescription rp::falist-consistent)
                               #|rp-termp-svex-eval-wog-meta||#)))))))

(local
 (encapsulate
   nil

   (local
    (in-theory (enable rp::is-rp
                       rp::is-if)))

   (defthm valid-sc-svex-apply-wog-meta
     (implies (rp::valid-sc-subterms args a)
              (rp::valid-sc
               (mv-nth 0 (svex-apply-wog-meta call args args-dontrw))
               a))
     :hints (("goal"
              :do-not-induct t
              :expand ((:free (x y)
                              (nth x y))
                       (:free (x y)
                              (nth-term x y)))
              :in-theory (e/d (svex-apply-wog-meta)
                              ((:definition rp::falist-consistent)
                               (:rewrite default-cdr)
                               (:rewrite default-car)
                               (:rewrite acl2::o-p-o-infp-car)
                               (:rewrite acl2::o-p-def-o-finp-1)
                               (:definition acl2::apply$-badgep)
                               (:rewrite acl2::apply$-badgep-properties . 3)
                               (:definition true-listp)
                               (:definition subsetp-equal)
                               (:definition member-equal)
                               (:rewrite
                                acl2::member-equal-newvar-components-1)
                               (:type-prescription rp::valid-sc))))))

   (local
    (defthm lemma1
      (implies (and (rp::falist-consistent-aux env-falist term)
                    (rp::valid-sc term a)
                    (hons-assoc-equal x env-falist))
               (rp::valid-sc (cdr (hons-assoc-equal x
                                                    env-falist))
                             a))))

   (defthm-svex-eval-wog-meta
     (defthmd valid-sc-svex-eval-wog-meta
       (implies (and (if good-env-flg
                         (rp::falist-consistent-aux env-falist term)
                       (equal term env-falist))
                     (rp::valid-sc term a))
                (rp::valid-sc
                 (mv-nth 0 (svex-eval-wog-meta x env-falist good-env-flg)) a))
       :flag expr)

     (defthmd rp::valid-sc-svex-eval-wog-meta-lst
       (implies (and (if good-env-flg
                         (rp::falist-consistent-aux env-falist term)
                       (equal term env-falist))
                     (rp::valid-sc term a))
                (rp::valid-sc-subterms
                 (mv-nth 0 (svex-eval-wog-meta-lst lst env-falist good-env-flg)) a))
       :flag list)
     :hints (("goal"
              :in-theory (e/d (svex-kind
                               svex-eval-wog-meta
                               svex-eval-wog-meta-lst
                               rp::is-falist)
                              ()))))

   (defthm-svexl-node-eval-wog-meta
     (defthmd valid-sc-svexl-node-eval-wog-meta
       (implies (and (if good-env-flg
                         (and (rp::falist-consistent-aux env-falist env-term)
                              (rp::falist-consistent-aux node-env-falist node-env-term))
                       (and (equal env-term env-falist)
                            (equal node-env-term node-env-falist)))
                     (rp::valid-sc node-env-term a)
                     (rp::valid-sc env-term a))
                (rp::valid-sc
                 (mv-nth 0 (svexl-node-eval-wog-meta x node-env-falist env-falist good-env-flg)) a))
       :flag expr)

     (defthmd rp::valid-sc-svexl-node-eval-wog-meta-lst
       (implies (and (if good-env-flg
                         (and (rp::falist-consistent-aux env-falist env-term)
                              (rp::falist-consistent-aux node-env-falist node-env-term))
                       (and (equal env-term env-falist)
                            (equal node-env-term node-env-falist)))
                     (rp::valid-sc node-env-term a)
                     (rp::valid-sc env-term a))
                (rp::valid-sc-subterms
                 (mv-nth 0 (svexl-nodelist-eval-wog-meta lst node-env-falist env-falist good-env-flg)) a))
       :flag list)
     :hints (("goal"
              :in-theory (e/d (svexl-node-kind
                               svexl-node-eval-wog-meta
                               svexl-nodelist-eval-wog-meta
                               rp::is-falist)
                              ()))))

   (local
    (defthm lemma2
      (implies (and (rp::valid-sc term a))
               (and (rp::valid-sc (rp::ex-from-rp term) a)))
      :hints (("goal"
               :in-theory (e/d (rp::ex-from-rp rp::is-rp) ())))))

   (local
    (defthm lemma3
      (implies (and (rp::valid-sc term a)
                    (consp term)
                    (equal (car term) 'falist)
                    (consp (cdr term))
                    (consp (cddr term)))
               (rp::valid-sc (caddr term) a))))

   (local
    (defthm rp-termp-and-falist-consistent-aux
      (implies (and (rp::rp-termp term)
                    (equal (car term) 'falist)
                    (consp (cdr term))
                    (consp (cddr term))
                    (not (cdddr term))
                    (quotep (cadr term)))
               (rp::falist-consistent-aux (cadr (cadr term))
                                          (caddr term)))))

   (defthm valid-sc-svex-eval-wog-meta-main
     (implies (and (rp::valid-sc term a)
                   (rp::rp-termp term))
              (rp::valid-sc (mv-nth 0 (svex-eval-wog-meta-main term))
                            a))
     :hints (("goal"
              :do-not-induct t
              :use ((:instance
                     valid-sc-svex-eval-wog-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                              term)))))
                     (x (cadr (cadr term)))
                     (good-env-flg t)
                     (term (caddr (rp::ex-from-rp (caddr term)))))
                    (:instance
                     valid-sc-svex-eval-wog-meta
                     (env-falist nil)
                     (x (cadr (cadr term)))
                     (good-env-flg t)
                     (term ''nil))

                    (:instance
                     valid-sc-svex-eval-wog-meta
                     (env-falist (caddr term))
                     (x (cadr (cadr term)))
                     (good-env-flg nil)
                     (term (caddr term))))
              :in-theory (e/d (svex-eval-wog-meta-main
                               rp::is-falist) ()))))

   (defthm valid-sc-svexl-node-eval-wog-meta-main
     (implies (and (rp::valid-sc term a)
                   (rp::rp-termp term))
              (rp::valid-sc (mv-nth 0 (svexl-node-eval-wog-meta-main term))
                            a))
     :hints (("goal"
              :do-not-induct t
              :use ((:instance
                     valid-sc-svexl-node-eval-wog-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (cadddr
                                                              term)))))
                     (node-env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                              term)))))
                     (x (cadr (cadr term)))
                     (good-env-flg t)
                     (env-term (caddr (rp::ex-from-rp (cadddr term))))
                     (node-env-term (caddr (rp::ex-from-rp (caddr term)))))
                    (:instance
                     valid-sc-svexl-node-eval-wog-meta
                     (env-falist nil)
                     (node-env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                              term)))))
                     (x (cadr (cadr term)))
                     (good-env-flg t)
                     (env-term ''nil)
                     (node-env-term (caddr (rp::ex-from-rp (caddr term)))))
                    (:instance
                     valid-sc-svexl-node-eval-wog-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (cadddr
                                                              term)))))
                     (node-env-falist nil)
                     (x (cadr (cadr term)))
                     (good-env-flg t)
                     (env-term (caddr (rp::ex-from-rp (cadddr term))))
                     (node-env-term ''nil))
                    (:instance
                     valid-sc-svexl-node-eval-wog-meta
                     (env-falist nil)
                     (node-env-falist nil)
                     (x (cadr (cadr term)))
                     (good-env-flg t)
                     (env-term ''nil)
                     (node-env-term ''nil))
                    (:instance
                     valid-sc-svexl-node-eval-wog-meta
                     (env-falist (cadddr term))
                     (node-env-falist (caddr term))
                     (x (cadr (cadr term)))
                     (good-env-flg nil)
                     (node-env-term (caddr term))
                     (env-term (cadddr term))))
              :in-theory (e/d (svexl-node-eval-wog-meta-main
                               rp::is-falist)
                              ((:DEFINITION RP::RP-TERMP)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE RP::VALID-SC-CADR)
                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               (:REWRITE LEMMA3)
                               (:DEFINITION RP::FALIST-CONSISTENT))))))))

#|(defthm valid-rp-meta-rulep-svex-eval-wog-meta-main
  (implies (and (rp-evl-meta-extract-global-facts)
                (svex-eval-wog-formula-checks state))
           (let ((rule (make rp::rp-meta-rule-rec
                             :fnc 'svex-eval-wog-meta-main
                             :trig-fnc 'svex-eval-wog
                             :dont-rw t
                             :valid-syntax t)))
             (and (rp::rp-meta-valid-syntaxp-sk rule state)
                  (rp::valid-rp-meta-rulep rule state))))
  :otf-flg t
  :hints (("goal"
           :in-theory (e/d (rp::rp-meta-valid-syntaxp)
                           (rp::rp-termp
                            svex-eval-wog-meta-main
                            rp::rp-term-listp
                            rp::valid-sc
                            rp::valid-sc)))))||#


#|(defthm valid-rp-meta-rulep-svexl-node-eval-wog-meta-main
  (implies (and (rp-evl-meta-extract-global-facts)
                (svex-eval-wog-formula-checks state))
           (let ((rule (make rp::rp-meta-rule-rec
                             :fnc 'svexl-node-eval-wog-meta-main
                             :trig-fnc 'svexl-node-eval-wog
                             :dont-rw t
                             :valid-syntax t)))
             (and (rp::rp-meta-valid-syntaxp-sk rule state)
                  (rp::valid-rp-meta-rulep rule state))))
  :otf-flg t
  :hints (("goal"
           :in-theory (e/d (rp::rp-meta-valid-syntaxp)
                           (rp::rp-termp
                            svexl-node-eval-wog-meta-main
                            rp::rp-term-listp
                            rp::valid-sc)))))||#

#|(rp::add-meta-rules svex-eval-wog-formula-checks
                    (list (make rp::rp-meta-rule-rec
                                :fnc 'svex-eval-wog-meta-main
                                :trig-fnc 'svex-eval-wog
                                :dont-rw t
                                :valid-syntax t)
                          (make rp::rp-meta-rule-rec
                                :fnc 'svexl-node-eval-wog-meta-main
                                :trig-fnc 'svexl-node-eval-wog
                                :dont-rw t
                                :valid-syntax t)))||#


(rp::add-meta-rule
 :meta-fnc svexl-node-eval-wog-meta-main
 :trig-fnc svexl-node-eval-wog
 :formula-checks svex-eval-wog-formula-checks
 :valid-syntaxp t
 :returns (mv term dont-rw))

(rp::add-meta-rule
 :meta-fnc svex-eval-wog-meta-main
 :trig-fnc svex-eval-wog
 :formula-checks svex-eval-wog-formula-checks
 :valid-syntaxp t
 :returns (mv term dont-rw))
