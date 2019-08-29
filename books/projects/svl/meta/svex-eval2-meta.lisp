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

(include-book "../svex-lemmas2")

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

;; does not seem to help much but will keep it anyways..
(define is-4vec-fix-necessary (term)
  (case-match term
    (('rp ''4vec-p &)
     nil)
    (& (b* ((term (rp::ex-from-rp term)))
         (case-match term
           (('quote x)
            (if (integerp x)
                nil
              t))
           (('4vec-concat & & &)
            nil)
           (('4vec-bitand & &)
            nil)
           (('4vec-bitor & &)
            nil)
           (('4vec-rsh & &)
            nil)
           (('4vec-lsh & &)
            nil)
           (('4vec-bitnot &)
            nil)
           ;; this list can go on with all the 4vec-functions...
           (&
            t))))))

(define nth-term (n argsvar)
  :guard (natp n)
  (if (atom argsvar)
      ''nil
    (if (zp n)
        (car argsvar)
      (nth-term (1- n) (cdr argsvar)))))

(defund svex-apply-collect-args2-meta (n max argsvar args-dontrw)
  (declare (xargs :measure (nfix (- (nfix max) (nfix n)))))
  (let* ((n (nfix n)) (max (nfix max)))
    (if (zp (- max n))
        (mv nil nil)
      (b* (((mv rest rest-dontrw)
            (svex-apply-collect-args2-meta (+ 1 n)
                                           max argsvar
                                           args-dontrw)))
        (mv (cons `(if (is-4vec-fix-necessary (nth-term ,n ,argsvar))
                       (list '4vec-fix2 (nth-term ,n ,argsvar))
                     (nth-term ,n ,argsvar))
                  rest)
            (cons `(if (is-4vec-fix-necessary (nth-term ,n ,argsvar))
                       (list 'nil (nth-term ,n ,args-dontrw))
                     (nth-term ,n ,args-dontrw))
                  rest-dontrw))))))

(defund svex-apply-cases-fn2-meta (argsvar args-dontrw optable)
  (b* (((when (atom optable))
        '((otherwise
           (mv (or (hard-error
                    'svex-apply-cases-fn2-meta
                    "attempting to apply unknown function ~x0~%"
                    (list (cons #\0 fn)))
                   (list 'quote (sv::4vec-x)))
               nil))))
       ((list sym fn args) (car optable))
       ((mv entry entry-dontrw)
        (svex-apply-collect-args2-meta 0 (len args) argsvar args-dontrw))
       (call `(mv (list ',fn . ,entry)
                  (list 'nil . ,entry-dontrw))))
    (cons (cons sym (cons call 'nil))
          (svex-apply-cases-fn2-meta argsvar args-dontrw (cdr optable)))))

(defmacro svex-apply-cases2-meta (fn args args-dontrw)
  (cons
   'case
   (cons fn
         (svex-apply-cases-fn2-meta args args-dontrw
                                    (cons '(ID sv::4VEC-FIX$INLINE (ACL2::X)
                                               "identity function") ;; had to
                                          ;; change this becaise 4vec-fix is
                                          ;; the only function that is inlined
                                          (cdr sv::*svex-op-table*))))))

(defund svex-apply2-meta (fn args args-dontrw)
  (declare (xargs :guard (and (true-listp args)
                              (true-listp args-dontrw))))
  (let* ((fn (fnsym-fix fn)))
    (svex-apply-cases2-meta fn args args-dontrw)))

(acl2::defines
 svex-eval2-meta
 :flag-defthm-macro defthm-svex-eval2-meta
 :flag-local nil

 (define svex-eval2-meta (x env-falist)
   :flag expr
   :measure (cons-count x)
   :hints (("Goal"
            :in-theory (e/d (svex-kind
                             measure-lemmas) ())))
   :verify-guards nil
   :returns (mv (result)
                (result-dont-rw rp::dont-rw-syntaxp))
   (let* ((x.kind (svex-kind2 x)))
     (case
       x.kind
       (:quote (mv (cond ((atom x) (list 'quote x))
                         ((atom (cdr x)) (list 'quote (sv::4vec-x)))
                         (t (list 'quote (cadr x))))
                   t))
       (:var (mv (let* ((val (hons-get x env-falist)))
                   (if val
                       (cdr val)
                     (list 'quote (sv::4vec-x))))
                 t))
       (otherwise
        (b* ((x.fn (car x))
             (x.args (cdr x))
             ((mv args args-dontrw)
              (svex-eval2-meta-lst x.args env-falist)))
          (svex-apply2-meta x.fn args args-dontrw))))))

 (define svex-eval2-meta-lst (lst env-falist)
   :flag list
   :measure (cons-count lst)
   :returns (mv (res true-listp)
                (res-dontrw rp::dont-rw-syntaxp))
   (if (atom lst)
       (mv nil nil)
     (b* (((mv car-term car-dontrw)
           (svex-eval2-meta (car lst) env-falist))
          ((mv rest rest-dontrw)
           (svex-eval2-meta-lst (cdr lst) env-falist)))
       (mv (cons car-term rest)
           (cons car-dontrw rest-dontrw)))))

 ///

 (acl2::more-returns
  svex-eval2-meta-lst
  (res-dontrw true-listp
              :hints (("Goal"
                       :induct (true-listp lst)
                       :in-theory (e/d () ())))))

 (verify-guards svex-eval2-meta
   :hints (("Goal"
            :in-theory (e/d (svex-kind) ())))))

(define svex-eval2-meta-main (term)
  (case-match term
    (('svex-eval2 ('quote svex) env)
     (b* ((env (rp::ex-from-rp env)))
       (case-match env
         (('falist ('quote env-falist) &)
          (svex-eval2-meta svex env-falist))
         (& (mv term nil)))))
    (& (mv term nil))))

;; (svex-eval2-meta '(partsel '0 '1 (bitand x y))
;;                  (make-fast-alist
;;                   '((x . (rp 'bitp a))
;;                     (y . b)))
;;                  'expr)

;; (svex-eval2-meta-main `(svex-eval2 '(partsel '0 '1 (bitand x y))
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
                    SVEX-ENV-FASTLOOKUP2)
                   (svex-kind2-is-svex-kind
                    4VEC-FIX2-IS-4VEC-FIX
                    SVEX-APPLY2-IS-SVEX-APPLY
                    SV::4VEC-EQUAL))))

  (local
   (defthm the-check-def
     (equal (the-check x y z)
            z)))

  (local
   (defthm SVEX-ENV-FASTLOOKUP2-def
     (equal (SVEX-ENV-FASTLOOKUP2 var env)
            (LET* ((LOOK (HONS-GET VAR ENV)))
                  (IF LOOK (CDR LOOK) (SV::4VEC-X))))
     :hints (("Goal"
              :in-theory (e/d (SVEX-ENV-FASTLOOKUP2) ())))))

  (with-output
    :off :all
    :gag-mode nil
    (rp::def-formula-checks
     svex-eval2-formula-checks
     (svex-eval2-meta-main
      sv::4vec-fix$inline
      svex-eval2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthmd svex-eval2-eval
   (implies (and (rp-evl-meta-extract-global-facts)
                 (svex-eval2-formula-checks state)
                 (consp x)
                 (equal (car x) 'svex-eval2)
                 (consp (cdr x))
                 (consp (cddr x))
                 (not (cdddr x)))
            (equal (rp-evl x a)
                   (svex-eval2 (rp-evl (cadr x) a)
                               (rp-evl (caddr x) a))))))

(local
 (defthmd rp-evl-of-ex-from-rp-reverse
   (implies (syntaxp (atom term))
            (equal (rp-evl term a)
                   (rp-evl (rp::ex-from-rp term) a)))
   :hints (("Goal"
            :in-theory (e/d (rp::is-rp) ())))))

(local
 (defthmd falist-eval
   (implies (and (rp-evl-meta-extract-global-facts)
                 (svex-eval2-formula-checks state)
                 (consp x)
                 (equal (car x) 'falist)
                 (consp (cdr x))
                 (consp (cddr x))
                 (not (cdddr x)))
            (equal (rp-evl x a)
                   (rp-evl (caddr x) a)))))

(local
 (defthmd falist-eval2
   (implies (and (rp-evl-meta-extract-global-facts)
                 (svex-eval2-formula-checks state)
                 (consp (rp::ex-from-rp x))
                 (equal (car (rp::ex-from-rp x)) 'falist)
                 (consp (cdr (rp::ex-from-rp x)))
                 (consp (cddr (rp::ex-from-rp x)))
                 (not (cdddr (rp::ex-from-rp x))))
            (equal (rp-evl x a)
                   (rp-evl (caddr (rp::ex-from-rp x)) a)))
   :hints (("Goal"
            :in-theory (e/d (rp-evl-of-ex-from-rp-reverse) ())))))

(local
 (defthm RP::FALIST-CONSISTENT-AUX-lemma
   (implies (and (rp::FALIST-CONSISTENT-AUX ENV-FALIST TERM)
                 (HONS-ASSOC-EQUAL X ENV-FALIST)
                 (HONS-ASSOC-EQUAL X (RP-EVL TERM A)))
            (EQUAL (RP-EVL (CDR (HONS-ASSOC-EQUAL X ENV-FALIST))
                           A)
                   (CDR (HONS-ASSOC-EQUAL X (RP-EVL TERM A)))))))

(local
 (defthm RP::FALIST-CONSISTENT-AUX-lemma-2
   (implies (and (rp::FALIST-CONSISTENT-AUX ENV-FALIST TERM)
                 (HONS-ASSOC-EQUAL X ENV-FALIST))
            (HONS-ASSOC-EQUAL X (RP-EVL TERM A)))))

(local
 (defthm RP::FALIST-CONSISTENT-AUX-lemma-3
   (implies (and (rp::FALIST-CONSISTENT-AUX ENV-FALIST TERM)
                 (HONS-ASSOC-EQUAL X (RP-EVL TERM A)))
            (HONS-ASSOC-EQUAL X ENV-FALIST))))

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
                 (4vec-part-install m x y z))
          )
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

   (defthm rp-evl-of-svex-apply2-meta
     (implies (and (rp-evl-meta-extract-global-facts)
                   (svex-eval2-formula-checks state))
              (equal (rp-evl (mv-nth 0 (svex-apply2-meta call args args-dontrw)) a)
                     (svex-apply2 call
                                  (rp-evl-lst args a))))
     :hints (("goal"
              :do-not-induct t
              :do-not '(preprocess)
              :expand ((:free (x y)
                              (nth x y))
                       (:free (x y)
                              (nth-term x y)))
              :in-theory (e/d (svex-apply2
                               svex-apply2-meta)
                              (svex-apply2-is-svex-apply
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
                               (:type-prescription is-4vec-fix-necessary)
                               (:type-prescription fnsym-fix)
                               (:rewrite sv::4vec-p-when-maybe-4vec-p)
                               (:type-prescription 4vec-p)
                               (:type-prescription sv::maybe-4vec-p)
                               (:rewrite
                                sv::4vec-p-when-member-equal-of-4veclist-p)
                               (:rewrite sv::maybe-4vec-p-when-4vec-p)
                               (:rewrite
                                sv::car-of-4veclist-fix-x-normalize-const-under-4vec-equiv)
                               (:rewrite sv::4vec-p-of-nth-when-4veclist-p)
                               (:type-prescription svex-eval2-formula-checks)
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
                               (:meta acl2::mv-nth-cons-meta)
                               )))))

   (defthm-svex-eval2-meta
     (defthmd rp-evl-of-svex-eval2-meta
       (implies (and (rp-evl-meta-extract-global-facts)
                     (svex-eval2-formula-checks state)
                     (rp::falist-consistent-aux env-falist term))
                (equal (rp-evl (mv-nth 0 (svex-eval2-meta x env-falist)) a)
                       (rp-evl `(svex-eval2 ,(list 'quote x) ,term) a)))
       :flag expr)

     (defthmd rp-evl-of-svex-eval2-meta-lst
       (implies (and (rp-evl-meta-extract-global-facts)
                     (svex-eval2-formula-checks state)
                     (rp::falist-consistent-aux env-falist term))
                (equal (rp-evl-lst (mv-nth 0 (svex-eval2-meta-lst lst env-falist)) a)
                       (rp-evl `(svexlist-eval2 ,(list 'quote lst) ,term) a)))
       :flag list)
     :hints (("goal"
              :in-theory (e/d (svex-eval2-meta-lst
                               svex-eval2
                               svexlist-eval2
                               svex-eval2-meta)
                              (svex-apply2-is-svex-apply)))))

   (local
    (defthm all-falist-consistent-lemma
      (implies (and (rp::all-falist-consistent term)
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

   (defthm rp-evl-of-svex-eval2-meta-main
     (implies (and (rp-evl-meta-extract-global-facts)
                   (rp::all-falist-consistent term)
                   (svex-eval2-formula-checks state))
              (equal (rp-evl (mv-nth 0 (svex-eval2-meta-main term)) a)
                     (rp-evl term a)))
     :hints (("goal"
              :use ((:instance rp-evl-of-svex-eval2-meta
                               (env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                                        term)))))
                               (a a)
                               (x (cadr (cadr term)))
                               (term (caddr (rp::ex-from-rp (caddr
                                                             term))))))
              :in-theory (e/d (svex-eval2-meta-main
                               falist-eval
                               falist-eval2
                               svex-eval2-eval) ()))))))

(local
 (encapsulate
   nil

   (defthm all-falist-consistent-svex-apply2-meta
     (implies (rp::all-falist-consistent-lst args)
              (rp::all-falist-consistent
               (mv-nth 0 (svex-apply2-meta call args args-dontrw))))
     :hints (("Goal"
              :do-not-induct t
              :expand ((:free (x y)
                              (nth x y))
                       (:free (x y)
                              (nth-term x y)))
              :in-theory (e/d (svex-apply2-meta)
                              ((:DEFINITION RP::FALIST-CONSISTENT)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE DEFAULT-CAR)
                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:TYPE-PRESCRIPTION IS-4VEC-FIX-NECESSARY)
                               (:REWRITE ACL2::O-P-DEF-O-FINP-1))))))

   (local
    (defthm lemma1
      (implies (and (RP::ALL-FALIST-CONSISTENT X)
                    (consp x)
                    (NOT (EQUAL (CAR X) 'QUOTE)))
               (RP::ALL-FALIST-CONSISTENT-LST (CDR X)))
      :hints (("Goal"
               :expand ((RP::ALL-FALIST-CONSISTENT X))
               :in-theory (e/d () ())))))

   (local
    (defthm lemma2
      (implies (and (rp::falist-consistent-aux env-falist term)
                    (rp::all-falist-consistent term)
                    (HONS-ASSOC-EQUAL X ENV-FALIST))
               (RP::ALL-FALIST-CONSISTENT (CDR (HONS-ASSOC-EQUAL X
                                                                 ENV-FALIST))))))

   #|(local
   (defthm lemma3
   (implies (and (rp::falist-consistent-aux env-falist term)
   (hons-assoc-equal x env-falist))
   (equal (rp-evl (cdr (hons-assoc-equal x env-falist))
   a)
   (cdr (hons-assoc-equal x (rp-evl term a)))))))||#

   (defthm-svex-eval2-meta
     (defthmd all-falist-consistent-svex-eval2-meta
       (implies (and ;(rp::all-falist-consistent x)
                 (rp::falist-consistent-aux env-falist term)
                 (rp::all-falist-consistent term))
                (rp::all-falist-consistent
                 (mv-nth 0 (svex-eval2-meta x env-falist))))
       :flag expr)

     (defthmd all-falist-consistent-svex-eval2-meta-lst
       (implies (and ;(rp::all-falist-consistent-lst lst)
                 (rp::falist-consistent-aux env-falist term)
                 (rp::all-falist-consistent term))
                (rp::all-falist-consistent-lst
                 (mv-nth 0 (svex-eval2-meta-lst lst env-falist))))
       :flag list)
     :hints (("Goal"
              :in-theory (e/d (svex-kind
                               SVEX-EVAL2-META
                               SVEX-EVAL2-META-LST
                               rp::is-falist)
                              ()))))

   (defthm ALL-FALIST-CONSISTENT-lemma3
     (implies (and (RP::ALL-FALIST-CONSISTENT term)
                   (rp::is-falist term))
              (and (RP::FALIST-CONSISTENT-AUX (CADR (CADR term))
                                              (CADDR term))
                   (RP::ALL-FALIST-CONSISTENT (CADDR term))))
     :hints (("Goal"
              :in-theory (e/d (rp::ex-from-rp) ()))))

   (defthm ALL-FALIST-CONSISTENT-lemma4
     (implies (and (RP::ALL-FALIST-CONSISTENT term))
              (RP::ALL-FALIST-CONSISTENT (rp::ex-from-rp term)))
     :hints (("Goal"
              :in-theory (e/d (rp::ex-from-rp
                               rp::is-rp
                               rp::is-falist) ()))))

   (defthm all-falist-consistent-svex-eval2-meta-main
     (implies (and (rp::all-falist-consistent term))
              (rp::all-falist-consistent (mv-nth 0 (svex-eval2-meta-main term))))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance
                     all-falist-consistent-svex-eval2-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                              term)))))
                     (x (cadr (cadr term)))
                     (term (caddr (rp::ex-from-rp (caddr term))))))
              :in-theory (e/d (svex-eval2-meta-main
                               rp::is-falist) ()))))))

(local
 (encapsulate
   nil

   (defthm pseudo-termp2-svex-apply2-meta
     (implies (rp::pseudo-term-listp2 args)
              (rp::pseudo-termp2
               (mv-nth 0 (svex-apply2-meta call args args-dontrw))))
     :hints (("Goal"
              :do-not-induct t
              :expand ((:free (x y)
                              (nth x y))
                       (:free (x y)
                              (nth-term x y)))
              :in-theory (e/d (svex-apply2-meta)
                              ((:DEFINITION RP::FALIST-CONSISTENT)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE DEFAULT-CAR)
                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:TYPE-PRESCRIPTION IS-4VEC-FIX-NECESSARY)
                               (:REWRITE ACL2::O-P-DEF-O-FINP-1)
                               (:REWRITE RP::PSEUDO-TERMP2-IMPLIES-CDR-LISTP)
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 3)
                               (:DEFINITION TRUE-LISTP)
                               (:DEFINITION SUBSETP-EQUAL)
                               (:DEFINITION MEMBER-EQUAL)
                               (:REWRITE
                                ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                               (:TYPE-PRESCRIPTION RP::PSEUDO-TERMP2))))))

   (local
    (defthm lemma1
      (implies (and (rp::falist-consistent-aux env-falist term)
                    (rp::pseudo-termp2 term)
                    (HONS-ASSOC-EQUAL X ENV-FALIST))
               (rp::pseudo-termp2 (CDR (HONS-ASSOC-EQUAL X
                                                         ENV-FALIST))))))

   (defthm-svex-eval2-meta
     (defthmd pseudo-termp2-svex-eval2-meta
       (implies (and ;(rp::all-falist-consistent x)
                 (rp::falist-consistent-aux env-falist term)
                 (rp::pseudo-termp2 term))
                (rp::pseudo-termp2
                 (mv-nth 0 (svex-eval2-meta x env-falist))))
       :flag expr)

     (defthmd rp::pseudo-termp2-svex-eval2-meta-lst
       (implies (and ;(rp::all-falist-consistent-lst lst)
                 (rp::falist-consistent-aux env-falist term)
                 (rp::pseudo-termp2 term))
                (rp::pseudo-term-listp2
                 (mv-nth 0 (svex-eval2-meta-lst lst env-falist))))
       :flag list)
     :hints (("Goal"
              :in-theory (e/d (svex-kind
                               SVEX-EVAL2-META
                               SVEX-EVAL2-META-LST
                               rp::is-falist)
                              ()))))

   (local
    (defthm lemma2
      (implies (and (rp::pseudo-termp2 term))
               (and (rp::pseudo-termp2 (rp::ex-from-rp term))))
      :hints (("Goal"
               :in-theory (e/d (rp::ex-from-rp rp::is-rp) ())))))

   (local
    (defthm lemma3
      (implies (and (rp::pseudo-termp2 term)
                    (consp term)
                    (not (equal (car term) 'quote))
                    (consp (cdr term))
                    (consp (cddr term)))
               (RP::PSEUDO-TERMP2 (CADDR term)))))

   (defthm pseudo-termp2-svex-eval2-meta-main
     (implies (and (rp::pseudo-termp2 term)
                   (rp::all-falist-consistent term))
              (rp::pseudo-termp2 (mv-nth 0 (svex-eval2-meta-main term))))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance
                     pseudo-termp2-svex-eval2-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                              term)))))
                     (x (cadr (cadr term)))
                     (term (caddr (rp::ex-from-rp (caddr term))))))
              :in-theory (e/d (svex-eval2-meta-main
                               rp::is-falist) ()))))))

(local
 (encapsulate
   nil

   (defthm rp-syntaxp-svex-apply2-meta
     (implies (rp::rp-syntaxp-lst args)
              (rp::rp-syntaxp
               (mv-nth 0 (svex-apply2-meta call args args-dontrw))))
     :hints (("Goal"
              :do-not-induct t
              :expand ((:free (x y)
                              (nth x y))
                       (:free (x y)
                              (nth-term x y)))
              :in-theory (e/d (svex-apply2-meta)
                              ((:DEFINITION RP::FALIST-CONSISTENT)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE DEFAULT-CAR)
                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:TYPE-PRESCRIPTION IS-4VEC-FIX-NECESSARY)
                               (:REWRITE ACL2::O-P-DEF-O-FINP-1)
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 3)
                               (:DEFINITION TRUE-LISTP)
                               (:DEFINITION SUBSETP-EQUAL)
                               (:DEFINITION MEMBER-EQUAL)
                               (:REWRITE
                                ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                               (:TYPE-PRESCRIPTION RP::RP-SYNTAXP))))))

   (local
    (defthm lemma1
      (implies (and (rp::falist-consistent-aux env-falist term)
                    (rp::rp-syntaxp term)
                    (HONS-ASSOC-EQUAL X ENV-FALIST))
               (rp::rp-syntaxp (CDR (HONS-ASSOC-EQUAL X
                                                      ENV-FALIST))))))

   (defthm-svex-eval2-meta
     (defthmd rp-syntaxp-svex-eval2-meta
       (implies (and ;(rp::all-falist-consistent x)
                 (rp::falist-consistent-aux env-falist term)
                 (rp::rp-syntaxp term))
                (rp::rp-syntaxp
                 (mv-nth 0 (svex-eval2-meta x env-falist))))
       :flag expr)

     (defthmd rp::rp-syntaxp-svex-eval2-meta-lst
       (implies (and ;(rp::all-falist-consistent-lst lst)
                 (rp::falist-consistent-aux env-falist term)
                 (rp::rp-syntaxp term))
                (rp::rp-syntaxp-lst
                 (mv-nth 0 (svex-eval2-meta-lst lst env-falist))))
       :flag list)
     :hints (("Goal"
              :in-theory (e/d (svex-kind
                               SVEX-EVAL2-META
                               SVEX-EVAL2-META-LST
                               rp::is-falist)
                              ()))))

   (local
    (defthm lemma2
      (implies (and (rp::rp-syntaxp term))
               (and (rp::rp-syntaxp (rp::ex-from-rp term))))
      :hints (("Goal"
               :in-theory (e/d (rp::ex-from-rp rp::is-rp) ())))))

   (local
    (defthm lemma3
      (implies (and (rp::rp-syntaxp term)
                    (consp term)
                    (not (equal (car term) 'quote))
                    (consp (cdr term))
                    (consp (cddr term)))
               (RP::RP-SYNTAXP (CADDR term)))))

   (defthm rp-syntaxp-svex-eval2-meta-main
     (implies (and (rp::rp-syntaxp term)
                   (rp::all-falist-consistent term))
              (rp::rp-syntaxp (mv-nth 0 (svex-eval2-meta-main term))))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance
                     rp-syntaxp-svex-eval2-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                              term)))))
                     (x (cadr (cadr term)))
                     (term (caddr (rp::ex-from-rp (caddr term))))))
              :in-theory (e/d (svex-eval2-meta-main
                               rp::is-falist) ()))))))

(local
 (encapsulate
   nil

   (local
    (in-theory (enable rp::is-rp
                       rp::is-if)))

   (defthm valid-sc-svex-apply2-meta
     (implies (rp::valid-sc-subterms args a)
              (rp::valid-sc
               (mv-nth 0 (svex-apply2-meta call args args-dontrw))
               a))
     :hints (("Goal"
              :do-not-induct t
              :expand ((:free (x y)
                              (nth x y))
                       (:free (x y)
                              (nth-term x y)))
              :in-theory (e/d (svex-apply2-meta)
                              ((:DEFINITION RP::FALIST-CONSISTENT)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE DEFAULT-CAR)
                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:TYPE-PRESCRIPTION IS-4VEC-FIX-NECESSARY)
                               (:REWRITE ACL2::O-P-DEF-O-FINP-1)
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 3)
                               (:DEFINITION TRUE-LISTP)
                               (:DEFINITION SUBSETP-EQUAL)
                               (:DEFINITION MEMBER-EQUAL)
                               (:REWRITE
                                ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                               (:TYPE-PRESCRIPTION RP::VALID-SC))))))

   (local
    (defthm lemma1
      (implies (and (rp::falist-consistent-aux env-falist term)
                    (rp::valid-sc term a)
                    (HONS-ASSOC-EQUAL X ENV-FALIST))
               (rp::valid-sc (CDR (HONS-ASSOC-EQUAL X
                                                    ENV-FALIST))
                             a))))

   (defthm-svex-eval2-meta
     (defthmd valid-sc-svex-eval2-meta
       (implies (and ;(rp::all-falist-consistent x)
                 (rp::falist-consistent-aux env-falist term)
                 (rp::valid-sc term a))
                (rp::valid-sc
                 (mv-nth 0 (svex-eval2-meta x env-falist)) a))
       :flag expr)

     (defthmd rp::valid-sc-svex-eval2-meta-lst
       (implies (and ;(rp::all-falist-consistent-lst lst)
                 (rp::falist-consistent-aux env-falist term)
                 (rp::valid-sc term a))
                (rp::valid-sc-subterms
                 (mv-nth 0 (svex-eval2-meta-lst lst env-falist)) a))
       :flag list)
     :hints (("Goal"
              :in-theory (e/d (svex-kind
                               SVEX-EVAL2-META
                               SVEX-EVAL2-META-LST
                               rp::is-falist)
                              ()))))

   (local
    (defthm lemma2
      (implies (and (rp::valid-sc term a))
               (and (rp::valid-sc (rp::ex-from-rp term) a)))
      :hints (("Goal"
               :in-theory (e/d (rp::ex-from-rp rp::is-rp) ())))))

   (local
    (defthm lemma3
      (implies (and (rp::valid-sc term a)
                    (consp term)
                    (equal (car term) 'falist)
                    (consp (cdr term))
                    (consp (cddr term)))
               (RP::VALID-SC (CADDR term) a))))

   (defthm valid-sc-svex-eval2-meta-main
     (implies (and (rp::valid-sc term a)
                   (rp::all-falist-consistent term))
              (rp::valid-sc (mv-nth 0 (svex-eval2-meta-main term))
                            a))
     :hints (("Goal"
              :do-not-induct t
              :use ((:instance
                     valid-sc-svex-eval2-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                              term)))))
                     (x (cadr (cadr term)))
                     (term (caddr (rp::ex-from-rp (caddr term))))))
              :in-theory (e/d (svex-eval2-meta-main
                               rp::is-falist) ()))))))

(defthm valid-rp-meta-rulep-svex-eval2-meta-main
  (implies (and (rp-evl-meta-extract-global-facts)
                (svex-eval2-formula-checks state))
           (let ((rule (make rp::rp-meta-rule-rec
                             :fnc 'svex-eval2-meta-main
                             :trig-fnc 'svex-eval2
                             :dont-rw t
                             :valid-syntax t)))
             (and (rp::rp-meta-valid-syntaxp-sk rule state)
                  (rp::valid-rp-meta-rulep rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (rp::RP-META-VALID-SYNTAXP)
                           (rp::PSEUDO-TERMP2
                            svex-eval2-meta-main
                            rp::PSEUDO-TERM-LISTP2
                            rp::VALID-SC
                            rp::VALID-SC)))))

(rp::add-meta-rules svex-eval2-formula-checks
                    (list (make rp::rp-meta-rule-rec
                                :fnc 'svex-eval2-meta-main
                                :trig-fnc 'svex-eval2
                                :dont-rw t
                                :valid-syntax t)))
