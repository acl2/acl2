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
; Original author: Mertcan Temel <mert@centech.com>

(in-package "SVL")

(include-book "svex-eval-wog-meta")
(include-book "../svex-eval-dollar-wog-openers")
(include-book "../svexl/svexl")
(include-book "../svexl/svexl-correct")
(include-book "../svexl/svexl-eval-dollar-correct")
(include-book "../svex-reduce-with-env")
;;(include-book "centaur/sv/svex/rewrite" :dir :system)

(include-book "std/alists/remove-assocs" :dir :system)

(local
 (include-book "../bits-sbits"))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (in-theory (enable hons-get)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; svex-apply-meta

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

(define light-4vec-fix (x)
  :enabled t
  (if (sv::4vec-p x)
      x
    (sv::4vec-x)))

(def-rp-rule :disabled-for-acl2 t
  LIGHT-4VEC-FIX-opener
  (implies (force (sv::4vec-p x))
           (equal (LIGHT-4VEC-FIX x)
                  x))
  :hints (("Goal"
           :in-theory (e/d (LIGHT-4VEC-FIX) ()))))

(add-rp-rule SV::4VECLIST-FIX)

(define list-to-consed-term (term-lst (dont-rw-lst true-listp))
  (if (atom term-lst)
      (mv ''nil nil)
    (b* (((mv rest-lst rest-dont-rw-lst)
          (list-to-consed-term (cdr term-lst) (cdr dont-rw-lst))))
      (mv `(cons ,(car term-lst)
                 ,rest-lst)
          `(cons ,(car dont-rw-lst)
                 ,rest-dont-rw-lst)))))

(defmacro svex-apply$-cases-wog-meta (fn args args-dontrw)
  `(b* ((quoted (quoted-4vec-listp args))
        (orig-args args)
        (args (if quoted (rp::unquote-all args) args)))
     (case ,fn
       ,@(take (len sv::*svex-op-table*)
               (svex-apply-cases-wog-fn-meta args args-dontrw
                                             (list* '(ID sv::4VEC-FIX$INLINE (ACL2::X)
                                                         "identity function") ;; had to
                                                    ;; change this because 4vec-fix is
                                                    ;; the only function that is
                                                    ;; inlined
                                                    (acl2::remove-assocs '(ID)
                                                                         sv::*svex-op-table*))))
       (otherwise
        (b* (((mv args args-dontrw)
              (list-to-consed-term orig-args args-dontrw)))
          (mv `(light-4vec-fix (apply$ ',fn (4veclist-fix-wog ,args)))
              `(light-4vec-fix (apply$ ',fn (4veclist-fix-wog ,args-dontrw))))))

       )))

(defund svex-apply$-wog-meta (fn args args-dontrw)
  (declare (xargs :guard (and (true-listp args)
                              (true-listp args-dontrw))
                  :verify-guards nil))
  (b* ((fn (fnsym-fix fn))
       ((mv term dont-rw)
        (svex-apply$-cases-wog-meta fn args args-dontrw)))
    (svex-apply-insert-part-select term dont-rw)))

(local
 (defthm true-listp-of-unquote-all
   (implies (true-listp x)
            (true-listp (rp::unquote-all x)))))

(local
 (defthm quoted-4vec-listp-implies-4vec-listp-when-unquoted
   (implies (and (QUOTED-4VEC-LISTP ARGS))
            (sv::4veclist-p (rp::unquote-all args)))
   :hints (("Goal"
            :in-theory (e/d (QUOTED-4VEC-LISTP) ())))))

(verify-guards svex-apply$-wog-meta
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d () ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; svex-eval$-meta (svex-eval$-wog-meta)

(acl2::defines
  svex-eval$-wog-meta
  :flag-defthm-macro defthm-svex-eval$-wog-meta
  :flag-local nil
  :prepwork ((local
              (in-theory (enable svex-kind-wog))))
  (define svex-eval$-wog-meta (x env-falist good-env-flg)
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
               (svex-eval$-wog-meta-lst x.args env-falist good-env-flg)))
           (svex-apply$-wog-meta x.fn args args-dontrw))))))

  (define svex-eval$-wog-meta-lst (lst env-falist good-env-flg)
    :flag list
    :measure (cons-count lst)
    :returns (mv (res true-listp)
                 (res-dontrw rp::dont-rw-syntaxp))
    (if (atom lst)
        (mv nil nil)
      (b* (((mv car-term car-dontrw)
            (svex-eval$-wog-meta (car lst) env-falist good-env-flg))
           ((mv rest rest-dontrw)
            (svex-eval$-wog-meta-lst (cdr lst) env-falist good-env-flg)))
        (mv (cons car-term rest)
            (cons car-dontrw rest-dontrw)))))

  ///

  (acl2::more-returns
   svex-eval$-wog-meta-lst
   (res-dontrw true-listp
               :hints (("Goal"
                        :induct (true-listp lst)
                        :in-theory (e/d () ())))))

  (verify-guards svex-eval$-wog-meta
    :hints (("Goal"
             :in-theory (e/d (svex-kind) ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; svex-eval$-wog-meta-main

(define svex-eval$-to-svexl-trig (svex env)
  :verify-guards nil
  (svex-eval$ svex env)
  ///
  (def-rp-rule svex-eval$-to-svexl-eval$
    (implies (force (svex-p svex))
             (equal (svex-eval$-to-svexl-trig svex env)
                    (svexl-eval$ (svex-to-svexl svex) env)))
    :hints (("Goal"
             :use ((:instance svexl-eval$-correct))
             :in-theory (e/d () ())))))

(define svex-eval$-wog-meta-main (term)
  (case-match term
    (('svex-eval$-wog ('quote svex) env)
     (b* ((env-orig env)
          (env (rp::ex-from-rp env)))
       (case-match env
         (('falist ('quote env-falist) &)
          (svex-eval$-wog-meta svex env-falist t))
         (''nil
          (svex-eval$-wog-meta svex nil t))
         (&
          (progn$
           (and (consp env)
                (equal (car env) 'cons)
                (cw "The environment of svex-eval$ is not a ~
fast-alist. Consider making it one for a better performance.~%"))
           (svex-eval$-wog-meta svex env-orig nil))))))
    (('svex-eval$ ('quote svex) env)
     (b* ((env-orig env))
       (b* ((large-svex (zp (nfix (svex-count-gt svex (expt 2 8)))))
            ((unless large-svex)
             ;; let the rewrite rule convert the term to svex-eva$-wog
             (mv term nil))
            ((unless (svex-p svex))
             (mv term (acl2::raise "svex-p test failed on ~p0" svex)))
            ;;(svex (svex-reduce-w/-env svex env-falist))
            )
         (mv `(svex-eval$-to-svexl-trig ',svex ,env-orig)
             `(nil t t)))))
    (& (mv term nil))))

(define svex-alist-eval$-to-svexl-alist-trig (x env)
  :verify-guards nil
  (svex-alist-eval$ x env)
  ///
  (def-rp-rule svex-alist-eval$-to-svexl-alist
    (implies (force (sv::svex-alist-p alist))
             (equal (svex-alist-eval$-to-svexl-alist-trig alist env)
                    (svexl-alist-eval$ (svex-alist-to-svexl-alist alist) env)))
    :hints (("Goal"
             :use ((:instance svexl-alist-eval$-correct))
             :in-theory (e/d () ())))))

(define svex-alist-eval$-meta (term)
  (case-match term
    (('svex-alist-eval$ ('quote alist) env)
     (b* ((- (cw "Entering svex-eval$-alist-meta ~%"))
          (env-orig env)
          (env (rp::ex-from-rp env)))
       (case-match env
         (('falist & &)
          (mv `(svex-alist-eval$-to-svexl-alist-trig ',alist ,env)
              `(nil t t)))
         (''nil
          (mv term nil))
         (&
          (if (and (consp env) (equal (car env) 'cons))
              (progn$
               (cw "Note: the environment of svex-eval$-alist is not a fast-alist. Making it a fast alist now.~%")
               (mv `(sv::svex-alist-eval$ ',alist (make-fast-alist ,env-orig))
                   `(nil t (nil t))))
            (mv term nil))))))
    (& (mv term nil))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; svexl-eval$-meta (svexl-eval$-wog-meta)

(acl2::defines
  svexl-node-eval$-wog-meta
  :flag-defthm-macro defthm-svexl-node-eval$-wog-meta
  :flag-local nil
  :prepwork ((local
              (in-theory (enable svexl-node-kind))))
  (define svexl-node-eval$-wog-meta (x node-env-falist env-falist good-env-flg)
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
               (svexl-nodelist-eval$-wog-meta x.args node-env-falist env-falist good-env-flg)))
           (svex-apply$-wog-meta x.fn args args-dontrw))))))

  (define svexl-nodelist-eval$-wog-meta (lst node-env-falist env-falist good-env-flg)
    :flag list
    :measure (cons-count lst)
    :returns (mv (res true-listp)
                 (res-dontrw rp::dont-rw-syntaxp))
    (if (atom lst)
        (mv nil nil)
      (b* (((mv car-term car-dontrw)
            (svexl-node-eval$-wog-meta (car lst) node-env-falist env-falist good-env-flg))
           ((mv rest rest-dontrw)
            (svexl-nodelist-eval$-wog-meta (cdr lst) node-env-falist env-falist good-env-flg)))
        (mv (cons car-term rest)
            (cons car-dontrw rest-dontrw)))))

  ///

  (acl2::more-returns
   svexl-nodelist-eval$-wog-meta
   (res-dontrw true-listp
               :hints (("Goal"
                        :induct (true-listp lst)
                        :in-theory (e/d () ())))))

  (verify-guards svexl-node-eval$-wog-meta
    :hints (("Goal"
             :in-theory (e/d (svexl-node-kind-wog) ())))))

(define svexl-node-eval$-wog-meta-main (term)
  (case-match term
    (('svexl-node-eval$-wog ('quote svex) node-env env)
     (b* ((env-orig env)
          (env (rp::ex-from-rp env))
          (node-env-orig node-env)
          (node-env (rp::ex-from-rp node-env)))
       (case-match env
         (('falist ('quote env-falist) &)
          (case-match node-env
            (('falist ('quote node-env-falist) &)
             (svexl-node-eval$-wog-meta svex node-env-falist env-falist t))
            (''nil
             (svexl-node-eval$-wog-meta svex nil env-falist t))
            (& (svexl-node-eval$-wog-meta svex node-env-orig env-orig nil))))
         (''nil
          (case-match node-env
            (('falist ('quote node-env-falist) &)
             (svexl-node-eval$-wog-meta svex node-env-falist nil t))
            (''nil
             (svexl-node-eval$-wog-meta svex nil nil t))
            (& (svexl-node-eval$-wog-meta svex node-env-orig env-orig nil))))
         (&
          (svexl-node-eval$-wog-meta svex node-env-orig env-orig nil)))))
    (& (mv term nil))))



;; (svex-eval$-wog-meta '(partsel '0 '1 (bitand x y))
;;                  (make-fast-alist
;;                   '((x . (rp 'bitp a))
;;                     (y . b)))
;;                  'expr)

;; (svex-eval$-wog-meta-main `(svex-eval$-wog '(partsel '0 '1 (bitand x y))
;;                                    (falist ',(make-fast-alist
;;                                               '((x . (rp 'bitp a))
;;                                                 (y . b)))
;;                                            corres)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proofs

(rp::def-formula-checks-default-evl
  rp::rp-evl
  (strip-cars rp::*small-evl-fncs*))

(local
 (encapsulate
   nil
   (local
    (in-theory (enable svexl-node-kind
                       SVEX-KIND
                       svexl-node-quote->val)))

   (local
    (set-body svexl-node-fix$inline (:definition svexl-node-fix$inline)))
   (local
    (set-body SVEXL-NODELIST-FIX$INLINE (:definition SVEXL-NODELIST-FIX$INLINE)))

   (make-flag svexl-node-fix-flag2 svexl-node-fix$inline
              :body :last
              :hints (("Goal"
                       :in-theory (e/d ()
                                       ()))))

   (local
    (set-body sv::svex-fix$inline (:definition sv::svex-fix$inline)))
   (local
    (set-body sv::SVEXLIST-FIX$INLINE (:definition sv::SVEXLIST-FIX$INLINE)))

   (make-flag svex-fix-flag2 sv::svex-fix$inline
              :body :last
              :hints (("goal"
                       :in-theory (e/d () ()))))

   ))

(encapsulate
  nil
  (local
   (in-theory (e/d (the-check
                    eql
                    hons
                    hons-get
                    SVEXL-NODE-KIND
                    svex-env-fastlookup-wog

                    )
                   (svex-kind-wog-is-svex-kind

                    SV::4VECLIST-FIX-OF-CONS
                    4VECLIST-FIX-WOG-IS-4VECLIST-FIX
                    ACL2::MEMBER-EQL-EXEC-IS-MEMBER-EQUAL
                    4VEC-ZERO-EXT-IS-4VEC-CONCAT

                    4vec-fix-wog-is-4vec-fix
                    hons-assoc-equal
                    svex-apply$-is-svex-apply$-wog
                    svexl-node-kind-wog-is-svexl-node-kind
                    sv::4vec-equal))))

; Commented out 11/2021 by Matt Kaufmann with the addition of the-check
; to guard-holcers.
;  (local
;   (defthm the-check-def
;       (equal (the-check x y z)
;              z)))

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

  (local
   (defthm hons-is-cons
     (equal (hons x y)
            (cons x Y))
     :hints (("Goal"
              :in-theory (e/d (hons) ())))))

  (local
   (defthm dummy-node-kind
     (implies (EQUAL (SVEXL-NODE-KIND X) :CALL)
              (consp x))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (SVEXL-NODE-KIND) ())))))

  ;; (make-flag PSEUDO-TERMP)

  ;; (make-flag ALL-VARS1)
  ;; (make-flag dumb-occur-var)

  (with-output
    :off :all
    :on (error)
    :gag-mode nil
    (rp::def-formula-checks
      svex-eval$-wog-formula-checks
      (

       svex-eval$-to-svexl-trig
       svex-alist-eval$-to-svexl-alist-trig
       ;;svex-eval$-wog-meta-main

       sv::4vec-fix$inline
       svl::4vec-concat$
       make-fast-alist
       svex-env-fastlookup-wog
       ;;svexl-node-eval$-wog-meta-main
       svexl-node-eval$-wog
       svexl-eval$-wog
       svexl-eval$
       svex-eval$
       svexl-alist-eval$-wog
       SVEXL-NODELIST-FIX$INLINE
       sv::svex-alist-eval$
       svexl-alist-eval$
       svex-eval$-wog
       light-4vec-fix)
      :skip '(rp-trans apply$))))

#|(local
(defthmd svex-eval$-wog-eval$
(implies (and (rp-evl-meta-extract-global-facts)
(svex-eval$-wog-formula-checks state)
(consp x)
(equal (car x) 'svex-eval$-wog)
(consp (cdr x))
(consp (cddr x))
(not (cdddr x)))
(and (equal (rp-evl x a)
(svex-eval$-wog (rp-evl (cadr x) a)
(rp-evl (caddr x) a)))
(equal (rp-evlt x a)
(svex-eval$-wog (rp-evlt (cadr x) a)
(rp-evlt (caddr x) a)))))))|#

#|(local
(defthmd svexl-node-eval$-wog-eval$
(implies (and (rp-evl-meta-extract-global-facts)
(svex-eval$-wog-formula-checks state)
(consp x)
(equal (car x) 'svexl-node-eval$-wog)
(consp (cdr x))
(consp (cddr x))
(consp (cdddr x))
(not (cddddr x)))
(and (equal (rp-evl x a)
(svexl-node-eval$-wog (rp-evl (cadr x) a)
(rp-evl (caddr x) a)
(rp-evl (cadddr x) a)))
(equal (rp-evlt x a)
(svexl-node-eval$-wog (rp-evlt (cadr x) a)
(rp-evlt (caddr x) a)
(rp-evlt (cadddr x) a)))))))|#

#|(local
(defthmd svex-env-fastlookup-wog-eval$
(implies (and (rp-evl-meta-extract-global-facts)
(svex-eval$-wog-formula-checks state)
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
(rp-evl (caddr x) a)))))))|#

(progn
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
   (defthmd falist-eval$
     (implies (and (rp-evl-meta-extract-global-facts)
                   (svex-eval$-wog-formula-checks state)
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
   (defthmd falist-eval$2
     (implies (and (rp-evl-meta-extract-global-facts)
                   (svex-eval$-wog-formula-checks state)
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
              (hons-assoc-equal x env-falist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rp-evl-of-svex-eval$-meta

(local
 (defret rp-evlt-of-svex-apply-insert-part-select
   (implies (and (rp-evl-meta-extract-global-facts)
                 (svex-eval$-wog-formula-checks state))
            (equal (rp-evlt res a)
                   (rp-evlt term a)))
   :fn svex-apply-insert-part-select
   :hints (("Goal"
            :in-theory (e/d (sv::4vec-sign-ext-of-4vec-part-select
                             svex-apply-insert-part-select
                             4VEC-CONCAT$
                             4vec-concat-insert-4vec-part-select)
                            ())))))

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

   (defthm rp-evl-of-if-call-to-if*
     (IMPLIES t
              (EQUAL (RP-EVL (cons 'if rest) ACL2::A)
                     (IF* (RP-EVL (car rest) ACL2::A)
                          (RP-EVL (CADR rest) ACL2::A)
                          (RP-EVL (CADDR rest) ACL2::A))))
     :hints (("Goal"
              :in-theory (e/d () ()))))

   (defthm RP-EVL-OF-LAMBDA-better
     (equal (rp-evl `((lambda . ,x) . ,y) a)
            (rp-evl (cadr x)
                    (pairlis$ (car x)
                              (rp-evl-lst y a))))
     :hints (("Goal"
              :in-theory (e/d (RP::RP-EVL-OF-LAMBDA) ()))))

   (defthm if*-of-constant
     (and (equal (if* t x y) x)
          (equal (if* nil x y) y))
     :hints (("Goal"
              :in-theory (e/d (if*) ()))))

   (defthm if*-of-true-first-arg
     (implies (sv::4vec-p test)
              (equal (if* (sv::4vec-p test) x y)
                     x)))

   (defthm rp-evl-of-trans-list-of-rp-trans-lst
     (equal (RP-EVL (RP::TRANS-LIST (RP-TRANS-LST ARGS))
                    A)
            (RP-EVLT-LST ARGS A))
     :hints (("Goal"
              :induct (len args)
              :in-theory (e/d (RP-TRANS-LST
                               rp-trans
                               rp-trans-lst
                               rp::trans-list)
                              ()))))

   (defthm rp-evlt-of-mv-nth-0-of-LIST-TO-CONSED-TERM
     (equal (rp-evlt (mv-nth 0
                             (list-to-consed-term args args-dontrw))
                     a)
            (rp-evlt `(list ,@args) a))
     :hints (("Goal"
              :in-theory (e/d (list-to-consed-term) ()))))

   (defthm rp-evl-of-svex-apply$-wog-meta
     (implies (and (rp-evl-meta-extract-global-facts)
                   (svex-eval$-wog-formula-checks state))
              (equal (rp-evlt (mv-nth 0 (svex-apply$-wog-meta call args args-dontrw)) a)
                     (rp-evlt `(svex-apply$-wog ',call (list ,@args)) a)))
     :hints (("goal"
              :do-not-induct t
              :do-not '(preprocess)
              :expand ((:free (x y)
                              (nth x y))
                       (:free (x y)
                              (nth-term x y)))
              :in-theory (e/d
                          (RP-EVL-OF-SVEX-APPLY$-WOG-WHEN-SVEX-EVAL$-WOG-FORMULA-CHECKS
                           rp-evl-of-fncall-args
                           svex-apply$-wog
                           svex-apply$-wog-meta)
                          ((:DEFINITION RP::TRANS-LIST)
                           (:TYPE-PRESCRIPTION RP-TRANS-LST)
                           (:REWRITE RP::RP-EVL-OF-NATP-CALL)
                           (:REWRITE RP::RP-EVL-OF-FORCE-CALL)
                           (:REWRITE
                            RP::RP-TRANS-LST-IS-LST-WHEN-LIST-IS-ABSENT)

                           (:TYPE-PRESCRIPTION IF*)
                           (:META
                            RP::BINARY-OR**/AND**-GUARD-META-CORRECT)
                           (:REWRITE
                            RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                           (:REWRITE RP::CONSP-RP-TRANS-LST)

                           (:REWRITE RP::RP-EVL-OF-ZP-CALL)
                           (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL)
                           (:REWRITE RP::RP-EVL-OF-UNARY---CALL)

                           NTH-OPENER
                           NTH-TERM-OPENER

                           4VEC-OVERRIDE-WHEN-INTEGERP
                           svex-apply$-is-svex-apply$-wog
                           (:definition nth)
                           (:rewrite default-cdr)
                           (:rewrite default-car)
                           (:rewrite sv::4vec-fix-of-4vec)
                           ;;                               (:rewrite acl2::o-p-o-infp-car)
                           ;;                               (:forward-chaining
                           ;;                                acl2::|a <= b & ~(a = b)  =>  a < b|)
                           (:rewrite sv::fnsym-fix-when-fnsym-p)
                           (:rewrite
                            rp::rp-evl-of-rp-equal-cnt-subterms-call)
                           (:rewrite rp::rp-evl-of-lambda)

                           (:type-prescription fnsym-fix)
                           (:rewrite sv::4vec-p-when-maybe-4vec-p)
                           (:type-prescription 4vec-p)
                           (:type-prescription sv::maybe-4vec-p)
                           (:rewrite
                            sv::4vec-p-when-member-equal-of-4veclist-p)
                           (:rewrite sv::maybe-4vec-p-when-4vec-p)
                           (:rewrite sv::4vec-p-of-nth-when-4veclist-p)
                           (:type-prescription svex-eval$-wog-formula-checks)
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
                           if*
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

   (defthm-svex-eval$-wog-meta
     (defthmd rp-evl-of-svex-eval$-wog-meta
       (implies (and (rp-evl-meta-extract-global-facts)
                     (svex-eval$-wog-formula-checks state)
                     (if good-env-flg
                         (rp::falist-consistent-aux env-falist term)
                       (equal term env-falist)))
                (equal (rp-evlt (mv-nth 0 (svex-eval$-wog-meta x env-falist good-env-flg)) a)
                       (rp-evlt `(svex-eval$-wog ',x ,term) a)))
       :flag expr)

     (defthmd rp-evl-of-svex-eval$-wog-meta-lst
       (implies (and (rp-evl-meta-extract-global-facts)
                     (svex-eval$-wog-formula-checks state)
                     (if good-env-flg
                         (rp::falist-consistent-aux env-falist term)
                       (equal term env-falist)))
                (equal (rp-evlt-lst
                        (mv-nth 0 (svex-eval$-wog-meta-lst lst env-falist good-env-flg))
                        a)
                       (rp-evlt `(svexlist-eval$-wog ',lst ,term) a)))
       :flag list)
     :hints (("goal"
              :do-not-induct t
              :expand ((:free (x y) (rp-trans (cons x y)))
                       (:free (x term) (RP-TRANS (LIST 'SVEX-EVAL$-WOG
                                                       (LIST 'QUOTE x)
                                                       TERM)))
                       (:free (lst term) (RP-TRANS (LIST 'SVEXLIST-EVAL$-WOG
                                                         (LIST 'QUOTE LST)
                                                         TERM)))
                       (:free (x y) (rp-trans-lst (cons x y))))
              :in-theory (e/d (svex-eval$-wog-meta-lst
                               SVEX-ENV-FASTLOOKUP-WOG
                               svex-eval$-wog
                               svexlist-eval$-wog
                               ;;svex-eval$-wog-eval
                               ;;svexl-node-eval$-wog-eval
                               ;;svex-env-fastlookup-wog-eval
                               svex-eval$-wog-meta
                               rp-evl-of-fncall-args)
                              (RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                               rp-evl-of-svex-eval$-wog-when-svex-eval$-wog-formula-checks
                               rp-evl-of-svexlist-eval$-wog-when-svex-eval$-wog-formula-checks
                               svex-apply$-is-svex-apply$-wog
                               rp-trans
                               rp-trans-lst
                               SVEX-ENV-FASTLOOKUP-WOG-DEF
                               if*
                               nth-opener

                               RP-EVL-OF-SVEX-APPLY$-WOG-WHEN-SVEX-EVAL$-WOG-FORMULA-CHECKS

                               )))
             (and STABLE-UNDER-SIMPLIFICATIONP
                  '(:use ((:instance
                           rp-evl-of-svex-eval$-wog-when-svex-eval$-wog-formula-checks
                           (x (LIST 'QUOTE X))
                           (env (LIST 'QUOTE (RP-EVLT TERM A)))
                           (cmr::env nil))

                          (:instance
                           rp-evl-of-svex-eval$-wog-when-svex-eval$-wog-formula-checks
                           (x (LIST 'QUOTE X))
                           (env (RP-EVLT TERM A))
                           (cmr::env a))
                          (:instance
                           rp-evl-of-svex-eval$-wog-when-svex-eval$-wog-formula-checks
                           (x (LIST 'QUOTE X))
                           (env (RP-TRANS ENV-FALIST))
                           (cmr::env a))

                          (:instance
                           rp-evl-of-svexlist-eval$-wog-when-svex-eval$-wog-formula-checks
                           (args (LIST 'QUOTE LST))
                           (env (RP-TRANS TERM))
                           (cmr::env a))
                          (:instance
                           rp-evl-of-svexlist-eval$-wog-when-svex-eval$-wog-formula-checks
                           (args (RP-TRANS (LIST 'QUOTE LST)))
                           (env (RP-TRANS ENV-FALIST))
                           (cmr::env a)))

                         ))))))

;; (define svex-reduce-w/-env-for-eval$ (svex env)
;;   :verify-guards nil
;;   (case-match env
;;     (('falist ('quote falist) rp::term)
;;      (svex-reduce-w/-env svex falist))
;;     (('falist ''nil ''nil)
;;      (svex-reduce-w/-env svex nil))
;;     (& svex))
;;   ///
;;   (define trig-svex-reduce-w/-env (svex env)
;;     :verify-guards nil
;;     :enabled t
;;     (svex-eval$ svex env))
;;   (def-rp-rule apply-svex-reduce-w/-env-for-svex-eval$
;;     (implies (and (rp-termp env)
;;                   (svex-p svex))
;;              (equal (trig-svex-reduce-w/-env


(local
 (encapsulate
   nil
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
               :in-theory (e/d (rp::is-rp rp::falist-consistent) ())))))

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

   (local
    (defthmd svexl-correct-reverse
      (implies (and (svex-p svex))
               (equal (svexl-eval$ (svex-to-svexl svex) env)
                      (svex-eval$ svex env)
                      ))
      :hints (("goal"
               :in-theory (e/d (svexl-eval$-correct) ())))))

   (defthm rp-evl-of-svex-eval$-wog-meta-main
     (implies (and (rp-evl-meta-extract-global-facts)
                   (rp::rp-termp term)
                   (svex-eval$-wog-formula-checks state))
              (equal (rp-evlt (mv-nth 0 (svex-eval$-wog-meta-main term)) a)
                     (rp-evlt term a)))
     :hints (("goal"
              :use ((:instance rp-evl-of-svex-eval$-wog-meta
                               (env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                                        term)))))
                               (a a)
                               (good-env-flg t)
                               (x (cadr (cadr term)))
                               (term (caddr (rp::ex-from-rp (caddr
                                                             term)))))
                    (:instance rp-evl-of-svex-eval$-wog-meta
                               (env-falist nil)
                               (a a)
                               (good-env-flg t)
                               (x (cadr (cadr term)))
                               (term ''nil))
                    (:instance rp-evl-of-svex-eval$-wog-meta
                               (good-env-flg nil)
                               (a a)
                               (x (cadr (cadr term)))
                               (term (CADDR TERM))
                               (env-falist (CADDR TERM))))
              :in-theory (e/d (svex-eval$-wog-meta-main
                               svexl-eval$-wog-is-svexl-eval$
                               svex-eval$-wog-is-svex-eval$
                               svexlist-eval$-wog-is-svexlist-eval$
                               falist-eval$
                               SVEXL-CORRECT-reverse
                               rp-trans
                               rp-trans-lst
                               rp::rp-evl-of-ex-from-rp
                               falist-eval$2
                               rp-evl-of-fncall-args
                               ;;svex-eval$-wog-eval$

                               RP-EVL-OF-SVEX-EVAL$-TO-SVEXL-TRIG-WHEN-SVEX-EVAL$-WOG-FORMULA-CHECKS
                               )

                              (;;RP::RP-EVL-OF-VARIABLE
                               svex-reduce-w/-env-correct
                               nfix
                               (:REWRITE ACL2::ZP-OPEN)
                               (:REWRITE ACL2::NFIX-UNDER-NAT-EQUIV)
                               zp)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rp-evl-of-svexl-node-eval$-wog-meta-main

(local
 (encapsulate
   nil

   (defthm-svexl-node-eval-wog-meta
     (defthmd rp-evl-of-svexl-node-eval$-wog-meta
       (implies (and (rp-evl-meta-extract-global-facts)
                     (svex-eval$-wog-formula-checks state)
                     (if good-env-flg
                         (and (rp::falist-consistent-aux env-falist env-term)
                              (rp::falist-consistent-aux node-env-falist node-env-term))
                       (and (equal env-term env-falist)
                            (equal node-env-term node-env-falist))))
                (equal (rp-evlt (mv-nth 0 (svexl-node-eval$-wog-meta
                                           x node-env-falist env-falist good-env-flg))
                                a)
                       (rp-evlt `(svexl-node-eval$-wog
                                  ,(list 'quote x) ,node-env-term ,env-term)
                                a)))
       :flag expr)

     (defthmd rp-evl-of-svexl-node-eval$-wog-meta-lst
       (implies (and (rp-evl-meta-extract-global-facts)
                     (svex-eval$-wog-formula-checks state)
                     (if good-env-flg
                         (and (rp::falist-consistent-aux env-falist env-term)
                              (rp::falist-consistent-aux node-env-falist node-env-term))
                       (and (equal env-term env-falist)
                            (equal node-env-term node-env-falist))))
                (equal (rp-evlt-lst
                        (mv-nth 0 (svexl-nodelist-eval$-wog-meta
                                   lst node-env-falist env-falist good-env-flg))
                        a)
                       (rp-evlt `(svexl-nodelist-eval$-wog
                                  ,(list 'quote lst) ,node-env-term ,env-term)
                                a)))
       :flag list)
     :hints (("goal"
              :do-not-induct t
              :in-theory (e/d (svex-eval$-wog-meta-lst
                               svex-env-fastlookup-wog
                               svexl-nodelist-eval$-wog-meta
                               svex-eval$-wog-meta
                               svexl-nodelist-eval$-wog
                               SVEXL-NODE-KIND-WOG
                               SVEX-KIND
                               svexl-node-eval$-wog-meta
                               svex-kind-wog
                               svexl-node-eval$-wog
                               rp-evl-of-fncall-args)
                              (RP::TRANS-LIST
                               (:REWRITE DEFAULT-CAR)
                               (:REWRITE DEFAULT-CDR)
                               ;;if*
                               ;;SVEX-ENV-FASTLOOKUP-WOG
                               ;;ACL2::MV-NTH-OF-CONS
                               ;;SVEX-ENV-FASTLOOKUP-WOG-DEF
                               svex-apply$-is-svex-apply$-wog)))
             (and STABLE-UNDER-SIMPLIFICATIONP
                  '(:use ((:instance
                           rp-evl-of-SVEXL-NODE-EVAL$-WOG-when-svex-eval$-wog-formula-checks
                           (x ''nil)
                           (node-env (LIST 'QUOTE (RP-EVLT NODE-ENV-TERM A)))
                           (env (LIST 'QUOTE (RP-EVLT ENV-TERM A)))
                           (cmr::env nil))
                          (:instance
                           rp-evl-of-SVEXL-NODE-EVAL$-WOG-when-svex-eval$-wog-formula-checks
                           (x ''nil)
                           (node-env (LIST 'QUOTE
                                           (RP-EVLT NODE-ENV-FALIST A)))
                           (env (LIST 'QUOTE (RP-EVLT ENV-FALIST A)))
                           (cmr::env nil))
                          (:instance
                           rp-evl-of-SVEXL-NODE-EVAL$-WOG-when-svex-eval$-wog-formula-checks
                           (x (LIST 'QUOTE X))
                           (node-env (LIST 'QUOTE (RP-EVLT NODE-ENV-TERM A)))
                           (env (LIST 'QUOTE (RP-EVLT ENV-TERM A)))
                           (cmr::env nil))
                          (:instance
                           rp-evl-of-SVEXL-NODE-EVAL$-WOG-when-svex-eval$-wog-formula-checks
                           (x (LIST 'QUOTE X))
                           (node-env (LIST 'QUOTE
                                           (RP-EVLT NODE-ENV-FALIST A)))
                           (env (LIST 'QUOTE (RP-EVLT ENV-FALIST A)))
                           (cmr::env nil))
                          (:instance
                           rp-evl-of-SVEXL-NODELIST-EVAL$-WOG-when-svex-eval$-wog-formula-checks
                           (lst (LIST 'QUOTE LST))
                           (node-env (LIST 'QUOTE (RP-EVLT NODE-ENV-TERM A)))
                           (env (LIST 'QUOTE (RP-EVLT ENV-TERM A)))
                           (cmr::env nil))
                          (:instance
                           rp-evl-of-SVEXL-NODELIST-EVAL$-WOG-when-svex-eval$-wog-formula-checks
                           (lst (LIST 'QUOTE LST))
                           (node-env (LIST 'QUOTE
                                           (RP-EVLT NODE-ENV-FALIST A)))
                           (env (LIST 'QUOTE (RP-EVLT ENV-FALIST A)))
                           (cmr::env nil))
                          )

                         ))))

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
               :in-theory (e/d (rp::is-rp rp::falist-consistent) ())))))

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

   (defthmd rp-evl-of-svexl-node-eval$-wog-meta-good-env-flg=nil
     (implies (and (rp-evl-meta-extract-global-facts)
                   (svex-eval$-wog-formula-checks state))
              (equal (rp-evlt (mv-nth 0 (svexl-node-eval$-wog-meta
                                         x node-env env nil))
                              a)
                     (rp-evlt `(svexl-node-eval$-wog
                                ,(list 'quote x) ,node-env ,env)
                              a)))
     :hints (("Goal"
              :use ((:instance rp-evl-of-svexl-node-eval$-wog-meta
                               (good-env-flg nil)
                               (NODE-ENV-TERM NODE-ENV)
                               (NODE-ENV-FALIST NODE-ENV)
                               (ENV-TERM env)
                               (ENV-FALIST env)))
              :in-theory (e/d () (rp-evl-of-svexl-node-eval$-wog-meta)))))

   (defthmd rp-evl-of-svexl-node-eval$-wog-meta-env=nil
     (implies (and (rp-evl-meta-extract-global-facts)
                   (svex-eval$-wog-formula-checks state))
              (equal (rp-evlt (mv-nth 0 (svexl-node-eval$-wog-meta
                                         x nil nil t))
                              a)
                     (rp-evlt `(svexl-node-eval$-wog
                                ,(list 'quote x) 'nil 'nil)
                              a)))
     :hints (("Goal"
              :use ((:instance rp-evl-of-svexl-node-eval$-wog-meta
                               (good-env-flg t)
                               (NODE-ENV-TERM ''nil)
                               (NODE-ENV-FALIST nil)
                               (ENV-TERM ''nil)
                               (ENV-FALIST nil)))
              :in-theory (e/d () (rp-evl-of-svexl-node-eval$-wog-meta)))))

   (defthmd rp-evl-of-svexl-node-eval$-wog-meta-1st-env=nil
     (implies (and (rp-evl-meta-extract-global-facts)
                   (svex-eval$-wog-formula-checks state)
                   (rp::falist-consistent-aux env-falist env-term))
              (equal (rp-evlt (mv-nth 0 (svexl-node-eval$-wog-meta
                                         x nil env-falist t))
                              a)
                     (rp-evlt `(svexl-node-eval$-wog
                                ,(list 'quote x) 'nil ,env-term)
                              a)))
     :hints (("Goal"
              :use ((:instance rp-evl-of-svexl-node-eval$-wog-meta
                               (good-env-flg t)
                               (NODE-ENV-TERM ''nil)
                               (NODE-ENV-FALIST nil)
                               ))
              :in-theory (e/d () (rp-evl-of-svexl-node-eval$-wog-meta)))))

   (defthmd rp-evl-of-svexl-node-eval$-wog-meta-2nd-env=nil
     (implies (and (rp-evl-meta-extract-global-facts)
                   (svex-eval$-wog-formula-checks state)
                   (rp::falist-consistent-aux node-env-falist node-env-term))
              (equal (rp-evlt (mv-nth 0 (svexl-node-eval$-wog-meta
                                         x node-env-falist nil t))
                              a)
                     (rp-evlt `(svexl-node-eval$-wog
                                ,(list 'quote x) ,node-env-term 'nil)
                              a)))
     :hints (("Goal"
              :use ((:instance rp-evl-of-svexl-node-eval$-wog-meta
                               (good-env-flg t)

                               (ENV-TERM ''nil)
                               (ENV-FALIST nil)))
              :in-theory (e/d () (rp-evl-of-svexl-node-eval$-wog-meta)))))

   (defthmd rp-evl-of-svexl-node-eval$-wog-meta-goof-env-fgl=t
     (implies (and (rp-evl-meta-extract-global-facts)
                   (svex-eval$-wog-formula-checks state)
                   (and (rp::falist-consistent-aux env-falist env-term)
                        (rp::falist-consistent-aux node-env-falist node-env-term)))
              (equal (rp-evlt (mv-nth 0 (svexl-node-eval$-wog-meta
                                         x node-env-falist env-falist t))
                              a)
                     (rp-evlt `(svexl-node-eval$-wog
                                ,(list 'quote x) ,node-env-term ,env-term)
                              a)))
     :hints (("Goal"
              :use ((:instance rp-evl-of-svexl-node-eval$-wog-meta
                               (good-env-flg t)
                               ))
              :in-theory (e/d () ()))))


   (defthm rp-evl-of-svexl-node-eval$-wog-meta-main
     (implies (and (rp-evl-meta-extract-global-facts)
                   (rp::rp-termp term)
                   (svex-eval$-wog-formula-checks state))
              (equal (rp-evlt (mv-nth 0 (svexl-node-eval$-wog-meta-main term)) a)
                     (rp-evlt term a)))
     :hints (("goal"

              :expand ((RP::FALIST-CONSISTENT (RP::EX-FROM-RP (CADDR TERM)))
                       (RP::FALIST-CONSISTENT (RP::EX-FROM-RP (CADDDR TERM))))
              :do-not-induct t
              :do-not '(preprocess fertilize generalize)
              :use ((:instance RP::RP-TERMP-EX-FROM-RP
                               (rp::term (caddr term)))
                    (:instance RP::RP-TERMP-EX-FROM-RP
                               (rp::term (cadddr term))))
              :in-theory (e/d (svexl-node-eval$-wog-meta-main
                               rp-evl-of-svexl-node-eval$-wog-meta
                               falist-eval$
                               rp::rp-evl-of-ex-from-rp
                               falist-eval$2
                               rp-evl-of-svexl-node-eval$-wog-meta-goof-env-fgl=t
                               rp-evl-of-svexl-node-eval$-wog-meta-good-env-flg=nil
                               rp-evl-of-svexl-node-eval$-wog-meta-env=nil
                               rp-evl-of-svexl-node-eval$-wog-meta-1st-env=nil
                               rp-evl-of-svexl-node-eval$-wog-meta-2nd-env=nil
                               ;;svex-eval$-wog-eval$
                               rp-evl-of-fncall-args
                               )
                              (ALL-FALIST-CONSISTENT-LEMMA
                               RP::FALIST-CONSISTENT-AUX
                               RP::RP-TERMP-EX-FROM-RP
                               RP::RP-TERMP-EXTRACT-FROM-RP
                               rp::rp-evl-of-variable
                               (:type-prescription rp::rp-termp)
                               (:type-prescription o<)
                               (:type-prescription rp::rp-term-listp)
                               (:type-prescription rp::is-rp$inline)
                               (:type-prescription rp::falist-consistent-aux)
                               (:type-prescription o-p)
                               ;;(:rewrite svex-eval$-wog-eval$)
                               ;;                               (:forward-chaining
                               ;;                                acl2::|a <= b & ~(a = b)  =>  a < b|)
                               (:rewrite rp::rp-evl-of-unary-/-call)
                               (:rewrite rp::rp-termp-caddr)
                               (:rewrite default-car)
                               (:rewrite rp::rp-termp-cadddr)
                               (:definition rp::ex-from-rp)
                               (:rewrite default-cdr)
                               (:rewrite rp::rp-termp-cadr)
                               (:rewrite rp::rp-termp-implies-cdr-listp)
                               (:type-prescription
                                svex-eval$-wog-formula-checks)
                               (:type-prescription rp::falist-consistent)
                               (:definition rp::falist-consistent-aux)
                               (:type-prescription
                                svexl-node-kind-wog$inline)
                               (:definition eq)
                               ;;                               (:rewrite acl2::o-p-o-infp-car)
                               (:definition rp::falist-consistent))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rp-termp-of-functions

(local
 (defret rp-termp-svex-apply$-insert-part-select
   (implies (rp::rp-termp term)
            (rp::rp-termp res))
   :fn svex-apply-insert-part-select
   :hints (("Goal"
            :in-theory (e/d (svex-apply-insert-part-select)
                            ())))))

(local
 (encapsulate
   nil

   (defthm RP::RP-TERMP-of-LIST-TO-CONSED-TERM
     (implies (force (rp::rp-term-listp args))
              (RP::RP-TERMP (MV-NTH 0
                                    (LIST-TO-CONSED-TERM ARGS ARGS-DONTRW))))
     :hints (("Goal"
              :in-theory (e/d (LIST-TO-CONSED-TERM) ()))))

   (defthm rp-termp-svex-apply$-wog-meta
     (implies (rp::rp-term-listp args)
              (rp::rp-termp
               (mv-nth 0 (svex-apply$-wog-meta call args args-dontrw))))
     :hints (("goal"
              :do-not-induct t
              :expand ((:free (x y)
                              (rp::rp-termp (cons x y)))
                       (:free (x y)
                              (nth x y))
                       (:free (x y)
                              (nth-term x y)))
              :in-theory (e/d (svex-apply$-wog-meta)
                              ((:definition rp::falist-consistent)
                               (:rewrite default-cdr)
                               (:rewrite default-car)
                               ;;                                (:rewrite acl2::o-p-o-infp-car)
                               ;;                                (:rewrite acl2::o-p-def-o-finp-1)
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

   (defthm-svex-eval$-wog-meta
     (defthmd rp-termp-svex-eval$-wog-meta
       (implies (and (if good-env-flg
                         (rp::falist-consistent-aux env-falist term)
                       (equal term env-falist))
                     (rp::rp-termp term))
                (rp::rp-termp
                 (mv-nth 0 (svex-eval$-wog-meta x env-falist good-env-flg))))
       :flag expr)

     (defthmd rp::rp-termp-svex-eval$-wog-meta-lst
       (implies (and (if good-env-flg
                         (rp::falist-consistent-aux env-falist term)
                       (equal term env-falist))
                     (rp::rp-termp term))
                (rp::rp-term-listp
                 (mv-nth 0 (svex-eval$-wog-meta-lst lst env-falist good-env-flg))))
       :flag list)
     :hints (("goal"
              :in-theory (e/d (svex-kind
                               svex-eval$-wog-meta
                               svex-eval$-wog-meta-lst
                               rp::is-falist)
                              ()))))

   (defthm-svexl-node-eval$-wog-meta
     (defthmd rp-termp-svexl-node-eval$-wog-meta
       (implies (and (if good-env-flg
                         (and (rp::falist-consistent-aux env-falist env-term)
                              (rp::falist-consistent-aux node-env-falist node-env-term))
                       (and (equal env-term env-falist)
                            (equal node-env-term node-env-falist)))
                     (rp::rp-termp node-env-term)
                     (rp::rp-termp env-term))
                (rp::rp-termp
                 (mv-nth 0 (svexl-node-eval$-wog-meta x node-env-falist env-falist good-env-flg))))
       :flag expr)

     (defthmd rp-termp-svexl-node-eval$-wog-meta-lst
       (implies (and (if good-env-flg
                         (and (rp::falist-consistent-aux env-falist env-term)
                              (rp::falist-consistent-aux node-env-falist node-env-term))
                       (and (equal env-term env-falist)
                            (equal node-env-term node-env-falist)))
                     (rp::rp-termp env-term)
                     (rp::rp-termp node-env-term))
                (rp::rp-term-listp
                 (mv-nth 0 (svexl-nodelist-eval$-wog-meta lst node-env-falist env-falist good-env-flg))))
       :flag list)
     :hints (("goal"
              :in-theory (e/d (svexl-node-kind
                               svexl-node-kind-wog
                               svexl-nodelist-eval$-wog-meta
                               svexl-node-eval$-wog-meta
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
                                          (caddr term)))
      :hints (("Goal"
               :in-theory (e/d (rp::falist-consistent) ())))))

   (defthm rp-termp-svex-eval$-wog-meta-main
     (implies (and (rp::rp-termp term))
              (rp::rp-termp (mv-nth 0 (svex-eval$-wog-meta-main term))))
     :hints (("goal"
              :do-not-induct t
              :do-not '(preprocess)
              :expand ((:free (x)
                              (rp::rp-termp (cons 'SVEX-EVAL$-TO-SVEXL-TRIG x)))
                       (:free (x)
                              (rp::rp-termp (cons 'svex-eval$-wog x)))
                       (:free (x)
                              (rp::rp-termp (cons 'svexl-eval$ x)))
                       (:free (x)
                              (rp::rp-termp (cons 'QUOTE x)))
                       (:free (x)
                              (rp::rp-termp (cons 'make-fast-alist x)))
                       (:free (x y)
                              (rp::rp-term-listp (cons x y))))
              :use ((:instance
                     rp-termp-svex-eval$-wog-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                              term)))))
                     (good-env-flg t)
                     (x (cadr (cadr term)))
                     (term (caddr (rp::ex-from-rp (caddr term)))))
                    (:instance
                     rp-termp-svex-eval$-wog-meta
                     (env-falist nil)
                     (good-env-flg t)
                     (x (cadr (cadr term)))
                     (term ''nil))
                    (:instance
                     rp-termp-svex-eval$-wog-meta
                     (env-falist (CADDR TERM))
                     (term (CADDR TERM))
                     (good-env-flg nil)
                     (x (CADR (CADR TERM)))
                     )
                    )
              :in-theory (e/d (svex-eval$-wog-meta-main
                               rp::is-falist)
                              ((:definition rp::falist-consistent)
                               rp-termp-svex-eval$-wog-meta
                               RP::RP-TERM-LISTP
                               RP::RP-TERMP
                               (:type-prescription rp::falist-consistent)
                               #|rp-termp-svex-eval$-wog-meta||#)))))

   (defthm rp-termp-svexl-node-eval$-wog-meta-main
     (implies (and (rp::rp-termp term))
              (rp::rp-termp (mv-nth 0 (svexl-node-eval$-wog-meta-main term))))
     :hints (("goal"
              :do-not-induct t
              :do-not '(preprocess)
              :use ((:instance
                     rp-termp-svexl-node-eval$-wog-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (cadddr
                                                              term)))))
                     (node-env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                                   term)))))
                     (good-env-flg t)
                     (x (cadr (cadr term)))
                     (env-term (caddr (rp::ex-from-rp (cadddr term))))
                     (node-env-term (caddr (rp::ex-from-rp (caddr term)))))
                    (:instance
                     rp-termp-svexl-node-eval$-wog-meta
                     (env-falist nil)
                     (node-env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                                   term)))))
                     (good-env-flg t)
                     (x (cadr (cadr term)))
                     (env-term ''nil)
                     (node-env-term (caddr (rp::ex-from-rp (caddr term)))))
                    (:instance
                     rp-termp-svexl-node-eval$-wog-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (cadddr
                                                              term)))))
                     (node-env-falist nil)
                     (good-env-flg t)
                     (x (cadr (cadr term)))
                     (env-term (caddr (rp::ex-from-rp (cadddr term))))
                     (node-env-term ''nil))
                    (:instance
                     rp-termp-svexl-node-eval$-wog-meta
                     (env-falist nil)
                     (node-env-falist nil)
                     (good-env-flg t)
                     (x (cadr (cadr term)))
                     (env-term ''nil)
                     (node-env-term ''nil))
                    (:instance
                     rp-termp-svexl-node-eval$-wog-meta
                     (env-falist (CADdDR TERM))
                     (node-env-falist (CADDR TERM))
                     (env-term (CAdDDR TERM))
                     (node-env-term (CADDR TERM))
                     (good-env-flg nil)
                     (x (CADR (CADR TERM)))
                     ))
              :in-theory (e/d (SVEXL-NODE-EVAL$-WOG-META-MAIN
                               rp::is-falist)
                              ((:definition rp::falist-consistent)
                               rp-termp-svex-eval$-wog-meta
                               RP::RP-TERM-LISTP
                               RP::RP-TERMP
                               (:type-prescription rp::falist-consistent)
                               #|rp-termp-svex-eval$-wog-meta||#)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; valid-sc-of-functions

(local
 (defret valid-sc-svex-apply$-insert-part-select
   (implies (rp::valid-sc term a)
            (rp::valid-sc res a))
   :fn svex-apply-insert-part-select
   :hints (("Goal"
            :in-theory (e/d (svex-apply-insert-part-select
                             rp::is-rp
                             rp::is-if)
                            ())))))

(local
 (defthm valid-sc-of-LIST-TO-CONSED-TERM
   (implies (rp::valid-sc-subterms args a)
            (RP::VALID-SC (MV-NTH 0
                                  (LIST-TO-CONSED-TERM ARGS ARGS-DONTRW))
                          A))
   :hints (("Goal"
            :in-theory (e/d (RP::VALID-SC
                             rp::is-rp
                             rp::is-if
                             LIST-TO-CONSED-TERM) ())))))

(local
 (encapsulate
   nil

   (local
    (in-theory (enable rp::is-rp
                       rp::is-if)))

   (defthm valid-sc-svex-apply$-wog-meta
     (implies (rp::valid-sc-subterms args a)
              (rp::valid-sc
               (mv-nth 0 (svex-apply$-wog-meta call args args-dontrw))
               a))
     :hints (("goal"
              :do-not-induct t
              :expand ((:free (x y)
                              (nth x y))
                       (:free (x y)
                              (nth-term x y)))
              :in-theory (e/d (svex-apply$-wog-meta)
                              ((:definition rp::falist-consistent)
                               (:rewrite default-cdr)
                               (:rewrite default-car)
                               ;;                               (:rewrite acl2::o-p-o-infp-car)
                               ;;                               (:rewrite acl2::o-p-def-o-finp-1)
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

   (defthm-svex-eval$-wog-meta
     (defthmd valid-sc-svex-eval$-wog-meta
       (implies (and (if good-env-flg
                         (rp::falist-consistent-aux env-falist term)
                       (equal term env-falist))
                     (rp::valid-sc term a))
                (rp::valid-sc
                 (mv-nth 0 (svex-eval$-wog-meta x env-falist good-env-flg)) a))
       :flag expr)

     (defthmd rp::valid-sc-svex-eval$-wog-meta-lst
       (implies (and (if good-env-flg
                         (rp::falist-consistent-aux env-falist term)
                       (equal term env-falist))
                     (rp::valid-sc term a))
                (rp::valid-sc-subterms
                 (mv-nth 0 (svex-eval$-wog-meta-lst lst env-falist good-env-flg)) a))
       :flag list)
     :hints (("goal"
              :in-theory (e/d (svex-kind
                               svex-eval$-wog-meta
                               svex-eval$-wog-meta-lst
                               rp::is-falist)
                              ()))))

   (defthm-svexl-node-eval$-wog-meta
     (defthmd valid-sc-svexl-node-eval$-wog-meta
       (implies (and (if good-env-flg
                         (and (rp::falist-consistent-aux env-falist env-term)
                              (rp::falist-consistent-aux node-env-falist node-env-term))
                       (and (equal env-term env-falist)
                            (equal node-env-term node-env-falist)))
                     (rp::valid-sc node-env-term a)
                     (rp::valid-sc env-term a))
                (rp::valid-sc
                 (mv-nth 0 (svexl-node-eval$-wog-meta x node-env-falist env-falist good-env-flg)) a))
       :flag expr)

     (defthmd rp::valid-sc-svexl-node-eval$-wog-meta-lst
       (implies (and (if good-env-flg
                         (and (rp::falist-consistent-aux env-falist env-term)
                              (rp::falist-consistent-aux node-env-falist node-env-term))
                       (and (equal env-term env-falist)
                            (equal node-env-term node-env-falist)))
                     (rp::valid-sc node-env-term a)
                     (rp::valid-sc env-term a))
                (rp::valid-sc-subterms
                 (mv-nth 0 (svexl-nodelist-eval$-wog-meta lst node-env-falist env-falist good-env-flg)) a))
       :flag list)
     :hints (("goal"
              :in-theory (e/d (svexl-node-kind
                               svexl-node-eval$-wog-meta
                               svexl-nodelist-eval$-wog-meta
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
                                          (caddr term)))
      :hints (("Goal"
               :in-theory (e/d (rp::falist-consistent) ())))))

   (defthm valid-sc-svex-eval$-wog-meta-main
     (implies (and (rp::valid-sc term a)
                   (rp::rp-termp term))
              (rp::valid-sc (mv-nth 0 (svex-eval$-wog-meta-main term))
                            a))
     :hints (("goal"
              :do-not-induct t
              :use ((:instance
                     valid-sc-svex-eval$-wog-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                              term)))))
                     (x (cadr (cadr term)))
                     (good-env-flg t)
                     (term (caddr (rp::ex-from-rp (caddr term)))))
                    (:instance
                     valid-sc-svex-eval$-wog-meta
                     (env-falist nil)
                     (x (cadr (cadr term)))
                     (good-env-flg t)
                     (term ''nil))

                    (:instance
                     valid-sc-svex-eval$-wog-meta
                     (env-falist (caddr term))
                     (x (cadr (cadr term)))
                     (good-env-flg nil)
                     (term (caddr term))))
              :in-theory (e/d (svex-eval$-wog-meta-main
                               rp::is-falist) ()))))

   (defthm valid-sc-svexl-node-eval$-wog-meta-main
     (implies (and (rp::valid-sc term a)
                   (rp::rp-termp term))
              (rp::valid-sc (mv-nth 0 (svexl-node-eval$-wog-meta-main term))
                            a))
     :hints (("goal"
              :do-not-induct t
              :use ((:instance
                     valid-sc-svexl-node-eval$-wog-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (cadddr
                                                              term)))))
                     (node-env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                                   term)))))
                     (x (cadr (cadr term)))
                     (good-env-flg t)
                     (env-term (caddr (rp::ex-from-rp (cadddr term))))
                     (node-env-term (caddr (rp::ex-from-rp (caddr term)))))
                    (:instance
                     valid-sc-svexl-node-eval$-wog-meta
                     (env-falist nil)
                     (node-env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                                   term)))))
                     (x (cadr (cadr term)))
                     (good-env-flg t)
                     (env-term ''nil)
                     (node-env-term (caddr (rp::ex-from-rp (caddr term)))))
                    (:instance
                     valid-sc-svexl-node-eval$-wog-meta
                     (env-falist (cadr (cadr (rp::ex-from-rp (cadddr
                                                              term)))))
                     (node-env-falist nil)
                     (x (cadr (cadr term)))
                     (good-env-flg t)
                     (env-term (caddr (rp::ex-from-rp (cadddr term))))
                     (node-env-term ''nil))
                    (:instance
                     valid-sc-svexl-node-eval$-wog-meta
                     (env-falist nil)
                     (node-env-falist nil)
                     (x (cadr (cadr term)))
                     (good-env-flg t)
                     (env-term ''nil)
                     (node-env-term ''nil))
                    (:instance
                     valid-sc-svexl-node-eval$-wog-meta
                     (env-falist (cadddr term))
                     (node-env-falist (caddr term))
                     (x (cadr (cadr term)))
                     (good-env-flg nil)
                     (node-env-term (caddr term))
                     (env-term (cadddr term))))
              :in-theory (e/d (svexl-node-eval$-wog-meta-main
                               rp::is-falist)
                              ((:DEFINITION RP::RP-TERMP)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE RP::VALID-SC-CADR)
                               ;;                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               (:REWRITE LEMMA3)
                               (:DEFINITION RP::FALIST-CONSISTENT))))))))

(rp::add-meta-rule
 :meta-fnc svexl-node-eval$-wog-meta-main
 :trig-fnc svexl-node-eval$-wog
 :formula-checks svex-eval$-wog-formula-checks
 :valid-syntaxp t
 :returns (mv term dont-rw))

(rp::add-meta-rule
 :meta-fnc svex-eval$-wog-meta-main
 :trig-fnc svex-eval$-wog
 :formula-checks svex-eval$-wog-formula-checks
 :valid-syntaxp t
 :returns (mv term dont-rw))

(progn
  (local
   (defthmd svexl-alist-correct-reverse
     (implies (sv::svex-alist-p alist)
              (equal (svexl-alist-eval$ (svex-alist-to-svexl-alist alist) env)
                     (sv::svex-alist-eval$ alist env)))
     :hints (("goal"
              :do-not-induct t
              :in-theory (e/d (svexl-alist-eval$-correct)
                              ())))))

  (local
   (defthm rp-termp-and-falist-consistent-aux
     (implies (and (rp::rp-termp term)
                   (equal (car term) 'falist)
                   (consp (cdr term))
                   (consp (cddr term))
                   (not (cdddr term))
                   (quotep (cadr term)))
              (rp::falist-consistent-aux (cadr (cadr term))
                                         (caddr term)))
     :hints (("Goal"
              :in-theory (e/d (rp::falist-consistent) ())))))

  (local
   (defthm rp-evlt-of-falist
     (implies (case-match term (('falist & &) t))
              (equal (rp-evlt term a)
                     (rp-evlt (caddr term) a)))))

  (local
   (defthmd
     rp::rp-evlt-of-ex-from-rp-reverse
     (implies (syntaxp (not (rp::include-fnc rp::term 'rp::ex-from-rp)))
              (equal
               (rp-evl (rp-trans rp::term) rp::a)
               (rp-evl (rp-trans (rp::ex-from-rp rp::term))
                       rp::a)))
     :hints
     (("goal" :in-theory (e/d (rp::ex-from-rp rp::is-rp) nil))))))

(rp::add-meta-rule
 :meta-fnc svex-alist-eval$-meta
 :trig-fnc sv::svex-alist-eval$
 :formula-checks svex-eval$-wog-formula-checks
 :valid-syntaxp t
 :returns (mv term dont-rw)

 :hints (("Goal"
          :in-theory (e/d (svex-alist-eval$-meta
                           svexl-alist-correct-reverse
                           rp::is-rp
                           rp-evl-of-fncall-args
                           RP::RP-EVLT-OF-EX-FROM-RP-reverse
                           rp::is-if

                           rp-evl-of-SVEX-ALIST-EVAL$-TO-SVEXL-ALIST-TRIG-when-svex-eval$-wog-formula-checks
                           )
                          (rp::rp-evlt-of-ex-from-rp)))))
