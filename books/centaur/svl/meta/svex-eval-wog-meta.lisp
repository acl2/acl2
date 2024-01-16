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

(include-book "../svex-eval-wog-openers")
(include-book "../svex-eval-dollar-wog-openers")
(include-book "../svexl/svexl")
(include-book "../svexl/svexl-correct")
(include-book "../svexl/svexl-eval-dollar-correct")
(include-book "../svex-reduce/top")
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

(define nth-term (n argsvar)
  :guard (natp n)
  (if (atom argsvar)
      ''nil
    (if (zp n)
        (car argsvar)
      (nth-term (1- n) (cdr argsvar)))))

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
                                       (list* '(ID sv::4VEC-FIX$INLINE (ACL2::X)
                                                   "identity function") ;; had to
                                              ;; change this because 4vec-fix is
                                              ;; the only function that is
                                              ;; inlined
                                              ;; '(sv::? 4vec-?-raw (x y z) nil)
                                              ;; '(sv::?* 4vec-?*-raw (x y z)
                                              ;;          nil)
                                              ;; '(sv::?! 4vec-?!-raw (x y z) nil)
                                              (acl2::remove-assocs '(ID ;;sv::?
                                                                     ;;sv::?* sv::?!
                                                                     )
                                                                   sv::*svex-op-table*))))))

(define list-to-consed-term (term-lst (dont-rw-lst true-listp))
  (if (atom term-lst)
      (mv ''nil nil)
    (b* (((mv rest-lst rest-dont-rw-lst)
          (list-to-consed-term (cdr term-lst) (cdr dont-rw-lst))))
      (mv `(cons ,(car term-lst)
                 ,rest-lst)
          `(cons ,(car dont-rw-lst)
                 ,rest-dont-rw-lst)))))

(define light-4vec-fix (x)
  :enabled t
  (if (sv::4vec-p x)
      x
    (sv::4vec-x)))

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

(progn
  (add-rp-rule sv::4veclist-fix)

  (def-rp-rule :disabled-for-acl2 t
    light-4vec-fix-opener
    (implies (force (sv::4vec-p x))
             (equal (light-4vec-fix x)
                    x))
    :hints (("goal"
             :in-theory (e/d (light-4vec-fix) ()))))

  (defthm light-4vec-fix-opener-side-cond
    (implies (force (sv::4vec-p x))
             (sv::4vec-p x))
    :rule-classes nil)

  (rp::rp-attach-sc light-4vec-fix-opener
                    light-4vec-fix-opener-side-cond))


(define svex-apply-insert-part-select (term dont-rw)
  :returns (mv res res-dont-rw)
  (case-match term
    (('sv::4vec-sign-ext width x)
     (b* ((width-dont-rw (rp::dont-rw-car (rp::dont-rw-cdr dont-rw)))
          (x-dont-rw  (rp::dont-rw-car (rp::dont-rw-cdr (rp::dont-rw-cdr dont-rw)))))
       (mv `(sv::4vec-sign-ext ,width (sv::4vec-part-select '0 ,width ,x))
           `(nil ,width-dont-rw (nil t ,width-dont-rw ,x-dont-rw)))))
    (('sv::4vec-zero-ext width x)
     (b* ((width-dont-rw (rp::dont-rw-car (rp::dont-rw-cdr dont-rw)))
          (x-dont-rw  (rp::dont-rw-car (rp::dont-rw-cdr (rp::dont-rw-cdr dont-rw)))))
       (mv `(sv::4vec-zero-ext ,width (sv::4vec-part-select '0 ,width ,x))
           `(nil ,width-dont-rw (nil t ,width-dont-rw ,x-dont-rw)))))
    (('sv::4vec-concat width x y)
     (b* ((width-dont-rw (rp::dont-rw-car (rp::dont-rw-cdr dont-rw)))
          (x-dont-rw  (rp::dont-rw-car (rp::dont-rw-cdr (rp::dont-rw-cdr dont-rw))))
          (y-dont-rw  (rp::dont-rw-car (rp::dont-rw-cdr
                                        (rp::dont-rw-cdr
                                         (rp::dont-rw-cdr dont-rw))))))
       (mv `(svl::4vec-concat$ ,width (sv::4vec-part-select '0 ,width ,x) ,y)
           `(nil ,width-dont-rw (nil t ,width-dont-rw ,x-dont-rw) ,y-dont-rw))))
    (('svl::4vec-concat$ width x y)
     (b* ((width-dont-rw (rp::dont-rw-car (rp::dont-rw-cdr dont-rw)))
          (x-dont-rw  (rp::dont-rw-car (rp::dont-rw-cdr (rp::dont-rw-cdr dont-rw))))
          (y-dont-rw  (rp::dont-rw-car (rp::dont-rw-cdr
                                        (rp::dont-rw-cdr
                                         (rp::dont-rw-cdr dont-rw))))))
       (mv `(svl::4vec-concat$ ,width (sv::4vec-part-select '0 ,width ,x) ,y)
           `(nil ,width-dont-rw (nil t ,width-dont-rw ,x-dont-rw) ,y-dont-rw))))
    (('sv::4VEC-PART-INSTALL lsb width x y)
     (b* (((unless (and (quotep width)
                        (consp (cdr width))
                        (natp (unquote width))))
           (mv term dont-rw))
          (lsb-dont-rw (rp::dont-rw-car (rp::dont-rw-cdr dont-rw)))
          (width-dont-rw (rp::dont-rw-car
                          (rp::dont-rw-cdr
                           (rp::dont-rw-cdr dont-rw))))
          (x-dont-rw  (rp::dont-rw-car
                       (rp::dont-rw-cdr
                        (rp::dont-rw-cdr
                         (rp::dont-rw-cdr dont-rw)))))
          (y-dont-rw (rp::dont-rw-car
                      (rp::dont-rw-cdr
                       (rp::dont-rw-cdr
                        (rp::dont-rw-cdr
                         (rp::dont-rw-cdr dont-rw)))))))
       (mv `(sv::4vec-part-install ,lsb ,width ,x (sv::4vec-part-select '0 ,width ,y))
           `(nil ,lsb-dont-rw ,width-dont-rw ,x-dont-rw (nil t ,width-dont-rw ,y-dont-rw)))))

    (&
     (mv term dont-rw))))

(defund svex-apply-wog-meta (fn args args-dontrw)
  (declare (xargs :guard (and (true-listp args)
                              (true-listp args-dontrw))
                  :verify-guards nil))
  (b* ((fn (fnsym-fix fn))
       ((mv term dont-rw)
        (svex-apply-cases-wog-meta fn args args-dontrw)))
    (svex-apply-insert-part-select term dont-rw)))

(defund svex-apply$-wog-meta (fn args args-dontrw)
  (declare (xargs :guard (and (true-listp args)
                              (true-listp args-dontrw))
                  :verify-guards nil))
  (b* ((fn (fnsym-fix fn))
       ((mv term dont-rw)
        (svex-apply$-cases-wog-meta fn args args-dontrw)))
    (svex-apply-insert-part-select term dont-rw)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; svex-eval-meta (svex-eval-wog-meta)

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

(local
 (in-theory (disable (:DEFINITION ACL2::APPLY$-BADGEP)
                     (:DEFINITION MEMBER-EQUAL)
                     (:DEFINITION SUBSETP-EQUAL))))

(svex-eval-lemma-tmpl
 (verify-guards svex-apply-wog-meta
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d ()
                            ((:REWRITE 4VEC-P-OF-IF)
                             (:REWRITE BITP-IMPLIES-4VECP)
                             (:DEFINITION BITP)))))))

(svex-eval-lemma-tmpl
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
              :in-theory (e/d (svex-kind) ()))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; svex-eval-wog-meta-main

(mutual-recursion
 (defun svex-count-gt (acl2::x val)
   (declare
    (xargs
     :hints
     ((and
       stable-under-simplificationp
       '(:expand
         ((svex-fix acl2::x)
          (sv::svexlist-fix acl2::x))
         :in-theory
         (e/d (sv::svex-var
               sv::svex-quote
               sv::svex-call
               SVEX-CALL->ARGS
               SVEX-KIND
               SVEX-KIND-WOG)))))
     :guard-hints (("Goal"
                    :in-theory (e/d (SVEX-KIND-WOG) ())))))

   (declare (xargs :measure (let ((acl2::x (svex-fix acl2::x)))
                              (acl2-count acl2::x))

                   :verify-guards t))
   (if (not (posp val))
       0
     (case (svex-kind-wog acl2::x)
       (:var (1- val))
       (:quote (1- val))
       (:call
        (svexlist-count-gt (cdr acl2::x) (+ val -1))))))
 (defun svexlist-count-gt (acl2::x val)
   (declare
    (xargs :verify-guards t

           :measure (let ((acl2::x (sv::svexlist-fix acl2::x)))
                      (acl2-count acl2::x))))
   (if (not (posp val))
       0
     (if (atom acl2::x)
         (1- val)
       (svexlist-count-gt (cdr acl2::x)
                          (svex-count-gt (car acl2::x) (1- val)))))))

(svex-eval-lemma-tmpl
 (define svex-eval-wog-meta-main (term
                                  (context rp::rp-term-listp))
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
           (progn$
            (and (consp env)
                 (equal (car env) 'cons)
                 (cw "The environment of svex-eval is not a ~
fast-alist. Consider making it one for a better performance.~%"))
            (svex-eval-wog-meta svex env-orig nil))))))
     (('svex-eval ('quote svex) env)
      (b* ((env-orig env)
           (env (rp::ex-from-rp env)))
        (case-match env
          (('falist ('quote env-falist) &)
           (b* ((large-svex (zp (nfix (svex-count-gt svex (expt 2 8)))))
                ((unless (and large-svex
                              (svex-p svex)))
                 (mv term nil))
                (svex (svex-reduce-w/-env svex :env env-falist :config nil))
                (svexl (svex-to-svexl svex)))
             (mv `(svexl-eval ',svexl ,env-orig)
                 `(nil t t))))
          (&
           (mv term nil)))))
     (& (mv term nil)))))

(svex-eval-lemma-tmpl
 (define svex-alist-eval-meta-aux (term
                                   (context rp::rp-term-listp)
                                   &key
                                   (convert-to-svexl 't))
   (case-match term
     (('sv::svex-alist-eval ('quote alist) env)
      (b* ((- (cw "Entering svex-eval-alist-meta ~%"))
           (- (or convert-to-svexl
                  (cw " (convert-to-svexl is disabled)~%")))
           (env-orig env)
           (env (rp::ex-from-rp env)))
        (case-match env
          (('falist ('quote env-falist) &)
           (b* (
                ((Unless (sv::svex-alist-p alist)) ;; for guards
                 (mv term nil))

                (- (cw "Starting: svl::svex-alist-reduce-w/-env. ~%"))
                (- (time-tracker :svex-alist-eval-meta-aux :end))
                (- (time-tracker :svex-alist-eval-meta-aux :init
                                 :times '(1 2 3 4 5)
                                 :interval 5
                                 ))
                (- (time-tracker :svex-alist-eval-meta-aux :start!))
                (alist (svexalist-convert-bitnot-to-bitxor alist))
                (alist (svex-alist-reduce-w/-env alist :env env-falist :config nil))
                (- (time-tracker :svex-alist-eval-meta-aux :stop))
                (- (time-tracker :svex-alist-eval-meta-aux :print?
                                 :min-time 0
                                 :msg "The total runtime of svl::svex-alist-reduce-w/-env ~
was ~st seconds."))

                ;;(- (cw "Starting: sv::svex-alist-rewrite-top ~%"))
                ;;(alist (sv::svex-alist-rewrite-top alist))
                ;;(alist (sv::svex-alist-rewrite-fixpoint alist))

                ((unless convert-to-svexl)
                 ;; return  identity  so  that  the  returned  term  can  be
                 ;; rewritten to sv::svex-alist-eval$
                 (mv `(identity (sv::svex-alist-eval ',alist ,env-orig))
                     `(nil t)))

                (- (cw "Starting: svl::svex-alist-to-svexl-alist ~%"))
                (svexl-alist (svex-alist-to-svexl-alist alist))
                (- (let ((x (svexl-alist->node-array svexl-alist))) ;; for guards
                     (cw "Finished: svl::svex-alist-to-svexl-alist. Resulting svexl-alist has ~p0 nodes.~%~%" (len x)))))
             (mv `(svexl-alist-eval ',svexl-alist ,env-orig)
                 `(nil t t))))
          (''nil
           (mv term nil))
          (&
           (if (and (consp env) (equal (car env) 'cons))
               (progn$
                (cw "Note: the environment of svex-eval-alist is not a fast-alist. Making it a fast alist now.~%")
                (mv `(sv::svex-alist-eval ',alist (make-fast-alist ,env-orig))
                    `(nil t (nil t))))
             (mv term nil))))))
     (& (mv term nil)))))

(svex-eval-lemma-tmpl
 (progn
   (define svex-alist-eval-meta (term
                                 (context rp::rp-term-listp))
     :enabled t
     (svex-alist-eval-meta-aux term context :convert-to-svexl t))

   (define svex-alist-eval-meta-w/o-svexl (term
                                           (context rp::rp-term-listp))
     :enabled t
     (svex-alist-eval-meta-aux term context :convert-to-svexl nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; svexl-eval-meta (svexl-eval-wog-meta)

(svex-eval-lemma-tmpl
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
              :in-theory (e/d (svexl-node-kind-wog) ()))))))

(svex-eval-lemma-tmpl
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
     (& (mv term nil)))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proofs

(rp::def-formula-checks-default-evl
  rp::rp-evl
  (list*
   'apply$ 'badge-userfn 'apply$-userfn
   (strip-cars rp::*small-evl-fncs*)))

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
                       :in-theory (e/d () ()))))))

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
                   ((:REWRITE DEFAULT-CAR)
                    4veclist-fix-wog-is-4veclist-fix
                    svex-kind-wog-is-svex-kind
                    ACL2::MEMBER-EQL-EXEC-IS-MEMBER-EQUAL
                    4VEC-ZERO-EXT-IS-4VEC-CONCAT

                    4vec-fix-wog-is-4vec-fix
                    hons-assoc-equal
                    svex-apply-is-svex-apply-wog
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

  (with-output
    :off :all
    :gag-mode nil
    (rp::def-formula-checks
      svex-ev-wog-formula-checks
      (;;svex-eval-wog-meta-main
       sv::4vec-fix$inline
       svexl-nodelist-fix$inline
       4veclist-fix-wog
       identity
       svl::4vec-concat$
       make-fast-alist
       svex-env-fastlookup-wog
       ;;svexl-node-eval-wog-meta-main
       svexl-node-eval-wog
       light-4vec-fix

       svexl-eval-wog
       svexl-eval
       svex-eval
       svexl-alist-eval-wog
       svex-alist-eval
       svexl-alist-eval
       svex-eval-wog

       svex-eval$
       svex-eval$-wog
       svexl-alist-eval$
       svex-alist-eval$
       svexl-eval$
       svexl-eval$-wog
       svexl-node-eval$-wog

       bits))))

(local
 (svex-eval-lemma-tmpl
  (defthmd svex-eval-wog-eval
    (implies (and (rp-evl-meta-extract-global-facts)
                  (svex-ev-wog-formula-checks state)
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
                                        (rp-evlt (caddr x) a))))))))

(local
 (svex-eval-lemma-tmpl
  (defthmd svexl-node-eval-wog-eval
    (implies (and (rp-evl-meta-extract-global-facts)
                  (svex-ev-wog-formula-checks state)
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
                                              (rp-evlt (cadddr x) a))))))))

(local
 (defthmd svex-env-fastlookup-wog-eval
   (implies (and (rp-evl-meta-extract-global-facts)
                 (svex-ev-wog-formula-checks state)
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
 (rp::create-regular-eval-lemma light-4vec-fix 1 svex-ev-wog-formula-checks))

(local
 (rp::create-regular-eval-lemma apply$ 2 svex-ev-wog-formula-checks))

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
                 (svex-ev-wog-formula-checks state)
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
                 (svex-ev-wog-formula-checks state)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rp-evl-of-svex-eval-meta

(local
 (defret rp-evlt-of-svex-apply-insert-part-select
   (implies (and (rp-evl-meta-extract-global-facts)
                 (svex-ev-wog-formula-checks state))
            (equal (rp-evlt res a)
                   (rp-evlt term a)))
   :fn svex-apply-insert-part-select
   :hints (("Goal"
            :in-theory (e/d (sv::4vec-sign-ext-of-4vec-part-select
                             svex-apply-insert-part-select
                             4VEC-CONCAT$
                             4vec-concat-insert-4vec-part-select)
                            ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rp-evl-of-svex-eval-meta

(local
 (defthm svex-ev-wog-formula-checks-implies-svex-reduce-formula-checks
   (implies (svex-ev-wog-formula-checks state)
            (svex-reduce-formula-checks state))
   :hints (("Goal"
            :in-theory (e/d (svex-reduce-formula-checks
                             svex-ev-wog-formula-checks)
                            ())))))

(local
 (svex-eval-lemma-tmpl
  (defret svex-alist-eval-of-svex-alist-reduce-w/-env-correct-less-general
    (implies (and (sv::svex-alist-p svex-alist)
                  (rp::rp-term-listp context)
                  (rp::valid-sc env-term a)
                  (rp::eval-and-all context a)
                  (rp::falist-consistent-aux env env-term)
                  (equal (svex-reduce-config->width-extns config) nil)
                  (equal (svex-reduce-config->integerp-extns config) nil)
                  (rp-evl-meta-extract-global-facts)
                  (svex-reduce-formula-checks state))
             (equal (svex-alist-eval res-alist (rp-evlt env-term a))
                    (svex-alist-eval svex-alist (rp-evlt env-term a))))
    :fn svex-alist-reduce-w/-env
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance
                    svex-alist-eval-of-svex-alist-reduce-w/-env-correct
                    (big-env env)))
             :in-theory (e/d ()
                             ()))))))

(local
 (svex-eval-lemma-tmpl
  (defret svex-eval-of-svex-reduce-w/-env-correct-less-general
    (implies (and (svex-p svex)
                  (rp::rp-term-listp context)
                  (rp::valid-sc env-term a)
                  (rp::eval-and-all context a)
                  (rp::falist-consistent-aux env env-term)
                  (equal (svex-reduce-config->width-extns config) nil)
                  (equal (svex-reduce-config->integerp-extns config) nil)
                  (rp-evl-meta-extract-global-facts)
                  (svex-reduce-formula-checks state))
             (equal (svex-eval (svex-reduce-w/-env svex) (rp-evlt env-term a))
                    (svex-eval svex (rp-evlt env-term a))))
    :fn svex-reduce-w/-env
    :hints (("Goal"
             :use ((:instance svex-eval-of-svex-reduce-w/-env-correct
                              (big-env env)))
             :in-theory (e/d () ()))))))

(local
 (defthm rp-evlt-of-mv-nth-0-of-LIST-TO-CONSED-TERM
   (equal (rp-evlt (mv-nth 0
                           (list-to-consed-term args args-dontrw))
                   a)
          (rp-evlt `(list ,@args) a))
   :hints (("Goal"
            :in-theory (e/d (list-to-consed-term) ())))))

(local
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

   (svex-eval-lemma-tmpl
    (defthm rp-evl-of-svex-apply-wog-meta
      (implies (and (rp-evl-meta-extract-global-facts)
                    (svex-ev-wog-formula-checks state))
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
                               (4VEC-OVERRIDE-WHEN-INTEGERP
                                svex-apply-is-svex-apply-wog
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
                                (:type-prescription svex-ev-wog-formula-checks)
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
                                (:meta acl2::mv-nth-cons-meta)))))))

   (svex-eval-lemma-tmpl
    (defthm-svex-eval-wog-meta
      (defthmd rp-evl-of-svex-eval-wog-meta
        (implies (and (rp-evl-meta-extract-global-facts)
                      (svex-ev-wog-formula-checks state)
                      (if good-env-flg
                          (rp::falist-consistent-aux env-falist term)
                        (equal term env-falist)))
                 (equal (rp-evlt (mv-nth 0 (svex-eval-wog-meta x env-falist good-env-flg)) a)
                        (rp-evlt `(svex-eval-wog ,(list 'quote x) ,term) a)))
        :flag expr)

      (defthmd rp-evl-of-svex-eval-wog-meta-lst
        (implies (and (rp-evl-meta-extract-global-facts)
                      (svex-ev-wog-formula-checks state)
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
                                rp-trans-lst))))))

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
    (in-theory (enable svexl-eval$-correct)))
   (local
    (svex-eval-lemma-tmpl
     (defthmd svexl-eval-correct-reverse
       (implies (and (svex-p svex))
                (equal (svexl-eval (svex-to-svexl svex) env)
                       (svex-eval svex env)
                       ))
       :hints (("goal"
                :in-theory (e/d (svexl-correct) ()))))))
   (local
    (in-theory (disable svexl-eval$-correct)))

   (svex-eval-lemma-tmpl
    (defthm rp-evl-of-svex-eval-wog-meta-main
      (implies (and (rp-evl-meta-extract-global-facts)
                    (rp::rp-termp term)
                    (svex-ev-wog-formula-checks state)
                    (rp::rp-term-listp context)
                    (rp::valid-sc term a)
                    (rp::eval-and-all context a))
               (equal (rp-evlt (mv-nth 0 (svex-eval-wog-meta-main term context)) a)
                      (rp-evlt term a)))
      :hints (("goal"
               :do-not-induct t
               :use ((:instance rp-evl-of-svex-eval-wog-meta
                                (env-falist (cadr (cadr (rp::ex-from-rp (caddr
                                                                         term)))))
                                (a a)
                                (good-env-flg t)
                                (x (cadr (cadr term)))
                                (term (caddr (rp::ex-from-rp (caddr term)))))
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
                                svexl-eval-wog-is-svexl-eval
                                svex-eval-wog-is-svex-eval
                                svexlist-eval-wog-is-svexlist-eval
                                falist-eval
                                SVEXL-eval-CORRECT-reverse
                                rp-trans
                                rp-trans-lst
                                rp::rp-evl-of-ex-from-rp
                                falist-eval2
                                svex-eval-wog-eval)
                               (rp::rp-evl-of-variable
                                rp-evl-of-svex-eval-wog-meta
                                nfix
                                (:REWRITE ACL2::ZP-OPEN)
                                (:REWRITE ACL2::NFIX-UNDER-NAT-EQUIV)
                                zp))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rp-evl-of-svexl-node-eval-wog-meta-main

(local
 (encapsulate
   nil

   (svex-eval-lemma-tmpl
    (defthm-svexl-node-eval-wog-meta
      (defthmd rp-evl-of-svexl-node-eval-wog-meta
        (implies (and (rp-evl-meta-extract-global-facts)
                      (svex-ev-wog-formula-checks state)
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
                      (svex-ev-wog-formula-checks state)
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
                               (svex-apply-is-svex-apply-wog))))))

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
    (defthmd
      rp::rp-evlt-of-ex-from-rp-reverse
      (implies (syntaxp (not (rp::include-fnc rp::term 'rp::ex-from-rp)))
               (equal
                (rp-evl (rp-trans rp::term) rp::a)
                (rp-evl (rp-trans (rp::ex-from-rp rp::term))
                        rp::a)))
      :hints
      (("goal" :in-theory (e/d (rp::ex-from-rp rp::is-rp) nil)))))

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

   (svex-eval-lemma-tmpl
    (defthm rp-evl-of-svexl-node-eval-wog-meta-main
      (implies (and (rp-evl-meta-extract-global-facts)
                    (rp::rp-termp term)
                    (svex-ev-wog-formula-checks state))
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
                                 svex-ev-wog-formula-checks)
                                (:type-prescription rp::falist-consistent)
                                (:definition rp::falist-consistent-aux)
                                (:type-prescription
                                 svexl-node-kind-wog$inline)
                                (:definition eq)
                                ;;                               (:rewrite acl2::o-p-o-infp-car)
                                (:definition rp::falist-consistent)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rp-termp-of-functions

(local
 (defret rp-termp-svex-apply-insert-part-select
   (implies (rp::rp-termp term)
            (rp::rp-termp res))
   :fn svex-apply-insert-part-select
   :hints (("Goal"
            :in-theory (e/d (svex-apply-insert-part-select)
                            ())))))

(local
 (defthm rp-termp-of-ligt-4vec-fix-lemma
   (equal (RP::RP-TERMP
           (cons 'LIGHT-4VEC-FIX x))
          (rp::rp-term-listp x))
   :hints (("Goal"
            :in-theory (e/d (RP::RP-TERMP
                             rp::rp-term-listp) ())))))

(local
 (defthm rp::rp-termp-of-list-to-consed-term
   (implies (force (rp::rp-term-listp args))
            (rp::rp-termp (mv-nth 0
                                  (list-to-consed-term args args-dontrw))))
   :hints (("goal"
            :in-theory (e/d (list-to-consed-term) ())))))

(local
 (encapsulate
   nil

   (svex-eval-lemma-tmpl
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
                                (:type-prescription rp::rp-termp)))))))

   (local
    (defthm lemma1
      (implies (and (rp::falist-consistent-aux env-falist term)
                    (rp::rp-termp term)
                    (hons-assoc-equal x env-falist))
               (rp::rp-termp (cdr (hons-assoc-equal x env-falist))))))

   (svex-eval-lemma-tmpl
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
                               ())))))

   (svex-eval-lemma-tmpl
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
                               ())))))

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

   (svex-eval-lemma-tmpl
    (defthm rp-termp-svex-eval-wog-meta-main
      (implies (and (rp::rp-termp term))
               (rp::rp-termp (mv-nth 0 (svex-eval-wog-meta-main term context))))
      :hints (("goal"
               :do-not-induct t
               :do-not '(preprocess)
               :expand ((:free (x)
                               (rp::rp-termp (cons 'svex-eval-wog x)))
                        (:free (x)
                               (rp::rp-termp (cons 'svexl-eval x)))
                        (:free (x)
                               (rp::rp-termp (cons 'QUOTE x)))
                        (:free (x)
                               (rp::rp-termp (cons 'make-fast-alist x)))
                        (:free (x y)
                               (rp::rp-term-listp (cons x y))))
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
                      )
                     )
               :in-theory (e/d (svex-eval-wog-meta-main
                                rp::is-falist)
                               ((:definition rp::falist-consistent)
                                rp-termp-svex-eval-wog-meta
                                RP::RP-TERM-LISTP
                                RP::RP-TERMP
                                (:type-prescription rp::falist-consistent)
                                #|rp-termp-svex-eval-wog-meta||#))))))

   (svex-eval-lemma-tmpl
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
                                #|rp-termp-svex-eval-wog-meta||#))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; valid-sc-of-functions

(local
 (defret valid-sc-svex-apply-insert-part-select
   (implies (rp::valid-sc term a)
            (rp::valid-sc res a))
   :fn svex-apply-insert-part-select
   :hints (("Goal"
            :in-theory (e/d (svex-apply-insert-part-select
                             rp::is-rp rp::is-equals
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
                             rp::is-rp rp::is-equals
                             rp::is-if
                             LIST-TO-CONSED-TERM) ())))))

(local
 (encapsulate
   nil

   (local
    (in-theory (enable rp::is-rp rp::is-equals
                       rp::is-if)))

   (svex-eval-lemma-tmpl
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
                                ;;                               (:rewrite acl2::o-p-o-infp-car)
                                ;;                               (:rewrite acl2::o-p-def-o-finp-1)
                                (:definition acl2::apply$-badgep)
                                (:rewrite acl2::apply$-badgep-properties . 3)
                                (:definition true-listp)
                                (:definition subsetp-equal)
                                (:definition member-equal)
                                (:rewrite
                                 acl2::member-equal-newvar-components-1)
                                (:type-prescription rp::valid-sc)))))))

   (local
    (defthm lemma1
      (implies (and (rp::falist-consistent-aux env-falist term)
                    (rp::valid-sc term a)
                    (hons-assoc-equal x env-falist))
               (rp::valid-sc (cdr (hons-assoc-equal x
                                                    env-falist))
                             a))))

   (svex-eval-lemma-tmpl
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
                               ())))))

   (svex-eval-lemma-tmpl
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
                               ())))))

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

   (svex-eval-lemma-tmpl
    (defthm valid-sc-svex-eval-wog-meta-main
      (implies (and (rp::valid-sc term a)
                    (rp::rp-termp term))
               (rp::valid-sc (mv-nth 0 (svex-eval-wog-meta-main term context))
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
                                rp::is-falist) ())))))

   (svex-eval-lemma-tmpl
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
                                ;;                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                                (:DEFINITION ACL2::APPLY$-BADGEP)
                                (:REWRITE LEMMA3)
                                (:DEFINITION RP::FALIST-CONSISTENT)))))))))

(svex-eval-lemma-tmpl
 (progn
   (rp::add-meta-rule
    :meta-fnc svexl-node-eval-wog-meta-main
    :trig-fnc svexl-node-eval-wog
    :formula-checks svex-ev-wog-formula-checks
    :valid-syntaxp t
    :returns (mv term dont-rw))

   (rp::add-meta-rule
    :meta-fnc svex-eval-wog-meta-main
    :trig-fnc svex-eval-wog
    :formula-checks svex-ev-wog-formula-checks
    :valid-syntaxp t
    :returns (mv term dont-rw))))

(progn
  (local
   (defthmd svexl-alist-eval-correct-reverse
     (implies (sv::svex-alist-p alist)
              (equal (svexl-alist-eval (svex-alist-to-svexl-alist alist) env)
                     (sv::svex-alist-eval alist env)))
     :hints (("goal"
              :do-not-induct t
              :in-theory (e/d (svexl-alist-correct)
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

(svex-eval-lemma-tmpl
 (rp::add-meta-rule
  :meta-fnc svex-alist-eval-meta-w/o-svexl
  :trig-fnc sv::svex-alist-eval
  :formula-checks svex-ev-wog-formula-checks
  :valid-syntaxp t
  :returns (mv term dont-rw)
  :disabled t
  :hints (("Goal"
           :in-theory (e/d (svex-alist-eval-meta-aux
                            svexl-alist-eval-correct-reverse
                            rp::is-rp
                            rp::is-equals
                            RP::RP-EVLT-OF-EX-FROM-RP-reverse
                            rp::is-if)
                           (rp::rp-evlt-of-ex-from-rp))))))

(svex-eval-lemma-tmpl
 (rp::add-meta-rule
  :meta-fnc svex-alist-eval-meta
  :trig-fnc svex-alist-eval
  :formula-checks svex-ev-wog-formula-checks
  :valid-syntaxp t
  :returns (mv term dont-rw)

  :hints (("Goal"
           :in-theory (e/d (svex-alist-eval-meta-aux
                            svexl-alist-eval-correct-reverse
                            rp::is-equals
                            rp::is-rp
                            rp::rp-evlt-of-ex-from-rp-reverse
                            rp::is-if)
                           (rp::rp-evlt-of-ex-from-rp))))))
