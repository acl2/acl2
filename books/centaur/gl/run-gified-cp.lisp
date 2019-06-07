; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "bfr")
(include-book "gtypes")
(include-book "tools/mv-nth" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/unify-subst" :dir :system)
(include-book "centaur/misc/evaluator-metatheorems" :dir :system)
(include-book "centaur/misc/interp-function-lookup" :dir :system)
(include-book "centaur/ubdds/witness" :dir :system)
(include-book "hyp-fix")
(local (include-book "std/lists/take" :dir :system))
(local (include-book "gtype-thms"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))

(local (defun before-run-gified-ev-tag () nil))

(acl2::defevaluator-fast run-gified-ev run-gified-ev-lst
  ((eql a b)
   (equal a b)
   (implies a b)
   (if a b c)
   (not a)
   (use-by-hint a)
   (acl2::use-these-hints a)
   (car x)
   (cdr x)
   (nth n x)
   (cons a b)
   (consp x)
   (synp vars form term)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced assoc-eq by assoc-equal).]
   (assoc-equal x a)
   (acl2::kwote-lst lst)
   (symbolp x)
   (pairlis$ a b)
   (cons a b)
   (atom a)
   (binary-+ a b)
   (hide a)
   (mv-nth n x)
   (mv-list n x)
   (acl2::return-last a b c)
   (force x)
   (bfr-eval x env)
   (bfr-hyp-eval x env)
   (acl2::typespec-check ts x)
   (iff a b)
   (binary-+ a b)
   (unary-- a)
   (len x)
   (return-last a b c)))

(defchoose run-gified-ev-falsify (a) (x)
  (not (run-gified-ev x a)))

(local
 (def-ruleset! run-gified-ev-constraints
   (set-difference-theories (current-theory :here)
                            (current-theory 'before-run-gified-ev-tag))))

(acl2::def-meta-extract run-gified-ev run-gified-ev-lst)

(local
 (progn
   (include-book "tools/def-functional-instance" :dir :system)


   (acl2::def-functional-instance
     check-ev-of-fncall-args-correct-for-run-gified-ev
     acl2::check-ev-of-fncall-args-correct
    ((acl2::evmeta-ev run-gified-ev)
     (acl2::evmeta-ev-lst run-gified-ev-lst)
     (acl2::evmeta-ev-falsify run-gified-ev-falsify)
     (acl2::evmeta-ev-meta-extract-global-badguy run-gified-ev-meta-extract-global-badguy))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable run-gified-ev-constraint-0)
                              :use ((:instance run-gified-ev-falsify)
                                    (:instance run-gified-ev-meta-extract-global-badguy))))))

   (acl2::def-functional-instance
     check-ev-of-variable-correct-for-run-gified-ev
     acl2::check-ev-of-variable-correct
     ((acl2::evmeta-ev run-gified-ev)
     (acl2::evmeta-ev-lst run-gified-ev-lst)
     (acl2::evmeta-ev-falsify run-gified-ev-falsify)
     (acl2::evmeta-ev-meta-extract-global-badguy run-gified-ev-meta-extract-global-badguy)))

   (acl2::def-functional-instance
     check-ev-of-quote-correct-for-run-gified-ev
     acl2::check-ev-of-quote-correct
    ((acl2::evmeta-ev run-gified-ev)
     (acl2::evmeta-ev-lst run-gified-ev-lst)
     (acl2::evmeta-ev-falsify run-gified-ev-falsify)
     (acl2::evmeta-ev-meta-extract-global-badguy run-gified-ev-meta-extract-global-badguy)))

   (acl2::def-functional-instance
     check-ev-of-lambda-correct-for-run-gified-ev
     acl2::check-ev-of-lambda-correct
    ((acl2::evmeta-ev run-gified-ev)
     (acl2::evmeta-ev-lst run-gified-ev-lst)
     (acl2::evmeta-ev-falsify run-gified-ev-falsify)
     (acl2::evmeta-ev-meta-extract-global-badguy run-gified-ev-meta-extract-global-badguy)))

   (acl2::def-functional-instance
     check-ev-of-nonsymbol-atom-correct-for-run-gified-ev
     acl2::check-ev-of-nonsymbol-atom-correct
    ((acl2::evmeta-ev run-gified-ev)
     (acl2::evmeta-ev-lst run-gified-ev-lst)
     (acl2::evmeta-ev-falsify run-gified-ev-falsify)
     (acl2::evmeta-ev-meta-extract-global-badguy run-gified-ev-meta-extract-global-badguy)))

   (acl2::def-functional-instance
     check-ev-of-bad-fncall-correct-for-run-gified-ev
     acl2::check-ev-of-bad-fncall-correct
    ((acl2::evmeta-ev run-gified-ev)
     (acl2::evmeta-ev-lst run-gified-ev-lst)
     (acl2::evmeta-ev-falsify run-gified-ev-falsify)
     (acl2::evmeta-ev-meta-extract-global-badguy run-gified-ev-meta-extract-global-badguy)))

   (acl2::def-functional-instance
     check-ev-of-call-correct-for-run-gified-ev
     acl2::check-ev-of-call-correct
    ((acl2::evmeta-ev run-gified-ev)
     (acl2::evmeta-ev-lst run-gified-ev-lst)
     (acl2::evmeta-ev-falsify run-gified-ev-falsify)
     (acl2::evmeta-ev-meta-extract-global-badguy run-gified-ev-meta-extract-global-badguy)))

   (acl2::def-functional-instance
     ev-of-arglist-is-ground-for-run-gified-ev
     acl2::ev-of-arglist-is-ground
    ((acl2::evmeta-ev run-gified-ev)
     (acl2::evmeta-ev-lst run-gified-ev-lst)
     (acl2::evmeta-ev-falsify run-gified-ev-falsify)
     (acl2::evmeta-ev-meta-extract-global-badguy run-gified-ev-meta-extract-global-badguy)))))


(defun run-gified-lhs-and-okp-breakdown (lhs okp)
  (case-match okp
    (('mv-nth ''0 (fn . '(fn actuals hyp clk config bvar-db state)))
     (case-match lhs
       ((ev ('mv-nth ''1 (!fn . '(fn actuals hyp clk config bvar-db state))) 'env)
        (mv nil ev fn))
       (& (mv "lhs mismatched" nil nil))))
    (& (mv "okp mismatched" nil nil))))

(local
 (defthm run-gified-lhs-and-okp-breakdown-correct
   (mv-let (erp geval run-gified)
     (run-gified-lhs-and-okp-breakdown lhs okp)
     (implies (not erp)
              (and (equal lhs
                          `(,geval (mv-nth '1 (,run-gified fn actuals hyp clk config bvar-db state))
                                   env))
                   (equal okp
                          `(mv-nth '0 (,run-gified fn actuals hyp clk config bvar-db state))))))
   :rule-classes :forward-chaining))

(in-theory (disable run-gified-lhs-and-okp-breakdown))

(defun run-gified-rhs-breakdown (rhs)
  (case-match rhs
    ((ev ('cons 'fn
                ('acl2::kwote-lst
                 (geval-list . '(actuals env))))
         . '('nil))
     (mv nil ev geval-list))
    (& (mv "rhs mismatched" nil nil))))

(local
 (defthm run-gified-rhs-breakdown-correct
   (mv-let (erp evfn geval-list)
     (run-gified-rhs-breakdown rhs)
     (implies (not erp)
              (equal rhs
                     `(,evfn (cons fn (acl2::kwote-lst (,geval-list actuals env)))
                             'nil))))
   :rule-classes :forward-chaining))

(in-theory (disable run-gified-rhs-breakdown))

(defun function-def-clause (rule fn formals body)
  `((not (use-by-hint ',rule))
    (equal (,fn . ,formals)
           ,body)))

(local
 (defthm function-def-clause-correct
   (implies (run-gified-ev (disjoin (function-def-clause rule fn formals body)) env)
            (equal (run-gified-ev (cons fn formals) env)
                   (run-gified-ev body env)))
   :hints(("Goal" :in-theory (enable use-by-hint function-def-clause)))))

(in-theory (disable function-def-clause))


(include-book "gl-util")

(defun f-i-thmname (thm eval)
  (incat 'gl-thm::foo (symbol-name thm) "-FOR-" (symbol-name eval)))

(defun geval-rule-alist (table geval world)
  (if (atom table)
      (mv nil nil)
    (let ((entry (car table)))
      (case-match entry
        ((& gfn (thm . thm-geval) . &)
         (b* (((mv erp alist)
               (geval-rule-alist (cdr table) geval world))
              ((when erp) (mv erp alist))
              (thmname (if (eq thm-geval geval)
                           thm
                         (f-i-thmname thm geval)))
              (theorem (fgetprop thmname 'theorem nil world))
              ((unless theorem) (mv (acl2::msg "theorem not found: ~x0"
                                               thmname)
                                    nil)))
           (mv nil (hons-acons gfn (cons thmname theorem)
                               alist))))
        (& (mv (acl2::msg "bad gl-function-info table entry: ~x0" entry) nil))))))

(in-theory (disable geval-rule-alist))



(defun run-gified-case-breakdown (body)
  (case-match body
    (('if ('eql 'fn ('quote fnname))
         ('(LAMBDA (MV)
                   ((LAMBDA (RES HYP)
                            (CONS 'T (CONS RES (CONS HYP 'NIL))))
                    (MV-NTH '0 MV)
                    (MV-NTH '1 MV)))
          (gfnname . args))
       rest)
     (mv nil fnname gfnname args rest))
    (& (mv (acl2::msg "Malformed case: ~x0" body) nil nil nil nil))))


(local
 (defthm run-gified-case-breakdown-correct
   (mv-let (erp fnname gfnname args rest)
     (run-gified-case-breakdown body)
     (implies (not erp)
              (equal (run-gified-ev body a)
                     (let ((fn (cdr (assoc-equal 'fn a))))
                       (if (equal fn fnname)
                           (list t
                                 (mv-nth 0 (run-gified-ev (cons gfnname args)
                                                          a))
                                 (mv-nth 1 (run-gified-ev (cons gfnname args) a)))
                         (run-gified-ev rest a))))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local
 (defthm run-gified-case-breakdown-rest-smaller
   (mv-let (erp fnname gfnname args rest)
     (run-gified-case-breakdown body)
     (declare (ignore fnname gfnname args))
     (implies (not erp)
              (< (acl2-count rest) (acl2-count body))))
   :rule-classes (:rewrite :linear)))

(in-theory (disable run-gified-case-breakdown))

(defun evals-of-formalsp (formals evals geval env)
  (if (atom formals)
      (equal evals nil)
    (and (consp evals)
         (let ((term (car evals)))
           (case-match term
             ((term-geval arg the-env)
              (and (equal the-env env)
                   (equal term-geval geval)
                   (equal arg (car formals))))))
         (evals-of-formalsp (cdr formals) (cdr evals) geval env))))

(defun make-evals-of-formals (formals geval env)
  (if (atom formals)
      nil
    (cons (list geval (car formals) env)
          (make-evals-of-formals (Cdr formals) geval env))))

(local
 (defthm evals-of-formalsp-correct
   (implies (evals-of-formalsp formals evals geval env)
            (equal evals
                   (make-evals-of-formals formals geval env)))
   :rule-classes :forward-chaining))

(in-theory (disable evals-of-formalsp))

(defun run-gified-check-geval-thm (thm gfn fn geval)
  (case-match thm
    (('implies
      '(bfr-hyp-eval hyp (car env))
      ('equal (the-geval ('mv-nth ''0 (!gfn . gformals)) . '(env))
              (!fn . evals)))
     (let ((nformals (len gformals)))
       (if (<= 5 nformals)
           (let ((formals (take (- nformals 5) gformals)))
             (if (and (equal the-geval geval)
                      (evals-of-formalsp formals evals geval 'env)
                      (nonnil-symbol-listp gformals)
                      (acl2::fast-no-duplicatesp gformals)
                      (not (member 'env gformals))
                      (equal (nthcdr (- nformals 5) gformals) '(hyp clk config bvar-db state)))
                 (mv nil gformals)
               (mv (acl2::msg "Malformed geval theorem: ~x0" thm) nil)))
         (mv (acl2::msg "Malformed geval theorem: ~x0" thm) nil))))
    (& (mv (acl2::msg "Malformed geval theorem: ~x0" thm) nil))))

(local
 (defthmd my-equal-of-cons
   (implies (syntaxp (not (and (quotep b) (quotep c))))
            (equal (equal a (cons b c))
                   (and (consp a)
                        (equal (car a) b)
                        (equal (cdr a) c))))))



(local
 (defthm append-take-nthcdr
   (implies (< n (len lst))
            (equal (append (take n lst) (nthcdr n lst))
                   lst))))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (local
;  (defthmd member-is-member-equal
;    (equal (member x y)
;           (member-equal x y))))
;
; (local (in-theory (enable member-is-member-equal)))

(local
 (defthm run-gified-check-geval-thm-formals
   (mv-let (erp formals)
     (run-gified-check-geval-thm thm gfn fn geval)
     (implies (not erp)
              (and (<= 5 (len formals))
                   (nonnil-symbol-listp formals)
                   (no-duplicatesp-equal formals)
                   (not (member-equal 'env formals))
                   (equal (nthcdr (+ -5 (len formals)) formals) '(hyp clk config bvar-db state)))))
   :rule-classes nil))

(local
 (defthmd run-gified-check-geval-thm-form
   (mv-let (erp formals)
     (run-gified-check-geval-thm thm gfn fn geval)
     (implies (not erp)
              (equal thm
                     `(implies (bfr-hyp-eval hyp (car env))
                               (equal (,geval (mv-nth '0 (,gfn . ,formals)) env)
                                      (,fn . ,(make-evals-of-formals
                                               (take (- (len formals) 5)
                                                     formals)
                                               geval 'env)))))))
   :rule-classes :forward-chaining))

(local
 (acl2::def-functional-instance
  run-gified-ev-lst-pairlis
  acl2::ifl-ev-lst-pairlis
  ((acl2::ifl-ev-lst run-gified-ev-lst)
   (acl2::ifl-ev run-gified-ev))
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable run-gified-ev-constraint-0))))))

(local
 (defthm nthcdr-nil
   (equal (nthcdr n nil) nil)))

(local
 (defthm nth-of-nthcdr
   (equal (nth n (nthcdr m y))
          (nth (+ (nfix n) (nfix m)) y))))

;; (encapsulate nil
;;   (local (include-book "arithmetic/top-with-meta" :dir :system))
;;   (defthmd equal-nthcdr-cons
;;     (equal (equal (nthcdr n x) (cons a b))
;;            (and (equal (nth n x) a)
;;                 (< (nfix n) (len x))
;;                 (equal (nthcdr (+ 1 (nfix n)) x) b)))
;;     :hints (("goal" :induct (nthcdr n x)))))




(local
 (encapsulate nil
   (local
    (defun the-induction (n keys vals)
      (if (zp n)
          (list keys vals)
        (the-induction (1- n) (cdr keys) (cdr vals)))))

   (local (defthm member-when-equal-nth
            (implies (and (equal key (nth n keys))
                          (< (nfix n) (len keys)))
                     (member-equal key keys))))

   (defthm assoc-equal-pairlis-nth
     (implies (and (equal (len keys) (len vals))
                   (< n (len keys))
                   (no-duplicatesp-equal keys))
              (equal (cdr (assoc-equal (nth n keys)
                                       (pairlis$ keys vals)))
                     (nth n vals)))
     :hints (("goal" :induct (the-induction n keys vals))))))

(local
 (defthm len-run-gified-ev-lst
   (equal (len (run-gified-ev-lst x a))
          (len x))))

(local
 (defthm nth-run-gified-ev-lst
   (equal (nth n (run-gified-ev-lst x a))
          (run-gified-ev (nth n x) a))))

(local
 (progn
   (defevaluator equality-cp-ev equality-cp-ev-lst
     ((equal a b) (if a b c) (not a) (hide x)))

   (acl2::def-join-thms equality-cp-ev)

   (defun find-remv-equality-hyp (clause term)
     (if (atom clause)
         (mv nil nil nil nil)
       (let ((lit (car clause)))
         (mv-let (ok other)
           (case-match lit
             (('not ('equal term1 term2))
              (cond ((equal term1 term) (mv t term2))
                    ((equal term2 term) (mv t term1))
                    (t (mv nil nil))))
             (& (mv nil nil)))
           (if ok
               (mv ok other (cdr clause) `(hide ,lit))
             (mv-let (ok new rest hide)
               (find-remv-equality-hyp (cdr clause) term)
               (if ok
                   (mv ok new (cons lit rest) hide)
                 (mv nil nil nil nil))))))))

   (defthm find-remv-equality-hyp-correct
     (mv-let (ok other new hide)
       (find-remv-equality-hyp clause term)
       (implies ok
                (iff (equality-cp-ev (disjoin clause) a)
                     (not (and (equal (equality-cp-ev term a)
                                      (equality-cp-ev other a))
                               (not (equality-cp-ev hide a))
                               (not (equality-cp-ev (disjoin new) a)))))))
     :hints(("Goal" :expand ((:free (x) (hide x))))))


   (mutual-recursion
    (defun replace-term (new old avoid x)
      (cond ((equal x new) old)
            ((member-equal x avoid) x)
            ((atom x) x)
            ((eq (car x) 'quote) x)
            (t (cons (car x) (replace-term-list new old avoid (cdr x))))))
    (defun replace-term-list (new old avoid x)
      (if (atom x)
          nil
        (cons (replace-term new old avoid (car x))
              (replace-term-list new old avoid (cdr x))))))

   (flag::make-flag replace-term-flg replace-term)

   (defthm-replace-term-flg
     replace-term-correct-lemma
     (replace-term
      (implies (equal (equality-cp-ev old a)
                      (equality-cp-ev new a))
               (equal (equality-cp-ev
                       (replace-term new old avoid x) a)
                      (equality-cp-ev x a)))
      :name replace-term-correct)
     (replace-term-list
      (implies (equal (equality-cp-ev old a)
                      (equality-cp-ev new a))
               (equal (equality-cp-ev-lst
                       (replace-term-list new old avoid x) a)
                      (equality-cp-ev-lst x a)))
      :name replace-term-list-correct)
     :hints (("goal" :induct (replace-term-flg flag new old avoid x))
             (and stable-under-simplificationp
                  '(:in-theory (enable equality-cp-ev-constraint-0)))))

   (in-theory (disable replace-term replace-term-list))

   (defthm replace-term-list-correct-disjoin
     (implies (equal (equality-cp-ev old a)
                     (equality-cp-ev new a))
              (iff (equality-cp-ev
                    (disjoin (replace-term-list new old avoid x)) a)
                   (equality-cp-ev (disjoin x) a)))
     :hints(("Goal" :in-theory (e/d (replace-term-list))
             :induct (len x))))


   (defun replace-equality-cp (clause hints)
     (b* (((list term avoid) hints)
          ((mv ok new-term new-clause hide)
           (find-remv-equality-hyp clause term))
          ((unless ok) (list clause))
          (repl-clause (replace-term-list term new-term avoid new-clause)))
       (list (cons hide repl-clause))))

   (defthm replace-equality-cp-correct
     (implies (and (pseudo-term-listp clause)
                   (alistp a)
                   (equality-cp-ev
                    (conjoin-clauses (replace-equality-cp clause hints))
                    a))
              (equality-cp-ev (disjoin clause) a))
     :hints(("Goal" :do-not-induct t))
     :rule-classes :clause-processor)))


(local
 (defthm run-gified-ev-lst-symbol-cdr-alist
   (implies (and (nonnil-symbol-listp vars)
                 (not (member-equal key vars)))
            (equal (run-gified-ev-lst vars (cons (cons key val) alist))
                   (run-gified-ev-lst vars alist)))))


(local (in-theory (disable  acl2::reflexivity-of-qs-subset)))



(local
 (defthm run-gified-ev-lst-make-evals-of-formals
   (implies (and (syntaxp (not (equal a ''nil)))
                 (not (equal geval 'quote)))
            (equal (run-gified-ev-lst (make-evals-of-formals lst geval env) a)
                   (run-gified-ev-lst (make-evals-of-formals
                                       (acl2::kwote-lst (run-gified-ev-lst lst a))
                                       geval `(quote ,(run-gified-ev env a)))
                                      nil)))
   :hints(("Goal" :in-theory (enable run-gified-ev-constraint-0)))))

(local
 (defthm run-gified-ev-lst-take
   (equal (run-gified-ev-lst (acl2::take n x) a)
          (acl2::take n (run-gified-ev-lst x a)))
   :hints(("Goal" :in-theory (enable acl2::take)))))

(local
 (defthm list-fix-run-gified-ev-lst
   (equal (acl2::list-fix (run-gified-ev-lst x a))
          (run-gified-ev-lst x a))
   :hints (("goal" :induct (len x)))))


(local
 (defthm run-gified-check-geval-thm-correct
   (mv-let (erp formals)
     (run-gified-check-geval-thm thm gfn fn geval)
     (let ((hyp (run-gified-ev (nth (+ -5 (len formals)) args)
                               a))
           ;; (env (cdr (assoc-equal 'env a)))
           )
       (implies (and (not erp)
                     (run-gified-ev
                      thm
                      (cons (cons 'env env)
                            (pairlis$ formals (run-gified-ev-lst args a))))
                     (not (eq geval 'quote))
                     (not (eq gfn 'quote))
                     (not (eq fn 'quote))
                     (equal (len formals) (len args))
                     (bfr-hyp-eval hyp (car env)))
                (equal (run-gified-ev
                        `(,geval (mv-nth '0 (,gfn . ,args)) (quote ,env))
                        a)
                       (run-gified-ev
                        `(,fn . ,(make-evals-of-formals
                                  (take (- (len formals) 5)
                                        args)
                                  geval (kwote env)))
                        a)))))
   :hints(("Goal"
           :in-theory (e/d () ;; equal-nthcdr-cons
                           (nth-of-nthcdr acl2::car-nthcdr assoc-equal-pairlis-nth
                                          run-gified-check-geval-thm))
           :use ((:instance run-gified-check-geval-thm-form)
                 (:instance run-gified-check-geval-thm-formals)
                 (:instance
                  nth-of-nthcdr
                  (n 0) (m (+ -5 (len args)))
                  (y (mv-nth 1 (run-gified-check-geval-thm thm gfn fn geval))))
                 (:instance
                  assoc-equal-pairlis-nth
                  (n (- (len args) 5))
                  (keys (mv-nth 1 (run-gified-check-geval-thm thm gfn fn geval)))
                  (vals (run-gified-ev-lst args a)))))
          (and stable-under-simplificationp
               '(:clause-processor
                 (replace-equality-cp
                  clause
                  (list 'thm (list
                              `(run-gified-check-geval-thm
                                thm gfn fn geval))))
                 :in-theory (e/d (run-gified-ev-constraint-0)
                                 (nth-of-nthcdr assoc-equal-pairlis-nth
                                                run-gified-check-geval-thm)))))
   :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil nil nil nil)))))


(local (in-theory (disable run-gified-check-geval-thm)))

(defun run-gified-get-geval-thm (gfn fn geval-alist geval)
  (b* ((look (hons-get gfn geval-alist))
       ((unless look)
        (mv (acl2::msg "No information about gfn ~x0 found" gfn) nil nil))
       (thmname (cadr look))
       (thm (cddr look))
       ((mv erp formals)
        (run-gified-check-geval-thm thm gfn fn geval))
       ((when erp) (mv erp nil nil)))
    (mv nil `((not (use-by-hint ',thmname))
              ,thm)
        formals)))





(local
 (defthm run-gified-get-geval-thm-correct
   (mv-let (erp thm formals)
     (run-gified-get-geval-thm gfn fn geval-alist geval)
     (let ((hyp (run-gified-ev (nth (+ -5 (len formals)) args) a))
           ;; (env (cdr (assoc-equal 'env a)))
           )
       (implies
        (and (not erp)
             (run-gified-ev-theoremp (disjoin thm))
             (bfr-hyp-eval hyp (car env))
             (not (equal geval 'quote))
             (not (equal gfn 'quote))
             (not (equal fn 'quote))
             (equal (len args) (len formals)))
        (equal (run-gified-ev `(,geval (mv-nth '0 (,gfn . ,args)) (quote ,env))
                              a)
               (run-gified-ev `(,fn
                                . ,(make-evals-of-formals
                                    (take (- (len formals) 5) args) geval (kwote env)))
                              a)))))
   :hints(("Goal" :in-theory (e/d (use-by-hint) ())
           :use ((:instance run-gified-ev-falsify
                            (x (disjoin (mv-nth 1 (run-gified-get-geval-thm
                                                   gfn fn geval-alist geval))))
                            (a (let ((formals
                                      (mv-nth 2 (run-gified-get-geval-thm
                                                 gfn fn geval-alist geval))))
                                 (cons (cons 'env env)
                                       (pairlis$ formals (run-gified-ev-lst
                                                          args a)))))))))))

(local
 (defthm run-gified-get-geval-thm-correct-corollary
   (mv-let (erp thm formals)
     (run-gified-get-geval-thm gfn fn geval-alist geval)
     (let ((hyp (run-gified-ev (nth (+ -5 (len formals)) args) a)))
       (implies
        (and (not erp)
             (run-gified-ev-theoremp (disjoin thm))
             (bfr-hyp-eval hyp (car env))
             (not (equal geval 'quote))
             (not (equal gfn 'quote))
             (not (equal fn 'quote))
             (equal (len args) (len formals)))
        (equal (run-gified-ev (list geval
                                    (list 'quote
                                          (mv-nth 0
                                                  (run-gified-ev
                                                   (cons
                                                    gfn
                                                    (acl2::kwote-lst
                                                     (run-gified-ev-lst args a)))
                                                   nil)))
                                    (list 'quote env))
                              nil)
               (run-gified-ev `(,fn
                                . ,(make-evals-of-formals
                                    (take (- (len formals) 5) args) geval (kwote env)))
                              a)))))
   :hints(("Goal" :in-theory (e/d (run-gified-ev-constraint-0)
                                  (run-gified-get-geval-thm-correct))
           :use ((:instance run-gified-get-geval-thm-correct))))))


(in-theory (disable run-gified-get-geval-thm))




(defun run-gified-get-eval-thm (fnname formals evfn eval-alist world)
  (b* ((look (hons-get fnname eval-alist))
       ((when (not look))
        (acl2::msg "Function ~x0 not recognized by evaluator." fnname))
       ((cons arity rune) (cdr look))
       ((unless (equal arity (len formals)))
        (acl2::msg "~x0 arity: ~x1 eval-alist, ~x2 geval"
                   fnname arity (len formals)))
       ((unless (acl2::check-ev-of-call evfn fnname arity (cadr rune) world))
        (acl2::msg "bad constraint: ~x0" fnname)))
    nil))

(local (in-theory (disable w)))

(local
 (defthm run-gified-get-eval-thm-correct
   (let ((erp (run-gified-get-eval-thm fn formals evfn eval-alist (w state))))
     (let ((ex (run-gified-ev x a)))
       (implies (and (not erp)
                     (run-gified-ev-theoremp (disjoin thm))
                     (run-gified-ev-meta-extract-global-facts)
                     (consp ex)
                     (equal (car ex) fn)
                     (not (equal evfn 'quote))
                     (not (equal fn 'quote)))
                (equal (run-gified-ev `(,evfn ,x ,ma) a)
                       (run-gified-ev
                        `(,fn . ,(acl2::ev-of-arglist
                                  (len formals) evfn (cdr (run-gified-ev x a))
                                  (run-gified-ev ma a)))
                        a)))))))

(in-theory (disable run-gified-get-eval-thm))



(defun nths-matching-formalsp (idx formals varname list)
  (declare (xargs :measure (acl2-count formals)))
  (if (atom formals)
      (eq list nil)
    (and (consp list)
         (let ((car (car list)))
           (case-match car
             (('nth ('quote !idx) !varname) t)))
         (nths-matching-formalsp (1+ idx) (cdr formals) varname (cdr list)))))

(local
 (progn
   (defun make-nths-matching-formals (idx formals varname)
     (if (atom formals)
         nil
       (cons `(nth ',idx ,varname)
             (make-nths-matching-formals (1+ idx) (cdr formals) varname))))

   (defthm nths-matching-formalsp-make-nths-matching-formals
     (implies (nths-matching-formalsp idx formals varname list)
              (equal list
                     (make-nths-matching-formals idx formals varname)))
     :hints(("Goal" :in-theory (enable my-equal-of-cons)))
     :rule-classes :forward-chaining)))



(in-theory (disable nths-matching-formalsp))









(local
 (defthm len-take
   (Equal (len (acl2::take n lst)) (nfix n))))


(local
 (defthm car-nthcdr
   (equal (car (nthcdr n a)) (nth n a))))

(local
 (defthm nth-kwote-lst
   (implies (< (nfix n) (len lst))
            (equal (nth n (acl2::kwote-lst lst))
                   (list 'quote (nth n lst))))))


(local (include-book "arithmetic/top-with-meta" :dir :system))




(local
 (in-theory (disable equal-of-booleans-rewrite
                     default-car default-cdr)))



(defun geval-list-def-thm (geval-list geval)
  `((not (use-by-hint ',geval-list))
    (equal (,geval-list x env)
           (if (atom x)
               'nil
             (cons (,geval (car x) env)
                   (,geval-list (cdr x) env))))))

(local
 (defthm geval-list-def-thm-correct
   (implies (and (run-gified-ev-theoremp
                  (disjoin (geval-list-def-thm
                            geval-list geval)))
                 ;;    (gobjectp (run-gified-ev x a))
                 ;;                 (or (atom (run-gified-ev x a))
                 ;;                     (gobjectp (car (run-gified-ev x a))))
                 (not (equal geval 'quote))
                 (not (equal geval-list 'quote)))
            (and (implies (atom (run-gified-ev x a))
                          (equal (run-gified-ev (list geval-list x env) a)
                                 nil))
                 (implies (consp (run-gified-ev x a))
                          (equal (run-gified-ev (list geval-list x env) a)
                                 (cons (run-gified-ev (list geval
                                                            (kwote (car (run-gified-ev x a)))
                                                            (kwote (run-gified-ev env a)))
                                                      nil)
                                       (run-gified-ev (list geval-list
                                                            (kwote (cdr (run-gified-ev x a)))
                                                            (kwote (run-gified-ev env a)))
                                                      nil))))))
   :hints(("Goal" :in-theory (enable use-by-hint run-gified-ev-constraint-0
                                     geval-list-def-thm)
           :use ((:instance run-gified-ev-falsify
                            (x (disjoin (geval-list-def-thm
                                         geval-list geval)))
                            (a `((x . ,(run-gified-ev x a))
                                 (env . ,(run-gified-ev env a))))))))))

;; (defthm gobj-listp-simple-take-implies
;;   (implies (and (gobj-listp (acl2::simple-take n x))
;;                 (natp n) (< 0 n))
;;            (or (atom x) (gobjectp (car x))))
;;   :rule-classes nil)



;; (defthm geval-geval-list-def-thm-correct-corollary
;;   (implies (and (run-gified-ev-theoremp
;;                  (disjoin (geval-geval-list-def-thm
;;                            geval rune)))
;;                 (gobjectp (run-gified-ev x a))
;;                 (gobj-listp (acl2::simple-take n (run-gified-ev x a)))
;;                 (natp n) (< 0 n)
;;                 (not (equal geval 'quote)))
;;            (and (equal (car (run-gified-ev (list geval x env) a))
;;                        (run-gified-ev (list geval `(car ,x) env) a))
;;                 (equal (cdr (run-gified-ev (list geval x env) a))
;;                        (run-gified-ev (list geval `(cdr ,x) env) a))))
;;   :hints(("Goal" :use (geval-geval-list-def-thm-correct
;;                        (:instance gobj-listp-simple-take-implies
;;                                   (x (run-gified-ev x a))))
;;           :in-theory (disable geval-geval-list-def-thm
;;                               geval-geval-list-def-thm-correct)
;;           :do-not-induct t))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0 nil 0 nil nil nil))))

;; (defthm geval-geval-list-def-thm-correct-corollary2
;;   (implies (and (run-gified-ev-theoremp
;;                  (disjoin (geval-geval-list-def-thm
;;                            geval rune)))
;;                 (gobj-listp (run-gified-ev x a))
;;                 (not (equal geval 'quote)))
;;            (and (equal (car (run-gified-ev (list geval x env) a))
;;                        (run-gified-ev (list geval `(car ,x) env) a))
;;                 (equal (cdr (run-gified-ev (list geval x env) a))
;;                        (run-gified-ev (list geval `(cdr ,x) env) a))))
;;   :hints(("Goal" :use geval-geval-list-def-thm-correct
;;           :in-theory (e/d (gobj-listp-impl-gobjectp)
;;                           (geval-geval-list-def-thm
;;                            geval-geval-list-def-thm-correct))
;;           :do-not-induct t))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0 1 nil))))

;; (defun geval-consp-when-gobj-listp-thm (geval rune)
;;   `((not (use-by-hint ',rune))
;;     ;; (not (gobjectp x))
;; ;;     (not (if (consp x)
;; ;;              (gobjectp (car x))
;; ;;            't))
;;     (not (gobj-listp x))
;;     (equal (consp (,geval x env))
;;            (consp x))))

;; (local
;;  (defthm geval-consp-when-gobj-listp-thm-correct
;;    (implies (and (run-gified-ev-theoremp
;;                   (disjoin (geval-consp-when-gobj-listp-thm
;;                             geval rune)))
;;                  ;; (gobjectp (run-gified-ev x a))
;;                  ;;                 (or (atom (run-gified-ev x a))
;;                  ;;                     (gobjectp (car (run-gified-ev x a))))
;;                  (gobj-listp (run-gified-ev x a))
;;                  (not (equal geval 'quote)))
;;             (equal (consp (run-gified-ev (list geval x env) a))
;;                    (consp (run-gified-ev x a))))
;;    :hints(("Goal" :in-theory (enable use-by-hint run-gified-ev-constraint-0)
;;            :use ((:instance run-gified-ev-falsify
;;                             (x (disjoin (geval-consp-when-gobj-listp-thm
;;                                          geval rune)))
;;                             (a `((x . ,(run-gified-ev x a))
;;                                  (env . ,(run-gified-ev env a))))))))))

;; (defthm geval-consp-when-gobj-listp-thm-correct-corollary
;;   (implies (and (run-gified-ev-theoremp
;;                  (disjoin (geval-consp-when-gobj-listp-thm
;;                            geval rune)))
;;                 (gobjectp (run-gified-ev x a))
;;                 (gobj-listp (acl2::simple-take n (run-gified-ev x a)))
;;                 (natp n) (< 0 n)
;;                 (not (equal geval 'quote)))
;;            (equal (consp (run-gified-ev (list geval x env) a))
;;                   (consp (run-gified-ev x a))))
;;   :hints(("Goal" :use (geval-consp-when-gobj-listp-thm-correct
;;                        (:instance gobj-listp-simple-take-implies
;;                                   (x (run-gified-ev x a))))
;;           :in-theory (disable geval-consp-when-gobj-listp-thm-correct
;;                               geval-consp-when-gobj-listp-thm)
;;           :do-not-induct t))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0 nil 0 nil nil nil))))

;; (defthm geval-consp-when-gobj-listp-thm-correct-corollary2
;;   (implies (and (run-gified-ev-theoremp
;;                  (disjoin (geval-consp-when-gobj-listp-thm
;;                            geval rune)))
;;                 (gobj-listp (run-gified-ev x a))
;;                 (natp n) (< 0 n)
;;                 (not (equal geval 'quote)))
;;            (equal (consp (run-gified-ev (list geval x env) a))
;;                   (consp (run-gified-ev x a))))
;;   :hints(("Goal" :use (geval-consp-when-gobj-listp-thm-correct)
;;           :in-theory (e/d (gobj-listp-impl-gobjectp)
;;                           (geval-consp-when-gobj-listp-thm-correct
;;                            geval-consp-when-gobj-listp-thm))
;;           :do-not-induct t))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0 0 nil nil nil))))

(defun geval-of-nil-thm (geval rune)
  `((not (use-by-hint ',rune))
    (equal (,geval 'nil env)
           'nil)))

(local
 (defthm geval-of-nil-thm-correct
   (implies (and (run-gified-ev-theoremp
                  (disjoin (geval-of-nil-thm geval rune)))
                 (not (equal geval 'quote)))
            (equal (run-gified-ev (list geval ''nil env) a)
                   nil))
   :hints(("Goal" :in-theory (enable use-by-hint run-gified-ev-constraint-0)
           :use ((:instance run-gified-ev-falsify
                            (x (disjoin (geval-of-nil-thm geval rune)))
                            (a `((env . ,(run-gified-ev env a))))))))))


(in-theory (disable geval-list-def-thm
                    geval-of-nil-thm))

(local
 (defthm nthcdr-kwote-lst
   (equal (nthcdr n (acl2::kwote-lst lst))
          (acl2::kwote-lst (nthcdr n lst)))))

(local
 (progn
   (defun make-n-cdrs (n term)
     (if (zp n)
         term
       (make-n-cdrs (1- n) (list 'cdr term))))


   (local (defthm cdr-nthcdr
            (equal (cdr (nthcdr n x))
                   (nthcdr (+ 1 (nfix n)) x))
            :hints(("Goal" :in-theory (enable default-cdr)))))

   (defthm run-gified-ev-make-n-cdrs
     (equal (run-gified-ev (make-n-cdrs n term) a)
            (nthcdr n (run-gified-ev term a)))
     :hints(("Goal" :in-theory (enable nthcdr))))))

(local
 (progn
   (defun test-constraint-0-result (args a mfc state)
     (declare (xargs :mode :program :stobjs state))
     (not (equal (acl2::mfc-rw+ `(acl2::kwote-lst (run-gified-ev-lst args a))
                                `((args . ,args) (a . ,a))
                                'acl2::? nil mfc state)
                 args)))


   (defthmd my-run-gified-ev-constraint-0
     (implies (and (syntaxp (test-constraint-0-result args a mfc state))
                   (not (equal fn 'quote)))
              (equal (run-gified-ev (cons fn args) a)
                     (run-gified-ev (cons fn (acl2::kwote-lst
                                              (run-gified-ev-lst args a)))
                                    nil)))
     :hints(("Goal" :in-theory (enable run-gified-ev-constraint-0))))

   ;; (defthm gobjectp-nth-gobj-listp
   ;;   (implies (gobj-listp lst)
   ;;            (gobjectp (nth n lst)))
   ;;   :hints(("Goal" :in-theory (enable gobj-listp))))

   (defthmd listp-nthcdr-gobj-listp
     (implies (and (gobj-listp lst)
                   (nthcdr n lst))
              (consp (nthcdr n lst)))
     :hints(("Goal" :in-theory (e/d (gobj-listp)))))

   (defthm gobj-listp-nthcdr
     (implies (gobj-listp lst)
              (gobj-listp (nthcdr n lst)))
     :hints(("Goal" :in-theory (e/d (gobj-listp)
                                    (cdr-nthcdr)))))

   (defthm gobj-listp-take
     (implies (gobj-listp gobj)
              (gobj-listp (acl2::take n gobj)))
     :hints(("Goal" :in-theory (enable gobj-listp acl2::take
                                       acl2::replicate))))

   (defun count-down2-cdr (n m l)
     (if (zp n)
         (list m l)
       (count-down2-cdr (1- (nfix n)) (1- (nfix m)) (cdr l))))

   (defthm gobj-listp-take1
     (implies (and (gobj-listp (acl2::take m gobj))
                   (< (nfix n) (nfix m)))
              (gobj-listp (acl2::take n gobj)))
     :hints (("goal" :induct (count-down2-cdr m n gobj)
              :in-theory (enable gobj-listp acl2::take nfix))))

   ;; (Defthm gobjectp-nth-when-gobj-listp-take
   ;;   (implies (and (gobj-listp (acl2::take m x))
   ;;                 (< (nfix n) (nfix m)))
   ;;            (gobjectp (nth n x)))
   ;;   :hints (("goal" :induct (count-down2-cdr m n x)
   ;;            :in-theory (enable gobj-listp))))

   (defthm cheap-default-car
     (implies (not (consp x))
              (equal (car x) nil))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))

   (defthm cheap-default-cdr
     (implies (not (consp x))
              (equal (cdr x) nil))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))

   (defthm nthcdr-when-not-consp
     (implies (and (not (consp x))
                   (not (zp n)))
              (equal (nthcdr n x) nil)))

   (defthm nthcdr-of-cons
     (implies (not (zp n))
              (equal (nthcdr n (cons a b))
                     (nthcdr (+ -1 n) b))))

   (defthm nthcdr-run-gified-of-geval-list
     (implies (and (run-gified-ev-theoremp
                    (disjoin (geval-list-def-thm
                              geval-list geval)))
                   (not (equal geval 'quote))
                   (not (equal geval-list 'quote))
                   ;; (acl2::take n (run-gified-ev args a))
                   )
              (equal
               (nthcdr n (run-gified-ev (list geval-list args env) a))
               (run-gified-ev (list geval-list (make-n-cdrs n args) env) a)))
     :hints(("Goal" :in-theory (e/d (my-run-gified-ev-constraint-0)
                                    (nthcdr nth))
             :induct (make-n-cdrs n args)
             :expand ((:free (x) (nthcdr 0 x))))))


   (defthm nth-run-gified-of-geval
     (implies (and (run-gified-ev-theoremp
                    (disjoin (geval-list-def-thm
                              geval-list geval)))
                   (run-gified-ev-theoremp
                    (disjoin (geval-of-nil-thm
                              geval geval-nil)))
                   (not (equal geval 'quote))
                   (not (equal geval-list 'quote)))
              (equal
               (nth n (run-gified-ev (list geval-list args env) a))
               (run-gified-ev (list geval (list 'car (make-n-cdrs n args)) env) a)))
     :hints(("Goal" :use ((:instance
                           car-nthcdr
                           (a (run-gified-ev (list gevalfn args env) a))))
             :in-theory (e/d (run-gified-ev-constraint-0)
                             (car-nthcdr acl2::car-nthcdr))
             :cases ((consp (run-gified-ev args a))))))

   (defthm run-gified-ev-lst-kwote-lst
     (equal (run-gified-ev-lst (acl2::kwote-lst x) a)
            (acl2::list-fix x)))

   (defthm cdr-kwote-lst
     (equal (cdr (acl2::kwote-lst lst))
            (acl2::kwote-lst (cdr lst))))

   (defthm car-kwote-lst
     (equal (car (acl2::kwote-lst lst))
            (and (consp lst)
                 (list 'quote (car lst)))))

   (defthm consp-nthcdr
     (equal (consp (nthcdr n x))
            (< (nfix n) (len x)))
     :hints(("Goal" :in-theory (enable equal-of-booleans-rewrite))))

   (defthm kwote-lst-cons
     (equal (acl2::kwote-lst (cons a b))
            (cons (list 'quote a)
                  (acl2::kwote-lst b))))

   (defthm kwote-lst-atom
     (implies (atom a)
              (equal (acl2::kwote-lst a) nil))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))

   (in-theory (disable acl2::kwote-lst nth))

   ;; (in-theory (disable acl2::ev-apply-arglist-on-result))

   (in-theory (disable nthcdr))

   (in-theory (disable acl2::true-list-listp-forward-to-true-listp-assoc-equal
                       equal-of-booleans-rewrite
                       default-car default-cdr))

   (defthm nth-when-len-smaller
     (implies (<= (len lst) (nfix n))
              (equal (nth n lst) nil))
     :hints(("Goal" :in-theory (enable nth))))

   (defthm run-gified-ev-lst-make-nths-matching-formals
     (implies (natp n)
              (equal (run-gified-ev-lst (make-nths-matching-formals
                                         n formals actuals) a)
                     (acl2::take (len formals)
                                        (nthcdr n (run-gified-ev actuals a)))))
     :hints(("Goal" :in-theory (enable nth nthcdr acl2::take))))




   (defthm asdfasdfa
     ;;   (let ((n (nfix (- (len actuals)
     ;;                     (len formals)))))
     (implies (and ;;  (natp n)
               ;;                 (< n (len actuals))
               (acl2::check-ev-of-quote evalfn quote-name (w state))
               (acl2::check-ev-of-variable evalfn var-name (w state))
               (run-gified-ev-meta-extract-global-facts)
               (run-gified-ev-theoremp
                (disjoin (geval-list-def-thm
                          geval-list gevalfn)))
               (run-gified-ev-theoremp
                (disjoin (geval-of-nil-thm
                          gevalfn geval-nil)))
               (not (equal gevalfn 'quote))
               (not (equal geval-list 'quote))
               (not (equal evalfn 'quote)))
              (equal (run-gified-ev-lst
                      (acl2::ev-of-arglist ;; acl2::ev-apply-arglist-on-result
                       n
                       evalfn
                       (acl2::kwote-lst
                        (run-gified-ev
                         (list geval-list
                               (list 'quote actuals)
                               env)
                         nil))
                       nil)
                      nil)
                     (run-gified-ev-lst
                      (make-evals-of-formals
                       (acl2::kwote-lst
                        (acl2::take
                         n
                         actuals))
                       gevalfn env)
                      nil)))
     :hints(("Goal"
             :induct t
             :in-theory (enable acl2::take)
             :expand ((:free (a b c)
                             (acl2::ev-of-arglist
                              n a b c))))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (my-run-gified-ev-constraint-0
                                    acl2::replicate))))))

   (encapsulate nil
     (local (defthm nthcdr-is-nil
              (implies (< (len lst) (nfix n))
                       (equal (nthcdr n lst) nil))
              :hints(("Goal" :in-theory (enable nthcdr)))))

     (defthmd nths-matching-formalsp-make-nths-matching-formals-ev
       (implies (and (nths-matching-formalsp idx formals varname list)
                     (natp idx))
                (equal (run-gified-ev-lst list a)
                       (acl2::take
                        (len formals)
                        (nthcdr idx (run-gified-ev varname a)))))
       :hints(("Goal" :in-theory (enable my-equal-of-cons
                                         acl2::take
                                         nths-matching-formalsp))))

     (defthmd nths-matching-formalsp-make-nths-matching-formals-ev1
       (implies (nths-matching-formalsp 0 formals varname list)
                (equal (run-gified-ev-lst list a)
                       (acl2::take
                        (len formals)
                        (run-gified-ev varname a))))
       :hints(("Goal" :in-theory (enable nthcdr)
               :use ((:instance
                      nths-matching-formalsp-make-nths-matching-formals-ev
                      (idx 0)))))))

   (defthm get-geval-thm-success-impl-len
     (implies (not (mv-nth 0 (run-gified-get-geval-thm gfn fn geval-alist geval)))
              (<= 5 (len (mv-nth 2 (run-gified-get-geval-thm gfn fn geval-alist
                                                             geval)))))
     :hints(("Goal" :in-theory (enable run-gified-get-geval-thm
                                       run-gified-check-geval-thm)))
     :rule-classes :linear)))

(local (in-theory (disable acl2-count)))

(defun run-gified-process-body (body eval-alist evalfn geval-alist gevalfn
                                     clauses world)
  (if (equal body
             '((LAMBDA (HYP)
                       (CONS 'NIL (CONS 'NIL (CONS HYP 'NIL))))
               ((LAMBDA (HYP) HYP)
                (RETURN-LAST 'ACL2::MBE1-RAW
                             HYP
                             (RETURN-LAST 'PROGN
                                          (ACL2::THROW-NONEXEC-ERROR ':NON-EXEC
                                                                     '(BFR-HYP-FIX HYP))
                                          (BFR-HYP-FIX HYP)))))
             ;; (cons 'nil (cons 'nil 'nil))
             )
      ;; done.
      (mv nil clauses)
    (b* (((mv erp fnname gfnname args rest)
          (run-gified-case-breakdown body))
         ((when erp) (mv erp nil))
         ((when (or (eq fnname 'quote)
                    (eq gfnname 'quote)))
          (mv "A function name is QUOTE which is bizzaro." nil))
         ((mv erp clauses)
          (run-gified-process-body rest eval-alist evalfn geval-alist gevalfn
                                   clauses world))
         ((when erp) (mv erp nil))
         ((mv erp geval-thm formals)
          (run-gified-get-geval-thm gfnname fnname geval-alist gevalfn))
         ((when erp) (mv erp nil))
         ((unless (equal (len args) (len formals)))
          (mv "The number of arguments doesn't match." nil))
         (erp
          (run-gified-get-eval-thm fnname (take (- (len formals) 5) formals)
                                   evalfn eval-alist world))
         ((when erp) (mv erp nil))
         ((unless (and (nths-matching-formalsp 0 (take (- (len formals) 5) formals)
                                               'actuals
                                               (take (- (len formals) 5) args))
                       (equal (nthcdr (- (len formals) 5) args) '(hyp clk
                                                                      config
                                                                      bvar-db state))))
          (mv (acl2::msg "Malformed function args: ~x0" (caddr body))
              nil))
         (clauses (list* geval-thm clauses)))
      (mv nil clauses))))

(defun ev-constraint-for-search (lemmas hyp-terms ev-term)
  (if (atom lemmas)
      nil
    (b* (((acl2::access acl2::rewrite-rule
                        equiv
                        lhs
                        hyps
                        rune) (car lemmas)))
      (if (and (eq equiv 'equal)
               (equal lhs ev-term)
               (equal hyps hyp-terms))
          rune
        (ev-constraint-for-search
         (cdr lemmas) hyp-terms ev-term)))))




(defun ev-constraint-for-fn (ev fn world)
  (b* ((lemmas (fgetprop ev 'acl2::lemmas nil world)) )
    (ev-constraint-for-search lemmas `((consp x) (equal (car x) ',fn))
                              `(,ev x a))))

(defmacro ev-constraint-for (ev fn)
  `(ev-constraint-for-fn ',ev ',fn world))

(local (Defthm take-of-run-gified-ev-lst
         (implies (<= (nfix n) (len x))
                  (equal (take n (run-gified-ev-lst x a))
                         (run-gified-ev-lst (take n x) a)))))


(local
 (encapsulate nil
   (local (defthm nth-when-nthcdr
            (implies (and (equal v (nthcdr n x))
                          (syntaxp (quotep v)))
                     (equal (nth n x) (car v)))))
   (local (in-theory (enable NTHS-MATCHING-FORMALSP-MAKE-NTHS-MATCHING-FORMALS-EV1)))
   (local (in-theory (disable run-gified-ev-lst-take)))
   (local
    (in-theory (disable
                        cheap-default-car cheap-default-cdr acl2::take
                        ;; ev-quote-clause-correct-for-run-gified-ev
                        ;; ev-lookup-var-clause-correct-for-run-gified-ev
                        nth-when-len-smaller
                        check-ev-of-bad-fncall-correct-for-run-gified-ev
                        check-ev-of-fncall-args-correct-for-run-gified-ev
                        check-ev-of-quote-correct-for-run-gified-ev
                        check-ev-of-lambda-correct-for-run-gified-ev
                        check-ev-of-nonsymbol-atom-correct-for-run-gified-ev
                        check-ev-of-variable-correct-for-run-gified-ev
                        (:definition run-gified-process-body)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-32)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-31)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-30)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-29)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-28)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-26)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-25)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-24)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-23)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-22)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-20)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-19)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-17)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-11)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-10)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-9)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-8)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-15)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-14)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-13)
                        ;; (:REWRITE RUN-GIFIED-EV-constraint-12)
                        (:META ACL2::CANCEL_TIMES-EQUAL-CORRECT)
                        (:META ACL2::CANCEL_PLUS-EQUAL-CORRECT)
                        ; (:REWRITE RUN-GIFIED-EV-CONSTRAINT-3)
                        ;; (:REWRITE ACL2::SYMBOLP-ASSOC-EQUAL)
                        (:d acl2::list-fix)
                        (:REWRITE GEVAL-LIST-DEF-THM-CORRECT)
                        (:DEFINITION SYMBOL-LISTP)
                        (:REWRITE CHEAP-DEFAULT-CDR)
                        (:TYPE-PRESCRIPTION SYMBOL-LISTP))))
;;    (local
;;     (in-theory (set-difference-theories
;;                 (current-theory :here)
;;                 (list ; (EV-CONSTRAINT-FOR RUN-GIFIED-EV GOBJ-LISTP)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV BFR-EVAL)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV BFR-HYP-EVAL)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV FORCE)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV MV-LIST)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV RETURN-LAST)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV HIDE)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV PAIRLIS$)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV SYMBOLP)
;; ; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;; ;  (replaced assoc-eq by assoc-equal).]
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV ASSOC-EQUAL)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV CONSP)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV NTH)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV IF)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV IMPLIES)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV EQUAL)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV EQL)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV CAR)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV ACL2::USE-THESE-HINTS)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV USE-BY-HINT)
;;                       (EV-CONSTRAINT-FOR RUN-GIFIED-EV NOT)))))

   (defthm run-gified-process-body-correct

     (mv-let (erp clauses)
       (run-gified-process-body body eval-alist evalfn geval-alist gevalfn
                                in-clauses (w state))
       (implies (and (not erp)
                     (run-gified-ev-meta-extract-global-facts)
                     (acl2::check-ev-of-quote evalfn quote-name (w state))
                     (acl2::check-ev-of-variable evalfn var-name (w state))
                     (run-gified-ev-theoremp (conjoin-clauses clauses))
                     (run-gified-ev-theoremp
                      (disjoin (geval-list-def-thm
                                geval-list gevalfn)))
                     (run-gified-ev-theoremp
                      (disjoin (geval-of-nil-thm
                                gevalfn geval-nil)))
                     (not (equal evalfn 'quote))
                     (not (equal gevalfn 'quote))
                     (not (equal geval-list 'quote))
                     (mv-nth 0 (run-gified-ev body a))
                     (bfr-hyp-eval (cdr (assoc-equal 'hyp a))
                               (car env)))
                (and
                 (equal (run-gified-ev
                         `(,gevalfn (quote ,(mv-nth 1 (run-gified-ev body a)))
                                    (quote ,env))
                         nil)
                        (run-gified-ev
                         `(,evalfn
                           (quote ,(cons (cdr (assoc 'fn a))
                                         (kwote-lst
                                          (run-gified-ev
                                           `(,geval-list (quote ,(cdr (assoc 'actuals a)))
                                                         (quote ,env))
                                           nil))))
                           'nil)
                         nil))
                 ;; (equal (run-gified-ev
                 ;;         `(,gevalfn (mv-nth '2 ,body) env)
                 ;;         a)
                 ;;        (run-gified-ev
                 ;;         `(,evalfn (list 'mv-nth ''1
                 ;;                         (cons fn (acl2::kwote-lst
                 ;;                                   (,geval-list actuals env))))
                 ;;                   'nil)
                 ;;         a))
                 )))
     :hints (("goal" :induct (run-gified-process-body body eval-alist evalfn
                                                      geval-alist gevalfn
                                                      in-clauses (w state))
              :expand ((run-gified-process-body body eval-alist evalfn
                                                geval-alist gevalfn
                                                in-clauses (w state))))
             (and stable-under-simplificationp
                  '(:in-theory (enable run-gified-ev-constraint-0
                                       my-run-gified-ev-constraint-0)
                    :do-not-induct t))
             ;; (and stable-under-simplificationp
             ;;      '(:use ((:instance
             ;;               nth-of-nthcdr
             ;;               (n 0)
             ;;               (y (MV-NTH 3 (RUN-GIFIED-CASE-BREAKDOWN BODY)))
             ;;               (m (+ -5 (LEN (MV-NTH 3 (RUN-GIFIED-CASE-BREAKDOWN
             ;;                                        BODY))))))
             ;;              (:instance
             ;;               nths-matching-formalsp-make-nths-matching-formals-ev1
             ;;               (list (ACL2::TAKE (+ -5
             ;;                                           (LEN (MV-NTH 3 (RUN-GIFIED-CASE-BREAKDOWN BODY))))
             ;;                                        (MV-NTH 3 (RUN-GIFIED-CASE-BREAKDOWN BODY))))
             ;;               (formals (ACL2::TAKE
             ;;                         (+ -5
             ;;                            (LEN (MV-NTH 3 (RUN-GIFIED-CASE-BREAKDOWN BODY))))
             ;;                         (MV-NTH
             ;;                          2
             ;;                          (RUN-GIFIED-GET-GEVAL-THM (MV-NTH 2 (RUN-GIFIED-CASE-BREAKDOWN BODY))
             ;;                                                    (MV-NTH 1 (RUN-GIFIED-CASE-BREAKDOWN BODY))
             ;;                                                    GEVAL-ALIST GEVALFN))))
             ;;               (varname 'ACTUALS)))
             ;;             :in-theory (e/d (my-run-gified-ev-constraint-0)
             ;;                             (nth-of-nthcdr))))
             ))))


(local
 (defthm run-gified-process-body-correct1
   (mv-let (erp clauses)
     (run-gified-process-body body eval-alist evalfn geval-alist gevalfn
                              in-clauses (w state))
     (implies (and (not erp)
                   (run-gified-ev-meta-extract-global-facts)
                   (acl2::check-ev-of-quote evalfn quote-name (w state))
                   (acl2::check-ev-of-variable evalfn var-name (w state))
                   (run-gified-ev-theoremp (conjoin-clauses clauses))
                   (run-gified-ev-theoremp
                    (disjoin (geval-list-def-thm
                              geval-list gevalfn)))
                   (run-gified-ev-theoremp
                    (disjoin (geval-of-nil-thm
                              gevalfn geval-nil)))
                   (not (equal evalfn 'quote))
                   (not (equal gevalfn 'quote))
                   (not (equal geval-list 'quote))
                   (mv-nth 0 (run-gified-ev body a))
                   (bfr-hyp-eval (cdr (assoc-equal 'hyp a))
                                 (car env)))
              (equal (run-gified-ev
                      (list gevalfn
                            (list 'quote (mv-nth 1 (run-gified-ev body a)))
                            (list 'quote env))
                      nil)
                     (run-gified-ev
                      `(,evalfn (cons fn (acl2::kwote-lst
                                          (,geval-list actuals (quote ,env))))
                                'nil)
                      a))))
   :hints(("Goal" :in-theory (e/d (run-gified-ev-constraint-0)
                                  (run-gified-process-body-correct))
           :use ((:instance run-gified-process-body-correct))))))





(defun run-gified-clause-proc (clause geval-nil state)
  (declare ; (ignore hints)
           (xargs :stobjs state
                  :verify-guards nil))
  (b* (((mv ok subst)
        (acl2::simple-one-way-unify-lst
         '((implies
            (if (bfr-hyp-eval hyp (car env))
                okp-term
              'nil)
            (equal lhs-term rhs-term)))
         clause nil))
       ((unless ok) (mv (acl2::msg "Clause didn't match pattern: ~x0~%"
                                   clause)
                        nil state))
       ((unless (and (eq (cdr (assoc-equal 'hyp subst)) 'hyp)
                     (eq (cdr (assoc-equal 'env subst)) 'env)))
        (mv "Clause variables are different than expected" nil state))
       (lhs (cdr (assoc-equal 'lhs-term subst)))
       (rhs (cdr (assoc-equal 'rhs-term subst)))
       (okp (cdr (assoc-equal 'okp-term subst)))
       ((mv erp geval-fn run-gified-fn)
        (run-gified-lhs-and-okp-breakdown lhs okp))
       ((when erp) (mv erp nil state))
       ((when (equal geval-fn 'quote))
        (mv "The geval function is QUOTE which is silly." nil state))
       ((when (equal run-gified-fn 'quote))
        (mv "The run-gified function is QUOTE which is silly." nil state))
       ((mv erp ev-fn geval-list-fn)
        (run-gified-rhs-breakdown rhs))
       ((when (eq geval-list-fn 'quote))
        (mv "The geval-list function is QUOTE which is silly." nil state))
       ((when erp) (mv erp nil state))
       ((mv ok ?formals body) (acl2::fn-get-def run-gified-fn state))
       ((unless ok)
        (mv (msg "Failed to get the function definition for ~x0" run-gified-fn) nil state))
       ((unless (equal formals '(fn actuals hyp clk config bvar-db state)))
        (mv (msg "Expected the formals of ~x0 to be ~x1" run-gified-fn '(fn actuals hyp clk config bvar-db state))
            nil state))
       (world (w state))
       ((when (eq ev-fn 'quote))
        (mv "The eval function is QUOTE which is silly."
            nil state))
       (eval-rule-alist (acl2::ev-collect-apply-lemmas ev-fn nil world))
       ((unless (acl2::check-ev-of-quote ev-fn (cadr (cdr (hons-get :quote eval-rule-alist))) world))
        (mv "The eval function doesn't have the expected QUOTE constraint." nil state))
       ((unless (acl2::check-ev-of-variable ev-fn (cadr (cdr (hons-get :lookup-var eval-rule-alist))) world))
        (mv "The eval function doesn't have the expected variable-lookup constraint." nil state))
       ((mv erp geval-rule-alist)
        (geval-rule-alist (table-alist 'gl-function-info world) geval-fn
                          world))
       ((when erp) (mv erp nil state))
       ((mv erp clauses)
        (run-gified-process-body body eval-rule-alist ev-fn
                                 geval-rule-alist geval-fn nil world))
       ((when erp) (mv erp nil state)))
    (value
     (list* (geval-list-def-thm geval-list-fn geval-fn)
            (geval-of-nil-thm geval-fn geval-nil)
            clauses))))

(local
 (acl2::def-unify run-gified-ev run-gified-ev-alist))

(local
 (defthm assoc-equal-run-gified-ev-alist
   (equal (cdr (assoc-equal x (run-gified-ev-alist subst a)))
          (run-gified-ev (cdr (assoc-equal x subst)) a))))

(local
 (encapsulate nil
   (local

    (defun cdr-down2 (a b)
      (if (atom a)
          b
        (cdr-down2 (cdr a) (cdr b)))))

   (local
    (defthm run-gified-ev-lst-equal-impl-disjoin-iff
      (implies (equal (run-gified-ev-lst lst a)
                      (run-gified-ev-lst lst2 a2))
               (iff (run-gified-ev (disjoin lst) a)
                    (run-gified-ev (disjoin lst2) a2)))
      :hints (("goal" :induct (cdr-down2 lst lst2)
               :in-theory (enable run-gified-ev-disjoin-when-consp))
              '(:cases ((consp lst2))))
      :rule-classes nil))

   (defthm simple-one-way-unify-lst-usage-disjoin
     (mv-let (ok subst)
       (acl2::simple-one-way-unify-lst template term alist)
       (implies (and ok
                     (pseudo-term-listp term)
                     (pseudo-term-listp template))
                (iff (run-gified-ev (disjoin term) a)
                     (run-gified-ev (disjoin template) (run-gified-ev-alist
                                                        subst a)))))
     :hints (("goal" :use ((:instance
                            run-gified-ev-lst-equal-impl-disjoin-iff
                            (lst term) (a a)
                            (lst2 template) (a2 (run-gified-ev-alist
                                                 (mv-nth 1
                                                         (acl2::simple-one-way-unify-lst
                                                          template term alist))
                                                 a)))))))))
(local
 (defthm run-gified-lhs-and-okp-breakdown-correct-eval
   (mv-let (erp geval run-gified)
     (run-gified-lhs-and-okp-breakdown lhs okp)
     (implies (not erp)
              (and (equal (run-gified-ev lhs a)
                          (run-gified-ev
                           `(,geval (mv-nth '1 (,run-gified fn actuals hyp clk config bvar-db state))
                                    env)
                           a))
                   (equal (run-gified-ev okp a)
                          (run-gified-ev
                           `(mv-nth '0 (,run-gified fn actuals hyp clk config bvar-db state))
                           a)))))
   :hints (("goal" :use run-gified-lhs-and-okp-breakdown-correct
            :in-theory (disable run-gified-lhs-and-okp-breakdown-correct)))))

(local
 (defthm run-gified-rhs-breakdown-correct-eval
   (mv-let (erp evfn geval-list-fn)
     (run-gified-rhs-breakdown rhs)
     (implies (not erp)
              (equal (run-gified-ev rhs a)
                     (run-gified-ev
                      `(,evfn (cons fn (acl2::kwote-lst (,geval-list-fn actuals env)))
                              'nil)
                      a))))))

(local
 (in-theory (disable run-gified-lhs-and-okp-breakdown-correct
                     run-gified-rhs-breakdown-correct)))

(local
 (in-theory (disable acl2::ev-collect-apply-lemmas body table-alist w)))

(local (in-theory (disable run-gified-process-body assoc-equal)))
(local (in-theory (disable SIMPLE-ONE-WAY-UNIFY-LST-WITH-RUN-GIFIED-EV
                           check-ev-of-bad-fncall-correct-for-run-gified-ev
                           check-ev-of-nonsymbol-atom-correct-for-run-gified-ev
                           check-ev-of-fncall-args-correct-for-run-gified-ev
                           check-ev-of-quote-correct-for-run-gified-ev
                           check-ev-of-lambda-correct-for-run-gified-ev
                           check-ev-of-variable-correct-for-run-gified-ev)))
(local (defthm assoc-equal-of-cons
         (implies (syntaxp (and (quotep var)
                                (quotep key)))
                  (equal (assoc var (cons (cons key val) rest))
                         (if (equal var key)
                             (cons key val)
                           (assoc var rest))))
         :hints(("Goal" :in-theory (enable assoc)))))
(local (defthm pairlis-open
         (equal (pairlis$ (cons a b) c)
                (cons (cons a (car c))
                      (pairlis$ b (cdr c))))))
(local (in-theory (disable pairlis$)))

(defthm run-gified-clause-proc-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (run-gified-ev-meta-extract-global-facts)
                (run-gified-ev
                 (conjoin-clauses
                  (acl2::clauses-result
                   (run-gified-clause-proc clause hints state)))
                 (run-gified-ev-falsify
                  (conjoin-clauses
                   (acl2::clauses-result
                    (run-gified-clause-proc clause hints state))))))
           (run-gified-ev (disjoin clause) a))
  :hints (("goal" :do-not-induct t
           :in-theory (enable run-gified-ev-constraint-0 ;; assoc-equal
                              ))
          (and stable-under-simplificationp
               '(:computed-hint-replacement
                 ('(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '(((CDR (ASSOC-EQUAL 'LHS-TERM subst)) . lhs)
                              ((CDR (ASSOC-EQUAL 'rhs-term subst)) . rhs)
                              ((CDR (ASSOC-EQUAL 'OKP-TERM subst)) . okp)
                              ((CDR (ASSOC-EQUAL 'hyp subst)) . hyp)
                              ((CDR (ASSOC-EQUAL 'actuals subst)) . actuals)
                              ((CDR (ASSOC-EQUAL 'env subst)) . env))))
                  '(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '(((MV-NTH '1 (RUN-GIFIED-LHS-AND-OKP-BREAKDOWN
                                           LHS OKP))
                               . geval-fn)
                              ((MV-NTH '2 (RUN-GIFIED-LHS-AND-OKP-BREAKDOWN
                                           LHS OKP))
                               . run-gified-fn))))
                  '(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '(((MV-NTH '1 (RUN-GIFIED-RHS-BREAKDOWN RHS))
                               . evalfn)
                              ((MV-NTH '2 (RUN-GIFIED-RHS-BREAKDOWN RHS))
                               . geval-list-fn)

                              ((MV-NTH '1
                                       (GEVAL-RULE-ALIST (TABLE-ALIST 'GL-FUNCTION-INFO
                                                                      (W STATE))
                                                         GEVAL-FN (W STATE)))
                               . geval-alist))))
                  ;; '(:use ((:instance run-gified-ev-meta-extract-fn-check-def
                  ;;          (st state)
                  ;;          (fn run-gified-fn)
                  ;;          (formals (mv-nth 1 (acl2::fn-get-def geval-fn state)))
                  ;;          (body (mv-nth 2 (acl2::fn-get-def geval-fn state)))
                  ;;          (args (list (LIST
                  ;;                       'QUOTE
                  ;;                       (MV-NTH 1
                  ;;                               (RUN-GIFIED-EV (LIST RUN-GIFIED-FN
                  ;;                                                    (LIST 'QUOTE (CDR (ASSOC-EQUAL 'FN A)))
                  ;;                                                    (LIST 'QUOTE
                  ;;                                                          (CDR (ASSOC-EQUAL 'ACTUALS A)))
                  ;;                                                    (LIST 'QUOTE (CDR (ASSOC-EQUAL 'HYP A)))
                  ;;                                                    (LIST 'QUOTE (CDR (ASSOC-EQUAL 'CLK A)))
                  ;;                                                    (LIST 'QUOTE
                  ;;                                                          (CDR (ASSOC-EQUAL 'CONFIG A)))
                  ;;                                                    (LIST 'QUOTE
                  ;;                                                          (CDR (ASSOC-EQUAL 'BVAR-DB A)))
                  ;;                                                    (LIST 'QUOTE
                  ;;                                                          (CDR (ASSOC-EQUAL 'STATE A))))
                  ;;                                              NIL)))
                  ;;                      (LIST 'QUOTE
                  ;;                            (CDR (ASSOC-EQUAL 'ENV A)))))
                  ;;          (a nil))))
                  ;; '(:clause-processor
                  ;;   (acl2::simple-generalize-cp
                  ;;    clause '(((ACL2::EV-COLLECT-APPLY-LEMMAS
                  ;;               evalfn 'NIL (W STATE)) . eval-alist))))
                  ;; '(:use ((:instance run-gified-ev-falsify
                  ;;                    (x (disjoin (function-def-clause
                  ;;                                 run-gified-fn run-gified-fn
                  ;;                                 '(fn actuals hyp clk config bvar-db state)
                  ;;                                 (MV-NTH 2 (ACL2::FN-GET-DEF GEVAL-FN STATE)))))
                  ;;                    (a a)))
                  ;;        :in-theory (enable run-gified-ev-constraint-0))
                  )
                 :clause-processor
                 (acl2::simple-generalize-cp
                  clause '(((MV-NTH '1 (ACL2::SIMPLE-ONE-WAY-UNIFY-LST
                                        '((IMPLIES (IF (BFR-HYP-EVAL HYP (CAR ENV))
                                                       OKP-TERM
                                                       'NIL)
                                                   (EQUAL LHS-TERM RHS-TERM)))
                                        CLAUSE 'NIL)) . subst))))))
  :rule-classes :clause-processor)

