; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>

(in-package "SV")
(include-book "structure")
(include-book "../svex/rewrite-base")
(include-book "../svex/env-ops")
;; (include-book "centaur/gl/gl-mbe" :dir :system)
(local (include-book "std/alists/hons-assoc-equal" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "std/osets/element-list" :dir :system))
(local (include-book "std/osets/under-set-equiv" :dir :system))
(local (std::add-default-post-define-hook :fix))

(fty::deflist svex-envlist :elt-type svex-env :true-listp t)

(defthm alist-keys-of-svex-alist-eval
  (equal (alist-keys (svex-alist-eval x env))
         (svex-alist-keys x))
  :hints(("Goal" :in-theory (enable alist-keys svex-alist-keys svex-alist-eval))))

(encapsulate nil
  (local (defthm svex-env-extract-when-car-not-member
           (implies (not (member (caar x) (svarlist-fix keys)))
                    (equal (svex-env-extract keys (cdr x))
                           (svex-env-extract keys x)))
           :hints(("Goal" :in-theory (enable svex-env-extract svex-env-lookup)))))

  (local (defthm svex-env-extract-when-car-not-consp
           (implies (not (and (consp (car x)) (svar-p (caar x))))
                    (equal (svex-env-extract keys (cdr x))
                           (svex-env-extract keys x)))
           :hints(("Goal" :in-theory (enable svex-env-extract svex-env-lookup)))))

  (local (defthm svarlist-p-of-alist-keys-of-env
           (implies (svex-env-p x)
                    (svarlist-p (alist-keys x)))
           :hints(("Goal" :in-theory (enable svex-env-p alist-keys)))))

  (defthm svex-env-extract-when-alist-keys-equal
    (implies (and (equal (alist-keys (svex-env-fix x)) keys)
                  (no-duplicatesp keys))
             (equal (svex-env-extract keys x)
                    (svex-env-fix x)))
    :hints(("Goal" :in-theory (enable svex-env-extract svex-env-fix alist-keys no-duplicatesp))
           (and stable-under-simplificationp
                (not (access acl2::clause-id id :pool-lst))
                '(:induct t))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-env-lookup))))))

(local (in-theory (disable acl2::hons-dups-p)))

(define svtv-fsm-run ((ins svex-envlist-p)
                      (prev-st svex-env-p)
                      (x svtv-p))
  :guard (and (consp ins)
              (equal (alist-keys prev-st) (svex-alist-keys (svtv->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv->nextstate x)))))
  :returns (outs svex-envlist-p)
  (b* (((svtv x))
       (current-cycle-env (make-fast-alist (append (mbe :logic (svex-env-extract (svex-alist-keys (svtv->nextstate x))
                                                                                 prev-st)
                                                        :exec prev-st)
                                                   (svex-env-fix (car ins)))))
       (outs (svex-alist-eval x.outexprs current-cycle-env))
       ((when (atom (cdr ins)))
        (clear-memoize-table 'svex-eval)
        (fast-alist-free current-cycle-env)
        (list outs))
       (next-st (svex-alist-eval x.nextstate current-cycle-env)))
    (clear-memoize-table 'svex-eval)
    (fast-alist-free current-cycle-env)
    (cons outs (svtv-fsm-run (cdr ins) next-st x)))
  ///
  (defthm svtv-fsm-run-of-cons
    (Equal (svtv-fsm-run (cons a b) prev-st x)
           (b* ((alist (append (svex-env-extract (svex-alist-keys (svtv->nextstate x)) prev-st)
                               (svex-env-fix a))))
             (cons (svex-alist-eval (svtv->outexprs x) alist)
                   (if (atom b)
                       nil
                     (svtv-fsm-run b
                                   (svex-alist-eval (svtv->nextstate x) alist) x)))))
    :hints(("Goal" :in-theory (enable svtv-fsm-run)))))


(defprod svtv-cycle-varname
  ((name)
   (cycle natp))
  :layout :tree
  :tag :svtv-cycle)


(define svtv-cycle-var ((x svar-p) (cycle natp))
  :returns (cycvar svar-p)
  (b* (((svar x)))
    (change-svar x :name (make-svtv-cycle-varname :name x.name :cycle cycle)))
  ///
  (defthm svtv-cycle-var-unique
    (implies (not (and (svar-equiv x y)
                       (nat-equiv cyc1 cyc2)))
             (not (equal (svtv-cycle-var x cyc1)
                         (svtv-cycle-var y cyc2))))
    :hints(("Goal" :in-theory (enable svar-fix-redef))))

  (defthmd svtv-cycle-var-unique-split
    (iff (equal (svtv-cycle-var x cyc1)
                (svtv-cycle-var y cyc2))
         (and (svar-equiv x y)
              (nat-equiv cyc1 cyc2)))
    :hints(("Goal" :in-theory (enable svar-fix-redef)))))

(define svtv-is-cycle-var ((x svar-p))
  :returns (is-cycle)
  (b* (((svar x)))
    (svtv-cycle-varname-p x.name))
  ///
  (defthm svtv-is-cycle-var-of-svtv-cycle-var
    (svtv-is-cycle-var (svtv-cycle-var x cycle))
    :hints(("Goal" :in-theory (enable svtv-cycle-var))))

  (defret svtv-cycle-var-differs-from-noncycle
    (implies (not (svtv-is-cycle-var y))
             (and (not (equal y (svtv-cycle-var x cycle)))
                  (not (equal (svar-fix y) (svtv-cycle-var x cycle)))))
    :hints(("Goal" :in-theory (enable svtv-cycle-var)))))

(define svtv-cycle-var->svar ((x svar-p))
  :guard (svtv-is-cycle-var x)
  :guard-hints (("goal" :in-theory (enable svtv-is-cycle-var)))
  :returns (svar svar-p)
  (change-svar x :name (svtv-cycle-varname->name (svar->name x)))
  ///
  (defthm svtv-cycle-var->svar-of-svtv-cycle-var
    (equal (svtv-cycle-var->svar (svtv-cycle-var x cycle))
           (svar-fix x))
    :hints(("Goal" :in-theory (enable svtv-cycle-var)))))

(define svtv-cycle-var->cycle ((x svar-p))
  :guard (svtv-is-cycle-var x)
  :guard-hints (("goal" :in-theory (enable svtv-is-cycle-var)))
  :returns (cycle natp :rule-classes :type-prescription)
  (svtv-cycle-varname->cycle (svar->name x))
  ///
  (defthm svtv-cycle-var->cycle-of-svtv-cycle-var
    (equal (svtv-cycle-var->cycle (svtv-cycle-var x cycle))
           (nfix cycle))
    :hints(("Goal" :in-theory (enable svtv-cycle-var))))

  (defthmd equal-of-svtv-cycle-var
    (equal (equal (svtv-cycle-var v cycle) cvar)
           (and (svar-p cvar)
                (svtv-is-cycle-var cvar)
                (equal (svtv-cycle-var->cycle cvar) (nfix cycle))
                (equal (svtv-cycle-var->svar cvar) (svar-fix v))))
    :hints(("Goal" :in-theory (enable svtv-cycle-var
                                      svtv-cycle-var->svar
                                      svtv-is-cycle-var)))))




(define svarlist-has-svtv-cycle-var ((x svarlist-p))
  :returns (has-cycle-var)
  (if (Atom x)
      nil
    (or (svtv-is-cycle-var (car x))
        (svarlist-has-svtv-cycle-var (cdr x))))
  ///
  (defret svtv-cycle-var-not-member-when-has-no-cycle-var
    (implies (not has-cycle-var)
             (and (not (member (svtv-cycle-var v cycle) x))
                  (not (member (svtv-cycle-var v cycle) (svarlist-fix x)))))))



(local (defthm svex-lookup-of-append
         (equal (svex-lookup v (append x y))
                (or (svex-lookup v x)
                    (svex-lookup v y)))
         :hints(("Goal" :in-theory (enable svex-lookup)))))


(define svtv-cycle-var-assigns ((x svarlist-p) (cycle natp))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  :returns (assigns svex-alist-p)
  (if (atom x)
      nil
    (cons (let ((v (svar-fix (car x))))
            (cons v (svex-var (svtv-cycle-var v cycle))))
          (svtv-cycle-var-assigns (cdr x) cycle)))
  ///
  (defret lookup-in-svtv-cycle-var-assigns
    (equal (svex-lookup v assigns)
           (and (member (svar-fix v) (svarlist-fix x))
                (svex-var (svtv-cycle-var v cycle))))
    :hints(("Goal" :in-theory (enable svex-lookup)))))

(define svex-envs-update-nth ((var svar-p)
                              (val 4vec-p)
                              (n natp)
                              (envs svex-envlist-p))
  :returns (new-envs svex-envlist-p)
  (if (zp n)
      (cons (cons (cons (svar-fix var) (4vec-fix val))
                  (svex-env-fix (car envs)))
            (Svex-envlist-fix (cdr envs)))
    (cons (svex-env-fix (car envs))
          (svex-envs-update-nth var val (1- n) (cdr envs))))
  ///
  (defret len-of-svex-envs-update-nth
    (implies (< (nfix n) (len envs))
             (equal (len new-envs) (len envs))))

  (local (defun lookup-ind (n0 n1 envs)
           (declare (xargs :measure (nfix n0)))
           (if (or (zp n1) (zp n0))
               (list n0 envs)
             (lookup-ind (1- n0) (1- n1) (cdr envs)))))

  (local (defthm nth-of-svex-envlist-fix
           (equal (nth n (svex-envlist-fix x))
                  (svex-env-fix (nth n x)))
           :hints(("Goal" :in-theory (enable svex-envlist-fix nth)))))

  (defret lookup-in-svex-envs-update-nth
    (equal (svex-env-lookup v0 (nth n0 (svex-envs-update-nth v1 val n1 envs)))
           (if (and (svar-equiv v0 v1)
                    (nat-equiv n0 n1))
               (4vec-fix val)
             (svex-env-lookup v0 (nth n0 envs))))
    :hints (("goal" :induct (lookup-ind n0 n1 envs)
             :expand ((:free (a b) (nth n0 (cons a b)))
                      (svex-envs-update-nth v1 val n1 envs)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-lookup)))))

  (defthm cdr-of-svex-envs-update-nth
    (equal (cdr (svex-envs-update-nth var val n envs))
           (if (zp n)
               (svex-envlist-fix (cdr envs))
             (svex-envs-update-nth var val (1- n) (cdr envs))))))


(local (defthmd svex-env-lookup-rec
         (equal (svex-env-lookup v x)
                (if (atom x)
                    (4vec-x)
                  (if (and (consp (car x))
                           (svar-p (caar x))
                           (equal (svar-fix v) (caar x)))
                      (4vec-fix (cdar x))
                    (svex-env-lookup v (cdr x)))))
         :hints(("Goal" :in-theory (enable svex-env-lookup)))
         :rule-classes :definition))

(define svex-env-to-cycle-envs-starting ((x svex-env-p)
                                         (start-cycle natp)
                                         (ncycles natp))
  :returns (cycle-envs svex-envlist-p)
  :hooks nil
  (b* (((when (atom x)) (make-list ncycles :initial-element nil))
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svex-env-to-cycle-envs-starting (cdr x) start-cycle ncycles))
       (cycle-envs (svex-env-to-cycle-envs-starting (cdr x) start-cycle ncycles))
       ((cons var val) (car x))
       ((when (and (svtv-is-cycle-var var)
                   (>= (svtv-cycle-var->cycle var) (lnfix start-cycle))
                   (< (svtv-cycle-var->cycle var) (+ (lnfix start-cycle) (lnfix ncycles)))))
        (svex-envs-update-nth (svtv-cycle-var->svar var)
                              val
                              (- (svtv-cycle-var->cycle var) (lnfix start-cycle))
                              cycle-envs)))
    cycle-envs)
  ///
  (deffixequiv svex-env-to-cycle-envs-starting
    :hints(("Goal" :in-theory (enable svex-env-fix))))

  (defret len-of-cycle-envs-of-svex-env-to-cycle-envs-starting
    (equal (len cycle-envs) (lnfix ncycles)))


  (local (defun nth-of-repeat-nil-ind (n m)
           (declare (xargs :measure (nfix n)))
           (if (or (zp n) (zp m))
               nil
             (nth-of-repeat-nil-ind (1- n) (1- m)))))

  (local (defthm nth-of-repeat-nil
           (equal (nth m (repeat n nil))
                  nil)
           :hints(("Goal" :in-theory (enable repeat nth)
                   :induct (nth-of-repeat-nil-ind n m)))))

  (defret lookup-in-cycle-envs-of-svex-env-to-cycle-envs-starting
    (implies (< (nfix m) (nfix n))
             (equal
              (svex-env-lookup
               v
               (nth m (svex-env-to-cycle-envs-starting env curr-cycle n)))
              (svex-env-lookup (svtv-cycle-var v (+ (nfix m) (nfix curr-cycle)))
                               env)))
    :hints(("Goal" :induct (svex-env-to-cycle-envs-starting env curr-cycle n)
            :expand ((:with svex-env-lookup-rec
                      (:free (v) (svex-env-lookup v env)))))
           (and stable-under-simplificationp
                '(:in-theory (enable equal-of-svtv-cycle-var)))))

  (defret lookup-in-car-cycle-envs-of-svex-env-to-cycle-envs-starting
    (implies (posp n)
             (equal
              (svex-env-lookup
               v
               (car (svex-env-to-cycle-envs-starting env curr-cycle n)))
              (svex-env-lookup (svtv-cycle-var v (nfix curr-cycle)) env)))
    :hints (("goal" :use ((:instance lookup-in-cycle-envs-of-svex-env-to-cycle-envs-starting
                           (m 0)))
             :in-theory (e/d (nth) (lookup-in-cycle-envs-of-svex-env-to-cycle-envs-starting)))))


  (defthm cdr-cycle-envs-of-svex-env-to-cycle-envs-starting
    (implies (posp remaining-cycles)
             (equal (cdr (svex-env-to-cycle-envs-starting
                          env curr-cycle remaining-cycles))
                    (svex-env-to-cycle-envs-starting
                     env (+ 1 (nfix curr-cycle)) (1- remaining-cycles))))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:expand ((repeat remaining-cycles nil)))))))

(define svex-env-to-cycle-envs ((x svex-env-p)
                                (ncycles natp))
  :returns (cycle-envs svex-envlist-p)
  :hooks nil
  (b* (((when (atom x)) (make-list ncycles :initial-element nil))
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svex-env-to-cycle-envs (cdr x) ncycles))
       (cycle-envs (svex-env-to-cycle-envs (cdr x) ncycles))
       ((cons var val) (car x))
       ((when (and (svtv-is-cycle-var var)
                   (< (svtv-cycle-var->cycle var) (lnfix ncycles))))
        (svex-envs-update-nth (svtv-cycle-var->svar var)
                              val
                              (svtv-cycle-var->cycle var)
                              cycle-envs)))
    cycle-envs)
  ///
  (deffixequiv svex-env-to-cycle-envs
    :hints(("Goal" :in-theory (enable svex-env-fix))))

  (defthm svex-env-to-cycle-envs-starting-is-svex-env-to-cycle-envs
    (equal (svex-env-to-cycle-envs-starting x 0 ncycles)
           (svex-env-to-cycle-envs x ncycles))
    :hints(("Goal" :in-theory (enable svex-env-to-cycle-envs-starting)))))


(defsection svex-eval-equiv-by-env-similarity-on-vars


  (defquant svex-envs-similar-on-vars (vars env1 env2)
    (forall v
            (implies (member v (svarlist-fix vars))
                     (equal (svex-env-lookup v env1)
                            (svex-env-lookup v env2))))
    :rewrite :direct)

  (local (in-theory (enable svex-envs-similar-on-vars-necc)))

  (local (defthm subsetp-of-union
           (iff (subsetp (union a b) c)
                (and (subsetp (sfix a) c)
                     (subsetp (sfix b) c)))
           :hints ((set-reasoning))))

  (defthm-svex-eval-flag
    (defthm svex-eval-when-envs-similar-on-vars
      (implies (and (svex-envs-similar-on-vars vars env1 env2)
                    (subsetp (svex-vars x) (svarlist-fix vars)))
               (equal (svex-eval x env1)
                      (svex-eval x env2)))
      :hints ('(:expand ((svex-vars x)
                         (:free (env) (svex-eval x env)))))
      :flag expr)
    (defthm svexlist-eval-when-envs-similar-on-vars
      (implies (and (svex-envs-similar-on-vars vars env1 env2)
                    (subsetp (svexlist-vars x) (svarlist-fix vars)))
               (equal (svexlist-eval x env1)
                      (svexlist-eval x env2)))
      :hints ('(:expand ((svexlist-vars x)
                         (:free (env) (svexlist-eval x env)))))
      :flag list))


  (defthm svex-alist-eval-when-svex-envs-similar-on-vars
    (implies (and (svex-envs-similar-on-vars vars env1 env2)
                  (subsetp (svex-alist-vars x) (svarlist-fix vars)))
             (equal (svex-alist-eval x env1)
                    (svex-alist-eval x env2)))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vars)))))
           


(local
 (progn

   (defun trees-differ-by-svex-alist-eval (x y)
     (if (or (atom x)
             (atom y))
         nil
       (if (and (eq (car x) 'svex-alist-eval)
                (eq (car y) 'svex-alist-eval))
           `(equal ,x ,y)
         (if (equal (car x) (car y))
             (trees-differ-by-svex-alist-eval (cdr x) (cdr y))
           (and (equal (cdr x) (cdr y))
                (trees-differ-by-svex-alist-eval (car x) (car y)))))))

   (defun find-alist-eval-diff (x clause)
     (if (atom clause)
         nil
       (or (trees-differ-by-svex-alist-eval x (car clause))
           (find-alist-eval-diff x (cdr clause)))))

   (defun base-hint-for-svex-alist-eval-equality (lit)
     (case-match lit
       (('equal ('svex-alist-eval x env1)
                ('svex-alist-eval x env2))
        `(:computed-hint-replacement
          ((acl2::witness :ruleset svex-envs-similar-on-vars-witnessing))
          :use ((:instance svex-alist-eval-when-svex-envs-similar-on-vars
                 (x ,x)
                 (vars (svex-alist-vars ,x))
                 (env1 ,env1)
                 (env2 ,env2)))))))

   (defun hint-for-svex-alist-eval-equality (clause)
     (declare (xargs :mode :program))
     (b* ((lit (Car (last clause))))
       (case-match lit
         (('equal ('svex-alist-eval x env1)
                  ('svex-alist-eval x env2))
          (declare (ignore x env1 env2))
          (base-hint-for-svex-alist-eval-equality lit))
         (& (b* ((lit1 (case-match lit
                         (('equal x1 x2)
                          (trees-differ-by-svex-alist-eval x1 x2))))
                 ((when lit1)
                  (base-hint-for-svex-alist-eval-equality lit1))
                 (lit2 (find-alist-eval-diff (acl2::dumb-negate-lit lit) clause))
                 ((When lit2)
                  (base-hint-for-svex-alist-eval-equality lit2)))
              nil)))))))


(fty::deflist svex-alistlist :elt-type svex-alist :true-listp t)

(define svex-alistlist-eval ((x svex-alistlist-p)
                             (env svex-env-p))
  :returns (envs svex-envlist-p)
  (if (atom x)
      nil
    (cons (svex-alist-eval (car x) env)
          (svex-alistlist-eval (cdr x) env)))
  ///
  (defthm nth-of-svex-alistlist-eval
    (equal (nth n (svex-alistlist-eval x env))
           (svex-alist-eval (nth n x) env))
    :hints (("goal" :induct t
             :expand ((svex-alist-eval nil env)))))

  (defthm svex-alistlist-eval-of-cons
    (equal (svex-alistlist-eval (cons a b) env)
           (cons (svex-alist-eval a env)
                 (svex-alistlist-eval b env))))

  (defthm svex-alistlist-eval-of-nil
    (equal (svex-alistlist-eval nil env) nil)))

(define svex-alistlist->svexes ((x svex-alistlist-p))
  :returns (svexes svexlist-p)
  (if (atom x)
      nil
    (append (svex-alist-vals (car x))
            (svex-alistlist->svexes (cdr x)))))



(define svex-alistlist-vals-to-envs ((x svex-alistlist-p)
                                     (vals 4veclist-p))
  :guard (equal (len vals) (len (svex-alistlist->svexes x)))
  :prepwork ((local (include-book "std/lists/take" :dir :system))
             (local (include-book "std/lists/nthcdr" :dir :system))
             
             (local (fty::deflist 4veclist :elt-type 4vec :true-listp t))

             (local (defthm nthcdr-of-4veclist-fix
                      (equal (nthcdr n (4veclist-fix x))
                             (4veclist-fix (nthcdr n x)))
                      :hints(("Goal" :in-theory (enable nthcdr 4veclist-fix)))))
             (local (defthm take-of-4veclist-fix
                      (4veclist-equiv (take n (4veclist-fix x))
                                      (take n x))
                      :hints(("Goal" :in-theory (enable 4veclist-fix)
                              :induct (nthcdr n x))))))
  :guard-hints (("goal" :in-theory (enable svex-alistlist->svexes)))
  (if (atom x)
      nil
    (b* ((keys (svex-alist-keys (car x)))
         (len (len keys)))
    (cons (pairlis$ keys (4veclist-fix (take len vals)))
          (svex-alistlist-vals-to-envs (cdr x) (nthcdr len vals)))))
  ///
  (local (defthm pairlis-keys-vals-is-svex-alist-eval
           (equal (pairlis$ (svex-alist-keys x)
                            (svexlist-eval (svex-alist-vals x) env))
                  (svex-alist-eval x env))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-keys svex-alist-vals)))))
  (local (defthm nthcdr-of-append
           (implies (equal n (len a))
                    (Equal (nthcdr n (append a b))
                           b))
           :hints (("goal" :induct (nthcdr n a)))))


  (defthm svex-alistlist-vals-to-envs-correct
    (equal (svex-alistlist-vals-to-envs x (svexlist-eval (svex-alistlist->svexes x) env))
           (svex-alistlist-eval x env))
    :hints(("Goal" :in-theory (enable svex-alistlist->svexes
                                      svex-alistlist-eval)
            :induct (svex-alistlist->svexes x)
            :expand ((:free (vals) (svex-alistlist-vals-to-envs x vals)))))))

(define svex-alistlist-eval-for-symbolic ((x svex-alistlist-p)
                                          (env svex-env-p)
                                          (symbolic-params alistp))
  :returns (res (equal res (svex-alistlist-eval x env)))
  :verify-guards nil
  (mbe :logic
       (svex-alistlist-vals-to-envs x (svexlist-eval-for-symbolic
                                       (hons-copy (svex-alistlist->svexes x))
                                       env
                                       symbolic-params))
       :exec (svex-alistlist-eval x env))
  ///
  (verify-guards svex-alistlist-eval-for-symbolic))


(define svtv-cycles-compose-aux ((x svtv-p)
                                 (remaining-cycles natp)
                                 (curr-cycle natp)
                                 (in-vars svarlist-p)
                                 (prev-state svex-alist-p))
  :returns (outalists svex-alistlist-p)
  (b* (((svtv x))
       (in-alist (svtv-cycle-var-assigns in-vars curr-cycle))
       (full-alist (make-fast-alist (append in-alist (svex-alist-fix prev-state))))
       (outs (svex-alist-compose x.outexprs full-alist))
       ((when (zp remaining-cycles))
        (clear-memoize-table 'svex-compose)
        (fast-alist-free full-alist)
        (list outs))
       (next-state (svex-alist-compose x.nextstate full-alist)))
    (clear-memoize-table 'svex-compose)
    (fast-alist-free full-alist)
    (cons outs
          (svtv-cycles-compose-aux x (1- remaining-cycles) (1+ (lnfix curr-cycle))
                                   in-vars next-state)))
  ///
  (local (defthm consp-by-len
           (implies (and (equal posp-len (posp (len x)))
                         (syntaxp (quotep posp-len)))
                    (equal (consp x) posp-len))))

  (local (defthm len-of-cdr
           (equal (len (cdr x))
                  (if (consp x)
                      (1- (len x))
                    0))))




  (local (in-theory (disable svex-alist-eval-when-svex-envs-similar-on-vars)))
                         
  ;; (local (defthm member-alist-keys-of-svex-env-fix
  ;;          (implies (svar-p v)
  ;;                   (iff (member v (alist-keys (svex-env-fix a)))
  ;;                        (member v (alist-keys a))))
  ;;          :hints(("Goal" :in-theory (enable svex-env-fix alist-keys)))))

  (local (defthm member-alist-keys
           (iff (member v (alist-keys x))
                (hons-assoc-equal v x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthm svex-env-lookup-of-append
           (equal (svex-env-lookup v (append a b))
                  (if (member (svar-fix v) (alist-keys (svex-env-fix a)))
                      (svex-env-lookup v a)
                    (svex-env-lookup v b)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))

  (local (in-theory (disable member-alist-keys)))

  (local (defthm alist-keys-of-svex-alist-eval
           (equal (alist-keys (svex-alist-eval x env))
                  (svex-alist-keys x))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-keys alist-keys)))))

  (local (defthmd svex-lookup-is-member-alist-keys
           ;; opposite of member-svex-alist-keys
           (iff (svex-lookup x a)
                (member (svar-fix x) (svex-alist-keys a)))))

  (local (defthm svar-p-when-member-of-svarlist
           (implies (and (member v x)
                         (svarlist-p x))
                    (svar-p v))))


  (local (defthm svex-eval-of-svex-var
           (equal (svex-eval (svex-var v) env)
                  (svex-env-lookup v env))
           :hints(("Goal" :in-theory (enable svex-eval)))))

  (local (include-book "hints/subgoalp" :dir :system))


  (local (defthm svex-alist-keys-of-svex-alist-compose
           (equal (svex-alist-keys (svex-alist-compose x subst))
                  (svex-alist-keys x))
           :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-compose)))))

  (defret svtv-cycles-compose-aux-eval-is-svtv-fsm-run
    (implies (and (not (svarlist-has-svtv-cycle-var (svex-alist-vars (svtv->outexprs x))))
                  (not (svarlist-has-svtv-cycle-var (svex-alist-vars (svtv->nextstate x))))
                  (set-equiv (svex-alist-keys prev-state) (svex-alist-keys (svtv->nextstate x)))
                  (not (intersectp (svarlist-fix in-vars) (svex-alist-keys (svtv->nextstate x))))
                  (subsetp (svex-alist-vars (svtv->outexprs x))
                           (append (svex-alist-keys (svtv->nextstate x))
                                   (svarlist-fix in-vars)))
                  (subsetp (svex-alist-vars (svtv->nextstate x))
                           (append (svex-alist-keys (svtv->nextstate x))
                                   (svarlist-fix in-vars))))
             (equal (svex-alistlist-eval outalists env)
                    (b* ((cycle-envs (svex-env-to-cycle-envs-starting env curr-cycle (+ 1 (nfix remaining-cycles)))))
                      (svtv-fsm-run cycle-envs
                                    (svex-alist-eval prev-state env)
                                    x))))
    :hints (("goal" :induct t :do-not-induct t)
            ;; (and (acl2::irrelevant-subgoal-p id "Subgoal *1/1")
            ;;      '(:by nil))
            (and stable-under-simplificationp
                 '(:expand (;; (SVEX-ENV-TO-CYCLE-ENVS-STARTING ENV CURR-CYCLE 1)
                            (:free (n pst) (svtv-fsm-run
                                            (svex-env-to-cycle-envs-starting env curr-cycle n)
                                            pst x)))))
            (and stable-under-simplificationp
                 (hint-for-svex-alist-eval-equality clause))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (svex-lookup-is-member-alist-keys)
                                   (member-svex-alist-keys))))
            (acl2::witness :ruleset acl2::set-reasoning-no-consp))
    :otf-flg t))

(local
 ;; for mergesort/difference thms
 (deflist svarlist
  :elt-type svar
  :true-listp t
  :elementp-of-nil nil))

(define svarlist-identity-alist ((x svarlist-p))
  :returns (alist svex-alist-p)
  (if (atom x)
      nil
    (cons (cons (svar-fix (car x)) (svex-var (car x)))
          (svarlist-identity-alist (cdr x))))
  ///
  (defret svarlist-identity-alist-lookup
    (equal (svex-lookup v (svarlist-identity-alist x))
           (and (member (svar-fix v) (svarlist-fix x))
                (svex-var v)))
    :hints(("Goal" :in-theory (enable svex-lookup svarlist-fix))))

  (defret svex-alist-vars-of-svarlist-identity-alist
    (equal (svex-alist-keys alist)
           (svarlist-fix x))
    :hints(("Goal" :in-theory (enable svex-alist-keys svarlist-fix))))

  (defthm eval-of-identity-alist-is-svex-env-extract
    (equal (svex-alist-eval (svarlist-identity-alist x) env)
           (svex-env-extract x env))
    :hints(("Goal" :in-theory (enable svex-env-extract svex-alist-eval)
            :expand ((:free (v) (svex-eval (svex-var v) env)))))))


(local (defthm append-set-diff
         (set-equiv (append a (set-difference$ b a))
                    (append a b))
         :hints ((set-reasoning))))

(local (defthm svexlist-vars-of-svex-alist-vals
         (equal (svexlist-vars (svex-alist-vals x))
                (svex-alist-vars x))
         :hints(("Goal" :in-theory (enable svex-alist-vals svex-alist-vars svexlist-vars)))))

(define svtv-cycles-compose ((x svtv-p)
                             (ncycles natp))
  :returns (outalists svex-alistlist-p)
  (b* (((svtv x))
       (all-vars (mergesort (svexlist-collect-vars (append (svex-alist-vals x.outexprs)
                                                           (svex-alist-vals x.nextstate)))))
       (state-vars (mergesort (svex-alist-keys x.nextstate)))
       (in-vars (difference all-vars state-vars)))
    (svtv-cycles-compose-aux x ncycles 0 in-vars (svarlist-identity-alist state-vars)))
  ///

  (local (defthmd member-alist-keys
           (iff (member v (alist-keys x))
                (hons-assoc-equal v x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthm svex-env-lookup-of-append
           (equal (svex-env-lookup v (append a b))
                  (if (member (svar-fix v) (alist-keys (svex-env-fix a)))
                      (svex-env-lookup v a)
                    (svex-env-lookup v b)))
           :hints(("Goal" :in-theory (enable svex-env-lookup member-alist-keys)))))

  (local (defthm alist-keys-of-svex-alist-eval
           (equal (alist-keys (svex-alist-eval x env))
                  (svex-alist-keys x))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-keys alist-keys)))))

  (local (defthm svex-eval-of-svex-var
           (equal (svex-eval (svex-var v) env)
                  (svex-env-lookup v env))
           :hints(("Goal" :in-theory (enable svex-eval)))))

  (local (defthm not-cycle-var-when-member
           (implies (and (member v noncycle-vars)
                         (not (svarlist-has-svtv-cycle-var noncycle-vars)))
                    (not (svtv-is-cycle-var v)))
           :hints(("Goal" :in-theory (enable svarlist-has-svtv-cycle-var)))))

  (local (defthm svtv-fsm-run-of-identity-state
           (equal (svtv-fsm-run cycle-envs
                                (svex-env-extract (mergesort keys) env)
                                x)
                  (svtv-fsm-run cycle-envs
                                (svex-env-extract keys env)
                                x))
           :hints (("goal" :expand ((:free (prevst) (svtv-fsm-run cycle-envs prevst x))))
                   (and stable-under-simplificationp
                        (hint-for-svex-alist-eval-equality clause)))))

  (local (defthm svex-env-extract-of-subset
           (implies (subsetp (svarlist-fix a) (svarlist-fix b))
                    (equal (svex-env-extract a (svex-env-extract b x))
                           (svex-env-extract a x)))
           :hints (("goal" :in-theory (enable (:i svex-env-extract))
                    :induct (svex-env-extract a x)
                    :expand ((:free (x) (svex-env-extract a x)))))))

  (local (defthm svtv-fsm-run-of-extract-alist-keys
           (equal (svtv-fsm-run cycle-envs (svex-env-extract (svex-alist-keys (svtv->nextstate x)) env) x)
                  (svtv-fsm-run cycle-envs env x))
           :hints(("Goal" :expand ((:free (prevst) (svtv-fsm-run cycle-envs prevst x)))))))


  (defret eval-of-svtv-cycles-compose
    (implies (and (not (svarlist-has-svtv-cycle-var (svex-alist-vars (svtv->outexprs x))))
                  (not (svarlist-has-svtv-cycle-var (svex-alist-vars (svtv->nextstate x)))))
             (equal (svex-alistlist-eval outalists env)
                    (b* ((cycle-envs (svex-env-to-cycle-envs env (+ 1 (nfix ncycles)))))
                      (svtv-fsm-run cycle-envs
                                    ;; (svex-alist-eval (svarlist-identity-alist
                                    ;;                   (mergesort (svex-alist-keys (svtv->nextstate x))))
                                    ;;                  env)
                                    env
                                    x))))
    :hints (("goal" :use ((:instance svtv-cycles-compose-aux-eval-is-svtv-fsm-run
                           (remaining-cycles ncycles)
                           (curr-cycle 0)
                           (in-vars (b* (((svtv x))
                                         (all-vars (mergesort (svexlist-collect-vars (append (svex-alist-vals x.outexprs)
                                                                                             (svex-alist-vals x.nextstate)))))
                                         (state-vars (mergesort (svex-alist-keys x.nextstate))))
                                      (difference all-vars state-vars)))
                           (prev-state (b* (((svtv x))
                                            (state-vars (mergesort (svex-alist-keys x.nextstate))))
                                         (svarlist-identity-alist state-vars)))))
             :in-theory (disable svtv-cycles-compose-aux-eval-is-svtv-fsm-run))
            (set-reasoning))))



(define svarlist-no-cycle-vars-below (n x)
  :verify-guards nil
  (if (atom x)
      t
    (and (or (not (svtv-is-cycle-var (car x)))
             (>= (svtv-cycle-var->cycle (car x)) (nfix n)))
         (svarlist-no-cycle-vars-below n (cdr x))))
  ///
  (defthm svarlist-no-cycle-vars-below-of-append
    (implies (and (svarlist-no-cycle-vars-below n a)
                  (svarlist-no-cycle-vars-below n b))
             (svarlist-no-cycle-vars-below n (append a b))))

  (defthm svarlist-no-cycle-vars-below-when-no-cycle-vars
    (implies (NOT (SVARLIST-HAS-SVTV-CYCLE-VAR x))
             (SVARLIST-NO-CYCLE-VARS-BELOW N x))
    :hints(("Goal" :in-theory (enable svarlist-has-svtv-cycle-var)))))


(define svex-env-add-cycle-num ((x svex-env-p)
                                (cycle natp))
  :returns (cycle-x svex-env-p)
  :hooks nil
  (if (atom x)
      nil
    (if (mbt (and (Consp (car x)) (svar-p (caar x))))
        (cons (cons (svtv-cycle-var (caar x) cycle) (4vec-fix (cdar x)))
              (svex-env-add-cycle-num (cdr x) cycle))
      (svex-env-add-cycle-num (cdr x) cycle)))
  ///
  (deffixequiv svex-env-add-cycle-num
    :hints(("Goal" :in-theory (enable svex-env-fix))))

  (defthm svarlist-no-cycle-vars-below-of-svex-env-add-cycle-num
    (implies (<= (nfix n) (nfix cycle))
             (svarlist-no-cycle-vars-below n (alist-keys (svex-env-add-cycle-num x cycle))))
    :hints(("Goal" :in-theory (enable svarlist-no-cycle-vars-below alist-keys)))))


(define svtv-cycle-envs-to-single-env ((x svex-envlist-p)
                                       (curr-cycle natp)
                                       (rest svex-env-p))
  :returns (env svex-env-p)
  (b* (((when (atom x)) (svex-env-fix rest)))
    (Append (Svex-env-add-cycle-num (car x) curr-cycle)
            (svtv-cycle-envs-to-single-env (cdr x) (1+ (lnfix curr-cycle)) rest)))
  ///
  (local (defthm svex-envlist-fix-when-atom
           (implies (not (consp x))
                    (equal (svex-envlist-fix x) nil))
           :hints(("Goal" :in-theory (enable svex-envlist-fix)))))

  (local (defthm svex-env-to-cycle-envs-starting-0-cycles
           (equal (svex-env-to-cycle-envs-starting x curr-cycle 0)
                  nil)
           :hints(("Goal" :in-theory (enable svex-env-to-cycle-envs-starting)))))

  

  (local (Defthm alist-keys-of-append
           (equal (alist-keys (append a b))
                  (append (alist-keys a) (alist-keys b)))
           :hints(("Goal" :in-theory (enable alist-keys)))))
  
  (local (defret svarlist-no-cycle-vars-below-of-svtv-cycle-envs-to-single-env
           (implies (and (<= (nfix n) (nfix curr-cycle))
                         (not (svarlist-has-svtv-cycle-var (alist-keys (svex-env-fix rest)))))
                    (svarlist-no-cycle-vars-below n (alist-keys env)))))

  (local (defthm svex-envs-update-nth-is-update-nth
           (equal (svex-envs-update-nth var val n x)
                  (update-nth n (cons (cons (svar-fix var) (4vec-fix val))
                                      (svex-env-fix (nth n x)))
                              (svex-envlist-fix x)))
           :hints(("Goal" :in-theory (enable svex-envs-update-nth)))))

  (local (defthm svex-env-p-nth-of-svex-envlist
           (implies (svex-envlist-p x)
                    (svex-env-p (nth n x)))
           :hints(("Goal" :in-theory (enable svex-envlist-p)))))

  (local (defthm nth-of-update-nth-equiv
           (implies (equal x (update-nth n v y))
                    (equal (nth n x) v))))

  (local (defthm update-nth-of-update-nth-equiv
           (implies (equal x (update-nth n v y))
                    (equal (update-nth n v1 x)
                           (update-nth n v1 y)))))

  (local (Defthm update-nth-of-nth
           (implies (< (nfix n) (len x))
                    (equal (update-nth n (nth n x) x) x))))

  (local (defthm svex-env-to-cycle-envs-starting-of-append-add-cycle-num
           (implies (and (<= (nfix curr-cycle) (nfix cycle))
                         (< (nfix cycle) (+ (nfix ncycles) (nfix curr-cycle))))
                    (equal (svex-env-to-cycle-envs-starting
                            (append (svex-env-add-cycle-num env cycle) rest)
                            curr-cycle ncycles)
                           (b* ((rest-envs (svex-env-to-cycle-envs-starting rest curr-cycle ncycles))
                                (n (- (nfix cycle) (nfix curr-cycle))))
                             (update-nth n
                                         (append (svex-env-fix env) (nth n rest-envs)) rest-envs))))
           :hints(("Goal" :in-theory (enable svex-env-add-cycle-num
                                             svex-env-to-cycle-envs-starting
                                             svex-env-fix)
                   :induct (svex-env-add-cycle-num env cycle)))))

  (local (defthm svex-envs-update-nth-car
           (implies (not (zp n))
                    (Equal (car (svex-envs-update-nth var val n x))
                           (svex-env-fix (car x))))
           :hints(("Goal" :in-theory (e/d (svex-envs-update-nth)
                                          (svex-envs-update-nth-is-update-nth))))))

  (local (defthm car-svex-env-to-cycle-envs-starting-when-no-cycle-vars-below
           (implies (svarlist-no-cycle-vars-below (+ 1 (nfix curr-cycle)) (alist-keys (svex-env-fix env)))
                    (equal (car (svex-env-to-cycle-envs-starting env curr-cycle ncycles)) nil))
           :hints(("Goal" :in-theory (e/d (svex-env-to-cycle-envs-starting
                                             svarlist-no-cycle-vars-below
                                             alist-keys svex-env-fix
                                             repeat)
                                          (svex-envs-update-nth-is-update-nth))
                   :induct t))))

  (defret svex-env-to-cycle-envs-of-svtv-cycle-envs-to-single-env-starting
    (implies (not (svarlist-has-svtv-cycle-var (alist-keys (svex-env-fix rest))))
             (equal (svex-env-to-cycle-envs-starting env curr-cycle (len x))
                    (svex-envlist-fix x))))

  (defret svex-env-to-cycle-envs-of-svtv-cycle-envs-to-single-env
    (implies (and (equal len (len x))
                  (not (svarlist-has-svtv-cycle-var (alist-keys (svex-env-fix rest)))))
             (equal (svex-env-to-cycle-envs (svtv-cycle-envs-to-single-env x 0 rest) len)
                    (svex-envlist-fix x)))
    :hints (("Goal" :use ((:instance svex-env-to-cycle-envs-of-svtv-cycle-envs-to-single-env-starting
                           (curr-cycle 0)))
             :in-theory (disable svex-env-to-cycle-envs-of-svtv-cycle-envs-to-single-env-starting))))

  (local (defthmd member-alist-keys
           (iff (member v (alist-keys x))
                (hons-assoc-equal v x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthm svex-env-lookup-of-append
           (equal (svex-env-lookup v (append a b))
                  (if (member (svar-fix v) (alist-keys (svex-env-fix a)))
                      (svex-env-lookup v a)
                    (svex-env-lookup v b)))
           :hints(("Goal" :in-theory (enable svex-env-lookup member-alist-keys)))))

  (local (defthm noncycle-var-member-svex-add-cycle-num
           (implies (not (svtv-is-cycle-var v))
                    (not (member (svar-fix v) (alist-keys (svex-env-add-cycle-num env cycle)))))
           :hints(("Goal" :in-theory (enable svex-env-add-cycle-num
                                             alist-keys
                                             svtv-is-cycle-var)))))

  (defret lookup-in-svex-envs-to-single-env-when-not-cycle
    (implies (not (svtv-is-cycle-var v))
             (equal (svex-env-lookup v (svtv-cycle-envs-to-single-env ins curr-cycle rest))
                    (svex-env-lookup v rest))))

  (local (defthm svex-env-extract-of-append-cycles
           (implies (not (svarlist-has-svtv-cycle-var keys))
                    (equal (svex-env-extract keys (append (svex-env-add-cycle-num env cycle) rest))
                           (svex-env-extract keys rest)))
           :hints(("Goal" :in-theory (enable svex-env-extract svarlist-has-svtv-cycle-var)))))

  (defthm svtv-cycle-envs-to-single-env-extract-non-cycle-keys
    (implies (not (svarlist-has-svtv-cycle-var keys))
             (equal (svex-env-extract keys (svtv-cycle-envs-to-single-env envs curr-cycle rest))
                    (svex-env-extract keys rest)))))


(define svtv-fsm-run-alt ((ins svex-envlist-p)
                          (prev-st svex-env-p)
                          (x svtv-p))
  :guard (consp ins)
  (b* (((svtv x))
       (outalists (svtv-cycles-compose x (1- (len ins))))
       (env (svtv-cycle-envs-to-single-env ins 0 prev-st)))
    (svex-alistlist-eval outalists env))
  ///

  (local (defthm natp-of-posp-minus-1
           (implies (posp x)
                    (natp (+ -1 x)))))

  (local (defthm posp-of-len-when-consp
           (implies (consp x)
                    (posp (len x)))
           :rule-classes :type-prescription))

  (local (defthm svarlist-has-svtv-cycle-var-when-subset
           (implies (and (subsetp vars noncycle-vars)
                         (not (svarlist-has-svtv-cycle-var noncycle-vars)))
                    (not (svarlist-has-svtv-cycle-var vars)))
           :hints(("Goal" :in-theory (enable svarlist-has-svtv-cycle-var subsetp)))))

  (local (defthmd member-alist-keys
           (iff (member v (alist-keys x))
                (hons-assoc-equal v x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthm svex-env-lookup-of-append
           (equal (svex-env-lookup v (append a b))
                  (if (member (svar-fix v) (alist-keys (svex-env-fix a)))
                      (svex-env-lookup v a)
                    (svex-env-lookup v b)))
           :hints(("Goal" :in-theory (enable svex-env-lookup member-alist-keys)))))

  (local (defthm alist-keys-of-svex-alist-eval
           (equal (alist-keys (svex-alist-eval x env))
                  (svex-alist-keys x))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-keys alist-keys)))))


  (local (defthm not-cycle-var-when-member
           (implies (and (member v noncycle-vars)
                         (not (svarlist-has-svtv-cycle-var noncycle-vars)))
                    (not (svtv-is-cycle-var v)))
           :hints(("Goal" :in-theory (enable svarlist-has-svtv-cycle-var)))))

  (local (defthm len-equal-len-cdr-plus-1
           (implies (consp x)
                    (equal (+ 1 (len (cdr x))) (len x)))))

  (defthmd svtv-fsm-run-is-run-alt
    (implies (and (not (svarlist-has-svtv-cycle-var (svex-alist-keys (svtv->nextstate x))))
                  (not (svarlist-has-svtv-cycle-var (svex-alist-vars (svtv->outexprs x))))
                  (not (svarlist-has-svtv-cycle-var (svex-alist-vars (svtv->nextstate x))))
                  (not (svarlist-has-svtv-cycle-var (alist-keys (svex-env-fix prev-st))))
                  (consp ins))
             (equal (svtv-fsm-run ins prev-st x)
                    (svtv-fsm-run-alt ins prev-st x)))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable set-equiv))
            (and stable-under-simplificationp
                 '(:expand ((:free (prev-st) (svtv-fsm-run ins prev-st x)))))
            (and stable-under-simplificationp
                 (hint-for-svex-alist-eval-equality clause)))))




