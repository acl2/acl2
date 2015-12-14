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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")
(include-book "svstmt")
(include-book "../mods/svmods")
(include-book "../svex/compose")
(include-book "../svex/env-ops")
(include-book "../svex/rewrite")
(include-book "centaur/vl/util/warnings" :dir :System)
(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))

(defxdoc svstmt-compile.lisp :parents (svstmt-compile))
(local (xdoc::set-default-parents svstmt-compile.lisp))

(local (defthm cdr-last-of-svex-alist-p
         (implies (svex-alist-p x)
                  (equal (cdr (last x)) nil))))


(local (defthmd cdr-lookup-when-svex-alist-p
         (implies (svex-alist-p x)
                  (iff (cdr (hons-assoc-equal k x))
                       (hons-assoc-equal k x)))
         :hints(("Goal" :in-theory (enable svex-alist-p hons-assoc-equal)))))

(defthm svex-lookup-in-fast-alist-fork
  (implies (and (svex-alist-p x)
                (svex-alist-p y))
           (iff (svex-lookup v (fast-alist-fork x y))
                (or (svex-lookup v x)
                    (svex-lookup v y))))
  :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix
                                    cdr-lookup-when-svex-alist-p))))


(fty::deflist svstack :elt-type svex-alist-p)

(define svstack-to-svex-alist ((x svstack-p))
  :returns (x-alist svex-alist-p)
  (if (atom x)
      nil
    (append (svex-alist-fix (Car x))
            (svstack-to-svex-alist (cdr x))))
  ///
  (local (in-theory (enable cdr-lookup-when-svex-alist-p)))

  (defthm svex-lookup-of-svstack-to-svex-alist-cons
    (equal (svex-lookup k (svstack-to-svex-alist (cons a b)))
           (or (svex-lookup k a)
               (svex-lookup k (svstack-to-svex-alist b))))
    :hints(("Goal" :in-theory (enable svstack-to-svex-alist
                                      svex-lookup))))

  (defthmd svex-lookup-of-svstack-to-svex-alist-consp
    (implies (consp x)
             (equal (svex-lookup k (svstack-to-svex-alist x))
                    (or (svex-lookup k (car x))
                        (svex-lookup k (svstack-to-svex-alist (cdr x))))))
    :hints(("Goal" :in-theory (enable svstack-to-svex-alist svex-lookup))))

  (defthm svstack-to-svex-alist-when-atom
    (implies (atom x)
             (equal (svstack-to-svex-alist x) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))

(define svstack-lookup ((k svar-p) (stack svstack-p))
  :returns (value? (iff (svex-p value?) value?))
  (if (atom stack)
      nil
    (or (svex-fastlookup k (car stack))
        (svstack-lookup k (cdr stack))))
  ///
  (local (in-theory (enable cdr-lookup-when-svex-alist-p)))

  (defret svstack-lookup-in-terms-of-svex-alist
    (equal value?
           (svex-lookup k (svstack-to-svex-alist stack)))
    :hints(("Goal" :in-theory (enable svstack-to-svex-alist
                                      svex-lookup)))))

(define svstack-assign ((k svar-p) (v svex-p) (stack svstack-p))
  :returns (new-stack svstack-p)
  (cond ((atom stack) (list (svex-fastacons k v nil)))
        ((atom (cdr stack)) (list (svex-fastacons k v (car stack))))
        ((svex-fastlookup k (car stack))
         (cons (svex-fastacons k v (car stack)) (svstack-fix (cdr stack))))
        (t (cons (svex-alist-fix (car stack))
                 (svstack-assign k v (cdr stack)))))
  ///
  (local (in-theory (enable cdr-lookup-when-svex-alist-p)))

  (defret svex-lookup-of-svstack-assign
    (equal (svex-lookup k1 (svstack-to-svex-alist new-stack))
           (if (svar-equiv k1 k)
               (svex-fix v)
             (svex-lookup k1 (svstack-to-svex-alist stack))))
    :hints(("Goal" :in-theory (enable svstack-to-svex-alist svex-lookup svex-acons))))

  (defret vars-of-svstack-assign
    (iff (member q (svex-alist-vars (svstack-to-svex-alist new-stack)))
         (or (member q (svex-alist-vars (svstack-to-svex-alist stack)))
             (member q (svex-vars v))))
    :hints(("Goal" :in-theory (enable svstack-to-svex-alist svex-acons svex-alist-vars))))

  (defret consp-of-svstack-assign
    (implies (consp stack)
             (consp new-stack)))

  (defret len-of-svstack-assign
    (<= (len stack) (len new-stack))
    :rule-classes :linear))



(defines svex-compose-svstack
  :parents (svex-composition)
  :short "Compose an svex with a substitution alist.  Variables not in the
substitution are left in place."
  (define svex-compose-svstack ((x svex-p) (a svstack-p))
    :verify-guards nil
    :measure (svex-count x)
    :returns (xa (equal xa (svex-compose x (svstack-to-svex-alist a)))
                 :hints ('(:expand ((svex-compose x (svstack-to-svex-alist a))))))
    (svex-case x
      :var (or (svstack-lookup x.name a)
               (mbe :logic (svex-fix x) :exec x))
      :quote (mbe :logic (svex-fix x) :exec x)
      :call (svex-call x.fn
                       (svexlist-compose-svstack x.args a))))
  (define svexlist-compose-svstack ((x svexlist-p) (a svstack-p))
    :measure (svexlist-count x)
    :returns (xa (equal xa (svexlist-compose x (svstack-to-svex-alist a)))
                 :hints ('(:expand ((svexlist-compose x (svstack-to-svex-alist a))))))
    (if (atom x)
        nil
      (cons (svex-compose-svstack (car x) a)
            (svexlist-compose-svstack (cdr x) a))))
  ///
  (verify-guards svex-compose-svstack)
  (fty::deffixequiv-mutual svex-compose-svstack
    :hints (("goal" :expand ((svexlist-fix x)))))

  (memoize 'svex-compose-svstack
           :condition '(svex-case x :call)))
    

(define svstack-free ((x svstack-p))
  (if (atom x)
      nil
    (prog2$ (fast-alist-free (car x))
            (svstack-free (cdr x)))))

(define svstack-clean ((x svstack-p))
  :returns (new-x svstack-p)
  (if (atom x)
      nil
    (cons (fast-alist-clean (svex-alist-fix (car x)))
          (svstack-clean (cdr x))))
  ///
  (defthm member-vars-of-svstack-clean
    (implies (not (member v (svex-alist-vars (svstack-to-svex-alist x))))
             (not (member v (svex-alist-vars (svstack-to-svex-alist (svstack-clean x))))))
    :hints(("Goal" :in-theory (enable svstack-to-svex-alist))))

  (defthm svex-lookup-of-svstack-clean
    (iff (svex-lookup v (svstack-to-svex-alist (svstack-clean x)))
         (svex-lookup v (svstack-to-svex-alist x)))
    :hints(("Goal" :in-theory (enable svstack-to-svex-alist
                                      svex-lookup)))))

(define svstack-fork ((x svstack-p))
  :returns (new-x svstack-p)
  (if (atom x)
      nil
    (cons (fast-alist-fork (svex-alist-fix (car x)) nil)
          (svstack-fork (cdr x))))
  ///
  (defret len-of-svstack-fork
    (equal (len new-x) (len x)))

  (defret lookup-in-svstack-fork
    (equal (svex-lookup v (svstack-to-svex-alist new-x))
           (svex-lookup v (svstack-to-svex-alist x)))
    :hints(("Goal" :in-theory (enable svex-lookup svstack-to-svex-alist))))

  (defret vars-of-svstack-fork
    (implies (not (member v (svex-alist-vars (svstack-to-svex-alist x))))
             (not (member v (svex-alist-vars (svstack-to-svex-alist new-x)))))
    :hints(("Goal" :in-theory (enable svstack-to-svex-alist))))

  (defret consp-of-svstack-fork
    (equal (consp new-x) (consp x))))


(defprod svstate
  :parents (svstmt-compile)
  :short "Structure containing currently assigned variable values for blocking
          and nonblocking assignments."
  :layout :tree
  ((blkst    svstack-p "State of blocking-assigned variables" :default '(nil))
   (nonblkst svex-alist-p "State of nonblocking-assigned variables")))

(define svstate-free ((x svstate-p))
  :enabled t
  (b* (((svstate x) (svstate-fix x)))
    (progn$ (svstack-free x.blkst)
            (fast-alist-free x.nonblkst)
            x)))

(define svstate-clean ((x svstate-p))
  :returns (new-x svstate-p)
  (b* (((svstate x)))
    (change-svstate x :blkst (svstack-clean x.blkst)
                    :nonblkst (fast-alist-clean x.nonblkst)))
  ///
  (defthm vars-of-svstate-clean-blkst
    (implies (not (member v (svex-alist-vars (svstack-to-svex-alist (svstate->blkst x)))))
             (not (member v (svex-alist-vars (svstack-to-svex-alist (svstate->blkst (svstate-clean x))))))))
  (defthm vars-of-svstate-clean-nonblkst
    (implies (not (member v (svex-alist-vars (svstate->nonblkst x))))
             (not (member v (svex-alist-vars (svstate->nonblkst (svstate-clean x)))))))
  (defthm keys-of-svstate-clean-blkst
    (iff (svex-lookup v (svstack-to-svex-alist (svstate->blkst (svstate-clean x))))
         (svex-lookup v (svstack-to-svex-alist (svstate->blkst x))))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable svex-lookup)))))
  (defthm keys-of-svstate-clean-nonblkst
    (iff (svex-lookup v (svstate->nonblkst (svstate-clean x)))
         (svex-lookup v (svstate->nonblkst x)))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable svex-lookup))))))

(define svstate-fork ((x svstate-p))
  :returns (new-x svstate-p)
  (b* (((svstate x)))
    (change-svstate x :blkst (svstack-fork x.blkst)
                    :nonblkst (fast-alist-fork x.nonblkst nil)))
  ///
  (defret svstate-fork-preserves-blkst-consp
    (implies (consp (svstate->blkst x))
             (consp (svstate->blkst new-x)))
    :hints(("Goal" :expand ((svstack-fork (svstate->blkst x))))))

  (defret svstate-fork-blkst-len
    (equal (len (svstate->blkst new-x))
           (len (svstate->blkst x)))))

(define 4vec-replace-range ((x 4vec-p "the non-replaced part")
                            &key
                            (lsb natp)
                            (width natp)
                            (val 4vec-p))
  :returns (new-x 4vec-p)
  (b* ((high-part (4vec-rsh (2vec (+ (lnfix width) (lnfix lsb))) x))
       (new+high (4vec-concat (2vec (lnfix width)) val high-part)))
    (4vec-concat (2vec (lnfix lsb)) x new+high)))


(define svex-replace-range ((expr svex-p "Expression to update.")
                            &key
                            (lsb   natp)
                            (width natp)
                            (val   svex-p "Thing to install into expr[lsb+width-1:lsb]"))
  :returns (res svex-p)
  (b* ((high-part (svex-rsh (+ (lnfix width) (lnfix lsb)) expr))
       (new+high  (svex-concat width val high-part)))
    (svex-concat lsb expr new+high))
  ///
  (defthm svex-replace-range-correct
    (equal (svex-eval (svex-replace-range x :lsb lsb :width width :val val) env)
           (4vec-replace-range (svex-eval x env) :lsb lsb :width width :val (svex-eval val env)))
    :hints(("Goal" :in-theory (enable 4vec-replace-range svex-apply))))
  (defthm vars-of-svex-replace-range
    (implies (and (not (member v (svex-vars expr)))
                  (not (member v (svex-vars val))))
             (not (member v (svex-vars (svex-replace-range
                                        expr
                                        :lsb lsb :width width :val val)))))))




(define svstacks-compatible ((then-st svstack-p)
                             (else-st svstack-p))
  (if (atom then-st)
      (atom else-st)
    (and (consp else-st)
         (if (atom (cdr then-st))
             (atom (cdr else-st))
           (and (consp (cdr else-st))
                (set-equiv (svex-alist-keys (car then-st))
                           (svex-alist-keys (car else-st)))
                (svstacks-compatible (cdr then-st) (cdr else-st))))))
  ///
  (deffixequiv svstacks-compatible)
  (defequiv svstacks-compatible)

  (defthm svstacks-compatible-of-svstack-assign
    (implies (consp x)
             (svstacks-compatible (svstack-assign k v x) x))
    :hints(("Goal" :in-theory (enable svstack-assign))))

  (defthm svstacks-compatible-of-cdr
    (implies (svstacks-compatible x y)
             (equal (svstacks-compatible (cdr x) (cdr y)) t)))

  (defcong equal svstacks-compatible (svstacks-compatible a b) 1)
  (defcong equal svstacks-compatible (svstacks-compatible a b) 2)

  (defthm svstacks-compatible-of-svstack-fork
    (svstacks-compatible (svstack-fork x) x)
    :hints(("Goal" :in-theory (enable svstack-fork))
           (set-reasoning)))

  (defthm svstacks-compatible-blkst-of-svstate-fork
    (svstacks-compatible (svstate->blkst (svstate-fork x))
                         (svstate->blkst x))
    :hints(("Goal" :in-theory (enable svstate-fork)))))


(define svstmt-assign->subst ((lhs lhs-p  "E.g., {a[3:0], b[2:1]}, reverse order lhs.")
                              (rhs svex-p)
                              (offset natp "Total bits of the lhs we've processed so far.")
                              (blockingp)
                              (st svstate-p))
  :verify-guards nil
  :returns (new-st svstate-p)
  :measure (len lhs)
  ;; We assume here that we have already defended against writing to the same
  ;; parts of the same variable.
  ;;
  ;; We need to make sure we update the state as we go, rather than build a
  ;; list of independent assignments from the previous state, because of cases
  ;; like {a[3:0], a[7:4]} = b.  If we built independent assignments here they
  ;; wouldn't be right because we'd end up only writing to half of A.
  (b* ((offset          (lnfix offset))
       ((mv first rest) (lhs-decomp lhs))
       ((unless first)
        ;; All done processing pieces of the LHS, so can stop.
        (svstate-fix st))
       ((lhrange first) first)
       (st (svstmt-assign->subst rest rhs (+ offset first.w) blockingp st))
       ((svstate st)))
    (lhatom-case first.atom
      :z st
      :var
      (b* ((var first.atom.name)
           (binding (or (if blockingp
                            (svstack-lookup var st.blkst)
                          (svex-fastlookup var st.nonblkst))
                        (make-svex-var :name var)))
           (new-val (svex-replace-range binding
                                        :lsb first.atom.rsh
                                        :width first.w
                                        :val (svex-rsh offset rhs)))
           (new-alist (if blockingp
                          (svstack-assign first.atom.name new-val st.blkst)
                        (hons-acons first.atom.name new-val st.nonblkst)))
           (st (if blockingp
                   (change-svstate st :blkst new-alist)
                 (change-svstate st :nonblkst new-alist))))
        st)))
  ///
  (verify-guards svstmt-assign->subst)


  (defthm svex-p-nonnil-compound-recognizer
    (implies (svex-p x) x)
    :rule-classes :compound-recognizer)
  (local (defthm svex-p-type-of-svex-replace-range
           (svex-p (svex-replace-range x :lsb lsb :width width :val val))
           :rule-classes
           ((:type-prescription :typed-term
             (svex-replace-range x :lsb lsb :width width :val val)))))

  ;; (local (defthm svstmt-assign->subst-preserves-lookup-fwd
  ;;          (implies (not (svex-lookup name (svstmt-assign->subst lhs rhs offset blockingp st)))
  ;;                   (not (svex-lookup name st)))
  ;;          :hints(("Goal" :in-theory (enable svex-lookup)))
  ;;          :rule-classes :forward-chaining))

  (defthm svstmt-assign->subst-preserves-blkst-when-nonblocking
    (equal (svstate->blkst (svstmt-assign->subst lhs rhs offset nil st))
           (svstate->blkst st)))

  (defthm svstmt-assign->subst-preserves-nonblkst-when-blocking
    (equal (svstate->nonblkst (svstmt-assign->subst lhs rhs offset t st))
           (svstate->nonblkst st)))


  (defthm keys-of-svstmt-assign->subst-blkst
    (implies (and (not (svex-lookup v (svstack-to-svex-alist (svstate->blkst st))))
                  (not (member (svar-fix v) (lhs-vars lhs))))
             (not (svex-lookup v (svstack-to-svex-alist (svstate->blkst (svstmt-assign->subst lhs rhs offset blockingp st))))))
    :hints(("Goal" :in-theory (enable lhs-vars lhatom-vars)
            :induct (svstmt-assign->subst lhs rhs offset blockingp st))))

  (defthm keys-of-svstmt-assign->subst-nonblkst
    (implies (and (not (svex-lookup v (svstate->nonblkst st)))
                  (not (member (svar-fix v) (lhs-vars lhs))))
             (not (svex-lookup v (svstate->nonblkst (svstmt-assign->subst lhs rhs offset blockingp st)))))
    :hints(("Goal" :in-theory (enable lhs-vars lhatom-vars)
            :induct (svstmt-assign->subst lhs rhs offset blockingp st))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-lookup lhs-vars lhatom-vars)))))

  (defthm vars-of-svstmt-assign->subst-blkst
    (implies (and (not (member v (svex-alist-vars (svstack-to-svex-alist (svstate->blkst st)))))
                  (not (member v (lhs-vars lhs)))
                  (not (member v (svex-vars rhs))))
             (not (member v (svex-alist-vars
                             (svstack-to-svex-alist (svstate->blkst
                                                     (svstmt-assign->subst lhs rhs offset blockingp st)))))))
    :hints(("Goal" :in-theory (enable svex-alist-vars lhs-vars lhatom-vars)
            :induct (svstmt-assign->subst lhs rhs offset blockingp state))))

  (defthm vars-of-svstmt-assign->subst-nonblkst
    (implies (and (not (member v (svex-alist-vars (svstate->nonblkst st))))
                  (not (member v (lhs-vars lhs)))
                  (not (member v (svex-vars rhs))))
             (not (member v (svex-alist-vars
                             (svstate->nonblkst
                              (svstmt-assign->subst lhs rhs offset blockingp st))))))
    :hints(("Goal" :in-theory (enable svex-alist-vars lhs-vars lhatom-vars)
            :induct (svstmt-assign->subst lhs rhs offset blockingp state))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-lookup lhs-vars lhatom-vars)))))

  (defret consp-blkst-of-svstmt-assign->subst
    (implies (consp (svstate->blkst st))
             (consp (svstate->blkst new-st))))

  (defret len-blkst-of-svstmt-assign->subst
    (<= (len (svstate->blkst st))
        (len (svstate->blkst new-st)))
    :rule-classes :linear)

  (defret svstacks-compatible-of-svstmt-assign->subst
    (implies (consp (svstate->blkst st))
             (svstacks-compatible (svstate->blkst new-st)
                                  (svstate->blkst st)))))


(define svstmt-merge-branches-aux ((key-alist svex-alist-p)
                                   (cond svex-p)
                                   (then-st svex-alist-p)
                                   (else-st svex-alist-p)
                                   (st-acc  svex-alist-p))
  :measure (len (Svex-alist-fix key-alist))
  :returns (merged-st svex-alist-p)
  :verbosep t
  ;; :prepwork ((local (in-theory (enable svex-alist-fix))))
  (b* ((key-alist (svex-alist-fix key-alist))
       ((when (atom key-alist))
        (svex-alist-fix st-acc))
       (key (caar key-alist))
       ((when (svex-fastlookup key st-acc))
        (svstmt-merge-branches-aux (cdr key-alist) cond then-st else-st st-acc))
       (then-val (or (svex-fastlookup key then-st)
                     (make-svex-var :name key)))
       (else-val (or (svex-fastlookup key else-st)
                     (make-svex-var :name key)))
       (val (if (mbe :logic (svex-equiv then-val else-val)
                     :exec (hons-equal then-val else-val))
                then-val
              (svex-call '? (list cond then-val else-val))))
       (st-acc  (hons-acons key val st-acc)))
    (svstmt-merge-branches-aux (cdr key-alist) cond then-st else-st st-acc))
  ///
  (local (in-theory (enable cdr-lookup-when-svex-alist-p)))

  (local (defthm svex-fix-under-iff
           (svex-fix x)
           :hints (("goal" :use ((:theorem (svex-p (svex-fix x))))
                    :in-theory nil)
                   (and stable-under-simplificationp
                        '(:in-theory (enable))))))

  (local (defthm cdar-of-svex-alist-fix-under-iff
           (iff (cdar (svex-alist-fix x))
                (consp (svex-alist-fix x)))
           :hints(("Goal" :in-theory (enable svex-alist-fix)))))

  (local (defthm svex-eval-when-var
           (implies (equal (svex-kind x) :var)
                    (equal (svex-eval x env)
                           (svex-env-lookup (svex-var->name x) env)))
           :hints(("Goal" :in-theory (enable svex-eval)))))

  (local (defthm svex-eval-of-svex-var
           (equal (svex-eval (svex-var name) env)
                  (svex-env-lookup name env))
           :hints(("Goal" :in-theory (enable svex-eval)))))



  (local (defthm 4vec-?-when-reduction-or-true
           (implies (equal (4vec-reduction-or test) -1)
                    (equal (4vec-? test then else)
                           (4vec-fix then)))
           :hints(("Goal" :in-theory (enable 4vec-? 3vec-?
                                             4vec-reduction-or
                                             3vec-reduction-or)))))

  (local (defthm 4vec-?-when-reduction-or-false
           (implies (equal (4vec-reduction-or test) 0)
                    (equal (4vec-? test then else)
                           (4vec-fix else)))
           :hints(("Goal" :in-theory (enable 4vec-? 3vec-?
                                             4vec-reduction-or
                                             3vec-reduction-or)))))


  (defthm svstmt-merge-branches-aux-lookup-under-iff
    (iff (svex-lookup k (svstmt-merge-branches-aux key-alist cond then-st else-st st-acc))
         (or (svex-lookup k st-acc)
             (svex-lookup k key-alist)))
    :hints(("Goal" :in-theory (e/d (svex-lookup)
                                   ((:d svstmt-merge-branches-aux)))
            :induct (svstmt-merge-branches-aux key-alist
                                               cond
                                               then-st
                                               else-st
                                               st-acc)
            :expand ((svstmt-merge-branches-aux key-alist cond then-st else-st st-acc)
                     (hons-assoc-equal (svar-fix k) (svex-alist-fix key-alist)))
            :do-not-induct t)))

  (defthm svstmt-merge-branches-aux-when-cond-true-lookup
    (implies (equal (4vec-reduction-or (svex-eval cond env)) -1)
             (equal (svex-eval (svex-lookup k (svstmt-merge-branches-aux key-alist
                                                                         cond
                                                                         then-st
                                                                         else-st
                                                                         st-acc))
                               env)
                    (if (svex-lookup k st-acc)
                        (svex-eval (svex-lookup k st-acc) env)
                      (if (svex-lookup k key-alist)
                          (if (svex-lookup k then-st)
                              (svex-eval (svex-lookup k then-st) env)
                            (svex-env-lookup k env))
                        (4vec-x)))))
    :hints(("Goal" :in-theory (e/d (svex-lookup)
                                   ((:d svstmt-merge-branches-aux)))
            :induct (svstmt-merge-branches-aux key-alist
                                               cond
                                               then-st
                                               else-st
                                               st-acc)
            :expand ((svstmt-merge-branches-aux key-alist cond then-st else-st st-acc)
                     (hons-assoc-equal (svar-fix k) (svex-alist-fix key-alist))))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-apply)))))

  (defthm svstmt-merge-branches-aux-when-cond-false-lookup
    (implies (equal (4vec-reduction-or (svex-eval cond env)) 0)
             (equal (svex-eval (svex-lookup k (svstmt-merge-branches-aux key-alist
                                                                         cond
                                                                         then-st
                                                                         else-st
                                                                         st-acc))
                               env)
                    (if (svex-lookup k st-acc)
                        (svex-eval (svex-lookup k st-acc) env)
                      (if (svex-lookup k key-alist)
                          (if (svex-lookup k else-st)
                              (svex-eval (svex-lookup k else-st) env)
                            (svex-env-lookup k env))
                        (4vec-x)))))
    :hints(("Goal" :in-theory (e/d (svex-lookup)
                                   ((:d svstmt-merge-branches-aux)))
            :induct (svstmt-merge-branches-aux key-alist
                                               cond
                                               then-st
                                               else-st
                                               st-acc)
            :expand ((svstmt-merge-branches-aux key-alist cond then-st else-st st-acc)
                     (hons-assoc-equal (svar-fix k) (svex-alist-fix key-alist)))
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable svex-apply)))))

  (local (defthm svex-lookup-of-caar
           (implies (consp (svex-alist-fix x))
                    (svex-lookup (caar (svex-alist-fix x)) x))
           :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix)))))

  (local (defthm not-svex-lookup-in-cdr
           (implies (not (svex-lookup v x))
                    (not (svex-lookup v (cdr (svex-alist-fix x)))))
           :hints(("Goal" :in-theory (enable svex-lookup hons-assoc-equal)))))

  (defthm keys-of-svstmt-merge-branches-aux
    (implies (and (not (member v (svex-alist-keys then-st)))
                  (not (member v (svex-alist-keys else-st)))
                  (not (member v (svex-alist-keys st-acc)))
                  (not (member v (svex-alist-keys key-alist))))
             (not (member v (svex-alist-keys
                             (svstmt-merge-branches-aux
                              key-alist cond then-st else-st st-acc)))))
    :hints(("Goal" :in-theory (enable svex-alist-keys)
            :induct (svstmt-merge-branches-aux
                     key-alist cond then-st else-st st-acc)
            :do-not-induct t)))

  (defthm svex-lookup-of-svstmt-merge-branches-aux
    (implies (and (not (member v (svex-alist-keys then-st)))
                  (not (member v (svex-alist-keys else-st)))
                  (not (member v (svex-alist-keys st-acc)))
                  (not (member v (svex-alist-keys key-alist)))
                  (svar-p v))
             (not (svex-lookup v (svstmt-merge-branches-aux
                                  key-alist cond then-st else-st st-acc))))
    :hints(("Goal" :in-theory (enable svex-alist-keys)
            :induct (svstmt-merge-branches-aux
                     key-alist cond then-st else-st st-acc)
            :do-not-induct t)))

  (defthm vars-of-svstmt-merge-branches-aux
    (implies (and (not (member v (svex-vars cond)))
                  (not (member v (svex-alist-vars then-st)))
                  (not (member v (svex-alist-vars else-st)))
                  (not (member v (svex-alist-vars st-acc)))
                  (not (member v (svex-alist-keys key-alist))))
             (not (member v (svex-alist-vars
                             (svstmt-merge-branches-aux
                              key-alist cond then-st else-st st-acc)))))
    :hints(("Goal" :in-theory (enable svex-alist-vars
                                      svex-alist-keys)
            :induct (svstmt-merge-branches-aux
                     key-alist cond then-st else-st st-acc)
            :do-not-induct t))))


(define svstmt-merge-branches-svstack ((cond svex-p)
                                           (then-st svstack-p)
                                           (else-st svstack-p))
  :measure (max (len then-st) (len else-st))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svstacks-compatible))))
  :returns (merged-st svstack-p)
  :verbosep t
  (b* (((when (or (atom then-st) (atom else-st)))
        nil)
       (first nil)
       (first (svstmt-merge-branches-aux (car then-st) cond (car then-st) (car else-st) first))
       (first (svstmt-merge-branches-aux (car else-st) cond (car then-st) (car else-st) first)))
    (cons first (svstmt-merge-branches-svstack cond (cdr then-st) (cdr else-st))))
  ///


  (defthm svstmt-merge-branches-svstack-lookup-under-iff
    (implies (double-rewrite (svstacks-compatible then-st else-st))
             (iff (svex-lookup k (svstack-to-svex-alist
                                  (svstmt-merge-branches-svstack cond then-st else-st)))
                  (or (svex-lookup k (svstack-to-svex-alist then-st))
                      (svex-lookup k (svstack-to-svex-alist else-st)))))
    :hints (("goal" :induct (svstmt-merge-branches-svstack cond then-st else-st))
            (and stable-under-simplificationp
                 '(:expand ((svstacks-compatible then-st else-st))))))


  (local (defthm svex-lookup-when-set-equiv
           (implies (and (svex-lookup k x)
                         (set-equiv (svex-alist-keys x) (svex-alist-keys y)))
                    (svex-lookup k y))
           :hints (("goal" :use ((:instance member-svex-alist-keys (k (svar-fix k)))
                                 (:instance member-svex-alist-keys (k (svar-fix k)) (x y)))
                    :in-theory (disable member-svex-alist-keys)))
           :rule-classes (:rewrite
                          (:rewrite :corollary
                           (implies (and (not (svex-lookup k y))
                                         (set-equiv (svex-alist-keys x) (svex-alist-keys y)))
                                    (not (svex-lookup k x)))))))

  (defthm svstmt-merge-branches-svstack-when-cond-true-lookup
    (implies (and (equal (4vec-reduction-or (svex-eval cond env)) -1)
                  (svstacks-compatible then-st else-st))
             (equal (svex-eval (svex-lookup k (svstack-to-svex-alist
                                               (svstmt-merge-branches-svstack
                                                cond
                                                then-st
                                                else-st)))
                               env)
                    (if (svex-lookup k (svstack-to-svex-alist then-st))
                        (svex-eval (svex-lookup k (svstack-to-svex-alist then-st)) env)
                      (if (svex-lookup k (svstack-to-svex-alist else-st))
                          (svex-env-lookup k env)
                        (4vec-x)))))
    :hints(("Goal" :in-theory (enable svex-lookup-of-svstack-to-svex-alist-consp)
            :induct (svstmt-merge-branches-svstack cond then-st else-st))
           (and stable-under-simplificationp
                '(:expand ((svstacks-compatible then-st else-st))))
           ))

  (defthm svstmt-merge-branches-svstack-when-cond-false-lookup
    (implies (and (equal (4vec-reduction-or (svex-eval cond env)) 0)
                  (svstacks-compatible then-st else-st))
             (equal (svex-eval (svex-lookup k (svstack-to-svex-alist
                                               (svstmt-merge-branches-svstack
                                                cond
                                                then-st
                                                else-st)))
                               env)
                    (if (svex-lookup k (svstack-to-svex-alist else-st))
                        (svex-eval (svex-lookup k (svstack-to-svex-alist else-st)) env)
                      (if (svex-lookup k (svstack-to-svex-alist then-st))
                          (svex-env-lookup k env)
                        (4vec-x)))))
    :hints(("Goal" :in-theory (enable svex-lookup-of-svstack-to-svex-alist-consp)
            :induct (svstmt-merge-branches-svstack cond then-st else-st))
           (and stable-under-simplificationp
                '(:expand ((svstacks-compatible then-st else-st))))
           ))

  (defthm keys-of-svstmt-merge-branches-svstack
    (implies (and (not (member v (svex-alist-keys (svstack-to-svex-alist then-st))))
                  (not (member v (svex-alist-keys (svstack-to-svex-alist else-st)))))
             (not (member v (svex-alist-keys
                             (svstack-to-svex-alist (svstmt-merge-branches-svstack
                                                      cond then-st else-st))))))
    :hints(("Goal" :in-theory (enable svex-alist-keys)
            :induct (svstmt-merge-branches-svstack cond then-st else-st)
            :do-not-induct t)))

  (defthm svex-lookup-of-svstmt-merge-branches-svstack
    (implies (and (not (member v (svex-alist-keys (svstack-to-svex-alist then-st))))
                  (not (member v (svex-alist-keys (svstack-to-svex-alist else-st))))
                  (svar-p v))
             (not (svex-lookup v
                               (svstack-to-svex-alist
                                (svstmt-merge-branches-svstack
                                 cond then-st else-st)))))
    :hints(("Goal" :in-theory (enable svex-alist-keys)
            :induct (svstmt-merge-branches-svstack cond then-st else-st)
            :do-not-induct t)))

  (local (defthm svex-alist-vars-of-apppend
           (set-equiv (svex-alist-vars (append a b))
                      (append (svex-alist-vars a) (svex-alist-vars b)))
           :hints(("Goal" :in-theory (enable svex-alist-vars)))))

  (local (in-theory (enable cdr-lookup-when-svex-alist-p)))

  (local (defthm svex-lookup-of-append-under-iff
           (iff (svex-lookup v (append a b))
                (or (svex-lookup v a)
                    (svex-lookup v b)))
           :hints(("Goal" :in-theory (enable svex-lookup)))))

  (defthm vars-of-svstmt-merge-branches-svstack
    (implies (and (not (member v (svex-vars cond)))
                  (not (member v (svex-alist-vars (svstack-to-svex-alist then-st))))
                  (not (member v (svex-alist-vars (svstack-to-svex-alist else-st))))
                  (not (member v (svex-alist-keys (svstack-to-svex-alist then-st))))
                  (not (member v (svex-alist-keys (svstack-to-svex-alist else-st))))
                  (double-rewrite (svstacks-compatible then-st else-st)))
             (not (member v (svex-alist-vars
                             (svstack-to-svex-alist
                              (svstmt-merge-branches-svstack
                                cond then-st else-st))))))
    :hints(("Goal" :in-theory (enable svex-alist-vars
                                      svex-alist-keys)
            :induct (svstmt-merge-branches-svstack cond then-st else-st)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:in-theory (e/d (svstack-to-svex-alist)
                                  (svex-lookup-when-set-equiv
                                   member-svex-alist-keys))
                  :expand ((svstacks-compatible then-st else-st))
                  :use ((:instance member-svex-alist-keys (k v) (x (car then-st)))
                        (:instance member-svex-alist-keys (k v) (x (car else-st))))))))

  (defret svstmt-merge-branches-svstack-compatible
    (implies (double-rewrite (svstacks-compatible then-st else-st))
             (svstacks-compatible merged-st (double-rewrite then-st)))
    :hints(("Goal" :in-theory (enable svstacks-compatible))
           (acl2::set-reasoning)))

  (defret svstmt-merge-branches-svstack-consp
    (implies (and (consp then-st)
                  (consp else-st))
             (consp merged-st)))
  
  (defret svstmt-merge-branches-svstack-len
    (Equal (len merged-st) (min (len then-st) (len else-st)))))



(define svstmt-merge-branches ((cond svex-p)
                               (then-st svstate-p)
                               (else-st svstate-p))
  :returns (merged-st svstate-p)
  (b* (((svstate then-st))
       ((svstate else-st))
       (blkst (svstmt-merge-branches-svstack cond then-st.blkst else-st.blkst))
       (nonblkst nil)
       (nonblkst (svstmt-merge-branches-aux then-st.nonblkst cond then-st.nonblkst else-st.nonblkst nonblkst))
       (nonblkst (svstmt-merge-branches-aux else-st.nonblkst cond then-st.nonblkst else-st.nonblkst nonblkst)))
    (svstate-free then-st)
    (svstate-free else-st)
    (make-svstate :blkst blkst :nonblkst nonblkst))
  ///
  (defthm svstmt-merge-branches-lookup-blkst-when-false
    (implies (and (equal (4vec-reduction-or (svex-eval cond env)) 0)
                  (svstacks-compatible (svstate->blkst then-st)
                                       (svstate->blkst else-st)))
             (equal
              (svex-eval (svex-lookup k (svstack-to-svex-alist (svstate->blkst (svstmt-merge-branches cond then-st else-st)))) env)
              (if (svex-lookup k (svstack-to-svex-alist (svstate->blkst else-st)))
                  (svex-eval (svex-lookup k (svstack-to-svex-alist (svstate->blkst else-st))) env)
                (if (svex-lookup k (svstack-to-svex-alist (svstate->blkst then-st)))
                    (svex-env-lookup k env)
                  (4vec-x))))))

  (defthm svstmt-merge-branches-lookup-nonblkst-when-false
    (implies (equal (4vec-reduction-or (svex-eval cond env)) 0)
             (equal
              (svex-eval (svex-lookup k (svstate->nonblkst (svstmt-merge-branches cond then-st else-st))) env)
              (if (svex-lookup k (svstate->nonblkst else-st))
                  (svex-eval (svex-lookup k (svstate->nonblkst else-st)) env)
                (if (svex-lookup k (svstate->nonblkst then-st))
                    (svex-env-lookup k env)
                  (4vec-x))))))

  (defthm svstmt-merge-branches-lookup-blkst-under-iff
    (implies (double-rewrite (svstacks-compatible (svstate->blkst then-st)
                                                  (svstate->blkst else-st)))
             (iff (svex-lookup k (svstack-to-svex-alist (svstate->blkst (svstmt-merge-branches cond then-st else-st))))
                  (or (svex-lookup k (svstack-to-svex-alist (svstate->blkst then-st)))
                      (svex-lookup k (svstack-to-svex-alist (svstate->blkst else-st)))))))

  (defthm svstmt-merge-branches-lookup-nonblkst-under-iff
    (iff (svex-lookup k (svstate->nonblkst (svstmt-merge-branches cond then-st else-st)))
         (or (svex-lookup k (svstate->nonblkst then-st))
             (svex-lookup k (svstate->nonblkst else-st)))))

  (defthm svstmt-merge-branches-lookup-blkst-when-true
    (implies (and (svstacks-compatible (svstate->blkst then-st)
                                       (svstate->blkst else-st))
                  (equal (4vec-reduction-or (svex-eval cond env)) -1))
             (equal
              (svex-eval (svex-lookup k (svstack-to-svex-alist (svstate->blkst (svstmt-merge-branches cond then-st else-st)))) env)
              (if (svex-lookup k (svstack-to-svex-alist (svstate->blkst then-st)))
                  (svex-eval (svex-lookup k (svstack-to-svex-alist (svstate->blkst then-st))) env)
                (if (svex-lookup k (svstack-to-svex-alist (svstate->blkst else-st)))
                    (svex-env-lookup k env)
                  (4vec-x))))))

  (defthm svstmt-merge-branches-lookup-nonblkst-when-true
    (implies (equal (4vec-reduction-or (svex-eval cond env)) -1)
             (equal
              (svex-eval (svex-lookup k (svstate->nonblkst (svstmt-merge-branches cond then-st else-st))) env)
              (if (svex-lookup k (svstate->nonblkst then-st))
                  (svex-eval (svex-lookup k (svstate->nonblkst then-st)) env)
                (if (svex-lookup k (svstate->nonblkst else-st))
                    (svex-env-lookup k env)
                  (4vec-x))))))

  (local (defthm svex-fix-under-iff
           (svex-fix x)
           :hints (("goal" :use ((:theorem (svex-p (svex-fix x))))
                    :in-theory nil)
                   (and stable-under-simplificationp
                        '(:in-theory (enable))))))

  (local (defthm svex-env-boundp-of-svex-alist-eval
           (iff (svex-env-boundp k (svex-alist-eval x env))
                (svex-lookup k x))
           :hints(("Goal" :in-theory (enable svex-env-boundp
                                             svex-lookup
                                             svex-alist-fix
                                             svex-alist-eval)))))

  (local (defthm svex-env-lookup-of-append
           (Equal (svex-env-lookup k (append a b))
                  (if (svex-env-boundp k a)
                      (svex-env-lookup k a)
                    (svex-env-lookup k b)))
           :hints(("Goal" :in-theory (enable svex-env-lookup
                                             svex-env-boundp)))))

  (defthm svstmt-merge-branches-blkst-when-true
    (implies (and (equal (4vec-reduction-or (svex-eval cond env)) -1)
                  (svstacks-compatible (svstate->blkst then-st)
                                       (svstate->blkst else-st)))
             (svex-envs-similar
              (append (svex-alist-eval (svstack-to-svex-alist (svstate->blkst (svstmt-merge-branches cond then-st else-st))) env) env)
              (append (svex-alist-eval (svstack-to-svex-alist (svstate->blkst then-st)) env) env)))
    :hints(("Goal" :in-theory (disable svstmt-merge-branches))
           (acl2::witness)))

  (defthm svstmt-merge-branches-nonblkst-when-true
    (implies (equal (4vec-reduction-or (svex-eval cond env)) -1)
             (svex-envs-similar
              (append (svex-alist-eval (svstate->nonblkst (svstmt-merge-branches cond then-st else-st)) env) env)
              (append (svex-alist-eval (svstate->nonblkst then-st) env) env)))
    :hints(("Goal" :in-theory (disable svstmt-merge-branches))
           (acl2::witness)))

  (defthm svstmt-merge-branches-blkst-when-false
    (implies (and (equal (4vec-reduction-or (svex-eval cond env)) 0)
                  (svstacks-compatible (svstate->blkst then-st)
                                       (svstate->blkst else-st)))
             (svex-envs-similar
              (append (svex-alist-eval (svstack-to-svex-alist (svstate->blkst (svstmt-merge-branches cond then-st else-st))) env) env)
              (append (svex-alist-eval (svstack-to-svex-alist (svstate->blkst else-st)) env) env)))
    :hints(("Goal" :in-theory (disable svstmt-merge-branches))
           (acl2::witness)))

  (defthm svstmt-merge-branches-nonblkst-when-false
    (implies (equal (4vec-reduction-or (svex-eval cond env)) 0)
             (svex-envs-similar
              (append (svex-alist-eval (svstate->nonblkst (svstmt-merge-branches cond then-st else-st)) env) env)
              (append (svex-alist-eval (svstate->nonblkst else-st) env) env)))
    :hints(("Goal" :in-theory (disable svstmt-merge-branches))
           (acl2::witness)))

  (defthm keys-of-svstmt-merge-branches-blkst
    (implies (and (not (member v (svex-alist-keys (svstack-to-svex-alist (svstate->blkst then-st)))))
                  (not (member v (svex-alist-keys (svstack-to-svex-alist (svstate->blkst else-st))))))
             (not (member v (svex-alist-keys
                             (svstack-to-svex-alist
                              (svstate->blkst (svstmt-merge-branches cond then-st else-st)))))))
    :hints(("Goal" :in-theory (disable member-svex-alist-keys))))

  (defthm svex-lookup-of-svstmt-merge-branches-blkst
    (implies (and (not (member v (svex-alist-keys (svstack-to-svex-alist (svstate->blkst then-st)))))
                  (not (member v (svex-alist-keys (svstack-to-svex-alist (svstate->blkst else-st)))))
                  (svar-p v))
             (not (svex-lookup v (svstack-to-svex-alist
                                  (svstate->blkst
                                   (svstmt-merge-branches cond then-st else-st))))))
    :hints(("Goal" :in-theory (disable member-svex-alist-keys))))

  (defthm vars-of-svstmt-merge-branches-blkst
    (implies (and (not (member v (svex-vars cond)))
                  (not (member v (svex-alist-vars (svstack-to-svex-alist (svstate->blkst then-st)))))
                  (not (member v (svex-alist-vars (svstack-to-svex-alist (svstate->blkst else-st)))))
                  (not (member v (svex-alist-keys (svstack-to-svex-alist (svstate->blkst then-st)))))
                  (not (member v (svex-alist-keys (svstack-to-svex-alist (svstate->blkst else-st)))))
                  (double-rewrite (svstacks-compatible (svstate->blkst then-st)
                                                       (svstate->blkst else-st))))
             (not (member v (svex-alist-vars
                             (svstack-to-svex-alist
                              (svstate->blkst
                               (svstmt-merge-branches cond then-st else-st))))))))

  (defthm keys-of-svstmt-merge-branches-nonblkst
    (implies (and (not (member v (svex-alist-keys (svstate->nonblkst then-st))))
                  (not (member v (svex-alist-keys (svstate->nonblkst else-st)))))
             (not (member v (svex-alist-keys
                             (svstate->nonblkst (svstmt-merge-branches cond then-st else-st)))))))

  (defthm vars-of-svstmt-merge-branches-nonblkst
    (implies (and (not (member v (svex-vars cond)))
                  (not (member v (svex-alist-vars (svstate->nonblkst then-st))))
                  (not (member v (svex-alist-vars (svstate->nonblkst else-st))))
                  (not (member v (svex-alist-keys (svstate->nonblkst then-st))))
                  (not (member v (svex-alist-keys (svstate->nonblkst else-st)))))
             (not (member v (svex-alist-vars
                             (svstate->nonblkst
                              (svstmt-merge-branches cond then-st else-st)))))))

  (defret svstmt-merge-branches-blkst-compatible
    (implies (double-rewrite (svstacks-compatible (svstate->blkst then-st)
                                                  (svstate->blkst else-st)))
             (svstacks-compatible (svstate->blkst merged-st)
                                  (double-rewrite (svstate->blkst then-st)))))

  (defret svstmt-merge-branches-preserves-blkst-consp
    (implies (and (consp (svstate->blkst then-st))
                  (consp (svstate->blkst else-st)))
             (consp (svstate->blkst merged-st))))

  (defret svstmt-merge-branches-blkst-len
    (Equal (len (svstate->blkst merged-st))
           (min (len (svstate->blkst then-st))
                (len (svstate->blkst else-st))))))




(define svar-subtract-delay ((x svar-p) (delay natp))
  :returns (xx svar-p)
  (change-svar x :delay (nfix (- (svar->delay x) (lnfix delay)))))

(defthm member-of-svarlist-add-delay
  (iff (member v (svarlist-add-delay x delay))
       (and (svar-p v)
            (<= (nfix delay) (svar->delay v))
            (member (svar-subtract-delay v delay) (svarlist-fix x))))
  :hints(("Goal" :in-theory (enable svar-add-delay
                                    svarlist-add-delay
                                    svar-subtract-delay))))

(define svstmt-initialize-locals ((locals svarlist-p))
  :returns (scope svex-alist-p)
  (if (atom locals)
      nil
    (svex-fastacons (car locals) (svex-x)
                    (svstmt-initialize-locals (cdr locals))))
  ///
  (defret svex-lookup-in-svstmt-initialize-locals
    (iff (svex-lookup x scope)
         (member (svar-fix x) (svarlist-fix locals))))

  (defret svex-alist-vars-of-initialize-locals
    (equal (svex-alist-vars scope) nil)))


(defines svstmt-compile
  :verify-guards nil
  (define svstmt-compile ((x svstmt-p)
                          (st svstate-p)
                          (reclimit natp)
                          (nb-delayp))
    :parents (svstmt)
    :returns (mv (ok)
                 (warnings1 vl::vl-warninglist-p)
                 (st1 svstate-p))
    :measure (two-nats-measure reclimit (svstmt-count x))
    (b* ((x              (svstmt-fix x))
         ((svstate st)   (svstate-fix st))
         (warnings       nil))
      (svstmt-case x
        :assign
        ;; {foo, bar[3]} = a + b
        ;;
        ;; We may have bindings for RHS variables like A and B in our
        ;; current state.
        ;;
        ;; We may have bindings for LHS variables like FOO and BAR.
        ;;
        ;;   - If we previously wrote to FOO, we don't care because we're
        ;;     overwriting its whole value anyway.  Except this will never
        ;;     happen because we never write to all of FOO.
        ;;
        ;;   - If we previously wrote to BAR, we do care because we need to
        ;;     merge this bar[3] update into it.
        ;;
        ;;   - What if we never previously wrote to BAR?  What do we want to
        ;;     assume?  I think we want to assume that, in the functions that
        ;;     either invoke svstmt-compile or that use its results, someone
        ;;     else is responsible for telling us what to do.  It might be
        ;;     after the fact in the form of a substitution.  So for that to
        ;;     make sense, here we want to act as though BAR is bound to
        ;;     itself, not e.g., to X, because maybe we're going to use this
        ;;     stuff to process latches or something where we need previous
        ;;     state.
        ;;
        ;; OK, so anything we look up in the LHS and don't find, we bind to
        ;; itself.  And that goes for the RHS as well.
        (b* (((mv mask-acc conf-acc) (lhs-check-masks x.lhs nil nil))
             (- (fast-alist-free mask-acc)
                (fast-alist-free conf-acc))
             ((when conf-acc)
              (svstate-free st)
              (mv nil
                  (vl::warn :type :svstmt-compile-fail
                            :msg "Overlapping writes in the same assignment: ~
                              ~a0 (conflicts: ~a1)"
                            :args (list x conf-acc))
                  (make-svstate)))
             ;;
             (composed-rhs (svex-compose-svstack x.rhs st.blkst))
             (composed-rhs (if (and (eq nb-delayp t)
                                    (not x.blockingp))
                               (svex-add-delay composed-rhs 1)
                             composed-rhs))
             (st (svstmt-assign->subst x.lhs composed-rhs 0 x.blockingp st)))
          (mv t warnings st))
        :if
        (b* (;; We need to compose ST into the condition to handle cases
             ;; like:
             ;;    A = 1;
             ;;    if (A) { ... } else {...}
             (cond-compose (svex-compose-svstack x.cond st.blkst))
             (st2 (svstate-fork st))
             ((vl::wmv ok warnings then-st)
              (svstmtlist-compile x.then st reclimit nb-delayp))
             ((unless ok)
              (svstate-free st2)
              (mv nil warnings (make-svstate)))
             ((vl::wmv ok warnings else-st)
              (svstmtlist-compile x.else st2 reclimit nb-delayp))
             ((unless ok)
              (svstate-free then-st)
              (mv nil warnings (make-svstate)))
             (st (svstmt-merge-branches cond-compose then-st else-st)))
          (mv t warnings st))
        :while
        (b* ((cond-compose (svex-compose-svstack x.cond st.blkst))
             (cond-rw (svex-maskfree-rewrite cond-compose))
             ((when (eql cond-rw 0))
              (mv t warnings st))
             ((when (zp reclimit))
              (svstate-free st)
              (mv nil
                  (warn :type :svstmt-compile-fail
                        :msg "couldn't determine bound on while loop ~
                              unrollings: ~a0. rewritten condition ~a1."
                        :args (list x cond-rw))
                  (make-svstate)))
             (norun-st (svstate-fork st))
             ((vl::wmv ok warnings run-st)
              (svstmtlist-compile x.body st reclimit nb-delayp))
             ((unless ok)
              (svstate-free norun-st)
              (mv nil warnings (make-svstate)))
             ((vl::wmv ok warnings run-st)
              (svstmt-compile x run-st (1- reclimit) nb-delayp))
             ((unless ok)
              (svstate-free norun-st)
              (mv nil warnings (make-svstate)))
             (st (svstmt-merge-branches cond-rw run-st norun-st)))
          (mv ok warnings st))
        :scope
        (b* ((subscope-blkst (cons (svstmt-initialize-locals x.locals) st.blkst))
             (subscope-st (change-svstate st :blkst subscope-blkst))
             ((vl::wmv ok warnings subscope-st)
              (svstmtlist-compile x.body subscope-st reclimit nb-delayp))
             ((unless ok) (mv nil warnings st))
             (blkst (mbe :logic (cdr (svstate->blkst subscope-st))
                         :exec (and (consp (svstate->blkst subscope-st))
                                    (cdr (svstate->blkst subscope-st))))))
          (mv t warnings (change-svstate subscope-st :blkst blkst))))))

  (define svstmtlist-compile ((x        svstmtlist-p)
                              (st       svstate-p)
                              (reclimit natp)
                              (nb-delayp))
    :returns (mv (ok)
                 (warnings1 vl::vl-warninglist-p)
                 (st1       svstate-p))
    :measure (two-nats-measure reclimit (svstmtlist-count x))
    (b* ((warnings nil)
         ((when (atom x))
          (mv t
              (vl::ok)
              (svstate-fix st)))
         ((vl::wmv okp1 warnings st)
          (svstmt-compile (car x) st reclimit nb-delayp))
         ((unless okp1)
          (mv nil warnings st)))
      (svstmtlist-compile (cdr x) st reclimit nb-delayp)))
  ///
  (verify-guards svstmtlist-compile :guard-debug t)


  (defthm-svstmt-compile-flag
    (defthm svstmt-compile-preserves-blkst-len
      (b* (((mv ?ok ?warnings ?new-st)
            (svstmt-compile x st reclimit nb-delayp)))
        (implies ok
                 (<= (len (svstate->blkst st))
                     (len (svstate->blkst new-st)))))
      :rule-classes :linear
      :flag svstmt-compile)
    (defthm svstmtlist-compile-preserves-blkst-len
      (b* (((mv ?ok ?warnings ?new-st)
            (svstmtlist-compile x st reclimit nb-delayp)))
        (implies ok
                 (<= (len (svstate->blkst st))
                     (len (svstate->blkst new-st)))))
      :rule-classes :linear
      :flag svstmtlist-compile))

  (local (defthm len-when-consp
           (implies (consp x)
                    (< 0 (len x)))
           :rule-classes :type-prescription))

  (defthm svstmt-compile-preserves-blkst-consp
    (b* (((mv ?ok ?warnings ?new-st)
          (svstmt-compile x st reclimit nb-delayp)))
      (implies (and ok (consp (svstate->blkst st)))
               (consp (svstate->blkst new-st))))
    :hints (("goal" :use ((:instance svstmt-compile-preserves-blkst-len))
             :in-theory (e/d (len) (svstmt-compile-preserves-blkst-len)))))

  (defthm svstmtlist-compile-preserves-blkst-consp
    (b* (((mv ?ok ?warnings ?new-st)
          (svstmtlist-compile x st reclimit nb-delayp)))
      (implies (and ok (consp (svstate->blkst st)))
               (consp (svstate->blkst new-st))))
    :hints (("goal" :use ((:instance svstmtlist-compile-preserves-blkst-len))
             :in-theory (e/d (len) (svstmtlist-compile-preserves-blkst-len)))))



  (local (defthm svstacks-compatible-of-cdr-when-cons
           (implies (svstacks-compatible x (cons a b))
                    (svstacks-compatible (cdr x) b))
           :hints(("Goal" :in-theory (enable svstacks-compatible)))))

  (defthm-svstmt-compile-flag
    (defthm svstmt-compile-preserves-blkst-compatible
      (b* (((mv ?ok ?warnings ?new-st)
            (svstmt-compile x st reclimit nb-delayp)))
        (implies (and ok
                      (consp (svstate->blkst st)))
                 (svstacks-compatible (svstate->blkst new-st)
                                      (double-rewrite (svstate->blkst st)))))
      :flag svstmt-compile)
    (defthm svstmtlist-compile-preserves-blkst-compatible
      (b* (((mv ?ok ?warnings ?new-st)
            (svstmtlist-compile x st reclimit nb-delayp)))
        (implies (and ok
                      (consp (svstate->blkst st)))
                 (svstacks-compatible (svstate->blkst new-st)
                                      (double-rewrite (svstate->blkst st)))))
      :flag svstmtlist-compile))


   (local (defthm rewrite-not-quote
            (implies (and (bind-free '((env1 . env1)))
                          (equal (svex-kind val) :quote)
                          (not (equal (svex-eval x env1) (svex-quote->val val))))
                     (not (Equal (svex-maskfree-rewrite x) val)))
            :hints (("goal" :use ((:instance svex-maskfree-rewrite-correct
                                   (env env1)))
                     :in-theory (disable svex-maskfree-rewrite-correct)))))


  (local (defthm svex-fix-under-iff
           (svex-fix x)
           :hints (("goal" :use ((:theorem (svex-p (svex-fix x))))
                    :in-theory nil)
                   (and stable-under-simplificationp
                        '(:in-theory (enable))))))

  (local (defthm svex-env-boundp-of-svex-alist-eval
           (iff (svex-env-boundp k (svex-alist-eval x env))
                (svex-lookup k x))
           :hints(("Goal" :in-theory (enable svex-env-boundp
                                             svex-lookup
                                             svex-alist-fix
                                             svex-alist-eval)))))

  (local (defthm svex-env-lookup-of-append
           (Equal (svex-env-lookup k (append a b))
                  (if (svex-env-boundp k a)
                      (svex-env-lookup k a)
                    (svex-env-lookup k b)))
           :hints(("Goal" :in-theory (enable svex-env-lookup
                                             svex-env-boundp)))))

   (local (defthm svex-envs-similar-of-append-eval-fork
            (implies (svex-alist-p x)
                     (svex-envs-similar (append (svex-alist-eval (fast-alist-fork x nil) env) env1)
                                        (append (svex-alist-eval x env) env1)))
            :hints ((acl2::witness)
                    (and stable-under-simplificationp
                         '(:in-theory (enable svex-lookup))))))

  (deffixequiv-mutual svstmt-compile)

  
  (local (in-theory (enable svstate-fork svstate-clean)))

  (local (in-theory (disable member append acl2::subsetp-member
                             fast-alist-fork
                             acl2::consp-of-car-when-alistp
                             not)))


  (local (defthm svex-lookup-svstack-of-cdr
           (implies (not (svex-lookup v (svstack-to-svex-alist x)))
                    (not (svex-lookup v (svstack-to-svex-alist (cdr x)))))
           :hints(("Goal" :in-theory (enable svstack-to-svex-alist svex-lookup
                                             cdr-lookup-when-svex-alist-p)))))

  (local (defthm member-vars-svstack-of-cdr
           (implies (not (member v (svex-alist-vars (svstack-to-svex-alist x))))
                    (not (member v (svex-alist-vars (svstack-to-svex-alist (cdr x))))))
           :hints(("Goal" :in-theory (enable svstack-to-svex-alist)))))


  (defthm-svstmt-compile-flag
    (defthm vars-of-svstmt-compile-blkst
      (b* (((mv & & final-st) (svstmt-compile x st reclimit nb-delayp))
           (st (svstate->blkst st))
           (final-st (svstate->blkst final-st)))
        (implies (and (not (member v (svstmt-vars x)))
                      (svar-p v)
                      (consp st)
                      (not (svex-lookup v (svstack-to-svex-alist st))))
                 (and (not (svex-lookup v (svstack-to-svex-alist final-st)))
                      (implies (not (member v (svex-alist-vars (svstack-to-svex-alist st))))
                               (not (member v (svex-alist-vars (svstack-to-svex-alist final-st))))))))
      :hints ('(:expand (svstmt-vars x))
              (and stable-under-simplificationp
                   '(:expand ((:free (a b) (svstack-to-svex-alist (cons a b)))))))
      :flag svstmt-compile)
    (defthm vars-of-svstmtlist-compile-blkst
      (b* (((mv & & final-st) (svstmtlist-compile x st reclimit nb-delayp))
           (st (svstate->blkst st))
           (final-st (svstate->blkst final-st)))
        (implies (and (not (member v (svstmtlist-vars x)))
                      (svar-p v)
                      (consp st)
                      (not (svex-lookup v (svstack-to-svex-alist st))))
                 (and (not (svex-lookup v (svstack-to-svex-alist final-st)))
                      (implies (not (member v (svex-alist-vars (svstack-to-svex-alist st))))
                               (not (member v (svex-alist-vars (svstack-to-svex-alist final-st))))))))
      :hints ('(:expand (svstmtlist-vars x)))
      :flag svstmtlist-compile)
     :hints ((acl2::just-expand-mrec-default-hint
              'svstmt-compile id nil world)))

  (defthm-svstmt-compile-flag
    (defthm vars-of-svstmt-compile-nonblkst
      (b* (((mv & & final-st) (svstmt-compile x st reclimit nb-delayp))
           (nonblkst (svstate->nonblkst st))
           (st (svstate->blkst st))
           (final-st (svstate->nonblkst final-st)))
        (implies (and (not (eq nb-delayp t))
                      (not (member v (svstmt-vars x)))
                      (svar-p v)
                      (consp st)
                      (not (svex-lookup v nonblkst))
                      (not (svex-lookup v (svstack-to-svex-alist st))))
                 (and (not (svex-lookup v final-st))
                      (implies (and (not (member v (svex-alist-vars (svstack-to-svex-alist st))))
                                    (not (member v (svex-alist-vars nonblkst))))
                               (not (member v (svex-alist-vars final-st)))))))
      :hints ('(:expand (svstmt-vars x))
              (and stable-under-simplificationp
                   '(:expand ((:free (a b) (svstack-to-svex-alist (cons a b)))))))
      :flag svstmt-compile)
    (defthm vars-of-svstmtlist-compile-nonblkst
      (b* (((mv & & final-st) (svstmtlist-compile x st reclimit nb-delayp))
           (nonblkst (svstate->nonblkst st))
           (st (svstate->blkst st))
           (final-st (svstate->nonblkst final-st)))
        (implies (and (not (eq nb-delayp t))
                      (not (member v (svstmtlist-vars x)))
                      (svar-p v)
                      (consp st)
                      (not (svex-lookup v nonblkst))
                      (not (svex-lookup v (svstack-to-svex-alist st))))
                 (and (not (svex-lookup v final-st))
                      (implies (and (not (member v (svex-alist-vars (svstack-to-svex-alist st))))
                                    (not (member v (svex-alist-vars nonblkst))))
                               (not (member v (svex-alist-vars final-st)))))))
      :hints ('(:expand (svstmtlist-vars x)))
      :flag svstmtlist-compile)
     :hints ((acl2::just-expand-mrec-default-hint
              'svstmt-compile id nil world)))


  (defthm-svstmt-compile-flag
    (defthm vars-of-svstmt-compile-nonblkst-nbdelay
      (b* (((mv & & final-st) (svstmt-compile x st reclimit nb-delayp))
           (nonblkst (svstate->nonblkst st))
           (st (svstate->blkst st))
           (final-st (svstate->nonblkst final-st)))
        (implies (and (not (member v (svstmt-vars x)))
                      (not (member v (svarlist-add-delay (svstmt-vars x) 1)))
                      (svar-p v)
                      (consp st)
                      (not (svex-lookup v nonblkst))
                      (not (svex-lookup v (svstack-to-svex-alist st))))
                 (and (not (svex-lookup v final-st))
                      (implies (and (not (member v (svex-alist-vars (svstack-to-svex-alist st))))
                                    (not (member v (svex-alist-vars nonblkst)))
                                    (not (member v (svarlist-add-delay (svex-alist-vars (svstack-to-svex-alist st)) 1)))
                                    (not (member v (svarlist-add-delay (svex-alist-keys (svstack-to-svex-alist st)) 1))))
                               (not (member v (svex-alist-vars final-st)))))))
      :hints ('(:expand (svstmt-vars x))
              (and stable-under-simplificationp
                   '(:expand ((:free (a b) (svstack-to-svex-alist (cons a b)))))))
      :flag svstmt-compile)
    (defthm vars-of-svstmtlist-compile-nonblkst-nbdelay
      (b* (((mv & & final-st) (svstmtlist-compile x st reclimit nb-delayp))
           (nonblkst (svstate->nonblkst st))
           (st (svstate->blkst st))
           (final-st (svstate->nonblkst final-st)))
        (implies (and (not (member v (svstmtlist-vars x)))
                      (not (member v (svarlist-add-delay (svstmtlist-vars x) 1)))
                      (svar-p v)
                      (consp st)
                      (not (svex-lookup v nonblkst))
                      (not (svex-lookup v (svstack-to-svex-alist st))))
                 (and (not (svex-lookup v final-st))
                      (implies (and (not (member v (svex-alist-vars (svstack-to-svex-alist st))))
                                    (not (member v (svex-alist-vars nonblkst)))
                                    (not (member v (svarlist-add-delay (svex-alist-vars (svstack-to-svex-alist st)) 1)))
                                    (not (member v (svarlist-add-delay (svex-alist-keys (svstack-to-svex-alist st)) 1))))
                               (not (member v (svex-alist-vars final-st)))))))
      :hints ('(:expand (svstmtlist-vars x)))
      :flag svstmtlist-compile)
     :hints ((acl2::just-expand-mrec-default-hint
              'svstmt-compile id nil world)))
  )



(defines svstmt-write-masks
  :verify-guards nil
  (define svstmt-write-masks ((x svstmt-p)
                              (masks 4vmask-alist-p)
                              (nb-masks 4vmask-alist-p))
    :parents (svstmt-compile)
    :short "Static analysis to tell what parts of what variables may be written
            by a statement."
    :returns (mv (masks 4vmask-alist-p)
                 (nb-masks 4vmask-alist-p))
    :measure (svstmt-count x)
    (b* ((x           (svstmt-fix x))
         (masks       (4vmask-alist-fix masks))
         (nb-masks    (4vmask-alist-fix nb-masks)))
      (svstmt-case x
        :assign
        (b* (((mv mask-acc conf-acc) (lhs-check-masks x.lhs (if x.blockingp masks nb-masks) nil))
             (- (fast-alist-free conf-acc)))
          (if x.blockingp
              (mv mask-acc nb-masks)
            (mv masks mask-acc)))
        :if
        (b* (((mv masks nb-masks) (svstmtlist-write-masks x.then masks nb-masks)))
          (svstmtlist-write-masks x.else masks nb-masks))
        :while
        (svstmtlist-write-masks x.body masks nb-masks)
        :scope
        ;; BOZO overly conservative
        (svstmtlist-write-masks x.body masks nb-masks))))

  (define svstmtlist-write-masks ((x        svstmtlist-p)
                                  (masks    4vmask-alist-p)
                                  (nb-masks 4vmask-alist-p))
    :returns (mv (masks 4vmask-alist-p)
                 (nb-masks 4vmask-alist-p))
    :measure (svstmtlist-count x)
    (b* (((when (atom x))
          (mv (4vmask-alist-fix masks)
              (4vmask-alist-fix nb-masks)))
         ((mv masks nb-masks) (svstmt-write-masks (car x) masks nb-masks)))
      (svstmtlist-write-masks (cdr x) masks nb-masks)))
  ///
  (verify-guards svstmtlist-write-masks)

  (deffixequiv-mutual svstmt-write-masks))




#||

;; Examples:

(b* (((vl::wmv ok warnings st)
      (cwtime
       (svstmtlist-compile
        (list (svstmt-assign '(concat 32 i '(0 . -1)) 0)
              (svstmt-assign '(concat 1 found '(0 . -1)) 0)
              (svstmt-while '(bitand (bitnot (uor (zerox 1 found)))
                                     (uor (< (zerox 8 i) 3)))
                            (list (svstmt-assign '(concat 1 found '(0 . -1))
                                                 '(zerox 1 (rsh (b- 3 (zerox 8 i))
                                                                (zerox 3 data))))

                                  (svstmt-if '(zerox 1 found)
                                             (list (svstmt-assign '(concat 8 res '(0 . -1))
                                                                  '(zerox 8 i)))
                                             nil)
                                  (svstmt-assign '(concat 8 i '(0 . -1))
                                                 '(+ 1 (zerox 8 i))))))
        nil 64 nil 'foo)))
     ((unless ok) warnings)
     (st (hons-shrink-alist st nil))
     (st (svex-alist-rewrite-fixpoint st 20)))
  st)


(b* (((vl::wmv ok warnings st)
      (cwtime (svstmtlist-compile
               (list (svstmt-assign '(concat 32 i '(0 . -1)) 0)
                     (svstmt-assign '(concat 1 found '(0 . -1)) 0)
                     (svstmt-while '(bitand (bitnot (uor (zerox 1 found)))
                                            (uor (< (zerox 8 i) 128)))
                                   (list (svstmt-assign '(concat 1 found '(0 . -1))
                                                        '(zerox 1 (rsh (b- 128 (zerox 8 i))
                                                                       (zerox 128 data))))
                                         (svstmt-if '(zerox 1 found)
                                                    (list (svstmt-assign '(concat 8 res '(0 . -1))
                                                                         '(zerox 8 i)))
                                                    nil)
                                         (svstmt-assign '(concat 8 i '(0 . -1))
                                                        '(+ 1 (zerox 8 i))))))
               nil 200 nil 'foo)))
     ((unless ok) warnings)
     (st (hons-shrink-alist st nil))
     (st (svex-alist-rewrite-fixpoint st 20))
     (env '((data . #x4004000040030f00)))
     ((with-fast env)))
  (4vec-zero-ext 8 (svex-eval (cdr (hons-assoc-equal 'res st)) env)))

||#
