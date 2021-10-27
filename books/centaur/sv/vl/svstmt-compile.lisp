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
;; (include-book "../svex/compose")
(include-book "../svex/constraints")
(include-book "../svex/env-ops")
(include-book "../svex/rewrite")
(include-book "../svex/select")
(include-book "centaur/vl/util/warnings" :dir :System)
(local (include-book "centaur/vl/util/default-hints" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
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

;; bozo -- prove svarlist-p-of-mergesort
(local (fty::deflist svarlist :elt-type svar :true-listp t :elementp-of-nil nil))


(defthm svex-lookup-in-fast-alist-fork
  (implies (and (svex-alist-p x)
                (svex-alist-p y))
           (iff (svex-lookup v (fast-alist-fork x y))
                (or (svex-lookup v x)
                    (svex-lookup v y))))
  :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix
                                    cdr-lookup-when-svex-alist-p))))


(fty::deflist svstack :elt-type svex-alist-p)

(defthm svex-fix-nonnil
  (svex-fix x)
  :hints(("Goal" :use (RETURN-TYPE-OF-SVEX-FIX.NEW-X)
          :in-theory (disable RETURN-TYPE-OF-SVEX-FIX.NEW-X)))
  :rule-classes :type-prescription)

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

  (defthm svex-vars-of-svstack-to-svex-alist-cons
    (set-equiv (svex-alist-vars (svstack-to-svex-alist (cons a b)))
               (append (svex-alist-vars a)
                       (svex-alist-vars (svstack-to-svex-alist b))))
    :hints(("Goal" :in-theory (enable svex-alist-vars))))

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

(define svstack-globalp ((k svar-p) (stack svstack-p))
  :guard (consp stack)
  (if (atom (cdr stack))
      t
    (and (not (svex-fastlookup k (car stack)))
         (svstack-globalp k (cdr stack)))))

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

  (local (defthm consp-of-svex-alist-fix-by-lookup
           (implies (and (hons-assoc-equal v x)
                         (svar-p v))
                    (consp (svex-alist-fix x)))
           :hints(("Goal" :in-theory (enable svex-alist-fix)))))

  (defthm svex-lookup-of-svstack-clean
    (iff (svex-lookup v (svstack-to-svex-alist (svstack-clean x)))
         (svex-lookup v (svstack-to-svex-alist x)))
    :hints(("Goal" :in-theory (enable svstack-to-svex-alist
                                      svex-lookup))))

  (defret consp-of-svstack-clean
    (equal (consp new-x)
           (consp x))))

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


(define svstack-nonempty-fix ((x svstack-p))
  :returns (new-x svstack-p)
  (b* ((x (svstack-fix x)))
    (if (atom x)
        (list nil)
      x))
  ///
  (defret consp-of-svstack-nonempty-fix
    (consp new-x))

  (defret svstack-nonempty-fix-when-consp
    (implies (consp x)
             (equal (svstack-nonempty-fix x) (svstack-fix x)))))


(defprod svstate
  :parents (svstmt-compile)
  :short "Structure containing currently assigned variable values for blocking
          and nonblocking assignments."
  :layout :tree
  ((blkst    svstack-p "State of blocking-assigned variables" :default '(nil)
             :reqfix (svstack-nonempty-fix blkst))
   (nonblkst svex-alist-p "State of nonblocking-assigned variables"))
  :require (consp blkst))



(define svstate-vars ((st svstate-p))
  :returns (vars (and (svarlist-p vars)
                      (setp vars)))
  (b* (((svstate st))
       (blkst-alist (svstack-to-svex-alist st.blkst)))
    (union (union (svex-alist-vars blkst-alist)
                  (mergesort (svex-alist-keys blkst-alist)))
           (union (svex-alist-vars st.nonblkst)
                  (mergesort (svex-alist-keys st.nonblkst)))))
  ///
  (defret vars-of-accessors-of-svstate-vars
    (implies (not (member v vars))
             (b* (((svstate st))
                  (blkst-alist (svstack-to-svex-alist st.blkst)))
               (and (not (member v (svex-alist-vars blkst-alist)))
                    (not (member v (svex-alist-keys blkst-alist)))
                    (not (member v (svex-alist-vars st.nonblkst)))
                    (not (member v (svex-alist-keys st.nonblkst)))))))

  (defret svar-lookup-of-accessors-of-svstate-vars
    (implies (not (member (svar-fix v) vars))
             (b* (((svstate st))
                  (blkst-alist (svstack-to-svex-alist st.blkst)))
               (and (not (svex-lookup v blkst-alist))
                    (not (svex-lookup v st.nonblkst)))))))


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
  ;; (defthm vars-of-svstate-clean-blkst
  ;;   (implies (not (member v (svex-alist-vars (svstack-to-svex-alist (svstate->blkst x)))))
  ;;            (not (member v (svex-alist-vars (svstack-to-svex-alist (svstate->blkst (svstate-clean x))))))))
  ;; (defthm vars-of-svstate-clean-nonblkst
  ;;   (implies (not (member v (svex-alist-vars (svstate->nonblkst x))))
  ;;            (not (member v (svex-alist-vars (svstate->nonblkst (svstate-clean x)))))))
  ;; (defthm keys-of-svstate-clean-blkst
  ;;   (iff (svex-lookup v (svstack-to-svex-alist (svstate->blkst (svstate-clean x))))
  ;;        (svex-lookup v (svstack-to-svex-alist (svstate->blkst x))))
  ;;   :hints((and stable-under-simplificationp
  ;;               '(:in-theory (enable svex-lookup)))))
  ;; (defthm keys-of-svstate-clean-nonblkst
  ;;   (iff (svex-lookup v (svstate->nonblkst (svstate-clean x)))
  ;;        (svex-lookup v (svstate->nonblkst x)))
  ;;   :hints((and stable-under-simplificationp
  ;;               '(:in-theory (enable svex-lookup)))))

  (defret vars-of-svstate-clean
    (implies (not (member v (svstate-vars x)))
             (not (member v (svstate-vars new-x))))
    :hints(("Goal" :in-theory (enable svstate-vars))))

  (defretd nonblkst-of-svstate-clean
    (equal (svstate->nonblkst new-x)
           (fast-alist-clean (svstate->nonblkst x)))))

(define svstate-fork ((x svstate-p))
  :returns (new-x svstate-p)
  (b* (((svstate x)))
    (change-svstate x :blkst (svstack-fork x.blkst)
                    :nonblkst (fast-alist-fork x.nonblkst nil)))
  ///

  (defret svstate-fork-blkst-len
    (equal (len (svstate->blkst new-x))
           (len (svstate->blkst x))))

  (defret vars-of-svstate-fork
    (implies (not (member v (svstate-vars x)))
             (not (member v (svstate-vars new-x))))
    :hints(("Goal" :in-theory (enable svstate-vars)))))

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
  :short "Predicate that describes two svstacks that are in the same scope, but
          may have different values for the bound variables."
  :long "<p>When we arrive at an IF, we create two versions of the state, one
for the THEN and one for the ELSE. When we are done symbolically simulating
both, we merge the two states.  These two resulting states are back in the
outer scope (the scopes for the then and else branches have been popped off)
and they may have different values assigned to variables at some scopes, but
the only place they may differ in which variables are bound is at the
outermost (global) scope.  This is because inside the inner block, there is no
way to declare a variable for an outer scope other than the global one.</p>

<p>Symbolically simulating an assignment statement preserves svstack
compatibility because it will only create a variable at the global scope; a
local scope can get a modified value of the variable, but only if it already
exists there.</p>"
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

(define svstates-compatible ((x svstate-p)
                             (y svstate-p))
  (svstacks-compatible (svstate->blkst x)
                       (svstate->blkst y))
  ///
  (defequiv svstates-compatible)
  (defcong svstates-compatible svstacks-compatible (svstate->blkst x) 1)
  (defcong svstacks-compatible svstates-compatible (svstate blkst nonblkst) 1
    :hints(("Goal" :in-theory (enable svstack-nonempty-fix
                                      svstacks-compatible))))

  (defthm svstate-normalize-nonblkst-under-svstates-compatible
    (implies (syntaxp (not (and (equal nonblkst ''nil))))
             (svstates-compatible (svstate blkst nonblkst)
                                  (svstate blkst nil))))

  (defthm svstate-reconstruct-under-svstates-compatible
    (svstates-compatible (svstate (svstate->blkst st) nonblkst)
                         st))

  (defthm svstates-compatible-blkst-of-svstate-fork
    (svstates-compatible (svstate-fork x) (double-rewrite x))
    :hints(("Goal" :in-theory (enable svstate-fork)))))

(defprod svjumpstate
  ((constraints constraintlist-p "Constraints collected")
   (breakcond svex-p "Condition under which we have hit an unmerged break")
   (breakst svstate-p "Current symbolic execution state, assuming we've hit a break")
   (continuecond svex-p "Condition under which we have hit a continue")
   (continuest svstate-p "Current symbolic execution state, assuming we've hit a continue")
   (returncond svex-p "Condition under which we have hit a return")
   (returnst svstate-p "Current symbolic execution state, assuming we've hit a return")))


(define svjumpstate-vars ((x svjumpstate-p))
  :returns (vars (and (svarlist-p vars)
                      (setp vars)))
  :prepwork ((local (in-theory (disable acl2::true-listp-append))))
  (b* (((svjumpstate x)))
    (union (union (svex-vars x.breakcond)
                  (svstate-vars x.breakst))
           (union (union (svex-vars x.continuecond)
                         (svstate-vars x.continuest))
                  (union (svex-vars x.returncond)
                         (union (svstate-vars x.returnst)
                                (mergesort (constraintlist-vars x.constraints)))))))
  ///
  (defthm svjumpstate-vars-of-svjumpstate
    (equal (svjumpstate-vars (svjumpstate constraints breakcond breakst continuecond continuest returncond returnst))
           (union (union (svex-vars breakcond)
                         (svstate-vars breakst))
                  (union (union (svex-vars continuecond)
                                (svstate-vars continuest))
                         (union (svex-vars returncond)
                                (union (svstate-vars returnst)
                                       (mergesort (constraintlist-vars constraints))))))))
  (defret vars-of-accessors-of-svjumpstate-vars
    (implies (not (member v vars))
             (b* (((svjumpstate x)))
               (and (not (member v (svex-vars x.breakcond)))
                    (not (member v (svstate-vars x.breakst)))
                    (not (member v (svex-vars x.continuecond)))
                    (not (member v (svstate-vars x.continuest)))
                    (not (member v (svex-vars x.returncond)))
                    (not (member v (svstate-vars x.returnst)))
                    (not (member v (constraintlist-vars x.constraints))))))))

(define make-empty-svjumpstate ((st svstate-p)
                                &key ((constraints constraintlist-p) 'nil))
  :returns (jst svjumpstate-p)
  ;; Note: We don't bother to fork st into these places.  We aren't going to
  ;; use these for lookups except when merging, at which point we'll ensure
  ;; that the component alists are fast.
  (make-svjumpstate :constraints constraints
                    :breakcond 0
                    :breakst st
                    :continuecond 0
                    :continuest st
                    :returncond 0
                    :returnst st)
  ///
  (defret vars-of-make-empty-svjumpstate
    (implies (and (not (member v (svstate-vars st)))
                  (not (member v (constraintlist-vars constraints))))
             (not (member v (svjumpstate-vars jst))))
    :hints(("Goal" :in-theory (enable svjumpstate-vars))))

  (defret accs-of-make-empty-svjumpstate
    (b* (((svjumpstate jst)))
      (and (equal jst.constraints (constraintlist-fix constraints))
           (equal jst.breakcond 0)
           (equal jst.breakst (svstate-fix st))
           (equal jst.continuecond 0)
           (equal jst.continuest (svstate-fix st))
           (equal jst.returncond 0)
           (equal jst.returnst (svstate-fix st))))))
  




(define svjumpstate-levels ((x svjumpstate-p))
  :returns (levels posp :rule-classes :type-prescription)
  :prepwork ((local (defthm len-when-consp
                      (implies (consp x)
                               (not (equal (len x) 0))))))
  (b* (((svjumpstate x))
       ((svstate x.breakst))
       ((svstate x.continuest))
       ((svstate x.returnst)))
    (min (len x.breakst.blkst)
         (min (len x.continuest.blkst)
              (len x.returnst.blkst))))
  ///
  )

(define svjumpstates-compatible ((x svjumpstate-p)
                                    (y svjumpstate-p))
  (b* (((svjumpstate x))
       ((svjumpstate y)))
    (and (svstates-compatible x.breakst y.breakst)
         (svstates-compatible x.continuest y.continuest)
         (svstates-compatible x.returnst y.returnst)))
  ///
  (defequiv svjumpstates-compatible)
  (defcong svjumpstates-compatible svstates-compatible (svjumpstate->breakst x) 1)
  (defcong svstates-compatible svjumpstates-compatible (svjumpstate constraints breakcond breakst
                                                                    continuecond continuest
                                                                    returncond returnst)
    2)
  (defcong svjumpstates-compatible svstates-compatible (svjumpstate->continuest x) 1)
  (defcong svstates-compatible svjumpstates-compatible (svjumpstate constraints breakcond breakst
                                                                    continuecond continuest
                                                                    returncond returnst)
    4)
  (defcong svjumpstates-compatible svstates-compatible (svjumpstate->returnst x) 1)
  (defcong svstates-compatible svjumpstates-compatible (svjumpstate constraints breakcond breakst
                                                                    continuecond continuest
                                                                    returncond returnst)
    6))

(define svjumpstate-svstate-compatible ((jst svjumpstate-p)
                                        (st svstate-p))
  (b* (((svjumpstate jst)))
    (and (svstates-compatible jst.breakst st)
         (svstates-compatible jst.continuest st)
         (svstates-compatible jst.returnst st)))
  ///
  (defcong svjumpstates-compatible equal (svjumpstate-svstate-compatible jst st) 1)
  (defcong svstates-compatible equal (svjumpstate-svstate-compatible jst st) 2)

  (defthm svjumpstate-svstate-compatible-of-make-empty
    (svjumpstate-svstate-compatible (make-empty-svjumpstate st) st)
    :hints(("Goal" :in-theory (enable make-empty-svjumpstate))))

  (local (defthm svstates-compatible-commutative-rw
           (equal (equal (svstates-compatible a b)
                         (svstates-compatible b a))
                  t)
           :hints (("goal" :cases ((svstates-compatible a b))))))

  (defthm svjumpstates-compatible-rewrite-to-svjumpstate-svstate-compatible
    (implies (svjumpstate-svstate-compatible jst1 st)
             (equal (svjumpstates-compatible jst1 jst2)
                    (svjumpstate-svstate-compatible jst2 st)))
    :hints(("Goal" :in-theory (enable svjumpstates-compatible))))

  (defthm svjumpstates-compatible-rewrite-to-svjumpstate-svstate-compatible-1
    (implies (svjumpstate-svstate-compatible jst2 st)
             (equal (svjumpstates-compatible jst1 jst2)
                    (svjumpstate-svstate-compatible jst1 st)))
    :hints(("Goal" :in-theory (enable svjumpstates-compatible))))

  (defthm svjumpstate-svstate-compatible-implies-rewrite-accs
    (implies (svjumpstate-svstate-compatible jst st)
             (And (svstates-compatible (svjumpstate->breakst jst) st)
                  (svstates-compatible (svjumpstate->continuest jst) st)
                  (svstates-compatible (svjumpstate->returnst jst) st))))

  (defthm svjumpstates-compatible-of-svjumpstate
    (implies (and (svjumpstate-svstate-compatible jst breakst)
                  (svjumpstate-svstate-compatible jst continuest)
                  (svjumpstate-svstate-compatible jst returnst))
             (and (equal (svjumpstates-compatible
                          (svjumpstate constraints breakcond breakst continuecond continuest returncond returnst)
                          jst)
                         t)
                  (equal (svjumpstates-compatible
                          jst
                          (svjumpstate constraints breakcond breakst continuecond continuest returncond returnst))
                         t)))
    :hints(("Goal" :in-theory (enable svjumpstates-compatible))))

  (defthm svjumpstates-compatible-of-change
    (svjumpstates-compatible (change-svjumpstate jst
                                                 :constraints constraints
                                                 :breakcond breakcond
                                                 :continuecond continuecond
                                                 :returncond returncond)
                             (double-rewrite jst))
    :hints(("Goal" :in-theory (enable svjumpstates-compatible))))


  (defthm svjumpstates-compatible-of-make-empty-svjumpstate
    (and (equal (svjumpstates-compatible (make-empty-svjumpstate st) jst)
                (svjumpstate-svstate-compatible jst (double-rewrite st)))
         (equal (svjumpstates-compatible jst (make-empty-svjumpstate st))
                (svjumpstate-svstate-compatible jst (double-rewrite st))))
    :hints(("Goal" :in-theory (enable svjumpstates-compatible
                                      make-empty-svjumpstate))))

  (defthm svjumpstates-svstate-compatible-of-svjumpstate
    (equal (svjumpstate-svstate-compatible
            (svjumpstate constraints breakcond breakst continuecond continuest returncond returnst)
            st)
           (and (svstates-compatible st breakst)
                (svstates-compatible st continuest)
                (svstates-compatible st returnst)))
    :hints(("Goal" :in-theory (enable svjumpstates-compatible))))

  (defthm svjumpstate-svstate-compatible-of-make-empty-svjumpstate
    (equal (svjumpstate-svstate-compatible (make-empty-svjumpstate st1) st2)
           (svstates-compatible (double-rewrite st1) st2))
    :hints(("Goal" :in-theory (enable make-empty-svjumpstate)))))

(define svjumpstate-free ((x svjumpstate-p))
  :returns (new-x (equal new-x (svjumpstate-fix x)))
  (b* (((svjumpstate x) (svjumpstate-fix x)))
    (svstate-free x.breakst)
    (svstate-free x.continuest)
    (svstate-free x.returnst)
    x))

(define svjumpstate-fork ((x svjumpstate-p))
  :returns (new-x svjumpstate-p)
  (b* (((svjumpstate x) x))
    (change-svjumpstate x
                           :breakst (svstate-fork x.breakst)
                           :continuest (svstate-fork x.continuest)
                           :returnst (svstate-fork x.returnst)))
  ///
  (defret svjumpstate-fork-preserves-compatible
    (svjumpstates-compatible new-x (double-rewrite x))
    :hints(("Goal" :in-theory (enable svjumpstates-compatible)))))





;; (define svex-resolve-single-assignment ((dynselect svex-p  "potentially a dynamic select
;;                                                       expression, in terms of
;;                                                       prefixvar")
;;                                         (rhs svex-p  "RHS of assignment")
;;                                         (prefixvar svar-p "variable standing in for static-prefix")
;;                                         (static-prefix svex-p
;;                                                          "the static prefix of the DYNSELECT"))
;;   ;; This function tries to take assignments such as
;;   ;;   my_arr[idx] = foo
;;   ;; and transform them into
;;   ;;   my_arr = { my_arr[max_idx:idx+1], foo, my_arr[idx-1:0] }.
;;   ;; In actuality, the VL expression->svex transform turns dynamic indices
;;   ;; into mostly partselects; e.g., if we have
;;   ;;    logic [15:0] e;
;;   ;;    logic [3:0] a;
;;   ;; then e[a] becomes
;;   ;;    (part-select a 1 e)

;;   ;; Historically (before part-select and part-install were added) these were
;;   ;; instead expressed as a horrendous mess like this:
;;   ;; (CONCAT 1
;;   ;;         (? (< (* 1 (CONCAT 4 "a" 0)) 0)
;;   ;;            (CONCAT (U- (* 1 (CONCAT 4 "a" 0)))
;;   ;;                    '(-1 . 0)
;;   ;;                    (CONCAT 16 "e" '(-1 . 0)))
;;   ;;            (RSH (* 1 (CONCAT 4 "a" 0))
;;   ;;                 (CONCAT 16 "e" '(-1 . 0))))
;;   ;;         '(0 . -1))
;;   ;; This is because we had to check the case where a is below the lowest
;;   ;; index of e -- in this case that's impossible, but in general it could be.

;;   ;; So we would recursively descend through that mess until we get to the
;;   ;; occurrences of e, transforming things as follows (where here capital Z
;;   ;; signifies X or Z, i.e. '(0 . -1) or '(-1 . 0)):

;;   ;; (concat w a Z) = rhs --> a = (concat w rhs (rsh w a))
;;   ;; (concat w Z b) = rhs --> b = (rsh w rhs)
;;   ;; (zerox w a) = rhs --> a = (concat w rhs (rsh w a))
;;   ;; (signx w a) = rhs --> a = (concat w rhs (rsh w a))
;;   ;; (rsh w v) = rhs --> v = (concat w v rhs)

;;   ;; (? test then else) = rhs
;;   ;; is more complicated.  Resolve
;;   ;; then = rhs -->  var = then-val
;;   ;; else = rhs -->  var = else-val
;;   ;; and if both are successful, then result is
;;   ;; var = (? test then-val else-val).

;;   :measure (svex-count dynselect)
;;   :returns (mv (err (iff (vl::vl-msg-p err) err))
;;                (final-rhs (implies (not err) (svex-p final-rhs))))
;;   :verify-guards nil
;;   (b* (((when (svex-case dynselect :var (svar-equiv prefixvar dynselect.name) :otherwise nil))
;;         (mv nil (svex-fix rhs)))
;;        ((mv ok al) (svex-unify '(partsel lsb w a) dynselect nil))
;;        ((when ok)
;;         (b* ((lsb (svex-lookup 'lsb al))
;;              (w (svex-lookup 'w al))
;;              (a (svex-lookup 'a al))
;;              (lsb-rhs (svex-replace-var lsb prefixvar static-prefix))
;;              (w-rhs (svex-replace-var w prefixvar static-prefix))
;;              (a-rhs (svex-replace-var a prefixvar static-prefix)))
;;           (svex-resolve-single-assignment
;;            a (svcall partinst lsb-rhs w-rhs a-rhs rhs) prefixvar static-prefix)))
;;        ((mv ok al) (svex-unify '(concat w a b)
;;                                dynselect nil))
;;        ((when ok)
;;         (b* ((w (svex-lookup 'w al))
;;              (a (svex-lookup 'a al))
;;              (b (svex-lookup 'b al))
;;              (w-rhs (svex-replace-var w prefixvar static-prefix))
;;              ((when (svex-case b :quote))
;;               ;; (concat w a Z) = rhs --> a = (concat w rhs (rsh w a))
;;               (b* ((a-rhs (svex-replace-var a prefixvar static-prefix)))
;;                 (svex-resolve-single-assignment
;;                  a
;;                  (svcall concat w-rhs rhs (svcall rsh w-rhs a-rhs))
;;                  prefixvar static-prefix)))
;;              ((when (svex-case a :quote))
;;               ;; (concat w Z b) = rhs --> b = (rsh w rhs)
;;               (svex-resolve-single-assignment
;;                b (svcall rsh w-rhs rhs) prefixvar static-prefix)))
;;           (mv (vl::vmsg "Unexpected form of svex assignment LHS: ~x0" (svex-fix dynselect))
;;               nil)))
;;        ((mv ok al) (svex-unify '(zerox w a) dynselect nil))
;;        ((mv ok al) (if ok
;;                        (mv ok al)
;;                      (svex-unify '(signx w a) dynselect nil)))
;;        ((when ok) ;; zerox or signx matched
;;         (b* ((w (svex-lookup 'w al))
;;              (a (svex-lookup 'a al))
;;              (a-rhs (svex-replace-var a prefixvar static-prefix))
;;              (w-rhs (svex-replace-var w prefixvar static-prefix)))
;;           ;; (zerox/signx w a) = rhs --> a = (concat w rhs (rsh w a))
;;           (svex-resolve-single-assignment
;;            a (svcall concat w-rhs rhs (svcall rsh w-rhs a-rhs))
;;            prefixvar static-prefix)))

;;        ((mv ok al) (svex-unify '(rsh w v) dynselect nil))
;;        ((when ok)
;;         (b* ((w (svex-lookup 'w al))
;;              (v (svex-lookup 'v al))
;;              (w-rhs (svex-replace-var w prefixvar static-prefix))
;;              (v-rhs (svex-replace-var v prefixvar static-prefix)))
;;           ;; (rsh w v) = rhs --> v = (concat w v rhs)
;;           (svex-resolve-single-assignment
;;            v (svcall concat w-rhs v-rhs rhs)
;;            prefixvar static-prefix)))
;;        ((mv ok al) (svex-unify '(? test then else) dynselect nil))
;;        ((when ok)
;;         (b* ((test (svex-lookup 'test al))
;;              (then (svex-lookup 'then al))
;;              (else (svex-lookup 'else al))
;;              ;; (? test then else) = rhs
;;              ;; is more complicated.  Resolve
;;              ;; then = rhs -->  var = then-val
;;              ;; else = rhs -->  var = else-val
;;              ;; and if both are successful, then result is
;;              ;; var = (? test then-val else-val).
;;              ((mv err then-val) (svex-resolve-single-assignment then rhs prefixvar static-prefix))
;;              ((when err) (mv err nil))
;;              ((mv err else-val) (svex-resolve-single-assignment else rhs prefixvar static-prefix))
;;              ((when err) (mv err nil)))
;;           (mv nil (svcall ? (svex-replace-var test prefixvar static-prefix)
;;                           then-val else-val)))))
;;     (mv (vl::vmsg "Unexpected form of svex assignment LHS: ~x0 (variable: ~x1)"
;;                   (svex-fix dynselect) (svar-fix prefixvar))
;;         nil))
;;   ///
;;   (local (defthm member-vars-of-svex-unify
;;            (b* (((mv ?ok al1) (svex-unify pat x al)))
;;              (implies (and (not (member v (svex-vars x)))
;;                            (not (member v (svex-alist-vars al))))
;;                       (not (member v (svex-alist-vars al1)))))
;;            :hints (("goal" :use svex-unify-subst-no-new-vars
;;                     :in-theory (disable svex-unify-subst-no-new-vars)))))

;;   (std::defret vars-of-svex-resolve-single-assignment-1
;;     (implies (and ;; (not (equal v (svar-fix prefixvar)))
;;                   (not (member v (svex-vars dynselect)))
;;                   (not (member v (svex-vars rhs)))
;;                   (not (member v (svex-vars static-prefix)))
;;                   (not err))
;;              (not (member v (svex-vars final-rhs))))
;;     :hints(("Goal" :in-theory (enable vars-of-svex-compose-strong
;;                                       svex-alist-vars))))

;;   (local (defthm svex-fix-under-iff
;;            (iff (svex-fix x) t)
;;            :hints (("goal" :use ((:instance return-type-of-svex-fix.new-x))
;;                     :in-theory (disable return-type-of-svex-fix.new-x)))))

;;   (local (defthm svex-vars-of-hons-assoc-equal
;;            (implies (and (not (member v (svex-alist-vars x)))
;;                          (hons-assoc-equal k x))
;;                     (not (member v (svex-vars (cdr (hons-assoc-equal k x))))))
;;            :hints(("Goal" :in-theory (enable svex-alist-vars
;;                                              hons-assoc-equal)))))

;;   (std::defret vars-of-svex-resolve-single-assignment-2
;;     (implies (and (case-split (equal v (svar-fix prefixvar)))
;;                   (not (member v (svex-vars rhs)))
;;                   (not (member v (svex-vars static-prefix)))
;;                   (not err))
;;              (not (member v (svex-vars final-rhs))))
;;     :hints(("Goal" :in-theory (enable vars-of-svex-compose-strong
;;                                       svex-alist-vars
;;                                       sv::svex-lookup))))
;;   (verify-guards svex-resolve-single-assignment))






#||
(trace$ (svstmt-assign->subst
         :entry (list 'svstmt-assign->subst
                      :lhs lhs
                      :rhs (car (svexlist-rewrite-fixpoint (list rhs)))
                      :offset offset
                      :blockingp blockingp)
         :exit (b* ((st value))
                 (list 'svstmt-assign->subst
                       :blkst (clean-svstack (svstate->blkst st))
                       :nonblkst (svex-alist-rewrite-fixpoint (fast-alist-free (fast-alist-fork (svstate->nonblkst st) nil)))))))
        

||#

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

  (defthm vars-of-svstmt-assign->subst
    (implies (and (not (member v (svstate-vars st)))
                  (not (member v (lhs-vars lhs)))
                  (not (member v (svex-vars rhs))))
             (not (member v (svstate-vars (svstmt-assign->subst lhs rhs offset blockingp st)))))
    :hints(("Goal" :in-theory (e/d (svstate-vars)
                                   (svstmt-assign->subst)))))

  (defret consp-blkst-of-svstmt-assign->subst
    (implies (consp (svstate->blkst st))
             (consp (svstate->blkst new-st))))

  (defret len-blkst-of-svstmt-assign->subst
    (<= (len (svstate->blkst st))
        (len (svstate->blkst new-st)))
    :rule-classes :linear)

  (defret svstates-compatible-of-svstmt-assign->subst
    (implies (consp (svstate->blkst st))
             (svstates-compatible new-st st))))



;; Procedure for performing an assignment.
;; We have an RHS expression (any svex), an LHS static and dynamic select
;; (svex-selects), and a state (bindings for variables).

;; Compose the state into the RHS and all LHS select indices -- in
;; particular, not the variable that the selects are selecting from (which in
;; the dynamic part is *svex-longest-static-prefix-var*, but in the static
;; part might be any variable).

;; Simplify the indices so that as many of them are constant as possible.

;; Some of the select operations may now be static which were previously
;; dynamic.  Rework the two LHS parts, moving inner expressions from dynamic
;; to static.

;; Crunch the static part into a lhs, and get the writemask from it.

;; Crunch the dynamic part with the RHS to produce the final expression to be
;; assigned to the static select.

(define svstmt-process-write ((write svstmt-write-p)
                              (blockingp)
                              (nb-delayp)
                              (xcond)
                              (st svstate-p))
  :returns (mv (new-st svstate-p)
               (lhs lhs-p))
  (b* (((svstmt-write write))
       ((svstate st))
       (svstack (if blockingp
                    st.blkst
                  (cons st.nonblkst st.blkst)))
       (lhs-indices (if xcond
                        (4veclist-quote (svexlist-xeval (svex-select->indices write.lhs)))
                      (svexlist-maskfree-rewrite
                       (svexlist-compose-svstack (svex-select->indices write.lhs) svstack))))
       (rhs (svex-compose-svstack write.rhs svstack))
       (rhs (if (and (eq nb-delayp t)
                     (not blockingp))
                (svex-add-delay rhs 1)
              rhs))
       ;; BOZO this is very coarse-grained but simple and easy and will work
       ;; for the cases I currently care about.
       (rhs (if xcond
                (svex-x)
              rhs))
       (lhs-select (svex-select-replace-indices write.lhs lhs-indices))
       (lhs-var (svex-select-inner-var write.lhs))
       (var-value (or (svstack-lookup lhs-var svstack) (svex-var lhs-var)))
       ((mv static-lhs-select static-rhs) (svex-select-staticify-assignment lhs-select rhs var-value))
       (lhs (svex-select-to-lhs static-lhs-select))
       (st (svstmt-assign->subst lhs static-rhs 0 blockingp st)))
    (mv st lhs))
  ///
  (defret svstates-compatible-of-svstmt-process-write
    (implies (consp (svstate->blkst st))
             (svstates-compatible new-st st)))


  (local (in-theory (disable member-equal
                             ;; MEMBER-OF-SVARLIST-ADD-DELAY
                             acl2::member-of-append
                             acl2::member-equal-append
                             svarlist-addr-p-when-subsetp-equal)))

  (defret svarlist-addr-p-of-svstmt-process-write
    (implies (and (svarlist-addr-p (svstmt-write-vars write))
                  (svarlist-addr-p (svstate-vars st))
                  ;; (svarlist-addr-p (svex-vars xcond))
                  )
             (Svarlist-addr-p (svstate-vars new-st)))
    :hints(("Goal" :in-theory (enable svstmt-write-vars
                                      svstate-vars)))))


(define svstmt-process-writelist ((x svstmt-writelist-p)
                                  (blockingp)
                                  (nb-delayp)
                                  (xcond)
                                  (st svstate-p))
  :returns (mv (new-st svstate-p)
               (all-lhs lhs-p "Concatenation of the static LHSes of all of the writes."))
  (b* (((when (atom x)) (mv (svstate-fix st) nil))
       ((mv st lhs1) (svstmt-process-write (car x) blockingp nb-delayp xcond st))
       ((mv st lhs2) (svstmt-process-writelist (cdr x) blockingp nb-delayp xcond st)))
    (mv st (append-without-guard lhs1 lhs2)))
  ///
  (defret svstates-compatible-of-svstmt-process-writelist
    (implies (consp (svstate->blkst st))
             (svstates-compatible new-st st)))

  (defret svarlist-addr-p-of-svstmt-process-writelist
    (implies (and (svarlist-addr-p (svstmt-writelist-vars x))
                  (svarlist-addr-p (svstate-vars st))
                  ;; (svarlist-addr-p (svex-vars xcond))
                  )
             (svarlist-addr-p (svstate-vars new-st)))
    :hints(("Goal" :in-theory (enable svstmt-writelist-vars)))))



(define svex-svstmt-ite ((test svex-p)
                         (then svex-p)
                         (else svex-p))
  :returns (ite svex-p)
  (b* ((test (svex-fix test))
       (then (svex-fix then))
       (else (svex-fix else)))
    (or (svex-case test
          :quote (if (eql (4vec-reduction-or test.val) -1)
                     then
                   (if (eql (4vec-reduction-or test.val) 0)
                       else
                     nil))
          :otherwise nil)
        (and (hons-equal then else) then)
        (svex-call '?* (list test then else))))
  ///
  (local (defthm svex-fix-under-iff
           (iff (svex-fix x) t)
           :hints (("Goal" :use RETURN-TYPE-OF-SVEX-FIX.NEW-X
                    :in-theory (disable RETURN-TYPE-OF-SVEX-FIX.NEW-X)))))

  (local (defthm 4vec-?*-when-reduction-or-true
           (implies (equal (4vec-reduction-or test) -1)
                    (equal (4vec-?* test then else)
                           (4vec-fix then)))
           :hints(("Goal" :in-theory (enable 4vec-reduction-or 3vec-reduction-or
                                             4vec-?* 3vec-?* 3vec-fix)))))

  (local (defthm 4vec-?*-when-reduction-or-false
           (implies (equal (4vec-reduction-or test) 0)
                    (equal (4vec-?* test then else)
                           (4vec-fix else)))
           :hints(("Goal" :in-theory (enable 4vec-reduction-or 3vec-reduction-or
                                             4vec-?* 3vec-?* 3vec-fix)))))

  (local (defthm 4vec-?*-when-equal
           (implies (4vec-equiv then else)
                    (equal (4vec-?* test then else)
                           (4vec-fix then)))
           :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?* 3vec-fix)))))
           


  (defret svex-svstmt-ite-correct
    (equal (svex-eval ite env)
           (4vec-?* (svex-eval test env)
                    (svex-eval then env)
                    (svex-eval else env)))
    :hints(("Goal" :in-theory (enable ;; 4vec-?* 3vec-?* 4vec-reduction-or 3vec-reduction-or
                                      ;; 3vec-fix
                                      svex-apply svexlist-eval)))
    :otf-flg t)


  (defret vars-of-svex-svstmt-ite
    (implies (And (not (member v (svex-vars test)))
                  (not (member v (svex-vars then)))
                  (not (member v (svex-vars else))))
             (not (member v (svex-vars ite)))))

  (defret svex-svstmt-ite-under-iff
    (iff ite t))

  (local (defthm svex-fix-under-iff
           (iff (svex-fix x) t)
           :hints (("goal" :use RETURN-TYPE-OF-SVEX-FIX.NEW-X
                    :in-theory (disable RETURN-TYPE-OF-SVEX-FIX.NEW-X)))))

  (defret svex-svstmt-ite-when-cond-true
    (implies (equal (4vec-reduction-or (svex-eval test env)) -1)
             (equal (svex-eval ite env)
                    (svex-eval then env)))
    :hints(("Goal" :in-theory (enable svex-apply))
           (and stable-under-simplificationp
                '(:in-theory (enable 4vec-?* 3vec-?* 4vec-reduction-or 3vec-reduction-or)))))

  (defret svex-svstmt-ite-when-cond-false
    (implies (equal (4vec-reduction-or (svex-eval test env)) 0)
             (equal (svex-eval ite env)
                    (svex-eval else env)))
    :hints(("Goal" :in-theory (enable svex-apply))
           (and stable-under-simplificationp
                '(:in-theory (enable 4vec-?* 3vec-?* 4vec-reduction-or 3vec-reduction-or))))))


; Matt K. addition: Avoid ACL2(p) failure due to logbitp-reasoning.
(local (include-book "std/system/non-parallel-book" :dir :system))
(local (acl2::non-parallel-book))

(define svex-svstmt-or ((a svex-p)
                        (b svex-p))
  :returns (or svex-p)
  (b* ((a (svex-fix a))
       (b (svex-fix b))
       ((when (svex-case a :quote (2vec-p a.val) :otherwise nil))
        (b* ((a (2vec->val (svex-quote->val a))))
          (if (eql a 0) b -1)))
       ((when (svex-case b :quote (2vec-p b.val) :otherwise nil))
        (b* ((b (2vec->val (svex-quote->val b))))
          (if (eql b 0) a -1))))
    (svex-call 'bitor (list (svex-call 'uor (list a))
                            (svex-call 'uor (list b)))))
  ///
  
  (local (defthm reduction-or-of-or-when-not-second
           (implies (and (equal (4vec->upper y) 0)
                         (equal (4vec->lower y) 0))
                    (equal (4vec-reduction-or (4vec-bitor x y))
                           (4vec-reduction-or x)))
           :hints(("Goal" :in-theory (enable 4vec-reduction-or
                                             3vec-reduction-or
                                             4vec-bitor
                                             3vec-bitor
                                             3vec-fix)))))

  (local (defthm reduction-or-of-or-when-not-first
           (implies (and (equal (4vec->upper x) 0)
                         (equal (4vec->lower x) 0))
                    (equal (4vec-reduction-or (4vec-bitor x y))
                           (4vec-reduction-or y)))
           :hints(("Goal" :in-theory (enable 4vec-reduction-or
                                             3vec-reduction-or
                                             4vec-bitor
                                             3vec-bitor
                                             3vec-fix)))))

  (local (defthm reduction-or-of-or-when-first
           (implies (and (equal (4vec->upper x) (4vec->lower x))
                         (not (equal (4vec->lower x) 0)))
                    (equal (4vec-reduction-or (4vec-bitor x y))
                           -1))
           :hints(("Goal" :in-theory (enable 4vec-reduction-or
                                             3vec-reduction-or
                                             4vec-bitor
                                             3vec-bitor
                                             3vec-fix))
                  (logbitp-reasoning))))

  (local (defthm reduction-or-of-or-when-second
           (implies (and (equal (4vec->upper y) (4vec->lower y))
                         (not (equal (4vec->lower y) 0)))
                    (equal (4vec-reduction-or (4vec-bitor x y))
                           -1))
           :hints(("Goal" :in-theory (enable 4vec-reduction-or
                                             3vec-reduction-or
                                             4vec-bitor
                                             3vec-bitor
                                             3vec-fix))
                  (logbitp-reasoning))))

  (local (defthm reduction-or-idempotent
           (equal (4vec-reduction-or (4vec-reduction-or x))
                  (4vec-reduction-or x))
           :hints(("Goal" :in-theory (enable 4vec-reduction-or
                                             3vec-reduction-or
                                             3vec-fix)))))

  (local (defthm bitor-of-reduction-or
           (equal (4vec-bitor (4vec-reduction-or x) (4vec-reduction-or y))
                  (4vec-reduction-or (4vec-bitor x y)))
           :hints(("Goal" :in-theory (enable 4vec-reduction-or
                                             3vec-reduction-or
                                             4vec-bitor
                                             3vec-bitor
                                             3vec-fix))
                  (logbitp-reasoning))))

  (defret svex-svstmt-or-correct
    (equal (4vec-reduction-or (svex-eval or env))
           (4vec-reduction-or
            (4vec-bitor (svex-eval a env)
                        (svex-eval b env))))
    :hints(("Goal" :in-theory (enable ;; 4vec-bitor 3vec-bitor 3vec-fix
                                      ;; 4vec-reduction-or 3vec-reduction-or
                                      svex-apply svexlist-eval))))

  (defret vars-of-svex-svstmt-or
    (implies (And (not (member v (svex-vars a)))
                  (not (member v (svex-vars b))))
             (not (member v (svex-vars or))))))

(define svex-svstmt-andc1 ((a svex-p)
                           (b svex-p))
  :returns (or svex-p)
  (b* ((a (svex-fix a))
       (b (svex-fix b))
       ((when (svex-case a :quote (2vec-p a.val) :otherwise nil))
        (b* ((a (2vec->val (svex-quote->val a))))
          (if (eql a 0) b 0)))
       ((when (svex-case b :quote (2vec-p b.val) :otherwise nil))
        (b* ((b (2vec->val (svex-quote->val b))))
          (if (eql b 0) 0 (svex-call 'bitnot (list (svex-call 'uor (list a))))))))
    (svex-call 'bitand (list (svex-call 'bitnot (list (svex-call 'uor (list a))))
                             (svex-call 'uor (list b)))))
  ///
  (defret vars-of-svex-svstmt-andc1
    (implies (And (not (member v (svex-vars a)))
                  (not (member v (svex-vars b))))
             (not (member v (svex-vars or))))))


(define constraintlist-add-pathcond ((cond svex-p)
                                     (negatedp)
                                     (constraints constraintlist-p))
  ;; negatedp is confusing (of course): this function produces:
  ;; (if not negatedp) constraints assumed if cond is true
  ;; (if negatedp) constraints assumed if cond is false
  :returns (new-constraints constraintlist-p)
  (if (atom constraints)
      nil
    (cons (change-constraint (car constraints)
                             :cond (svcall bitor
                                           (if negatedp
                                               cond
                                             (svcall bitnot (svcall uor cond)))
                                           (constraint->cond (car constraints))))
          (constraintlist-add-pathcond cond negatedp (cdr constraints))))
  ///
  (defret vars-of-constraintlist-add-pathcond
    (implies (and (not (member v (constraintlist-vars constraints)))
                  (not (member v (svex-vars cond))))
             (not (member v (constraintlist-vars new-constraints))))
    :hints(("Goal" :in-theory (enable constraintlist-vars)))))

(defthm constraintlist-vars-of-append
  (equal (constraintlist-vars (append a b))
         (append (constraintlist-vars a)
                 (constraintlist-vars b)))
  :hints(("Goal" :in-theory (enable constraintlist-vars))))

(define constraintlist-merge-branches ((cond svex-p)
                                       (then-constraints constraintlist-p)
                                       (else-constraints constraintlist-p))
  :returns (new-constraints constraintlist-p)
  (append (constraintlist-add-pathcond cond nil then-constraints)
          (constraintlist-add-pathcond cond t else-constraints))
  ///
  (defret vars-of-constraintlist-merge-branches
    (implies (and (not (member v (constraintlist-vars then-constraints)))
                  (not (member v (constraintlist-vars else-constraints)))
                  (not (member v (svex-vars cond))))
             (not (member v (constraintlist-vars new-constraints))))))
  

(define svex-alist-merge-branches ((key-alist svex-alist-p)
                                   (cond svex-p)
                                   (then-st svex-alist-p)
                                   (else-st svex-alist-p)
                                   (st-acc  svex-alist-p))
  ;; No longer makes a fast alist.
  :returns (merged-st svex-alist-p)
  :verbosep t
  ;; :prepwork ((local (in-theory (enable svex-alist-fix))))
  (b* (((when (atom key-alist))
        (svex-alist-fix st-acc))
       ((unless (mbt (and (consp (car key-alist))
                          (svar-p (caar key-alist)))))
        (svex-alist-merge-branches (cdr key-alist) cond then-st else-st st-acc))
       (key (caar key-alist))
       ((when (svex-fastlookup key st-acc))
        (svex-alist-merge-branches (cdr key-alist) cond then-st else-st st-acc))
       (then-val (or (svex-fastlookup key then-st)
                     (make-svex-var :name key)))
       (else-val (or (svex-fastlookup key else-st)
                     (make-svex-var :name key)))
       (val (svex-svstmt-ite cond then-val else-val))
       (st-acc  (hons-acons key val st-acc)))
    (svex-alist-merge-branches (cdr key-alist) cond then-st else-st st-acc))
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



  (local (defthm 4vec-?*-when-reduction-or-true
           (implies (equal (4vec-reduction-or test) -1)
                    (equal (4vec-?* test then else)
                           (4vec-fix then)))
           :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?*
                                             4vec-reduction-or
                                             3vec-reduction-or)))))

  (local (defthm 4vec-?*-when-reduction-or-false
           (implies (equal (4vec-reduction-or test) 0)
                    (equal (4vec-?* test then else)
                           (4vec-fix else)))
           :hints(("Goal" :in-theory (enable 4vec-?* 3vec-?*
                                             4vec-reduction-or
                                             3vec-reduction-or)))))

  (local (in-theory (disable hons-assoc-equal-of-svex-alist-fix)))

  (defthm svex-alist-merge-branches-lookup-under-iff
    (iff (svex-lookup k (svex-alist-merge-branches key-alist cond then-st else-st st-acc))
         (or (svex-lookup k st-acc)
             (svex-lookup k key-alist)))
    :hints(("Goal" :in-theory (e/d (svex-lookup)
                                   ((:d svex-alist-merge-branches)))
            :induct (svex-alist-merge-branches key-alist
                                               cond
                                               then-st
                                               else-st
                                               st-acc)
            :expand ((svex-alist-merge-branches key-alist cond then-st else-st st-acc)
                     (svex-alist-fix key-alist)
                     ;; (hons-assoc-equal (svar-fix k) (svex-alist-fix key-alist))
                     )
            :do-not-induct t)))

  (defthm svex-alist-merge-branches-when-cond-true-lookup
    (implies (equal (4vec-reduction-or (svex-eval cond env)) -1)
             (equal (svex-eval (svex-lookup k (svex-alist-merge-branches key-alist
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
                                   ((:d svex-alist-merge-branches)))
            :induct (svex-alist-merge-branches key-alist
                                               cond
                                               then-st
                                               else-st
                                               st-acc)
            :expand ((svex-alist-merge-branches key-alist cond then-st else-st st-acc)
                     (svex-alist-fix key-alist)))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-apply)))))

  (defthm svex-alist-merge-branches-when-cond-false-lookup
    (implies (equal (4vec-reduction-or (svex-eval cond env)) 0)
             (equal (svex-eval (svex-lookup k (svex-alist-merge-branches key-alist
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
                                   ((:d svex-alist-merge-branches)))
            :induct (svex-alist-merge-branches key-alist
                                               cond
                                               then-st
                                               else-st
                                               st-acc)
            :expand ((svex-alist-merge-branches key-alist cond then-st else-st st-acc)
                     (svex-alist-fix key-alist))
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

  (defthm keys-of-svex-alist-merge-branches
    (implies (and (not (member v (svex-alist-keys then-st)))
                  (not (member v (svex-alist-keys else-st)))
                  (not (member v (svex-alist-keys st-acc)))
                  (not (member v (svex-alist-keys key-alist))))
             (not (member v (svex-alist-keys
                             (svex-alist-merge-branches
                              key-alist cond then-st else-st st-acc)))))
    :hints(("Goal" :in-theory (enable svex-alist-keys)
            :induct (svex-alist-merge-branches
                     key-alist cond then-st else-st st-acc)
            :do-not-induct t)))

  (defthm svex-lookup-of-svex-alist-merge-branches
    (implies (and (not (member v (svex-alist-keys then-st)))
                  (not (member v (svex-alist-keys else-st)))
                  (not (member v (svex-alist-keys st-acc)))
                  (not (member v (svex-alist-keys key-alist)))
                  (svar-p v))
             (not (svex-lookup v (svex-alist-merge-branches
                                  key-alist cond then-st else-st st-acc))))
    :hints(("Goal" :in-theory (enable svex-alist-keys)
            :induct (svex-alist-merge-branches
                     key-alist cond then-st else-st st-acc)
            :do-not-induct t)))

  (local (defthm caar-when-not-lookup
           (implies (and (not (svex-lookup v alist))
                         (consp (svex-alist-fix alist)))
                    (not (equal v (caar (svex-alist-fix alist)))))
           :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix)))))

  (defthm vars-of-svex-alist-merge-branches
    (implies (and (not (member v (svex-vars cond)))
                  (not (member v (svex-alist-vars then-st)))
                  (not (member v (svex-alist-vars else-st)))
                  (not (member v (svex-alist-vars st-acc)))
                  (not (member v (svex-alist-keys key-alist))))
             (not (member v (svex-alist-vars
                             (svex-alist-merge-branches
                              key-alist cond then-st else-st st-acc)))))
    :hints(("Goal" :in-theory (enable svex-alist-vars
                                      svex-alist-keys)
            :induct (svex-alist-merge-branches
                     key-alist cond then-st else-st st-acc)
            :do-not-induct t)))

  (Deffixequiv svex-alist-merge-branches :args (key-alist)
    :hints (("goal" :in-theory (e/d (svex-lookup)
                                   ((:d svex-alist-merge-branches)))
            :induct (svex-alist-merge-branches key-alist
                                               cond
                                               then-st
                                               else-st
                                               st-acc)
            :expand ((svex-alist-merge-branches key-alist cond then-st else-st st-acc)
                     (svex-alist-merge-branches nil cond then-st else-st st-acc)
                     (:free (a b) (svex-alist-merge-branches (cons a b) cond then-st else-st st-acc))
                     (svex-alist-fix key-alist)))))
  ) ;; for fixequiv hook


(define svstack-merge-branches ((cond svex-p)
                                           (then-st svstack-p)
                                           (else-st svstack-p))
  :measure (max (len then-st) (len else-st))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svstacks-compatible))))
  :returns (merged-st svstack-p)
  :verbosep t
  (b* (((when (or (atom then-st) (atom else-st)))
        nil)
       (then-alist (car then-st))
       (else-alist (car else-st))
       (first
        (b* (((with-fast then-alist else-alist))
             (first nil)
             (first (svex-alist-merge-branches then-alist cond then-alist else-alist first))
             (first (svex-alist-merge-branches else-alist cond then-alist else-alist first)))
          first)))
    (cons first (svstack-merge-branches cond (cdr then-st) (cdr else-st))))
  ///


  (defthm svstack-merge-branches-lookup-under-iff
    (implies (double-rewrite (svstacks-compatible then-st else-st))
             (iff (svex-lookup k (svstack-to-svex-alist
                                  (svstack-merge-branches cond then-st else-st)))
                  (or (svex-lookup k (svstack-to-svex-alist then-st))
                      (svex-lookup k (svstack-to-svex-alist else-st)))))
    :hints (("goal" :induct (svstack-merge-branches cond then-st else-st))
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

  (defthm svstack-merge-branches-when-cond-true-lookup
    (implies (and (equal (4vec-reduction-or (svex-eval cond env)) -1)
                  (svstacks-compatible then-st else-st))
             (equal (svex-eval (svex-lookup k (svstack-to-svex-alist
                                               (svstack-merge-branches
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
            :induct (svstack-merge-branches cond then-st else-st))
           (and stable-under-simplificationp
                '(:expand ((svstacks-compatible then-st else-st))))
           ))

  (defthm svstack-merge-branches-when-cond-false-lookup
    (implies (and (equal (4vec-reduction-or (svex-eval cond env)) 0)
                  (svstacks-compatible then-st else-st))
             (equal (svex-eval (svex-lookup k (svstack-to-svex-alist
                                               (svstack-merge-branches
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
            :induct (svstack-merge-branches cond then-st else-st))
           (and stable-under-simplificationp
                '(:expand ((svstacks-compatible then-st else-st))))
           ))

  (defthm keys-of-svstack-merge-branches
    (implies (and (not (member v (svex-alist-keys (svstack-to-svex-alist then-st))))
                  (not (member v (svex-alist-keys (svstack-to-svex-alist else-st)))))
             (not (member v (svex-alist-keys
                             (svstack-to-svex-alist (svstack-merge-branches
                                                      cond then-st else-st))))))
    :hints(("Goal" :in-theory (enable svex-alist-keys)
            :induct (svstack-merge-branches cond then-st else-st)
            :do-not-induct t)))

  (defthm svex-lookup-of-svstack-merge-branches
    (implies (and (not (member v (svex-alist-keys (svstack-to-svex-alist then-st))))
                  (not (member v (svex-alist-keys (svstack-to-svex-alist else-st))))
                  (svar-p v))
             (not (svex-lookup v
                               (svstack-to-svex-alist
                                (svstack-merge-branches
                                 cond then-st else-st)))))
    :hints(("Goal" :in-theory (enable svex-alist-keys)
            :induct (svstack-merge-branches cond then-st else-st)
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

  (defthm vars-of-svstack-merge-branches
    (implies (and (not (member v (svex-vars cond)))
                  (not (member v (svex-alist-vars (svstack-to-svex-alist then-st))))
                  (not (member v (svex-alist-vars (svstack-to-svex-alist else-st))))
                  (not (member v (svex-alist-keys (svstack-to-svex-alist then-st))))
                  (not (member v (svex-alist-keys (svstack-to-svex-alist else-st))))
                  (double-rewrite (svstacks-compatible then-st else-st)))
             (not (member v (svex-alist-vars
                             (svstack-to-svex-alist
                              (svstack-merge-branches
                                cond then-st else-st))))))
    :hints(("Goal" :in-theory (enable svex-alist-vars
                                      svex-alist-keys)
            :induct (svstack-merge-branches cond then-st else-st)
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:in-theory (e/d (svstack-to-svex-alist)
                                  (svex-lookup-when-set-equiv
                                   member-svex-alist-keys))
                  :expand ((svstacks-compatible then-st else-st))
                  :use ((:instance member-svex-alist-keys (k v) (x (car then-st)))
                        (:instance member-svex-alist-keys (k v) (x (car else-st))))))))

  (defret svstack-merge-branches-compatible
    (implies (double-rewrite (svstacks-compatible then-st else-st))
             (svstacks-compatible merged-st (double-rewrite then-st)))
    :hints(("Goal" :in-theory (enable svstacks-compatible))
           (acl2::set-reasoning)))

  (defret svstack-merge-branches-consp
    (implies (and (consp then-st)
                  (consp else-st))
             (consp merged-st)))
  
  (defret svstack-merge-branches-len
    (Equal (len merged-st) (min (len then-st) (len else-st)))))



(define svstate-merge-branches ((cond svex-p)
                                (then-st svstate-p)
                                (else-st svstate-p))
  :returns (merged-st svstate-p)
  (b* (((svstate then-st) (svstate-fix then-st))
       ((svstate else-st) (svstate-fix else-st))
       ((when (hons-equal then-st else-st)) then-st)
       (blkst (svstack-merge-branches cond then-st.blkst else-st.blkst))
       (nonblkst nil)
       (nonblkst (svex-alist-merge-branches then-st.nonblkst cond then-st.nonblkst else-st.nonblkst nonblkst))
       (nonblkst (svex-alist-merge-branches else-st.nonblkst cond then-st.nonblkst else-st.nonblkst nonblkst)))
    (svstate-free then-st)
    (svstate-free else-st)
    (make-svstate :blkst blkst :nonblkst nonblkst))
  ///
  (defthm svstate-merge-branches-lookup-blkst-when-false
    (implies (and (equal (4vec-reduction-or (svex-eval cond env)) 0)
                  (svstacks-compatible (svstate->blkst then-st)
                                       (svstate->blkst else-st)))
             (equal
              (svex-eval (svex-lookup k (svstack-to-svex-alist (svstate->blkst (svstate-merge-branches cond then-st else-st)))) env)
              (if (svex-lookup k (svstack-to-svex-alist (svstate->blkst else-st)))
                  (svex-eval (svex-lookup k (svstack-to-svex-alist (svstate->blkst else-st))) env)
                (if (svex-lookup k (svstack-to-svex-alist (svstate->blkst then-st)))
                    (svex-env-lookup k env)
                  (4vec-x))))))

  (defthm svstate-merge-branches-lookup-nonblkst-when-false
    (implies (equal (4vec-reduction-or (svex-eval cond env)) 0)
             (equal
              (svex-eval (svex-lookup k (svstate->nonblkst (svstate-merge-branches cond then-st else-st))) env)
              (if (svex-lookup k (svstate->nonblkst else-st))
                  (svex-eval (svex-lookup k (svstate->nonblkst else-st)) env)
                (if (svex-lookup k (svstate->nonblkst then-st))
                    (svex-env-lookup k env)
                  (4vec-x))))))

  (defthm svstate-merge-branches-lookup-blkst-under-iff
    (implies (double-rewrite (svstacks-compatible (svstate->blkst then-st)
                                                  (svstate->blkst else-st)))
             (iff (svex-lookup k (svstack-to-svex-alist (svstate->blkst (svstate-merge-branches cond then-st else-st))))
                  (or (svex-lookup k (svstack-to-svex-alist (svstate->blkst then-st)))
                      (svex-lookup k (svstack-to-svex-alist (svstate->blkst else-st)))))))

  (defthm svstate-merge-branches-lookup-nonblkst-under-iff
    (iff (svex-lookup k (svstate->nonblkst (svstate-merge-branches cond then-st else-st)))
         (or (svex-lookup k (svstate->nonblkst then-st))
             (svex-lookup k (svstate->nonblkst else-st)))))

  (defthm svstate-merge-branches-lookup-blkst-when-true
    (implies (and (svstacks-compatible (svstate->blkst then-st)
                                       (svstate->blkst else-st))
                  (equal (4vec-reduction-or (svex-eval cond env)) -1))
             (equal
              (svex-eval (svex-lookup k (svstack-to-svex-alist (svstate->blkst (svstate-merge-branches cond then-st else-st)))) env)
              (if (svex-lookup k (svstack-to-svex-alist (svstate->blkst then-st)))
                  (svex-eval (svex-lookup k (svstack-to-svex-alist (svstate->blkst then-st))) env)
                (if (svex-lookup k (svstack-to-svex-alist (svstate->blkst else-st)))
                    (svex-env-lookup k env)
                  (4vec-x))))))

  (defthm svstate-merge-branches-lookup-nonblkst-when-true
    (implies (equal (4vec-reduction-or (svex-eval cond env)) -1)
             (equal
              (svex-eval (svex-lookup k (svstate->nonblkst (svstate-merge-branches cond then-st else-st))) env)
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

  (defthm svstate-merge-branches-blkst-when-true
    (implies (and (equal (4vec-reduction-or (svex-eval cond env)) -1)
                  (svstacks-compatible (svstate->blkst then-st)
                                       (svstate->blkst else-st)))
             (svex-envs-similar
              (append (svex-alist-eval (svstack-to-svex-alist (svstate->blkst (svstate-merge-branches cond then-st else-st))) env) env)
              (append (svex-alist-eval (svstack-to-svex-alist (svstate->blkst then-st)) env) env)))
    :hints(("Goal" :in-theory (disable svstate-merge-branches))
           (acl2::witness)))

  (defthm svstate-merge-branches-nonblkst-when-true
    (implies (equal (4vec-reduction-or (svex-eval cond env)) -1)
             (svex-envs-similar
              (append (svex-alist-eval (svstate->nonblkst (svstate-merge-branches cond then-st else-st)) env) env)
              (append (svex-alist-eval (svstate->nonblkst then-st) env) env)))
    :hints(("Goal" :in-theory (disable svstate-merge-branches))
           (acl2::witness)))

  (defthm svstate-merge-branches-blkst-when-false
    (implies (and (equal (4vec-reduction-or (svex-eval cond env)) 0)
                  (svstacks-compatible (svstate->blkst then-st)
                                       (svstate->blkst else-st)))
             (svex-envs-similar
              (append (svex-alist-eval (svstack-to-svex-alist (svstate->blkst (svstate-merge-branches cond then-st else-st))) env) env)
              (append (svex-alist-eval (svstack-to-svex-alist (svstate->blkst else-st)) env) env)))
    :hints(("Goal" :in-theory (disable svstate-merge-branches))
           (acl2::witness)))

  (defthm svstate-merge-branches-nonblkst-when-false
    (implies (equal (4vec-reduction-or (svex-eval cond env)) 0)
             (svex-envs-similar
              (append (svex-alist-eval (svstate->nonblkst (svstate-merge-branches cond then-st else-st)) env) env)
              (append (svex-alist-eval (svstate->nonblkst else-st) env) env)))
    :hints(("Goal" :in-theory (disable svstate-merge-branches))
           (acl2::witness)))

  ;; (defthm keys-of-svstate-merge-branches-blkst
  ;;   (implies (and (not (member v (svex-alist-keys (svstack-to-svex-alist (svstate->blkst then-st)))))
  ;;                 (not (member v (svex-alist-keys (svstack-to-svex-alist (svstate->blkst else-st))))))
  ;;            (not (member v (svex-alist-keys
  ;;                            (svstack-to-svex-alist
  ;;                             (svstate->blkst (svstate-merge-branches cond then-st else-st)))))))
  ;;   :hints(("Goal" :in-theory (disable member-svex-alist-keys))))

  ;; (defthm svex-lookup-of-svstate-merge-branches-blkst
  ;;   (implies (and (not (member v (svex-alist-keys (svstack-to-svex-alist (svstate->blkst then-st)))))
  ;;                 (not (member v (svex-alist-keys (svstack-to-svex-alist (svstate->blkst else-st)))))
  ;;                 (svar-p v))
  ;;            (not (svex-lookup v (svstack-to-svex-alist
  ;;                                 (svstate->blkst
  ;;                                  (svstate-merge-branches cond then-st else-st))))))
  ;;   :hints(("Goal" :in-theory (disable member-svex-alist-keys))))

  ;; (defthm vars-of-svstate-merge-branches-blkst
  ;;   (implies (and (not (member v (svex-vars cond)))
  ;;                 (not (member v (svex-alist-vars (svstack-to-svex-alist (svstate->blkst then-st)))))
  ;;                 (not (member v (svex-alist-vars (svstack-to-svex-alist (svstate->blkst else-st)))))
  ;;                 (not (member v (svex-alist-keys (svstack-to-svex-alist (svstate->blkst then-st)))))
  ;;                 (not (member v (svex-alist-keys (svstack-to-svex-alist (svstate->blkst else-st)))))
  ;;                 (double-rewrite (svstacks-compatible (svstate->blkst then-st)
  ;;                                                      (svstate->blkst else-st))))
  ;;            (not (member v (svex-alist-vars
  ;;                            (svstack-to-svex-alist
  ;;                             (svstate->blkst
  ;;                              (svstate-merge-branches cond then-st else-st))))))))

  ;; (defthm keys-of-svstate-merge-branches-nonblkst
  ;;   (implies (and (not (member v (svex-alist-keys (svstate->nonblkst then-st))))
  ;;                 (not (member v (svex-alist-keys (svstate->nonblkst else-st)))))
  ;;            (not (member v (svex-alist-keys
  ;;                            (svstate->nonblkst (svstate-merge-branches cond then-st else-st)))))))

  ;; (defthm vars-of-svstate-merge-branches-nonblkst
  ;;   (implies (and (not (member v (svex-vars cond)))
  ;;                 (not (member v (svex-alist-vars (svstate->nonblkst then-st))))
  ;;                 (not (member v (svex-alist-vars (svstate->nonblkst else-st))))
  ;;                 (not (member v (svex-alist-keys (svstate->nonblkst then-st))))
  ;;                 (not (member v (svex-alist-keys (svstate->nonblkst else-st)))))
  ;;            (not (member v (svex-alist-vars
  ;;                            (svstate->nonblkst
  ;;                             (svstate-merge-branches cond then-st else-st)))))))

  (defret vars-of-svstate-merge-branches
    (implies (and (double-rewrite (svstates-compatible then-st else-st))
                  (not (member v (svex-vars cond)))
                  (not (member v (svstate-vars then-st)))
                  (not (member v (svstate-vars else-st))))
             (not (member v (svstate-vars merged-st))))
    :hints(("Goal" :in-theory (enable svstate-vars svstates-compatible))))

  (defret svstate-merge-branches-blkst-compatible
    (implies (double-rewrite (svstates-compatible then-st else-st))
             (svstates-compatible merged-st (double-rewrite then-st)))
    :hints(("Goal" :in-theory (enable svstates-compatible))))

  (defret svstate-merge-branches-preserves-blkst-consp
    (implies (and (consp (svstate->blkst then-st))
                  (consp (svstate->blkst else-st)))
             (consp (svstate->blkst merged-st))))

  (defret svstate-merge-branches-blkst-len
    (Equal (len (svstate->blkst merged-st))
           (min (len (svstate->blkst then-st))
                (len (svstate->blkst else-st))))))


(define svjumpstate-merge-svstate-branches ((cond svex-p)
                                            (thencond svex-p)
                                            (elsecond svex-p)
                                            (thenst svstate-p)
                                            (elsest svstate-p))
  ;; For the (common) special case when one or both of the existing jump
  ;; conditions is syntactically 0, we don't want to do the work of a merge,
  ;; because that means the corresponding jumpstate is actually just
  ;; irrelevant.
  :returns (merged-st svstate-p)
  (b* ((thencond (svex-fix thencond))
       (elsecond (svex-fix elsecond))
       (thenst (svstate-fix thenst))
       (elsest (svstate-fix elsest))
       ((when (eql 0 elsecond)) thenst)
       ((when (eql 0 thencond)) elsest))
    (svstate-merge-branches cond thenst elsest))
  ///
  (defret vars-of-svjumpstate-merge-svstate-branches
    (implies (and (svstates-compatible thenst elsest)
                  (not (member v (svex-vars cond)))
                  (not (member v (svstate-vars thenst)))
                  (not (member v (svstate-vars elsest))))
             (not (member v (svstate-vars merged-st)))))

  (defret svjumpstate-merge-svstate-branches-preserves-compatible
    (implies (svstates-compatible thenst elsest)
             (svstates-compatible merged-st thenst))))

(define svjumpstate-merge-branches ((cond svex-p)
                                    (then svjumpstate-p)
                                    (else svjumpstate-p))
  :returns (ite svjumpstate-p)
  :prepwork ((local (in-theory (disable acl2::true-listp-append
                                        acl2::subsetp-member
                                        (:t append) append
                                        acl2::consp-of-append))))
  (b* (((svjumpstate then))
       ((svjumpstate else)))
    (make-svjumpstate
     :constraints (constraintlist-merge-branches cond then.constraints else.constraints)
     :breakcond (svex-svstmt-ite cond then.breakcond else.breakcond)
     :breakst (svjumpstate-merge-svstate-branches cond then.breakcond else.breakcond then.breakst else.breakst)
     :continuecond (svex-svstmt-ite cond then.continuecond else.continuecond)
     :continuest (svjumpstate-merge-svstate-branches cond then.continuecond else.continuecond then.continuest else.continuest)
     :returncond (svex-svstmt-ite cond then.returncond else.returncond)
     :returnst (svjumpstate-merge-svstate-branches cond then.returncond else.returncond then.returnst else.returnst)))
  ///
  (defret vars-of-svjumpstate-merge-branches
    (implies (and (double-rewrite (svjumpstates-compatible then else))
                  (not (member v (svex-vars cond)))
                  (not (member v (svjumpstate-vars then)))
                  (not (member v (svjumpstate-vars else))))
             (not (member v (svjumpstate-vars ite))))
    :hints(("Goal" :in-theory (enable svjumpstate-vars
                                      svjumpstates-compatible))))

  (defret svjumpstate-merge-branches-preserves-compatible
    (implies (double-rewrite (svjumpstates-compatible then else))
             (svjumpstates-compatible ite (double-rewrite then)))
    :hints(("Goal" :in-theory (enable svjumpstates-compatible)))))


(define svjumpstate-sequence-svstates ((cond1 svex-p)
                                       (cond2 svex-p)
                                       (st1 svstate-p)
                                       (st2 svstate-p))
  :returns (seq svstate-p)
  (b* ((cond1 (svex-fix cond1))
       (cond2 (svex-fix cond2))
       (st1 (svstate-fix st1))
       (st2 (svstate-fix st2))
       ((when (eql 0 cond1)) st2)
       ((when (eql 0 cond2)) st1))
    (svstate-merge-branches cond1 st1 st2))
  ///
  (defret vars-of-svjumpstate-sequence-svstates
    (implies (and (not (member v (svstate-vars st1)))
                  (not (member v (svstate-vars st2)))
                  (not (member v (svex-vars cond1)))
                  (svstates-compatible st1 st2))
             (not (member v (svstate-vars seq)))))

  (defret svstates-compatible-of-svjumpstate-sequence-svstates
    (implies (svstates-compatible st1 st2)
             (svstates-compatible seq st1))))

(define svjumpstate-sequence ((jst1 svjumpstate-p)
                              (jst2 svjumpstate-p))
  ;; If we are running:
  ;;    stmt1; stmt2
  ;; and stmt1 produces jst1, stmt2 produces jst2, produce the jumpstate that
  ;; correctly reflects the sequence.  That is, for each jump cond/state,
  ;;
  ;; newcond = stmt1.jumpcond | ("statement 1 didn't do ANY jump" & stmt2.jumpcond)
  ;; newst   = stmt1.jumpcond ? stmt1.jumpst : stmt2.jumpst
  ;;
  ;; Note that the continuecond, breakcond, and returncond are all kept
  ;; mutually exclusive: we should never create a jumpst where there is any
  ;; overlap between them. (Except that we really aren't defending against
  ;; tests becoming X/Z and if that happens then who knows what we do.)

  :returns (seq svjumpstate-p)
  (b* (((svjumpstate jst1))
       ((svjumpstate jst2))
       (jst1.anyjump (svex-svstmt-or jst1.breakcond (svex-svstmt-or jst1.continuecond
                                                                    jst1.returncond))))
    (make-svjumpstate
     :constraints (append-without-guard jst1.constraints jst2.constraints)
     :breakcond (svex-svstmt-or jst1.breakcond
                                (svex-svstmt-andc1 jst1.anyjump jst2.breakcond))
     :breakst (svjumpstate-sequence-svstates jst1.breakcond jst2.breakcond
                                             jst1.breakst jst2.breakst)
     :continuecond (svex-svstmt-or jst1.continuecond
                                (svex-svstmt-andc1 jst1.anyjump jst2.continuecond))
     :continuest (svjumpstate-sequence-svstates jst1.continuecond jst2.continuecond
                                                jst1.continuest jst2.continuest)
     :returncond (svex-svstmt-or jst1.returncond
                                (svex-svstmt-andc1 jst1.anyjump jst2.returncond))
     :returnst (svjumpstate-sequence-svstates jst1.returncond jst2.returncond
                                              jst1.returnst jst2.returnst)))
  ///
  (defret vars-of-svjumpstate-sequence
    (implies (and (not (member v (svjumpstate-vars jst1)))
                  (not (member v (svjumpstate-vars jst2)))
                  (double-rewrite (svjumpstates-compatible jst1 jst2)))
             (not (member v (svjumpstate-vars seq))))
    :hints(("Goal" :in-theory (enable svjumpstate-vars
                                      svjumpstates-compatible))))

  (defret svjumpstates-compatible-of-svjumpstate-sequence
    (implies (double-rewrite (svjumpstates-compatible jst1 jst2))
             (svjumpstates-compatible seq (double-rewrite jst1)))
    :hints(("Goal" :in-theory (enable svjumpstates-compatible))))

  (defret svstates-compatible-of-svjumpstate-sequence
    (implies (double-rewrite (svjumpstates-compatible jst1 jst2))
             (b* (((svjumpstate seq))
                  ((svjumpstate jst1) (double-rewrite jst1)))
               (and (svstates-compatible seq.breakst jst1.breakst)
                    (svstates-compatible seq.continuest jst1.continuest)
                    (svstates-compatible seq.returnst jst1.returnst))))
    :hints(("Goal" :in-theory (enable svjumpstates-compatible)))))



(define svar-subtract-delay ((x svar-p) (delay natp))
  :returns (xx svar-p)
  (change-svar x :delay (nfix (- (svar->delay x) (lnfix delay))))
  ///
  (defret svar-addr-p-of-svar-subtract-delay
    (iff (svar-addr-p xx)
         (svar-addr-p x))
    :hints(("Goal" :in-theory (enable svar-addr-p)))))

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

;; (define svjumpstate-push-scope ((locals svarlist-p)
;;                                    (x svjumpstate-p))
;;   :returns (new-x svjumpstate-p)
;;   (b* (((svjumpstate x))
;;        ((svstate x.breakst))
;;        ((svstate x.continuest))
;;        ((svstate x.returnst)))
;;     (change-svjumpstate
;;      x
;;      :breakst
;;      (change-svstate x.breakst
;;                      :blkst (cons (svstmt-initialize-locals locals) x.breakst.blkst))
;;      :continuest
;;      (change-svstate x.continuest
;;                      :blkst (cons (svstmt-initialize-locals locals) x.continuest.blkst))
;;      :returnst
;;      (change-svstate x.returnst
;;                      :blkst (cons (svstmt-initialize-locals locals) x.returnst.blkst))))
;;   ///
;;   (local (in-theory (enable cdr-lookup-when-svex-alist-p)))
;;   (local (defthm svex-lookup-of-append-under-iff
;;            (iff (svex-lookup v (append a b))
;;                 (or (svex-lookup v a)
;;                     (svex-lookup v b)))
;;            :hints(("Goal" :in-theory (enable svex-lookup)))))

;;   (defret svjumpstate-vars-of-push-scope
;;     (implies (and (not (member v (svjumpstate-vars x)))
;;                   (not (member v (svarlist-fix locals))))
;;              (not (member v (svjumpstate-vars new-x))))
;;     :hints(("Goal" :in-theory (e/d (svjumpstate-vars
;;                                     svstack-to-svex-alist)
;;                                    (acl2::true-listp-append
;;                                     acl2::subsetp-member
;;                                     (:t append) append
;;                                     acl2::consp-of-append))))))

(define svstate-push-scope ((x svstate-p)
                            (locals svarlist-p))
  :returns (new-x svstate-p)
  (b* (((svstate x)))
    (change-svstate x :blkst (cons (svstmt-initialize-locals locals) x.blkst)))
  ///
  (local (in-theory (enable cdr-lookup-when-svex-alist-p)))
  (local (defthm svex-lookup-of-append-under-iff
           (iff (svex-lookup v (append a b))
                (or (svex-lookup v a)
                    (svex-lookup v b)))
           :hints(("Goal" :in-theory (enable svex-lookup)))))
  (defret vars-of-svstate-push-scope
    (implies (and (not (member v (svstate-vars x)))
                  (not (member v (svarlist-fix locals))))
             (not (member v (svstate-vars  new-x))))
    :hints(("Goal" :in-theory (enable svstate-vars
                                      svstack-to-svex-alist)))))

(define svstate-pop-scope ((x svstate-p))
  :returns (new-x svstate-p)
  (b* (((svstate x)))
    (change-svstate x :blkst (if (consp (cdr x.blkst))
                                 (cdr x.blkst)
                               (list nil))))
  ///
  (local (in-theory (enable cdr-lookup-when-svex-alist-p)))
  (local (defthm svex-lookup-of-append-under-iff
           (iff (svex-lookup v (append a b))
                (or (svex-lookup v a)
                    (svex-lookup v b)))
           :hints(("Goal" :in-theory (enable svex-lookup)))))
  (defret vars-of-svate-pop-scope
    (implies (not (member v (svstate-vars x)))
             (not (member v (svstate-vars new-x))))
    :hints(("Goal" :in-theory (enable svstate-vars svstack-to-svex-alist))))

  (defthm svstates-compatible-of-pop-of-push
    (svstates-compatible (svstate-pop-scope (svstate-push-scope x locals))
                         x)
    :hints(("Goal" :in-theory (enable svstates-compatible
                                      svstate-push-scope))))

  (defthm svstates-compatible-of-pop
    (implies (svstates-compatible x y)
             (equal (svstates-compatible (svstate-pop-scope x)
                                         (svstate-pop-scope y))
                    t))
    :hints(("Goal" :in-theory (enable svstates-compatible svstacks-compatible))))


  (defcong svstates-compatible svstates-compatible
    (svstate-pop-scope x) 1
    :hints(("Goal" :in-theory (enable svstates-compatible
                                      svstacks-compatible)))))


(define svjumpstate-pop-scope ((x svjumpstate-p))
  :returns (new-x svjumpstate-p)
  (b* (((svjumpstate x)))
    ;; BOZO this should be guarded with (< 0 (svjumpstate-levels x))
    ;; but then we'd have to prove stuff about the levels for all operations.
    (change-svjumpstate
     x
     :breakst (svstate-pop-scope x.breakst)
     :continuest (svstate-pop-scope x.continuest)
     :returnst (svstate-pop-scope x.returnst)))
  ///
  (local (in-theory (enable cdr-lookup-when-svex-alist-p)))
  (local (defthm svex-lookup-of-append-under-iff
           (iff (svex-lookup v (append a b))
                (or (svex-lookup v a)
                    (svex-lookup v b)))
           :hints(("Goal" :in-theory (enable svex-lookup)))))

  (defret svjumpstate-vars-of-pop-scope
    (implies (not (member v (svjumpstate-vars x)))
             (not (member v (svjumpstate-vars new-x))))
    :hints(("Goal" :in-theory (e/d (svjumpstate-vars
                                    svstack-to-svex-alist)
                                   (acl2::true-listp-append
                                    acl2::subsetp-member
                                    (:t append) append
                                    acl2::consp-of-append)))))

  (defret svjumpstate-pop-scope-compatible-with-svstate-pop-scope
    (implies (svjumpstate-svstate-compatible jst st)
             (svjumpstate-svstate-compatible (svjumpstate-pop-scope jst)
                                             (svstate-pop-scope st)))
    :hints(("Goal" :in-theory (enable svjumpstate-svstate-compatible))))

  (defret svjumpstate-pop-scope-compatible-with-svstate-pop-scope-free
    (implies (svjumpstate-svstate-compatible jst st)
             (equal (svjumpstate-svstate-compatible (svjumpstate-pop-scope jst) st1)
                    (svstates-compatible (svstate-pop-scope st) st1)))
    :hints(("Goal" :in-theory (enable svjumpstate-svstate-compatible))))

  (defcong svjumpstates-compatible svjumpstates-compatible
    (svjumpstate-pop-scope jst) 1
    :hints(("Goal" :in-theory (enable svjumpstates-compatible)))))
                           


(define svar-delayed-member ((v svar-p) (x svarlist-p))
  (if (atom x)
      nil
    (if (equal (svar->name v) (svar->name (car x)))
        (svarlist-fix x)
      (svar-delayed-member v (cdr x)))))


#||


(define clean-svstack ((x svstack-p))
  (if (atom x)
      nil
    (cons (svex-alist-rewrite-fixpoint (fast-alist-free (fast-alist-fork (car x) nil)))
          (clean-svstack (cdr x)))))

(trace$ (svstmt-compile :entry (list 'svstmt-compile
                                     (svstmt-kind x))
                        :exit (b* (((list ?ok ?warnings st ?jst) values))
                                (list 'svstmt-compile
                                      (svstmt-kind x)
                                      :blkst (clean-svstack (svstate->blkst st))
                                      :nonblkst (svex-alist-rewrite-fixpoint (fast-alist-free (fast-alist-fork (svstate->nonblkst st) nil)))
                                      
                                      ;; :returncond (car (svexlist-rewrite-fixpoint
                                      ;;                   (list (svjumpstate->returncond jst))))
                                      ;; :returnst
                                      ;; (clean-svstack
                                      ;;  (svstate->blkst (svjumpstate->returnst jst)))
                                      ))
                        :hide nil
                        :evisc-tuple '(nil 10 10 nil)))


(define svex-compose-svstack-trace ((x svex-p) (a svstack-p))
  :enabled t
  (svex-compose-svstack x a))

(trace$ (svex-compose-svstack-trace
         :entry (list 'svex-compose-svstack (car (svexlist-rewrite-fixpoint (list x))) (clean-svstack a))
         :exit (list 'svex-compose-svstack (car (svexlist-rewrite-fixpoint (list (car values)))))))


(define base16-munge (x)
  (if (atom x)
      (if (integerp x)
          (if (<= 0 x)
              (str::hexify x)
            (list '- (str::hexify (loghead (max 32 (+ 1 (integer-length x))) x))))
        x)
    (cons (base16-munge (car x))
          (base16-munge (cdr x))))
  ///
  (memoize 'base16-munge :condition '(consp x)))
                                         

;; More specialized -- compose everything with assignments to "a" and "b"
(defconst *svstmt-compile-env* (make-fast-alist '(("a" . #b1001) ("b" . #b0101))))

(define clean-svstack-env ((x svstack-p)
                           (env svex-alist-p))
  (if (atom x)
      nil
    (cons (svex-alist-rewrite-fixpoint
           (svex-alist-compose (fast-alist-free (fast-alist-fork (car x) nil)) env))
          (clean-svstack-env (cdr x) env))))


(define svjumpstate-trace ((x svjumpstate-p)
                           (env svex-alist-p))
  (b* (((svjumpstate x)))
    (append (and (not (eql 0 x.breakcond))
                 (list :breakcond (car (svexlist-rewrite-fixpoint
                                        (list
                                         (svex-compose x.breakcond env))))
                       :breakst (clean-svstack-env (svstate->blkst x.breakst) env)))
            (and (not (eql 0 x.continuecond))
                 (list :continuecond (car (svexlist-rewrite-fixpoint
                                        (list
                                         (svex-compose x.continuecond env))))
                       :continuest (clean-svstack-env (svstate->blkst x.continuest) env)))
            (and (not (eql 0 x.returncond))
                 (list :returncond (car (svexlist-rewrite-fixpoint
                                        (list
                                         (svex-compose x.returncond env))))
                       :returnst (clean-svstack-env (svstate->blkst x.returnst) env))))))

(trace$ (svstmt-compile :entry (base16-munge
                                (list 'svstmt-compile
                                      (svstmt-kind x)))
                        :exit (base16-munge
                               (b* (((list ?ok ?warnings st jst) values))
                                 (list* 'svstmt-compile
                                       (clean-svstack-env (svstate->blkst st) *svstmt-compile-env*)
                                       (svjumpstate-trace jst *svstmt-compile-env*))))
                        :hide nil
                        :evisc-tuple '(nil 8 12 nil)))

||#

(define svstack-filter-global-lhs-vars ((x lhs-p)
                                        (stack svstack-p))
  :guard (consp stack)
  :measure (len x)
  :returns (filtered-lhs lhs-p)
  (b* (((when (atom x)) nil)
       ((lhrange x1) (lhrange-fix (car x)))
       ((when (lhatom-case x1.atom :z))
        (svstack-filter-global-lhs-vars (cdr x) stack))
       ((lhatom-var x1.atom))
       ((unless (svstack-globalp x1.atom.name stack))
        (svstack-filter-global-lhs-vars (cdr x) stack)))
    (cons x1 (svstack-filter-global-lhs-vars (cdr x) stack))))
    


(define svstmt-lhs-check-masks ((blk-masks 4vmask-alist-p)
                                (nonblk-masks 4vmask-alist-p)
                                (full-lhs lhs-p)
                                (blockingp)
                                (stack svstack-p))
  :guard (consp stack)
  :returns (mv (new-blk-masks 4vmask-alist-p)
               (new-nonblk-masks 4vmask-alist-p)
               (conflicts 4vmask-alist-p))
  (b* (((mv masks1 conflicts) (lhs-check-masks full-lhs nil nil))
       (- (fast-alist-free masks1))
       (filtered-lhs (svstack-filter-global-lhs-vars full-lhs stack))
       ((mv new-masks confs1) (lhs-check-masks filtered-lhs
                                               (if blockingp blk-masks nonblk-masks)
                                               nil)))
    (fast-alist-free confs1)
    (if blockingp
        (mv new-masks (4vmask-alist-fix nonblk-masks) conflicts)
      (mv (4vmask-alist-fix blk-masks) new-masks conflicts))))


(define constraintlist-compose-svstack ((x constraintlist-p)
                                        (a svstack-p))
  :returns (new-x (equal new-x (constraintlist-compose x (svstack-to-svex-alist a)))
                  :hints(("Goal" :in-theory (enable constraintlist-compose))))
  (if (atom x)
      nil
    (cons (change-constraint (car x)
                             :cond (svex-compose-svstack (constraint->cond (car x)) a))
          (constraintlist-compose-svstack (cdr x) a))))



(defines svstmt-compile
  :verify-guards nil
  (define svstmt-compile ((x svstmt-p)
                          (st svstate-p)
                          (sclimit natp)
                          (nb-delayp)
                          (blk-masks 4vmask-alist-p)
                          (nonblk-masks 4vmask-alist-p)
                          (xcond))
    :parents (svstmt)
    :returns (mv (ok)
                 (warnings1 vl::vl-warninglist-p)
                 (st1 svstate-p)
                 (jst svjumpstate-p)
                 (new-blk-masks 4vmask-alist-p)
                 (new-nonblk-masks 4vmask-alist-p))
    :measure (two-nats-measure sclimit (svstmt-count x))
    (b* ((x              (svstmt-fix x))
         ((svstate st)   (svstate-fix st))
         (warnings       nil)
         (blk-masks     (4vmask-alist-fix blk-masks))
         (nonblk-masks  (4vmask-alist-fix nonblk-masks)))
      (clear-memoize-table 'svex-compose-svstack)
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
        (b* (((mv st full-lhs) (svstmt-process-writelist x.writes x.blockingp nb-delayp xcond st))
             ;; BOZO collect writemask as well
             ((mv blk-masks nonblk-masks conf-acc) (svstmt-lhs-check-masks 
                                                    blk-masks nonblk-masks full-lhs x.blockingp
                                                    (svstate->blkst st)))
             (- (fast-alist-free conf-acc))
             ((when conf-acc)
              (svstate-free st)
              (b* ((st (make-svstate)))
                (mv nil
                    (vl::warn :type :svstmt-compile-fail
                              :msg "Overlapping writes in the same assignment: ~
                              ~a0 (conflicts: ~a1)"
                              :args (list x conf-acc))
                    st
                    (make-empty-svjumpstate st)
                    blk-masks nonblk-masks))))
          (mv t warnings st
              (make-empty-svjumpstate st)
              blk-masks nonblk-masks))
        :if
        (b* (;; We need to compose ST into the condition to handle cases
             ;; like:
             ;;    A = 1;
             ;;    if (A) { ... } else {...}
             (cond-compose (if xcond
                               (svex-quote (svex-xeval x.cond))
                             (svex-compose-svstack x.cond st.blkst)))
             (st2 (svstate-fork st))
             ((vl::wmv ok warnings then-st then-jst blk-masks nonblk-masks)
              (svstmtlist-compile x.then st sclimit nb-delayp blk-masks nonblk-masks xcond))
             ((unless ok)
              (b* ((st (make-svstate)))
                (svstate-free st2)
                (mv nil warnings st (make-empty-svjumpstate st) blk-masks nonblk-masks)))
             ((vl::wmv ok warnings else-st else-jst blk-masks nonblk-masks)
              (svstmtlist-compile x.else st2 sclimit nb-delayp blk-masks nonblk-masks xcond))
             ((unless ok)
              (b* ((st (make-svstate)))
                (svstate-free then-st)
                (mv nil warnings st (make-empty-svjumpstate st) blk-masks nonblk-masks)))
             (st (svstate-merge-branches cond-compose then-st else-st))
             (jst (svjumpstate-merge-branches cond-compose then-jst else-jst)))
          (mv t warnings st jst blk-masks nonblk-masks))
        :while
        (b* (;; could try to do something smart with xcond here but we hope not
             ;; to see loops inside unique cases :-p
             (cond-compose (if xcond
                               (svex-quote (svex-xeval x.cond))
                             (svex-compose-svstack x.cond st.blkst)))
             (cond-rw (svex-maskfree-rewrite cond-compose))
             ((when (eql cond-rw 0))
              ;; Loop condition is syntactically just always false so there is
              ;; no reason to run anything.
              (mv t warnings st (make-empty-svjumpstate st) blk-masks nonblk-masks))
             ((when (zp sclimit))
              (svstate-free st)
              (b* ((st (make-svstate)))
                (mv nil
                    (warn :type :svstmt-compile-fail
                          :msg "couldn't determine bound on while loop ~
                              unrollings: ~a0. rewritten condition ~a1."
                          :args (list x cond-rw))
                    st (make-empty-svjumpstate st)
                    blk-masks nonblk-masks)))

             ;; Even though the loop condition is not syntactically obviously
             ;; 0, it may be some symbolic expression that is sometimes zero,
             ;; so we don't know for sure that we are going to do any loop
             ;; iterations.  The following state/jumpstates are for this case.
             (norun-st (svstate-fork st))
             (norun-jst (make-empty-svjumpstate norun-st))

             ((vl::wmv ok warnings run-st body-jst blk-masks nonblk-masks)
              (svstmtlist-compile x.body st sclimit nb-delayp blk-masks nonblk-masks xcond))
             ((unless ok)
              (svstate-free norun-st)
              (b* ((st (make-svstate)))
                (mv nil warnings st (make-empty-svjumpstate st) blk-masks nonblk-masks)))
             
             ;; Before processing the next forms and the rest of the loop
             ;; iterations, we merge the continue statement into the current
             ;; run state.  That way the next iteration starts from a correct
             ;; state whether the first iteration exited normally or skipped
             ;; part of its execution.
             ((svjumpstate body-jst))
             (run-st (svstate-fork
                      (svstate-merge-branches
                       body-jst.continuecond body-jst.continuest run-st)))

             
             ((vl::wmv ok warnings run-st ?next-jst blk-masks nonblk-masks)
              ;; The for loop step can only be certain things,
              ;; break/continue/return not among them.  So for now at least, we
              ;; ignore the jumpstate from this part.
              (svstmtlist-compile x.next run-st sclimit nb-delayp blk-masks nonblk-masks xcond))

             (- (b* (((svjumpstate next-jst)))
                  (and (or (not (eql 0 next-jst.breakcond))
                           (not (eql 0 next-jst.continuecond))
                           (not (eql 0 next-jst.returncond)))
                       (raise "Unexpectedly encountered a break/continue/return
                               in a for loop iterator"))))

             ((unless ok)
              (svstate-free norun-st)
              (b* ((st (make-svstate)))
                (mv nil warnings st (make-empty-svjumpstate st) blk-masks nonblk-masks)))

             ;; We could possibly avoid evaluating the rest of the loop if we
             ;; found that there was a break statement that was always taken.
             ;; But that seems very unlikely, because even in a loop like "for
             ;; (i=0;....) if (data[i]==0) break;" we don't know anything about
             ;; data when we're processing the body, so we won't know for sure
             ;; that we are breaking.
             ((vl::wmv ok warnings run-st loop-jst blk-masks nonblk-masks)
              (svstmt-compile x run-st (1- sclimit) nb-delayp blk-masks nonblk-masks xcond))

             ((unless ok)
              (svstate-free norun-st)
              (b* ((st (make-svstate)))
                (mv nil warnings st (make-empty-svjumpstate st) blk-masks nonblk-masks)))

             ;; Convention: the loop-jst we get back from compiling the rest of
             ;; the loop will never have any unmerged continue conditions
             ;; (because we merge them before processing each loop iteration)
             ;; and will never have any unmerged break conditions (because we
             ;; will merge them right here before returning).  So, the only way
             ;; that loop-jst can have a jump is if it has a return.

             ;; We now merge the break condition.  Possibilities:
             ;;   (1) The first iteration had a break -- the rest of the loop
             ;;       doesn't happen.
             ;;   (2) The first iteration had no break -- the rest of the loop
             ;;       happens.
             (run-st (svstate-fork
                      (svstate-merge-branches
                       body-jst.breakcond body-jst.breakst run-st)))
             ;; Clear out continue/break since we've now merged them all.
             ;; Subtle: We clear the continue condition before sequentially
             ;; merging the iter1 and loop jump states, but clear the break
             ;; condition after.  Why? If we hit a break in body-jst, we need
             ;; to account for that by not allowing a return from loop-jst.
             (iter1-jst (change-svjumpstate body-jst
                                            :continuecond 0))
             (run-jst (svjumpstate-sequence iter1-jst loop-jst))
             (run-jst (change-svjumpstate run-jst :breakcond 0))

             ;; Now we just have to account for any cases where we didn't run
             ;; anything (even a single iteration) because the loop condition
             ;; turned out to be false.
             (st (svstate-merge-branches cond-rw run-st norun-st))
             (jst (svjumpstate-merge-branches cond-rw run-jst norun-jst)))
          (mv ok warnings st jst blk-masks nonblk-masks))
        :xcond
        (b* (((when xcond)
              (svstmtlist-compile x.body st sclimit nb-delayp blk-masks nonblk-masks xcond))
             (cond1 (svex-compose-svstack x.cond st.blkst))

             (st2 (svstate-fork st))
             ((vl::wmv ok warnings good-st good-jst blk-masks nonblk-masks)
              (svstmtlist-compile x.body st sclimit nb-delayp blk-masks nonblk-masks nil))
             ((unless ok)
              (b* ((st (make-svstate)))
                (svstate-free st2)
                (mv nil warnings st (make-empty-svjumpstate st) blk-masks nonblk-masks)))
             ((vl::wmv ok warnings bad-st bad-jst blk-masks nonblk-masks)
              (svstmtlist-compile x.body st2 sclimit nb-delayp blk-masks nonblk-masks t))
             ((unless ok)
              (b* ((st (make-svstate)))
                (svstate-free good-st)
                (mv nil warnings st (make-empty-svjumpstate st) blk-masks nonblk-masks)))
             (st (svstate-merge-branches cond1 bad-st good-st))
             (jst (svjumpstate-merge-branches cond1 bad-jst good-jst)))
          (mv t warnings st jst blk-masks nonblk-masks))
        :constraints (mv t warnings st
                         (make-empty-svjumpstate st :constraints
                                                 (constraintlist-compose-svstack x.constraints st.blkst))
                         blk-masks nonblk-masks)
        :scope
        (b* ((subscope-st (svstate-push-scope st x.locals))
             ((vl::wmv ok warnings subscope-st subscope-jst blk-masks nonblk-masks)
              (svstmtlist-compile x.body subscope-st sclimit nb-delayp blk-masks nonblk-masks xcond))
             ((unless ok) (mv nil warnings subscope-st subscope-jst blk-masks nonblk-masks))
             (st (svstate-pop-scope subscope-st))
             (jst (svjumpstate-pop-scope subscope-jst)))
          (mv t warnings st jst blk-masks nonblk-masks))
        :jump
        (b* ((empty-jst (make-empty-svjumpstate st)))
          (case x.type
            (:break (mv t warnings st (change-svjumpstate empty-jst :breakcond 1) blk-masks nonblk-masks))
            (:continue (mv t warnings st (change-svjumpstate empty-jst :continuecond 1) blk-masks nonblk-masks))
            (:return (mv t warnings st (change-svjumpstate empty-jst :returncond 1) blk-masks nonblk-masks))
            (otherwise (mv (acl2::impossible) warnings st empty-jst blk-masks nonblk-masks)))))))

  (define svstmtlist-compile ((x        svstmtlist-p)
                              (st       svstate-p)
                              (sclimit natp)
                              (nb-delayp)
                              (blk-masks 4vmask-alist-p)
                              (nonblk-masks 4vmask-alist-p)
                              (xcond))
    :returns (mv (ok)
                 (warnings1 vl::vl-warninglist-p)
                 (st1       svstate-p)
                 (jst       svjumpstate-p)
                 (new-blk-masks 4vmask-alist-p)
                 (new-nonblk-masks 4vmask-alist-p))
    :measure (two-nats-measure sclimit (svstmtlist-count x))
    (b* ((warnings nil)
         ((when (atom x))
          (mv t
              (vl::ok)
              (svstate-fix st)
              (make-empty-svjumpstate st)
              (4vmask-alist-fix blk-masks)
              (4vmask-alist-fix nonblk-masks)))
         ((vl::wmv okp warnings st jst1 blk-masks nonblk-masks)
          (svstmt-compile (car x) st sclimit nb-delayp blk-masks nonblk-masks xcond))
         ((unless okp)
          (mv nil warnings st jst1 blk-masks nonblk-masks))
         ((vl::wmv okp warnings st jst2 blk-masks nonblk-masks)
          (svstmtlist-compile (cdr x) st sclimit nb-delayp blk-masks nonblk-masks xcond))
         ((unless okp)
          (mv nil warnings st jst2 blk-masks nonblk-masks))
         (jst (svjumpstate-sequence jst1 jst2)))
      (mv t warnings st jst blk-masks nonblk-masks)))
  ///
  (verify-guards svstmtlist-compile :guard-debug t)

  (local (in-theory (disable svstmt-compile svstmtlist-compile)))

  ;; (defthm-svstmt-compile-flag
  ;;   (defthm svstmt-compile-preserves-blkst-len
  ;;     (b* (((mv ?ok ?warnings ?new-st)
  ;;           (svstmt-compile x st sclimit nb-delayp)))
  ;;       (implies ok
  ;;                (<= (len (svstate->blkst st))
  ;;                    (len (svstate->blkst new-st)))))
  ;;     :rule-classes :linear
  ;;     :flag svstmt-compile)
  ;;   (defthm svstmtlist-compile-preserves-blkst-len
  ;;     (b* (((mv ?ok ?warnings ?new-st)
  ;;           (svstmtlist-compile x st sclimit nb-delayp)))
  ;;       (implies ok
  ;;                (<= (len (svstate->blkst st))
  ;;                    (len (svstate->blkst new-st)))))
  ;;     :rule-classes :linear
  ;;     :flag svstmtlist-compile))

  ;; (local (defthm len-when-consp
  ;;          (implies (consp x)
  ;;                   (< 0 (len x)))
  ;;          :rule-classes :type-prescription))

  ;; (defthm svstmt-compile-preserves-blkst-consp
  ;;   (b* (((mv ?ok ?warnings ?new-st)
  ;;         (svstmt-compile x st sclimit nb-delayp)))
  ;;     (implies (and ok (consp (svstate->blkst st)))
  ;;              (consp (svstate->blkst new-st))))
  ;;   :hints (("goal" :use ((:instance svstmt-compile-preserves-blkst-len))
  ;;            :in-theory (e/d (len) (svstmt-compile-preserves-blkst-len)))))

  ;; (defthm svstmtlist-compile-preserves-blkst-consp
  ;;   (b* (((mv ?ok ?warnings ?new-st)
  ;;         (svstmtlist-compile x st sclimit nb-delayp)))
  ;;     (implies (and ok (consp (svstate->blkst st)))
  ;;              (consp (svstate->blkst new-st))))
  ;;   :hints (("goal" :use ((:instance svstmtlist-compile-preserves-blkst-len))
  ;;            :in-theory (e/d (len) (svstmtlist-compile-preserves-blkst-len)))))



  ;; (local (defthm svstacks-compatible-of-cdr-when-cons
  ;;          (implies (svstacks-compatible x (cons a b))
  ;;                   (svstacks-compatible (cdr x) b))
  ;;          :hints(("Goal" :in-theory (enable svstacks-compatible)))))

  (defthm-svstmt-compile-flag
    (defthm svstmt-compile-preserves-blkst-compatible
      (b* (((mv ?ok ?warnings ?new-st ?jst)
            (svstmt-compile x st sclimit nb-delayp blk-masks nonblk-masks xcond)))
        (implies ok
                 (and (svstates-compatible new-st (double-rewrite st))
                      (svjumpstates-compatible jst (double-rewrite (make-empty-svjumpstate st))))))
      :hints ('(:expand ((:free (xcond) (svstmt-compile x st sclimit nb-delayp blk-masks nonblk-masks xcond)))
                :do-not-induct t)
              (and stable-under-simplificationp
                   '(:in-theory (enable svjumpstate-svstate-compatible)))
              )
      :flag svstmt-compile)
    (defthm svstmtlist-compile-preserves-blkst-compatible
      (b* (((mv ?ok ?warnings ?new-st ?jst)
            (svstmtlist-compile x st sclimit nb-delayp blk-masks nonblk-masks xcond)))
        (implies ok
                 (and (svstates-compatible new-st (double-rewrite st))
                      (svjumpstates-compatible jst (double-rewrite (make-empty-svjumpstate st))))))
      :hints ('(:expand ((svstmtlist-compile x st sclimit nb-delayp blk-masks nonblk-masks xcond))))
      :flag svstmtlist-compile))


  (local (defthm member-union
           (iff (member v (union a b))
                (or (member v (sfix a))
                    (member v (sfix b))))))

  ;; (defthm-svstmt-compile-flag
  ;;   (defthm vars-of-svstmt-compile
  ;;     (b* (((mv ?ok ?warnings ?new-st ?jst)
  ;;           (svstmt-compile x st sclimit nb-delayp)))
  ;;       (implies (and (not (member v (svstmt-vars x)))
  ;;                     (not (member v (svstate-vars st)))
  ;;                     (not (member v (svarlist-add-delay (svstmt-vars x) 1)))
  ;;                     ;; (not (member v (svarlist-add-delay (svstate-vars st) 1)))
  ;;                     ok)
  ;;                (and (not (member v (svstate-vars new-st)))
  ;;                     (not (member v (svjumpstate-vars jst))))))
  ;;     :hints ('(:expand ((svstmt-compile x st sclimit nb-delayp)
  ;;                        (svstmt-vars x))
  ;;               :do-not-induct t)
  ;;             )
  ;;     :flag svstmt-compile)
  ;;   (defthm svstmtlist-compile-preserves-blkst-compatible
  ;;     (b* (((mv ?ok ?warnings ?new-st ?jst)
  ;;           (svstmtlist-compile x st sclimit nb-delayp)))
  ;;       (implies (and (not (member v (svstmtlist-vars x)))
  ;;                     (not (member v (svstate-vars st)))
  ;;                     (not (svar-delayed-member v (svstmtlist-vars x)))
  ;;                     ;; (not (member v (svarlist-add-delay (svstate-vars st) 1)))
  ;;                     ok)
  ;;                (and (not (member v (svstate-vars new-st)))
  ;;                     (not (member v (svjumpstate-vars jst))))))
  ;;     :hints ('(:expand ((svstmtlist-compile x st sclimit nb-delayp))))
  ;;     :flag svstmtlist-compile))

  ;; (local (DEFTHM
  ;;          SVARLIST-ADDR-P-BY-BADGUY-strong
  ;;          (IMPLIES (NOT (MEMBER (SVARLIST-ADDR-P-BADGUY X)
  ;;                                (double-rewrite (SVARLIST-FIX X))))
  ;;                   (SVARLIST-ADDR-P X))
  ;;          :HINTS (("goal" :INDUCT (SVARLIST-FIX X)
  ;;                   :EXPAND ((SVARLIST-ADDR-P X)
  ;;                            (SVARLIST-ADDR-P-BADGUY X)
  ;;                            (SVARLIST-FIX X))
  ;;                   :IN-THEORY (ENABLE (:I SVARLIST-FIX))))))

  (local (in-theory (disable member-equal
                             MEMBER-OF-SVARLIST-ADD-DELAY
                             acl2::member-of-append
                             acl2::member-equal-append
                             ;; SVARLIST-ADDR-P-BY-BADGUY-STRONG
                             svarlist-addr-p-when-subsetp-equal
                             acl2::list-fix-when-len-zero
                             true-listp
                             acl2::append-of-nil
                             set::sets-are-true-lists)))

  (defthm-svstmt-compile-flag
    (defthm vars-of-svstmt-compile
      (b* (((mv ?ok ?warnings ?new-st ?jst)
            (svstmt-compile x st sclimit nb-delayp blk-masks nonblk-masks xcond)))
        (implies (and (svarlist-addr-p (svstmt-vars x))
                      (svarlist-addr-p (svstate-vars st))
                      ;; (svarlist-addr-p (svex-vars xcond))
                      ;; (not (member v (svarlist-add-delay (svstate-vars st) 1)))
                      ok)
                 (and (svarlist-addr-p (svstate-vars new-st))
                      (svarlist-addr-p (svjumpstate-vars jst)))))
      :hints ('(:expand ((:free (xcond) (svstmt-compile x st sclimit nb-delayp blk-masks nonblk-masks xcond))
                         (svstmt-vars x))
                :do-not-induct t)
              )
      :flag svstmt-compile)
    (defthm vars-of-svstmtlist-compile
      (b* (((mv ?ok ?warnings ?new-st ?jst)
            (svstmtlist-compile x st sclimit nb-delayp blk-masks nonblk-masks xcond)))
        (implies (and (svarlist-addr-p (svstmtlist-vars x))
                      (svarlist-addr-p (svstate-vars st))
                      ;; (svarlist-addr-p (svex-vars xcond))
                      ;; (not (member v (svarlist-add-delay (svstate-vars st) 1)))
                      ok)
                 (and (svarlist-addr-p (svstate-vars new-st))
                      (svarlist-addr-p (svjumpstate-vars jst)))))
      :hints ('(:expand ((svstmtlist-compile x st sclimit nb-delayp blk-masks nonblk-masks xcond))))
      :flag svstmtlist-compile))

  (deffixequiv-mutual svstmt-compile))

;; (defconst *svstmt-compile-reclimit* 100000)

(define svstmtlist-compile-top ((x svstmtlist-p)
                                &key 
                                ;; ((sclimit natp) '*svstmt-compile-reclimit*)
                                (sclimit natp)
                                (nb-delayp 't))
  :Returns (mv (ok)
               (warnings vl-warninglist-p)
               (final-st svstate-p)
               (constraints sv::constraintlist-p)
               (blk-masks 4vmask-alist-p)
               (nonblk-masks 4vmask-alist-p))
  (b* (((mv ok warnings st jst blk-masks nonblk-masks)
        (svstmtlist-compile x (make-svstate) sclimit nb-delayp nil nil nil))
       ((svjumpstate jst))
       (final-st (svstate-fork (svstate-merge-branches
                                jst.returncond jst.returnst st))))
    (svjumpstate-free jst)
    (svstate-free st)
    (mv ok warnings final-st jst.constraints blk-masks nonblk-masks))
  ///
  (defret vars-of-svstmtlist-compile-top
    (implies (and (svarlist-addr-p (svstmtlist-vars x))
                  ok)
             (and (svarlist-addr-p (svstate-vars final-st))
                  (svarlist-addr-p (constraintlist-vars constraints))))))






(defalist svar-size-alist :key-type svar :val-type natp)

(define svstmt-write-var-sizes ((x svstmt-write-p)
                                (blockstack svstack-p)
                                (acc svar-size-alist-p))
  :guard (consp blockstack)
  :returns (sizes svar-size-alist-p)
  (b* (((svstmt-write x))
       (acc (svar-size-alist-fix acc))
       (lhs-var (svex-select-inner-var x.lhs))
       ((unless (svstack-globalp lhs-var blockstack)) acc))
    (cons (cons lhs-var (svex-select-inner-width x.lhs)) acc)))

(define svstmt-writelist-var-sizes ((x svstmt-writelist-p)
                                    (blockstack svstack-p)
                                    (acc svar-size-alist-p))
  :guard (consp blockstack)
  :returns (sizes svar-size-alist-p)
  (if (atom x)
      (svar-size-alist-fix acc)
    (svstmt-writelist-var-sizes
     (cdr x) blockstack
     (svstmt-write-var-sizes (car x) blockstack acc))))

(defines svstmt-lhs-var-sizes 
  (define svstmt-lhs-var-sizes ((x svstmt-p)
                                (blockstack svstack-p)
                                (acc svar-size-alist-p))
    :guard (consp blockstack)
    :measure (svstmt-count x)
    :returns (sizes svar-size-alist-p)
    :verify-guards nil
    (svstmt-case x
      :assign (svstmt-writelist-var-sizes x.writes blockstack acc)
      :if (svstmtlist-lhs-var-sizes
           x.else blockstack (svstmtlist-lhs-var-sizes x.then blockstack acc))
      :while (svstmtlist-lhs-var-sizes
              x.next blockstack
              (svstmtlist-lhs-var-sizes x.body blockstack acc))
      :xcond (svstmtlist-lhs-var-sizes x.body blockstack acc)
      :scope (svstmtlist-lhs-var-sizes
              x.body (cons (svstmt-initialize-locals x.locals) blockstack) acc)
      :constraints (svar-size-alist-fix acc)
      :jump (svar-size-alist-fix acc)))
  (define svstmtlist-lhs-var-sizes ((x svstmtlist-p)
                                    (blockstack svstack-p)
                                    (acc svar-size-alist-p))
    :guard (consp blockstack)
    :measure (svstmtlist-count x)
    :returns (sizes svar-size-alist-p)
    (if (atom x)
        (svar-size-alist-fix acc)
      (svstmtlist-lhs-var-sizes
       (cdr x) blockstack
       (svstmt-lhs-var-sizes (car x) blockstack acc))))
  ///
  (verify-guards svstmt-lhs-var-sizes))
             
       



;; (defines svstmt-write-masks
;;   :verify-guards nil
;;   (define svstmt-write-masks ((x svstmt-p)
;;                               (masks 4vmask-alist-p)
;;                               (nb-masks 4vmask-alist-p))
;;     :parents (svstmt-compile)
;;     :short "Static analysis to tell what parts of what variables may be written
;;             by a statement."
;;     :returns (mv (masks 4vmask-alist-p)
;;                  (nb-masks 4vmask-alist-p))
;;     :measure (svstmt-count x)
;;     (b* ((x           (svstmt-fix x))
;;          (masks       (4vmask-alist-fix masks))
;;          (nb-masks    (4vmask-alist-fix nb-masks)))
;;       (svstmt-case x
;;         :assign
;;         (b* (((mv mask-acc conf-acc) (lhs-check-masks x.lhs (if x.blockingp masks nb-masks) nil))
;;              (- (fast-alist-free conf-acc)))
;;           (if x.blockingp
;;               (mv mask-acc nb-masks)
;;             (mv masks mask-acc)))
;;         :if
;;         (b* (((mv masks nb-masks) (svstmtlist-write-masks x.then masks nb-masks)))
;;           (svstmtlist-write-masks x.else masks nb-masks))
;;         :while
;;         (svstmtlist-write-masks x.body masks nb-masks)
;;         :scope
;;         ;; BOZO overly conservative
;;         (svstmtlist-write-masks x.body masks nb-masks)
;;         :jump (mv masks nb-masks))))

;;   (define svstmtlist-write-masks ((x        svstmtlist-p)
;;                                   (masks    4vmask-alist-p)
;;                                   (nb-masks 4vmask-alist-p))
;;     :returns (mv (masks 4vmask-alist-p)
;;                  (nb-masks 4vmask-alist-p))
;;     :measure (svstmtlist-count x)
;;     (b* (((when (atom x))
;;           (mv (4vmask-alist-fix masks)
;;               (4vmask-alist-fix nb-masks)))
;;          ((mv masks nb-masks) (svstmt-write-masks (car x) masks nb-masks)))
;;       (svstmtlist-write-masks (cdr x) masks nb-masks)))
;;   ///
;;   (verify-guards svstmtlist-write-masks)

;;   (deffixequiv-mutual svstmt-write-masks))




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


