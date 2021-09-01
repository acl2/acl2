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
(include-book "compose-theory-compose-steps")
(include-book "compose")
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))

(local (std::add-default-post-define-hook :fix))

(std::make-returnspec-config :hints-sub-returnnames t)







;; This book uses the theory of compositional network evaluations introduced in
;; compose-theory-base.lisp and shows that the SVEX-COMPOSE-DFS algorithm used
;; initially for composing together the network of assignments into update
;; functions is "correct."  This correctness is a bit complicated:

;; A neteval is a set of concrete values for signals that are a "correct
;; evaluation" of a network of assignments given an input environment. We are
;; producing formulas, not concrete values; these should produce a "correct
;; evaluation" for every environment.

;; The composition may not be complete: we sometimes (e.g. in the case of
;; apparent combinational loops) leave an internal signal variable in one of
;; the updates functions.  This complicates the statement of correctness: every
;; evaluation of the resulting update functions isn't a neteval, because it
;; might be using nonsensical values for these internal signals.  Rather, we
;; show that something that is a neteval for the update functions is also a
;; neteval for the original assignments.

;; Finally, the DFS algorithm is (of course) mutually recursive and it is
;; a tricky proof and invariant.  Here is a basic explanation:

;; First, what is the recursive invariant?  At a given entry point into the
;; algorithm, we have the input assignments, some update functions already
;; composed, a memo table, a stack of variables we're not done processing, and
;; an expression we're currently traversing.  The algorithm then returns a new
;; formulation of that expression, a new set of update functions, and a new
;; memo table.  We show that anything that is a neteval for the network
;; consisting of the new update functions and the original assingnments for any
;; signals not included in them -- formulated as (append new-updates assigns)
;; -- is also a neteval for the network with the input update functions and
;; original assignments, (append updates assigns).  These are the theorems
;; neteval-for-svex-compose-dfs-is-neteval-for-assigns and
;; neteval-for-svexlist-compose-dfs-is-neteval-for-assigns.

;; Since neteval-p is an existentially quantified function, what we really do
;; take a neteval-ordering for the final network, (append new-updates assigns),
;; and show that we can produce a neteval-ordering for the original network,
;; (append updates assigns), for which the resulting neteval is the same.  The
;; functions that map a witness for the final network to a witness for the
;; original network are neteval-ordering-for-svex(list)-compose-dfs and the
;; theorems that prove its correctness are
;; neteval-ordering-for-svex(list)-compose-dfs-correct.

;; We need to show a couple of invariants before we can do this proof.  In
;; particular we have to deal with the memo table and formulate what
;; expression(lists) the svex(list)-compose-dfs functions return.  We show that
;; these functions always return a result expression(list) which equals the
;; svex(list)-compose* of the input expression and resulting updates, and we
;; show that every pairing in the memo table reflects this as well.  In order
;; to show this we also need another invariant concerning what variables may be
;; present in the resulting expressions.  We show that the input expression's
;; variables and the resulting updates' bindings satisfy a condition
;; svex-compose-dfs-vars-cond, defined as
;;   (subsetp (intersection input-expr-vars assigns-keys)
;;            (append updates-keys stack-keys))
;; and that every key in the memo table also satisfies this property.
;; Since every time a variable is popped off the stack that variable is bound
;; in the update functions, this invariant is preserved down the call stack, and since 
;; the update functions are only extended with new pairs, this is preserved over calls.





(defsection svex-compose*-when-reduce-equiv
  (local (defthm consp-of-hons-assoc-equal
           (iff (consp (hons-assoc-equal k x))
                (hons-assoc-equal k x))))

  (local (defthm equal-cons-of-svex-alist-reduce
           (implies (not (svex-lookup var envb))
                    (not (equal (cons (cons var val) rest)
                                (svex-alist-reduce vars envb))))
           :hints(("Goal" :in-theory (enable svex-alist-reduce)))))


  (local (defthm svex-lookup-when-equal-svex-alist-reduce
           (implies (and (bind-free (and (eq enva 'enva) '((envb . envb))) (envb))
                         (equal (svex-alist-reduce vars enva)
                                (svex-alist-reduce vars envb))
                         (member-equal (svar-fix var) (svarlist-fix vars)))
                    (equal (svex-lookup var enva)
                           (svex-lookup var envb)))
           :hints(("Goal" :in-theory (enable svex-alist-reduce svarlist-fix)))))

  (defthm-svex-compose*-flag
    (defthm svex-compose*-when-reduce-equiv
      (implies (and (equal (svex-alist-reduce vars enva)
                           (svex-alist-reduce vars envb))
                    (subsetp-equal (svex-vars x) (svarlist-fix vars)))
               (equal (svex-compose* x enva)
                      (svex-compose* x envb)))
      :hints ('(:expand ((:free (env) (svex-compose* x env))
                         (svex-vars x))))
      :flag svex-compose*)

    (defthm svexlist-compose*-when-reduce-equiv
      (implies (and (equal (svex-alist-reduce vars enva)
                           (svex-alist-reduce vars envb))
                    (subsetp-equal (svexlist-vars x) (svarlist-fix vars)))
               (equal (svexlist-compose* x enva)
                      (svexlist-compose* x envb)))
      :hints ('(:expand ((:free (env) (svexlist-compose* x env))
                         (svexlist-vars x))))
      :flag svexlist-compose*)))



(defsection vars-of-svex-compose-dfs
  (std::defret-mutual boundp-preserved-of-svex-compose-dfs
    (defret boundp-preserved-of-<fn>
      (implies (svex-lookup var updates)
               (equal (svex-lookup var updates1)
                      (svex-lookup var updates)))
      :hints ('(:expand (<call>)))
      :fn svex-compose-dfs)
    (defret boundp-preserved-of-<fn>
      (implies (svex-lookup var updates)
               (equal (svex-lookup var updates1)
                      (svex-lookup var updates)))
      :hints ('(:expand (<call>)))
      :fn svexlist-compose-dfs)
    :mutual-recursion svex-compose-dfs)

  ;; (defun-sk svex-compose-dfs-memo-vars-okp (memo assigns updates stack)
  ;;   (forall (var svex)
  ;;           (implies (and (svex-lookup svex memo)
  ;;                         (member-equal (svar-fix var) (svex-vars svex))
  ;;                         (not (hons-assoc-equal (svar-fix var) stack))
  ;;                         (svex-lookup var assigns))
  ;;                    (svex-lookup var updates)))
  ;;   :rewrite :direct)

  ;; (in-theory (Disable svex-compose-dfs-memo-vars-okp
  ;;                     svex-compose-dfs-memo-vars-okp-necc))

  ;; (implies (and (not (hons-assoc-equal (svar-fix var) stack))
  ;;               (svex-lookup var assigns)
  ;;               (not (svex-lookup var updates)))

  ;; (defun-sk svex-compose-dfs-memo-var-okp (var memo assigns updates stack)
  ;;   (forall svex
  ;;           (implies (svex-lookup svex memo)
  ;;                    (not (member-equal (svar-fix var) (svex-vars svex)))))
  ;;   :rewrite :direct)

  ;; (in-theory (Disable svex-compose-dfs-memo-var-okp
  ;;                     svex-compose-dfs-memo-var-okp-necc))

  (define svex-compose-dfs-memo-var-okp ((var svar-p)
                                         (memo svex-svex-memo-p))
    (if (atom memo)
        t
      (and (or (atom (car memo))
               (not (member-equal (svar-fix var) (svex-vars (caar memo)))))
           (svex-compose-dfs-memo-var-okp var (cdr memo))))
    ///
    ;; (defthm svex-compose-dfs-memo-var-okp-implies
    ;;   (implies (and (svex-compose-dfs-memo-var-okp var memo)
    ;;                 (hons-assoc-equal (svex-fix svex) (svex-svex-memo-fix memo)))
    ;;            (not (member-equal (svar-fix var) (svex-vars svex))))
    ;;   :hints(("Goal" :in-theory (enable svex-svex-memo-fix))))

    (defthmd svex-compose-dfs-memo-var-okp-implies
      (implies (and (svex-compose-dfs-memo-var-okp var memo)
                    (hons-assoc-equal (svex-fix svex) (svex-svex-memo-fix memo)))
               (not (member-equal var (svex-vars svex))))
      :hints(("Goal" :in-theory (enable svex-svex-memo-fix))))

    (defthmd svex-compose-dfs-memo-var-okp-implies2
      (implies (and (svex-compose-dfs-memo-var-okp var memo)
                    (member-equal (svar-fix var) (svex-vars svex)))
               (not (hons-assoc-equal svex (svex-svex-memo-fix memo))))
      :hints(("Goal" :in-theory (enable svex-svex-memo-fix))))


    (defthm svex-compose-dfs-memo-var-okp-of-acons
      (implies (svex-compose-dfs-memo-var-okp var memo)
               (iff (svex-compose-dfs-memo-var-okp var (cons (cons key val) memo))
                    (not (member-equal (svar-fix var) (svex-vars key))))))


    (local (in-theory (enable svex-svex-memo-fix))))

  (local (in-theory (enable svex-compose-dfs-memo-var-okp-implies2
                            svex-compose-dfs-memo-var-okp-implies)))


  (std::defret-mutual boundp-of-svex-compose-dfs
    (defret boundp-of-<fn>
      (implies (and (not (hons-assoc-equal (svar-fix var) stack))
                    (svex-lookup var assigns)
                    (svex-compose-dfs-memo-var-okp var memo))
               (and (implies (not (svex-lookup var updates1))
                             (svex-compose-dfs-memo-var-okp var memo1))
                    (implies (member (svar-fix var) (svex-vars x))
                             (svex-lookup var updates1))))
      :hints ('(:expand (<call>
                         (svex-vars x))))
      :fn svex-compose-dfs)
    (defret boundp-of-<fn>
      (implies (and (not (hons-assoc-equal (svar-fix var) stack))
                    (svex-lookup var assigns)
                    (svex-compose-dfs-memo-var-okp var memo))
               (and (implies (not (svex-lookup var updates1))
                             (svex-compose-dfs-memo-var-okp var memo1))
                    (implies (member (svar-fix var) (svexlist-vars x))
                             (svex-lookup var updates1))))
      :hints ('(:expand (<call>
                         (svexlist-vars x))))
      :fn svexlist-compose-dfs)
    :mutual-recursion svex-compose-dfs)

  (std::defret-mutual not-boundp-by-stack-of-svex-compose-dfs
    (defret not-boundp-by-stack-of-<fn>
      (implies (and (not (svex-lookup var updates))
                    (hons-assoc-equal (svar-fix var) stack))
               (not (svex-lookup var updates1)))
      :hints ('(:expand (<call>)))
      :fn svex-compose-dfs)
    (defret not-boundp-by-stack-of-<fn>
      (implies (and (not (svex-lookup var updates))
                    (hons-assoc-equal (svar-fix var) stack))
               (not (svex-lookup var updates1)))
      :hints ('(:expand (<call>)))
      :fn svexlist-compose-dfs)
    :mutual-recursion svex-compose-dfs)

  (std::defret-mutual not-boundp-by-assigns-of-svex-compose-dfs
    (defret not-boundp-by-assigns-of-<fn>
      (implies (and (not (svex-lookup var updates))
                    (not (svex-lookup var assigns)))
               (not (svex-lookup var updates1)))
      :hints ('(:expand (<call>)))
      :fn svex-compose-dfs)
    (defret not-boundp-by-assigns-of-<fn>
      (implies (and (not (svex-lookup var updates))
                    (not (svex-lookup var assigns)))
               (not (svex-lookup var updates1)))
      :hints ('(:expand (<call>)))
      :fn svexlist-compose-dfs)
    :mutual-recursion svex-compose-dfs)



  (local (in-theory (enable svex-env-acons)))

  (local (defthm svex-env-lookup-of-cons
           (equal (svex-env-lookup key (cons (cons var val) rest))
                  (if (and (svar-p var)
                           (equal (svar-fix key) var))
                      (4vec-fix val)
                    (svex-env-lookup key rest)))
           :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-fix)))))

  (local (defthm svex-env-boundp-of-cons
           (equal (svex-env-boundp key (cons (cons var val) rest))
                  (if (and (svar-p var)
                           (equal (svar-fix key) var))
                      t
                    (svex-env-boundp key rest)))
           :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-fix)))))


  (defret update-keys-subsetp-of-assigns-keys-of-<fn>
    (implies (subsetp-equal (svex-alist-keys updates) (svex-alist-keys assigns))
             (subsetp-equal (svex-alist-keys updates1) (svex-alist-keys assigns)))
    :hints ((acl2::set-reasoning))
    :fn svex-compose-dfs)

  (defret update-keys-subsetp-of-assigns-keys-of-<fn>
    (implies (subsetp-equal (svex-alist-keys updates) (svex-alist-keys assigns))
             (subsetp-equal (svex-alist-keys updates1) (svex-alist-keys assigns)))
    :hints ((acl2::set-reasoning))
    :fn svexlist-compose-dfs)



  (defret vars-subsetp-of-<fn>
    (subsetp-equal (set-difference-equal
                    (intersectp-equal (svex-vars x) (svex-alist-keys assigns))
                    (alist-keys stack))
                   (svex-alist-keys updates1))
    :hints ((acl2::set-reasoning))
    :fn svex-compose-dfs)

  (defret vars-subsetp-of-<fn>
    (subsetp-equal (set-difference-equal
                    (intersectp-equal (svexlist-vars x) (svex-alist-keys assigns))
                    (alist-keys stack))
                   (svex-alist-keys updates1))
    :hints ((acl2::set-reasoning))
    :fn svexlist-compose-dfs)

  (local (defthm member-alist-keys-is-hons-assoc-equal
           (iff (member-equal k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defret stack-not-intersectp-of-<fn>
    (implies (not (intersectp-equal (alist-keys stack) (svex-alist-keys updates)))
             (not (intersectp-equal (alist-keys stack) (svex-alist-keys updates1))))
    :hints ((acl2::set-reasoning))
    :fn svex-compose-dfs)

  (defret stack-not-intersectp-of-<fn>
    (implies (not (intersectp-equal (alist-keys stack) (svex-alist-keys updates)))
             (not (intersectp-equal (alist-keys stack) (svex-alist-keys updates1))))
    :hints ((acl2::set-reasoning))
    :fn svexlist-compose-dfs)

  


  (define svex-compose-dfs-vars-cond ((vars svarlist-p)
                                      (assigns svex-alist-p)
                                      (updates svex-alist-p)
                                      (stack alistp))
    (subsetp-equal (intersection-equal (svarlist-fix vars)
                                       (svex-alist-keys assigns))
                   (append (svex-alist-keys updates) (alist-keys stack)))
    ///
    (local (in-theory (disable acl2::commutativity-of-append-under-set-equiv)))

    (defret svex-alist-reduce-vars-of-<fn>when-svex-compose-dfs-vars-cond
      (implies (svex-compose-dfs-vars-cond vars assigns updates stack)
               (equal (svex-alist-reduce vars updates1)
                      (svex-alist-reduce vars updates)))
      :hints(("Goal" :in-theory (enable svex-alist-reduce
                                        intersection-equal)))
      :fn svex-compose-dfs)

    (defret svex-alist-reduce-vars-of-<fn>when-svex-compose-dfs-vars-cond
      (implies (svex-compose-dfs-vars-cond vars assigns updates stack)
               (equal (svex-alist-reduce vars updates1)
                      (svex-alist-reduce vars updates)))
      :hints(("Goal" :in-theory (enable svex-alist-reduce
                                        intersection-equal)))
      :fn svexlist-compose-dfs))


  (define svex-compose-dfs-memo-vars-okp ((memo svex-svex-memo-p)
                                          (assigns svex-alist-p)
                                          (updates svex-alist-p)
                                          (stack alistp))
    (if (atom memo)
        t
      (and (or (atom (car memo))
               (b* ((key (svex-fix (caar memo)))
                    (vars (svex-vars key)))
                 (svex-compose-dfs-vars-cond vars assigns updates stack)))
           (svex-compose-dfs-memo-vars-okp (cdr memo) assigns updates stack)))
    ///
    (local (in-theory (enable svex-svex-memo-fix)))

    (defthm svex-compose-dfs-memo-vars-okp-implies
      (implies (and (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
                    (hons-assoc-equal key (svex-svex-memo-fix memo)))
               (b* ((vars (svex-vars key)))
                 (svex-compose-dfs-vars-cond vars assigns updates stack))))

    (defthmd svex-compose-dfs-memo-vars-okp-implies-var
      (implies (and (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
                    (hons-assoc-equal key (svex-svex-memo-fix memo)))
               (b* ((vars (svex-vars key)))
                 (implies (and (member-equal (svar-fix var) vars)
                               (svex-lookup var assigns)
                               (not (hons-assoc-equal (svar-fix var) stack)))
                          (svex-lookup var updates))))
      :hints(("Goal" :in-theory (e/d (svex-compose-dfs-vars-cond)
                                     (svex-compose-dfs-memo-vars-okp-implies
                                      svex-compose-dfs-memo-vars-okp))
              :use svex-compose-dfs-memo-vars-okp-implies)
             (acl2::set-reasoning)))

    (local (in-theory (enable svex-compose-dfs-memo-vars-okp-implies-var)))

    (defthm svex-compose-dfs-memo-vars-okp-implies-svex-compose-dfs-memo-var-okp
      (implies (and (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
                    (svex-lookup var assigns)
                    (not (hons-assoc-equal (svar-fix var) stack))
                    (case-split (not (svex-lookup var updates))))
               (svex-compose-dfs-memo-var-okp var memo))
      :hints(("Goal" :in-theory (e/d (svex-compose-dfs-memo-vars-okp
                                      svex-compose-dfs-memo-var-okp
                                      svex-compose-dfs-vars-cond))
              :induct (svex-compose-dfs-memo-vars-okp memo assigns updates stack))
             (acl2::set-reasoning)))

    

    (defret svex-compose-dfs-vars-cond-of-<fn>
      (implies (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
               (svex-compose-dfs-vars-cond (svex-vars x) assigns updates1 stack))
      :hints (("goal" :in-theory (e/d (svex-compose-dfs-vars-cond)
                                      (svex-compose-dfs-memo-vars-okp)))
              (acl2::set-reasoning))
      :fn svex-compose-dfs)

    (defret svex-compose-dfs-vars-cond-of-<fn>
      (implies (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
               (svex-compose-dfs-vars-cond (svexlist-vars x) assigns updates1 stack))
      :hints (("goal" :in-theory (e/d (svex-compose-dfs-vars-cond)
                                      (svex-compose-dfs-memo-vars-okp)))
              (acl2::set-reasoning))
      :fn svexlist-compose-dfs))

  
  (define svex-compose-dfs-memo-vars-okp-badguy ((memo svex-svex-memo-p)
                                                 (assigns svex-alist-p)
                                                 (updates svex-alist-p)
                                                 (stack alistp))
    :returns (mv svex var)
    (if (atom memo)
        (mv nil nil)
      (if (atom (car memo))
          (svex-compose-dfs-memo-vars-okp-badguy (cdr memo) assigns updates stack)
        (b* ((key (svex-fix (caar memo)))
             (vars (svex-vars key)))
          (if (svex-compose-dfs-vars-cond vars assigns updates stack)
              (svex-compose-dfs-memo-vars-okp-badguy (cdr memo) assigns updates stack)
            (mv key
                (car (set-difference-equal (intersection-equal vars (svex-alist-keys assigns))
                                           (append (svex-alist-keys updates) (alist-keys stack)))))))))
    ///
    (local (defthmd car-set-difference-witnesses-subset
             (iff (subsetp-equal a b)
                  (not (let ((k (car (set-difference-equal a b))))
                         (and (member k a)
                              (not (member k b))))))
             :hints(("Goal" :in-theory (enable subsetp set-difference-equal)))))

    (local (in-theory (enable svex-svex-memo-fix)))

    (defret svex-compose-dfs-memo-vars-okp-by-badguy
      (implies (or (not (hons-assoc-equal svex (svex-svex-memo-fix memo)))
                   (not (member-equal (svar-fix var) (svex-vars svex)))
                   (not (svex-lookup var assigns))
                   (hons-assoc-equal (svar-fix var) stack)
                   (svex-lookup var updates))
               (svex-compose-dfs-memo-vars-okp memo assigns updates stack))
      :hints(("Goal" :in-theory (enable svex-compose-dfs-memo-vars-okp
                                        svex-compose-dfs-vars-cond)
              :induct <call>)
             (and stable-under-simplificationp
                  '(:in-theory (enable car-set-difference-witnesses-subset)))))

    (defthmd svex-compose-dfs-memo-vars-okp-redef
      (equal (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
             (mv-let (svex var)
               (svex-compose-dfs-memo-vars-okp-badguy memo assigns updates stack)
               (and (or (not (hons-assoc-equal svex (svex-svex-memo-fix memo)))
                        (not (member-equal (svar-fix var) (svex-vars svex)))
                        (not (svex-lookup var assigns))
                        (hons-assoc-equal (svar-fix var) stack)
                        (svex-lookup var updates))
                    t)))
      :hints (("goal" :cases ((svex-compose-dfs-memo-vars-okp memo assigns updates stack))
               :in-theory (e/d (svex-compose-dfs-memo-vars-okp-implies-var)
                               (svex-compose-dfs-memo-vars-okp-badguy))))
      :rule-classes :definition)

    (defthmd svex-compose-dfs-memo-vars-okp-implies-svex-compose-dfs-memo-var-okp-redef
      (equal (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
             (mv-let (svex var)
               (svex-compose-dfs-memo-vars-okp-badguy memo assigns updates stack)
               (declare (ignore svex))
               (implies (and (svex-lookup var assigns)
                             (not (hons-assoc-equal (svar-fix var) stack))
                             (not (svex-lookup var updates)))
                        (svex-compose-dfs-memo-var-okp var memo))))
      :hints(("Goal" :cases ((svex-compose-dfs-memo-vars-okp memo assigns updates stack))
              :do-not-induct t)
             (and stable-under-simplificationp
                  '(:in-theory (enable svex-compose-dfs-memo-vars-okp-redef))))
      :otf-flg t
      :rule-classes :definition))


  (defret svex-compose-dfs-memo-vars-okp-of-<fn>
    (implies (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
             (svex-compose-dfs-memo-vars-okp memo1 assigns updates1 stack))
    :hints ((and stable-under-simplificationp
                 `(:expand ((:with svex-compose-dfs-memo-vars-okp-implies-svex-compose-dfs-memo-var-okp-redef ,(car (last clause))))
                   :do-not-induct t)))
    :fn svex-compose-dfs)

  (defret svex-compose-dfs-memo-vars-okp-of-<fn>
    (implies (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
             (svex-compose-dfs-memo-vars-okp memo1 assigns updates1 stack))
    :hints ((and stable-under-simplificationp
                 `(:expand ((:with svex-compose-dfs-memo-vars-okp-implies-svex-compose-dfs-memo-var-okp-redef ,(car (last clause))))
                   :do-not-induct t)))
    :fn svexlist-compose-dfs))


(defret svex-compose*-of-updates-of-<fn>
  (implies (Svex-compose-dfs-vars-cond (svex-vars y) assigns updates stack)
           (equal (svex-compose* y updates1)
                  (svex-compose* y updates)))
  :hints (("goal" :use ((:instance svex-compose*-when-reduce-equiv
                         (x y)
                         (vars (svex-vars y))
                         (enva updates1)
                         (envb updates)))))
  :fn svex-compose-dfs)

(defret svexlist-compose*-of-updates-of-<fn>
  (implies (Svex-compose-dfs-vars-cond (svexlist-vars y) assigns updates stack)
           (equal (svexlist-compose* y updates1)
                  (svexlist-compose* y updates)))
  :hints (("goal" :use ((:instance svexlist-compose*-when-reduce-equiv
                         (x y)
                         (vars (svexlist-vars y))
                         (enva updates1)
                         (envb updates)))))
  :fn svex-compose-dfs)


(defret svex-compose*-of-updates-of-<fn>
  (implies (Svex-compose-dfs-vars-cond (svex-vars y) assigns updates stack)
           (equal (svex-compose* y updates1)
                  (svex-compose* y updates)))
  :hints (("goal" :use ((:instance svex-compose*-when-reduce-equiv
                         (x y)
                         (vars (svex-vars y))
                         (enva updates1)
                         (envb updates)))))
  :fn svexlist-compose-dfs)

(defret svexlist-compose*-of-updates-of-<fn>
  (implies (Svex-compose-dfs-vars-cond (svexlist-vars y) assigns updates stack)
           (equal (svexlist-compose* y updates1)
                  (svexlist-compose* y updates)))
  :hints (("goal" :use ((:instance svexlist-compose*-when-reduce-equiv
                         (x y)
                         (vars (svexlist-vars y))
                         (enva updates1)
                         (envb updates)))))
  :fn svexlist-compose-dfs)





;; We want to take a composition step applied to some network and show that an
;; evaluation of the composed network produces an evaluation of the original
;; network.  So we take a neteval-ordering for the composed network and map it
;; to one for the original network.  We assume here that the composition step
;; is of the form:
;; (cons (cons var (svex-compose (svex-lookup var network)
;;                               (svex-alist-reduce composed-vars network)))
;;       network).



       
    



(local (include-book "centaur/misc/dfs-measure" :dir :system))


(deffixcong svex-alist-equiv svex-alist-equiv (append x y) x)
(deffixcong svex-alist-equiv svex-alist-equiv (append x y) y)


(local (defthm svex-lookup-of-cons
         (equal (svex-lookup key (cons (cons var val) rest))
                (if (and (svar-p var)
                         (equal (svar-fix key) var))
                    (svex-fix val)
                  (svex-lookup key rest)))
         :hints(("Goal" :in-theory (enable svex-lookup)))))

(defsection svex-compose-dfs-is-svex-compose*

  (define svex-compose-dfs-memo-correct ((memo svex-svex-memo-p)
                                         (updates svex-alist-p))
    (b* (((when (atom memo)) t)
         ((unless (mbt (consp (car memo))))
          (svex-compose-dfs-memo-correct (cdr memo) updates))
         ((cons x x1) (car memo)))
      (and (svex-equiv x1 (svex-compose* x updates))
           (svex-compose-dfs-memo-correct (cdr memo) updates)))
    ///
    (defthm svex-compose-dfs-memo-correct-implies
      (implies (and (svex-compose-dfs-memo-correct memo updates)
                    (hons-assoc-equal x (svex-svex-memo-fix memo)))
               (equal (cdr (hons-assoc-equal x (svex-svex-memo-fix memo)))
                      (svex-compose* x updates)))
      :hints(("Goal" :in-theory (enable svex-svex-memo-fix))))

    (defthm svex-compose-dfs-memo-correct-of-cons
      (equal (svex-compose-dfs-memo-correct (cons (cons x x1) rest) updates)
             (and (svex-equiv x1 (svex-compose* x updates))
                  (svex-compose-dfs-memo-correct rest updates))))

    (defthm svex-compose-dfs-memo-correct-of-nil
      (svex-compose-dfs-memo-correct nil updates))

    (local
     (defthm-svex-compose*-flag
       (defthm svex-compose*-of-cons-when-subsetp
         (implies (and (subsetp-equal (intersection-equal (svex-vars x)
                                                          vars1)
                                      (append vars2 (svex-alist-keys a)))
                       (member-equal (svar-fix var) vars1)
                       (not (member-equal (svar-fix var) vars2))
                       (not (svex-lookup var a)))
                  (equal (svex-compose* x (cons (cons var val) a))
                         (svex-compose* x a)))
         :hints ('(:expand ((:free (a) (svex-compose* x a))
                            (svex-vars x)))
                 (acl2::set-reasoning))
         :flag svex-compose*)
       (defthm svexlist-compose*-of-cons-when-subsetp
         (implies (and (subsetp-equal (intersection-equal (svexlist-vars x)
                                                          vars1)
                                      (append vars2 (svex-alist-keys a)))
                       (member-equal (svar-fix var) vars1)
                       (not (member-equal (svar-fix var) vars2))
                       (not (svex-lookup var a)))
                  (equal (svexlist-compose* x (cons (cons var val) a))
                         (svexlist-compose* x a)))
         :hints ('(:expand ((:free (a) (svexlist-compose* x a))
                            (svexlist-vars x))))
         :flag svexlist-compose*)))

    (local (defthm member-alist-keys
             (iff (member-equal x (alist-keys y))
                  (hons-assoc-equal x y))
             :hints(("Goal" :in-theory (enable alist-keys)))))

    (defthm svex-compose-dfs-memo-correct-of-cons-updates
      (implies (and (svex-compose-dfs-memo-correct memo updates)
                    (bind-free '((stack . stack) (assigns . assigns)) (stack assigns))
                    (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
                    (svex-lookup var assigns)
                    (not (svex-lookup var updates))
                    (not (hons-assoc-equal (svar-fix var) stack)))
               (svex-compose-dfs-memo-correct memo (cons (cons var val) updates)))
      :hints(("Goal" :in-theory (enable svex-compose-dfs-memo-vars-okp
                                        svex-compose-dfs-vars-cond))))

    (local (in-theory (enable svex-svex-memo-fix))))

  (local
   (defretd svex-compose-dfs-memo-vars-okp-by-badguy-split
     (implies (case-split
                (or (not (hons-assoc-equal svex (svex-svex-memo-fix memo)))
                    (not (member-equal (svar-fix var) (svex-vars svex)))
                    (not (svex-lookup var assigns))
                    (hons-assoc-equal (svar-fix var) stack)
                    (svex-lookup var updates)))
              (svex-compose-dfs-memo-vars-okp memo assigns updates stack))
     :fn svex-compose-dfs-memo-vars-okp-badguy))

  (std::defret-mutual svex-compose-dfs-vars-ok-other-memo-invar
    (defret <fn>-vars-ok-other-memo-invar
      (implies (svex-compose-dfs-memo-vars-okp mem assigns updates stack)
               (svex-compose-dfs-memo-vars-okp mem assigns updates1 stack))
      :hints ('(:expand (<call>))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-compose-dfs-memo-vars-okp-by-badguy-split
                                        SVEX-COMPOSE-DFS-MEMO-VARS-OKP-IMPLIES-VAR))))
      :fn svex-compose-dfs)
    (defret <fn>-vars-ok-other-memo-invar
      (implies (svex-compose-dfs-memo-vars-okp mem assigns updates stack)
               (svex-compose-dfs-memo-vars-okp mem assigns updates1 stack))
      :hints ('(:expand (<call>)))
      :fn svexlist-compose-dfs)
    :mutual-recursion svex-compose-dfs)

  (std::defret-mutual svex-compose-dfs-redef-memo-invar
    (defret <fn>-memo-invar
      (implies (and (svex-compose-dfs-memo-correct mem updates)
                    (svex-compose-dfs-memo-vars-okp mem assigns updates stack))
               (svex-compose-dfs-memo-correct mem updates1))
      :hints ('(:expand (<call>)
                :in-theory (enable svex-acons
                                   SVEX-COMPOSE-DFS-MEMO-VARS-OKP-IMPLIES-VAR)))
      :fn svex-compose-dfs)
    (defret <fn>-memo-invar
      (implies (and (svex-compose-dfs-memo-correct mem updates)
                    (svex-compose-dfs-memo-vars-okp mem assigns updates stack))
               (svex-compose-dfs-memo-correct mem updates1))
      :hints ('(:expand (<call>)))
      :fn svexlist-compose-dfs)
    :mutual-recursion svex-compose-dfs)


  (std::defret-mutual svex-compose-dfs-redef
    (defret <fn>-is-svex-compose*
      (implies (and (svex-compose-dfs-memo-correct memo updates)
                    (svex-compose-dfs-memo-vars-okp memo assigns updates stack))
               (and (svex-compose-dfs-memo-correct memo1 updates1)
                    (equal x1
                           (svex-compose* x updates1))))
      :hints ('(:expand (<call>
                         (:free (a) (svex-compose* x a)))
                :in-theory (enable svex-acons
                                   SVEX-COMPOSE-DFS-MEMO-VARS-OKP-IMPLIES-VAR)))
      :fn svex-compose-dfs)
    (defret <fn>-is-svexlist-compose*
      (implies (and (svex-compose-dfs-memo-correct memo updates)
                    (svex-compose-dfs-memo-vars-okp memo assigns updates stack))
               (and (svex-compose-dfs-memo-correct memo1 updates1)
                    (equal x1
                           (svexlist-compose* x updates1))))
      :hints ('(:expand (<call>
                         (:free (a) (svexlist-compose* x a)))))
      :fn svexlist-compose-dfs)
    :mutual-recursion svex-compose-dfs))



(defcong svex-eval-equiv svex-alist-eval-equiv (svex-acons var val x) 2
  :hints(("Goal" :in-theory (enable svex-alist-eval-equiv))))

(defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-acons var val x) 3
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))

(defthm svex-compose*-under-svex-eval-equiv
  (svex-eval-equiv (svex-compose* x al)
                   (svex-compose x al))
  :hints(("Goal" :in-theory (enable svex-eval-equiv))))

(defsection netcomp-p-of-svex-compose-dfs
  ;;   (local (defthm alist-keys-of-cons
  ;;          (equal (alist-keys (cons (cons a b) c))
  ;;                 (cons a (alist-keys c)))
  ;;          :hints(("Goal" :in-theory (enable alist-keys)))))

  ;; (local (defthm svex-lookup-of-append
  ;;          (equal (svex-lookup k (append a b))
  ;;                 (or (svex-lookup k a)
  ;;                     (svex-lookup k b)))
  ;;          :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix)))))


  ;; (defthm svex-compose-svex-alist-eval-equiv-congruence
  ;;   (implies (svex-alist-eval-equiv a b)
  ;;            (svex-eval-equiv (svex-compose x a) (svex-compose x b)))
  ;;   :hints(("Goal" :in-theory (enable svex-eval-equiv)))
  ;;   :rule-classes :congruence)

  ;; (defthm svex-compose*-svex-alist-eval-equiv-congruence
  ;;   (implies (svex-alist-eval-equiv a b)
  ;;            (svex-eval-equiv (svex-compose* x a) (svex-compose* x b)))
  ;;   :hints(("Goal" :in-theory (enable svex-eval-equiv)))
  ;;   :rule-classes :congruence)

  ;; (local (defthm svex-alist-eval-equiv-cons-cons
  ;;          (implies (svex-eval-equiv x y)
  ;;                   (svex-alist-eval-equiv (cons (cons var x) rest)
  ;;                                          (cons (cons var y) rest)))
  ;;          :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))
  ;;          :rule-classes :congruence))

  ;; (local (defthm svex-compose-to-svex-compose*
  ;;          (svex-eval-equiv (svex-compose x a)
  ;;                           (svex-compose* x a))
  ;;          :hints(("Goal" :in-theory (enable svex-eval-equiv)))))

  ;; (local (defthm svex-alist-reduce-of-svex-alist-keys
  ;;          (svex-alist-eval-equiv (svex-alist-reduce (svex-alist-keys updates)
  ;;                                                    (append updates assigns))
  ;;                                 updates)
  ;;          :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))))

  ;; (local (defthm append-acons-compose-is-svex-network-compose-step
  ;;          (implies
  ;;           (not (svex-lookup var updates))
  ;;           (svex-alist-eval-equiv
  ;;            (append (svex-acons var (svex-compose* (svex-lookup var assigns) updates)
  ;;                                updates)
  ;;                    assigns)
  ;;            (svex-network-compose-step var (svex-alist-keys updates) (append updates assigns))))
  ;;          :hints(("Goal" :in-theory (enable svex-network-compose-step
  ;;                                            svex-alist-eval-equiv)))))

  (std::defret-mutual netcomp-p-of-<fn>
    (defret netcomp-p-of-<fn>
      (implies (and (svex-compose-dfs-memo-correct memo updates)
                    (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
                    (netcomp-p updates network)
                    (netcomp-p assigns network))
               (netcomp-p updates1 network))
      :hints ('(:expand (<call>)))
      :fn svex-compose-dfs)
    (defret netcomp-p-of-<fn>
      (implies (and (svex-compose-dfs-memo-correct memo updates)
                    (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
                    (netcomp-p updates network)
                    (netcomp-p assigns network))
               (netcomp-p updates1 network))
      :hints ('(:expand (<call>)) 
              (and stable-under-simplificationp
                   '(:in-theory (enable netcomp-p-transitive2))))
      :fn svexlist-compose-dfs)
    :mutual-recursion svex-compose-dfs))
                    
