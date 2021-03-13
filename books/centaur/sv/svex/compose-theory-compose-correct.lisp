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
(include-book "compose-theory-base")
(include-book "compose")
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))

(local (std::add-default-post-define-hook :fix))

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
;; take a neteval-witness for the final network, (append new-updates assigns),
;; and show that we can produce a neteval-witness for the original network,
;; (append updates assigns), for which the resulting neteval is the same.  The
;; functions that map a witness for the final network to a witness for the
;; original network are neteval-witness-for-svex(list)-compose-dfs and the
;; theorems that prove its correctness are
;; neteval-witness-for-svex(list)-compose-dfs-correct.

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


(local (defthm svex-lookup-of-cons
         (equal (svex-lookup key (cons (cons var val) rest))
                (if (and (svar-p var)
                         (equal (svar-fix key) var))
                    (svex-fix val)
                  (svex-lookup key rest)))
         :hints(("Goal" :in-theory (enable svex-lookup)))))



;; We want to take a composition step applied to some network and show that an
;; evaluation of the composed network produces an evaluation of the original
;; network.  So we take a neteval-witness for the composed network and map it
;; to one for the original network.  We assume here that the composition step
;; is of the form:
;; (cons (cons var (svex-compose (svex-lookup var network)
;;                               (svex-alist-reduce composed-vars network)))
;;       network).


(define svex-network-compose-step ((var svar-p)
                                   (composed-vars svarlist-p)
                                   (network svex-alist-p))
  :guard (svex-lookup var network)
  :returns (new-network svex-alist-p)
  (cons (cons (svar-fix var)
              (svex-compose (svex-lookup var network)
                            (svex-alist-reduce composed-vars network)))
        (svex-alist-fix network))
  ///
  (defret svex-lookup-of-<fn>
    (equal (svex-lookup key new-network)
           (if (equal (svar-fix key) (svar-fix var))
               (svex-compose (svex-lookup var network)
                             (svex-alist-reduce composed-vars network))
             (svex-lookup key network)))
    :hints(("Goal" :in-theory (enable svex-lookup))))

  (defret svex-network-join-envs-of-<fn>
    (implies (svex-lookup var network)
             (svex-envs-equivalent (svex-network-join-envs new-network env1 env2)
                                   (svex-network-join-envs network env1 env2)))
    :hints(("Goal" :in-theory (enable svex-envs-equivalent)))))


(local (defthm neteval-witness-p-of-append
         (implies (and (neteval-witness-p x)
                       (neteval-witness-p y))
                  (neteval-witness-p (append x y)))))

(local (fty::deflist neteval-witnesslist :elt-type neteval-witness :true-listp t))

(local (defthm neteval-witness-p-of-pairlis$
         (implies (and (svarlist-p x)
                       (neteval-witnesslist-p y)
                       (equal (len x) (len y)))
                  (neteval-witness-p (pairlis$ x y)))
         :hints(("Goal" :in-theory (enable pairlis$)))))

(local (deffixcong neteval-witness-equiv neteval-witness-equiv (append x y) x))
(local (deffixcong neteval-witness-equiv neteval-witness-equiv (append x y) y))

(local (include-book "clause-processors/generalize" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))

(define neteval-witness-for-compose-step ((var svar-p)
                                          (composed-vars svarlist-p)
                                          (new-witness neteval-witness-p))
  :returns (witness neteval-witness-p)
  (b* (((when (atom new-witness)) nil)
       ((unless (mbt (and (consp (car new-witness)) (svar-p (caar new-witness)))))
        (neteval-witness-for-compose-step var composed-vars (cdr new-witness)))
       ((cons wit-var sub-witness) (car new-witness))
       (sub-witness2 (neteval-witness-for-compose-step
                      var composed-vars sub-witness))
       ((unless (equal wit-var (svar-fix var)))
        (cons (cons wit-var sub-witness2)
              (neteval-witness-for-compose-step var composed-vars (cdr new-witness))))
       (sub-witness3
        (append (pairlis$ (svarlist-fix composed-vars)
                          (repeat (len composed-vars) sub-witness2))
                sub-witness2)))
    (cons (cons wit-var sub-witness3)
          (neteval-witness-for-compose-step var composed-vars (cdr new-witness))))
  ///
  (local (in-theory (enable neteval-witness-fix)))

  (deffixequiv neteval-witness-for-compose-step)

  (defret lookup-in-<fn>
    (equal (hons-assoc-equal key witness)
           (let ((new-look (hons-assoc-equal key (neteval-witness-fix new-witness))))
             (and new-look
                  (let ((sub-witness2
                         (neteval-witness-for-compose-step
                          var composed-vars (cdr new-look))))
                    (if (equal key (svar-fix var))
                        (cons key (append (pairlis$ (svarlist-fix composed-vars)
                                                    (repeat (len composed-vars) sub-witness2))
                                          sub-witness2))
                      (cons key sub-witness2))))))
    :hints (("goal" :induct (len new-witness)
             :expand (<call>))))

  (local (defthm neteval-witness->neteval-of-append
           (equal (neteval-witness->neteval (append x y) network env)
                  (append (neteval-witness->neteval x network env)
                          (neteval-witness->neteval y network env)))
           :hints(("Goal" 
                   :expand ((:free (x y) (neteval-witness->neteval (cons x y) network env))
                            (append x y)
                            (neteval-witness->neteval x network env))
                   :induct (neteval-witness->neteval x network env)
                   :in-theory (enable (:i neteval-witness->neteval)))
                  (and stable-under-simplificationp
                       '(:expand ((neteval-witness->neteval y network env)))))))

  (local (defthmd neteval-witness->neteval-of-pairlis$-repeat-lemma
           (implies (svarlist-p keys)
                    (equal (neteval-witness->neteval (pairlis$ keys (repeat (len keys) x)) network env)
                           (svex-env-reduce keys
                                            (svex-alist-eval network
                                                             (svex-network-join-envs
                                                              network
                                                              (neteval-witness->neteval x network env)
                                                              env)))))
           :hints(("Goal" :in-theory (enable svex-env-reduce-redef pairlis$)
                   :expand ((:free (x y) (neteval-witness->neteval (cons x y) network env))
                            (neteval-witness->neteval nil network env))
                   :induct (len keys)))))

  (local (defthm neteval-witness->neteval-of-pairlis$-repeat
           (equal (neteval-witness->neteval (pairlis$ (svarlist-fix keys) (repeat (len keys) x)) network env)
                  (svex-env-reduce keys
                                   (svex-alist-eval network
                                                    (svex-network-join-envs
                                                     network
                                                     (neteval-witness->neteval x network env)
                                                     env))))
           :hints (("goal" :use ((:instance neteval-witness->neteval-of-pairlis$-repeat-lemma
                                  (keys (svarlist-fix keys))))))))

  (local (defthm acl2-count-of-hons-assoc-equal
           (<= (acl2-count (hons-assoc-equal k x)) (acl2-count x))
           :rule-classes :linear))


  (local (defun correct-induction (var composed-vars network new-witness env)
           (declare (xargs :measure (acl2-count (neteval-witness-fix new-witness))
                           :hints (("goal" :in-theory (disable hons-assoc-equal-of-neteval-witness-fix)))))
           (b* ((witness (neteval-witness-for-compose-step
                          var composed-vars new-witness))
                (badguy (svex-envs-equivalent-witness
                         (neteval-witness->neteval
                          witness network env)
                         (neteval-witness->neteval
                          new-witness
                          (svex-network-compose-step var composed-vars network)
                          env)))
                (look (hons-assoc-equal (svar-fix badguy) (neteval-witness-fix new-witness)))
                ((unless look) (list witness badguy)))
             (correct-induction var composed-vars network (cdr look) env))))


  (local (defthm svex-env-boundp-of-svex-env-reduce
           (iff (svex-env-boundp key (svex-env-reduce vars x))
                (and (member-equal (svar-fix key) (svarlist-fix vars))
                     (svex-env-boundp key x)))
           :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-reduce)))))

  (local (defthm lemma
           (svex-envs-equivalent (SVEX-NETWORK-JOIN-ENVS
                                  NETWORK
                                  (APPEND
                                   (SVEX-ENV-REDUCE
                                    COMPOSED-VARS
                                    (SVEX-ALIST-EVAL
                                     NETWORK
                                     neteval1))
                                   neteval)
                                  ENV)
                                 (APPEND
                                  (SVEX-ENV-REDUCE
                                   COMPOSED-VARS
                                   (SVEX-ALIST-EVAL
                                    NETWORK
                                    neteval1))
                                  (SVEX-NETWORK-JOIN-ENVS
                                   NETWORK
                                   neteval
                                   ENV)))
           :hints(("Goal" :in-theory (enable svex-envs-equivalent))
                  (and stable-under-simplificationp
                       (let ((wit (acl2::find-call-lst 'svex-envs-equivalent-witness clause)))
                         `(:clause-processor (acl2::simple-generalize-cp
                                              clause
                                              '((,wit . badguy-key)))))))))

  

  (defret <fn>-correct
    (implies (svex-lookup var network)
             (svex-envs-equivalent
              (neteval-witness->neteval
               witness network env)
              (neteval-witness->neteval
               new-witness
               (svex-network-compose-step var composed-vars network)
               env)))
    :hints(("Goal" ;; :in-theory (enable svex-envs-equivalent)
            :induct (correct-induction var composed-vars network new-witness env))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))
           (and stable-under-simplificationp
                (let ((wit (acl2::find-call-lst 'svex-envs-equivalent-witness clause)))
                  `(:clause-processor (acl2::simple-generalize-cp
                                       clause
                                       '((,wit . badguy-key))))))
           ;; (and stable-under-simplificationp
           ;;      '(:in-theory (enable svex-network-join-envs)))
           )
    :otf-flg t))
       
    



(local (include-book "centaur/misc/dfs-measure" :dir :system))


(deffixcong svex-alist-equiv svex-alist-equiv (append x y) x)
(deffixcong svex-alist-equiv svex-alist-equiv (append x y) y)

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
                    





(defines neteval-witness-for-svex-compose-dfs
  :flag-local nil
  (define neteval-witness-for-svex-compose-dfs ((x svex-p "svex we're traversing")
                                                (assigns svex-alist-p "alist of assign stmts")
                                                (updates svex-alist-p "alist of composed update fns")
                                                (memo svex-svex-memo-p "memo table for internal nodes")
                                                (stack "alist of seen vars"
                                                       alistp)
                                                (witness neteval-witness-p))
    :verify-guards nil
    :returns (new-witness neteval-witness-p)
    :well-founded-relation acl2::nat-list-<
    :measure (list (len (set-difference-equal
                         (svex-alist-keys assigns)
                         (strip-cars stack)))
                   (svex-count x))

    (b* ((x (mbe :logic (svex-fix x) :exec x))
         (memo (svex-svex-memo-fix memo))
         (updates (mbe :logic (svex-alist-fix updates) :exec updates)))
      (svex-case x
        :quote (neteval-witness-fix witness)
        :call (b* ((look (hons-get x memo))
                   ((when look) (neteval-witness-fix witness)))
                (neteval-witness-for-svexlist-compose-dfs x.args assigns updates memo stack witness))
        :var (b* ((update-fn (svex-fastlookup x.name updates))
                  ((when update-fn) (neteval-witness-fix witness))
                  (assign (svex-fastlookup x.name assigns))
                  ((unless assign)
                   (neteval-witness-fix witness))
                  ((when (hons-get x.name stack))
                   (neteval-witness-fix witness))
                  (stack (hons-acons x.name t stack))
                  ((mv & updates1 &)
                   (svex-compose-dfs assign assigns updates nil stack))
                  (witness (neteval-witness-for-compose-step x.name
                                                             ;; (set-difference-equal (svex-vars x.name)
                                                             ;;                       (alist-keys stack))
                                                             (svex-alist-keys updates1)
                                                             witness))
                  (witness
                   (neteval-witness-for-svex-compose-dfs assign assigns updates nil stack witness))
                  (- (acl2::fast-alist-pop stack)))
               witness))))
  (define neteval-witness-for-svexlist-compose-dfs ((x svexlist-p)
                                (assigns svex-alist-p)
                                (updates svex-alist-p)
                                (memo svex-svex-memo-p)
                                (stack alistp)
                                (witness neteval-witness-p))
    :measure (list (len (set-difference-equal
                         (svex-alist-keys assigns)
                         (strip-cars stack)))
                   (svexlist-count x))
    :returns (new-witness neteval-witness-p)
    (b* ((updates (mbe :logic (svex-alist-fix updates) :exec updates))
         (memo (svex-svex-memo-fix memo))
         ((when (atom x)) (neteval-witness-fix witness))
         ;; (witness (neteval-witness-for-svex-compose-dfs
         ;;           (car x) assigns updates memo stack witness))
         ((mv ?first updates1 memo1)
          (svex-compose-dfs (car x) assigns updates memo stack))
         (witness1 (neteval-witness-for-svexlist-compose-dfs
                    (cdr x) assigns updates1 memo1 stack witness)))
      (neteval-witness-for-svex-compose-dfs
       (car x) assigns updates memo stack witness1)))
  ///

  (local (defthm alist-keys-of-cons
           (equal (alist-keys (cons (cons a b) c))
                  (cons a (alist-keys c)))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthm svex-lookup-of-append
           (equal (svex-lookup k (append a b))
                  (or (svex-lookup k a)
                      (svex-lookup k b)))
           :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix)))))


  (defthm svex-compose-svex-alist-eval-equiv-congruence
    (implies (svex-alist-eval-equiv a b)
             (svex-eval-equiv (svex-compose x a) (svex-compose x b)))
    :hints(("Goal" :in-theory (enable svex-eval-equiv)))
    :rule-classes :congruence)

  (defthm svex-compose*-svex-alist-eval-equiv-congruence
    (implies (svex-alist-eval-equiv a b)
             (svex-eval-equiv (svex-compose* x a) (svex-compose* x b)))
    :hints(("Goal" :in-theory (enable svex-eval-equiv)))
    :rule-classes :congruence)

  (local (defthm svex-alist-eval-equiv-cons-cons
           (implies (svex-eval-equiv x y)
                    (svex-alist-eval-equiv (cons (cons var x) rest)
                                           (cons (cons var y) rest)))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))
           :rule-classes :congruence))

  (defthm svex-compose-to-svex-compose*
    (svex-eval-equiv (svex-compose x a)
                     (svex-compose* x a))
    :hints(("Goal" :in-theory (enable svex-eval-equiv))))

  (local (defthm svex-alist-reduce-of-svex-alist-keys
           (svex-alist-eval-equiv (svex-alist-reduce (svex-alist-keys updates)
                                                     (append updates assigns))
                                  updates)
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))))

  (local (in-theory (disable neteval-witness-for-compose-step-correct)))

  (local
   (defthm neteval-witness-for-compose-step-correct-for-compose-dfs
     (b* ((witness (neteval-witness-for-compose-step var (svex-alist-keys updates) new-witness)))
       (implies (and (svex-lookup var assigns)
                     (not (svex-lookup var updates))
                     (svar-p var))
                (svex-envs-equivalent
                 (neteval-witness->neteval
                  new-witness
                  (cons (cons var (svex-compose*
                                   (svex-lookup var assigns)
                                   updates))
                        (append updates assigns))
                  env)
                 (neteval-witness->neteval
                  witness (append updates assigns) env))))
     :hints(("Goal" :use ((:instance neteval-witness-for-compose-step-correct
                           (composed-vars (svex-alist-keys updates))
                           (network (append updates assigns))))
             :in-theory (enable svex-network-compose-step)
            ;; (and stable-under-simplificationp
            ;;      '(:in-theory (enable svex-network-join-envs)))
            ))))


  (std::defret-mutual neteval-witness-for-svex-compose-dfs-correct
    (defret <fn>-correct
      (b* (((mv ?x1 updates1 ?memo1)
            (svex-compose-dfs x assigns updates memo stack))
           (neteval1 (neteval-witness->neteval new-witness
                                               (append updates assigns)
                                               env))
           (neteval2 (neteval-witness->neteval witness
                                               (append updates1 assigns)
                                               env)))
        (implies (And (svex-compose-dfs-memo-correct memo updates)
                      (svex-compose-dfs-memo-vars-okp memo assigns updates stack))
                 (svex-envs-equivalent neteval1 neteval2)))
      :hints ('(:expand (<call>
                         (svex-compose-dfs x assigns updates memo stack))
                :in-theory (enable svex-acons)))
      :fn neteval-witness-for-svex-compose-dfs)

    (defret <fn>-correct
      (b* (((mv ?x1 updates1 ?memo1)
            (svexlist-compose-dfs x assigns updates memo stack))
           (neteval1 (neteval-witness->neteval new-witness
                                               (append updates assigns)
                                               env))
           (neteval2 (neteval-witness->neteval witness
                                               (append updates1 assigns)
                                               env)))
        (implies (And (svex-compose-dfs-memo-correct memo updates)
                      (svex-compose-dfs-memo-vars-okp memo assigns updates stack))
                 (svex-envs-equivalent neteval1 neteval2)))
      :hints ('(:expand (<call>
                         (svexlist-compose-dfs x assigns updates memo stack))))
      :fn neteval-witness-for-svexlist-compose-dfs)))


(defret neteval-for-<fn>-is-neteval-for-assigns
  (implies (And (svex-compose-dfs-memo-correct memo updates)
                (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
                (neteval-p neteval (append updates1 assigns) env))
           (neteval-p neteval (append updates assigns) env))
  :hints (("goal" :expand ((neteval-p neteval (append updates1 assigns) env))
           :use ((:instance neteval-p-suff
                  (network (append updates assigns))
                  (neteval-witness (neteval-witness-for-svex-compose-dfs
                                    x assigns updates memo stack 
                                    (neteval-p-witness neteval (append updates1 assigns) env)))))))
  :fn svex-compose-dfs
  :rule-classes nil)


(defret neteval-for-<fn>-is-neteval-for-assigns
  (implies (And (svex-compose-dfs-memo-correct memo updates)
                (svex-compose-dfs-memo-vars-okp memo assigns updates stack)
                (neteval-p neteval (append updates1 assigns) env))
           (neteval-p neteval (append updates assigns) env))
  :hints (("goal" :expand ((neteval-p neteval (append updates1 assigns) env))
           :use ((:instance neteval-p-suff
                  (network (append updates assigns))
                  (neteval-witness (neteval-witness-for-svexlist-compose-dfs
                                    x assigns updates memo stack 
                                    (neteval-p-witness neteval (append updates1 assigns) env)))))))
  :fn svexlist-compose-dfs
  :rule-classes nil)















