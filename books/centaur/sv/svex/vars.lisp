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
(include-book "svex")
(include-book "std/osets/top" :dir :system)
(include-book "clause-processors/witness-cp" :dir :system)
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "std/osets/element-list" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defxdoc vars.lisp :parents (svex))
(local (xdoc::set-default-parents vars.lisp))

(local (std::deflist svarlist-p (x) (svar-p x) :true-listp t :elementp-of-nil nil))

(defthm setp-singleton
  (setp (list x))
  :hints(("Goal" :in-theory (enable setp))))

(defines svex-vars
  :verify-guards nil
  :flag-local nil
  (define svex-vars ((x svex-p))
    :returns (vars (and (svarlist-p vars)
                        (setp vars)))
    :measure (svex-count x)
    (svex-case x
      :quote nil
      :var (list x.name)
      :call (svexlist-vars x.args)))
  (define svexlist-vars ((x svexlist-p))
    :returns (vars (and (svarlist-p vars)
                        (setp vars)))
    :measure (svexlist-count x)
    (if (atom x)
        nil
      (set::union (svex-vars (car x))
                  (svexlist-vars (cdr x)))))
  ///
  (local (defthm svarlist-p-impl-true-listp
           (implies (svarlist-p x)
                    (true-listp x))
           :hints(("Goal" :in-theory (enable svarlist-p)))))
  (verify-guards svex-vars)

  (memoize 'svex-vars)

  (fty::deffixequiv-mutual svex-vars
    :hints (("Goal" :expand ((svexlist-fix x)))))


  (defthm svex-vars-of-svex-call
    (equal (svex-vars (svex-call fn args))
           (svexlist-vars args))
    :hints (("goal" :expand (svex-vars (svex-call fn args)))))

  (defthm svex-vars-of-svex-var
    (equal (svex-vars (Svex-var name))
           (list (svar-fix name))))

  (defthm svex-vars-of-svex-quote
    (equal (svex-vars (svex-quote val))
           nil))

  (defthm svexlist-vars-of-cons
    (set-equiv (svexlist-vars (cons a b))
               (append (svex-vars a)
                       (svexlist-vars b))))

  (defthm svex-vars-when-var
    (implies (equal (svex-kind x) :var)
             (equal (svex-vars x) (list (svex-var->name x))))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm svex-vars-when-quote
    (implies (equal (svex-kind x) :quote)
             (equal (svex-vars x) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm svex-vars-when-call
    (implies (equal (svex-kind x) :call)
             (equal (svex-vars x)
                    (svexlist-vars (svex-call->args x))))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))

(define svex-alist-vars ((x svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-p))))
  :verify-guards nil
  :returns (vars (and (svarlist-p vars) (setp vars)))
  (if (atom x)
      nil
    (set::union (and (consp (car x))
                      (svex-vars (cdar x)))
                 (svex-alist-vars (cdr x))))
  ///
  (local (defthm svarlist-p-impl-true-listp
           (implies (svarlist-p x)
                    (true-listp x))
           :hints(("Goal" :in-theory (enable svarlist-p)))))

  (verify-guards svex-alist-vars)

  (fty::deffixequiv svex-alist-vars
    :hints (("goal" :expand ((Svex-alist-fix x)))))

  (defthm svex-vars-of-svex-alist-lookup
    (subsetp-equal (svex-vars (svex-lookup k x))
                   (svex-alist-vars x))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))

  (defthm svex-vars-of-svex-acons
    (equal (svex-alist-vars (svex-acons k v x))
           (set::union (svex-vars v)
                        (svex-alist-vars x)))
    :hints(("Goal" :in-theory (enable svex-acons))))

  (defthm svex-alist-vars-of-append
    (set-equiv (svex-alist-vars (append a b))
               (append (svex-alist-vars a)
                       (svex-alist-vars b))))

  (defthm vars-of-svex-alist-lookup
    (implies (not (member v (svex-alist-vars x)))
             (not (member v (svex-vars (cdr (hons-assoc-equal k (svex-alist-fix x)))))))
    :hints(("Goal" :in-theory (enable svex-alist-vars
                                      svex-alist-fix
                                      hons-assoc-equal))))

  (defthm vars-of-fast-alist-fork
    (implies (and (not (member v (svex-alist-vars x)))
                  (not (member v (svex-alist-vars y))))
             (not (member v (svex-alist-vars (fast-alist-fork x y)))))
    :hints(("Goal" :in-theory (enable svex-alist-vars
                                      fast-alist-fork)))))





;; Want to prove that this function correctly computes (up to set-equivalence)
;; the same svex-vars as svex-vars/svex-vars-list, defined in
;; svex-rewrite-base.
(defines svex-collect-vars1
  :verify-guards nil
  :flag-local nil
  (define svex-collect-vars1 ((x svex-p) (seen) (vars svarlist-p))
    :returns (mv seen1 (vars1 svarlist-p))
    :measure (svex-count x)
    (b* ((x (svex-fix x))
         (vars (svarlist-fix vars)))
      (svex-case x
        :quote (mv seen vars)
        :var (if (hons-get x seen)
                 (mv seen vars)
               (mv (hons-acons x t seen)
                   (cons x.name vars)))
        :call (if (hons-get x seen)
                  (mv seen vars)
                (b* ((seen (hons-acons x t seen)))
                  (svexlist-collect-vars1 x.args seen vars))))))
  (define svexlist-collect-vars1 ((x svexlist-p) (seen) (vars svarlist-p))
    :returns (mv seen1 (vars1 svarlist-p))
    :measure (svexlist-count x)
    (if (atom x)
        (mv seen (svarlist-fix vars))
      (b* (((mv seen vars) (svex-collect-vars1 (car x) seen vars)))
        (svexlist-collect-vars1 (cdr x) seen vars))))
  ///
  (verify-guards svex-collect-vars1)
  (deffixequiv-mutual svex-collect-vars1))

(define svex-collect-vars ((x svex-p))
  :returns (vars svarlist-p)
  (b* (((mv seen vars) (svex-collect-vars1 x nil nil)))
    (fast-alist-free seen)
    vars)
  ///
  (deffixequiv svex-collect-vars))

(define svexlist-collect-vars ((x svexlist-p))
  :returns (vars svarlist-p)
  (b* (((mv seen vars) (svexlist-collect-vars1 x nil nil)))
    (fast-alist-free seen)
    vars)
  ///
  (deffixequiv svexlist-collect-vars))

(defsection svexlist-vars-set-equiv-congruence

  (defthm svex-vars-subset-of-svexlist-vars-when-member
    (implies (member x y)
             (subsetp (svex-vars x) (svexlist-vars y)))
    :hints(("Goal" :in-theory (enable svexlist-vars))))

  (defthm svexlist-vars-of-subset
    (implies (subsetp x y)
             (subsetp (svexlist-vars x) (svexlist-vars y)))
    :hints(("Goal" :in-theory (enable subsetp svexlist-vars))))

  ;; (defthm setp-of-svexlist-vars
  ;;   (setp (svexlist-vars x))
  ;;   :hints(("Goal" :in-theory (enable svexlist-vars)
  ;;           :induct (len x))))

   (defcong set-equiv equal (svexlist-vars x) 1
     :hints(("Goal" :in-theory (enable double-containment
                                       set::subset-to-subsetp))))

   (defthm svexlist-vars-of-append
     (equal (svexlist-vars (append x y))
            (union (svexlist-vars x)
                   (svexlist-vars y)))
     :hints(("Goal" :in-theory (enable svexlist-vars)))))





;; Invariant: svex-collect-vars1 uses a preorder accumulator.  Working off the
;; template in centaur/aig/accumulate-nodes-vars.lisp, the invariant we needs
;; is: when recurring on a node a, for every subnode x of a, if x is in the
;; seen list then every subnode of x is in the seen list.

;; we don't collect quotes because svex-collect-vars doesn't either

(defines svex-subnodes
  (define svex-subnodes ((x svex-p))
    :returns (subnodes svexlist-p)
    :measure (svex-count x)
    (svex-case x
      :var (list (svex-fix x))
      :quote nil
      :call (cons (svex-fix x) (svexlist-subnodes x.args))))
  (define svexlist-subnodes ((x svexlist-p))
    :returns (subnodes svexlist-p)
    :measure (svexlist-count x)
    (if (atom x)
        nil
      (append (svex-subnodes (car x))
              (svexlist-subnodes (cdr x)))))
  ///
  (deffixequiv-mutual svex-subnodes)


  (defthm-svex-subnodes-flag
    (defthm member-svex-subnodes-transitive
      (implies (and (member z (svex-subnodes y))
                    (member y (svex-subnodes x)))
               (member z (svex-subnodes x)))
      :flag svex-subnodes)
    (defthm member-svexlist-subnodes-transitive
      (implies (and (member z (svex-subnodes y))
                    (member y (svexlist-subnodes x)))
               (member z (svexlist-subnodes x)))
      :flag svexlist-subnodes))

  (defthm-svex-subnodes-flag
    (defthm nonmember-svex-subnodes-by-count
      (implies (< (svex-count x) (svex-count y))
               (not (member y (svex-subnodes x))))
      :flag svex-subnodes)
    (defthm nonmember-svexlist-subnodes-by-count
      (implies (< (svexlist-count x) (svex-count y))
               (not (member y (svexlist-subnodes x))))
      :flag svexlist-subnodes))

  (defthm-svex-subnodes-flag
    (defthm member-var-of-svex-subnodes-transitive
      (implies (and (member v (svex-vars y))
                    (member y (svex-subnodes x)))
               (member v (svex-vars x)))
      :hints ('(:expand ((svex-vars x)
                         (svex-subnodes x))))
      :flag svex-subnodes)
    (defthm member-var-of-svexlist-subnodes-transitive
      (implies (and (member v (svex-vars y))
                    (member y (svexlist-subnodes x)))
               (member v (svexlist-vars x)))
      :hints ('(:expand ((svexlist-vars x)
                         (svexlist-subnodes x))))
      :flag svexlist-subnodes))
  (in-theory (disable member-var-of-svex-subnodes-transitive
                      member-var-of-svexlist-subnodes-transitive))


  (defthm-svex-subnodes-flag
    (defthm member-svex-var-of-subnodes
      (iff (member (svex-var v) (svex-subnodes x))
           (member (svar-fix v) (svex-vars x)))
      :hints ('(:expand ((svex-vars x)
                         (svex-subnodes x))))
      :flag svex-subnodes)
    (defthm member-svexlist-var-of-subnodes
      (iff (member (svex-var v) (svexlist-subnodes x))
           (member (svar-fix v) (svexlist-vars x)))
      :hints ('(:expand ((svexlist-vars x)
                         (svexlist-subnodes x))))
      :flag svexlist-subnodes))

  (defthm-svex-vars-flag
     (defthm svexlist-vars-of-svex-subnodes
       (equal (svexlist-vars (svex-subnodes x))
              (svex-vars x))
       :hints ('(:expand ((svex-subnodes x)
                          (svex-vars x)
                          (:free (a b) (svexlist-vars (cons a b))))))
       :flag svex-vars)
     (defthm svexlist-vars-of-svexlist-subnodes
       (equal (svexlist-vars (svexlist-subnodes x))
              (svexlist-vars x))
       :hints ('(:expand ((svexlist-subnodes x)
                          (svexlist-vars x))))
       :flag svexlist-vars)))

(local (in-theory (enable member-var-of-svex-subnodes-transitive
                          member-var-of-svexlist-subnodes-transitive)))







(local (defthmd member-alist-keys
         (iff (member k (alist-keys x))
              (hons-assoc-equal k x))
         :hints(("Goal" :in-theory (enable alist-keys)))))





(local
 (defsection svex-collect-vars1-seenlist-invariant

   (acl2::defquant svex-seenlist-invariant (x seen)
     (forall (y z)
             (implies (and (member y (svex-subnodes x))
                           (member y seen)
                           (not (member z seen)))
                      (not (member z (svex-subnodes y)))))
     :rewrite :direct)

   (acl2::defexample svex-seenlist-invariant-example
     :pattern (member z (svex-subnodes y))
     :templates (y z)
     :instance-rulename svex-seenlist-invariant-instancing)

   (acl2::defquant svexlist-seenlist-invariant (x seen)
     (forall (y z)
             (implies (and (member y (svexlist-subnodes x))
                           (member y seen)
                           (not (member z seen)))
                      (not (member z (svex-subnodes y)))))
     :rewrite :direct)

   (acl2::defexample svexlist-seenlist-invariant-example
     :pattern (member z (svex-subnodes y))
     :templates (y z)
     :instance-rulename svexlist-seenlist-invariant-instancing)

   (defthm svexlist-seenlist-invariant-of-call-args
     (implies (and (svex-seenlist-invariant x seen)
                   (equal (svex-kind x) :call))
              (svexlist-seenlist-invariant (svex-call->args x) seen))
     :hints (("goal" :in-theory (enable svex-seenlist-invariant-necc)
              :expand ((svex-subnodes x)))
             (acl2::witness)))

   (defthm svex-seenlist-invariant-of-car
     (implies (and (svexlist-seenlist-invariant x seen)
                   (consp x))
              (svex-seenlist-invariant (car x) seen))
     :hints (("goal" :in-theory (enable svexlist-seenlist-invariant-necc)
              :expand ((svexlist-subnodes x)))
             (acl2::witness)))

   (defthm svexlist-seenlist-invariant-of-cdr
     (implies (svexlist-seenlist-invariant x seen)
              (svexlist-seenlist-invariant (cdr x) seen))
     :hints (("goal" :in-theory (enable svexlist-seenlist-invariant-necc)
              :cases ((consp x))
              :expand ((svexlist-subnodes x)))
             (acl2::witness)))

   (defthm svex-seenlist-invariant-initial
     (svex-seenlist-invariant x nil)
     :hints ((acl2::witness)))

   (defthm svexlist-seenlist-invariant-initial
     (svexlist-seenlist-invariant x nil)
     :hints ((acl2::witness)))


   (local (in-theory (disable set-equiv)))

   (local (defthm member-when-set-equiv-append
            (implies (set-equiv x (append y z))
                     (iff (member k x)
                          (or (member k y) (member k z))))))

   ;; (local (defthm append-cons-under-set-equiv
   ;;          (set-equiv (append (cons b a) c)
   ;;                     (append a (cons b c)))
   ;;          :hints((acl2::set-reasoning))))

   (local (acl2::defexample svex-seenlist-invariant-example-args
            :pattern (member z (svexlist-subnodes (svex-call->args y)))
            :templates ((svex-fix y) z)
            :instance-rulename svex-seenlist-invariant-instancing))


   (defthm svexlist-seenlist-invariant-of-descend
     (implies (and (svex-seenlist-invariant x (alist-keys seen))
                   (equal (svex-kind x) :call))
              (and (svexlist-seenlist-invariant (svex-call->args x)
                                                (alist-keys (cons (cons (svex-fix x) v) seen)))
                   (svexlist-seenlist-invariant (svex-call->args x)
                                                (cons (svex-fix x) (alist-keys seen)))))
     :hints (("goal" :in-theory (enable svex-seenlist-invariant-necc)
              :expand ((:free (a b) (alist-keys (cons a b)))
                       (svex-subnodes x))
              :do-not-induct t)
             (acl2::witness :ruleset svexlist-seenlist-invariant-witnessing)
             (acl2::Set-reasoning)
             (acl2::witness :ruleset svex-seenlist-invariant-example)
             ))

   (defthm-svex-collect-vars1-flag
     (defthm svex-collect-vars1-seenlist1
       (implies (svex-seenlist-invariant x (alist-keys seen))
                (set-equiv (alist-keys (mv-nth 0 (svex-collect-vars1 x seen vars)))
                           (append (svex-subnodes x) (alist-keys seen))))
       :hints ('(:expand ((svex-collect-vars1 x seen vars)
                          (svex-subnodes x))
                 :in-theory (enable svex-seenlist-invariant-necc
                                    member-alist-keys))
               (acl2::witness :ruleset svexlist-seenlist-invariant-witnessing)
               (acl2::Set-reasoning)
               (acl2::witness :ruleset svex-seenlist-invariant-example-args)
               )
       :flag svex-collect-vars1)
     (defthm svexlist-collect-vars1-seenlist1
       (implies (svexlist-seenlist-invariant x (alist-keys seen))
                (set-equiv (alist-keys (mv-nth 0 (svexlist-collect-vars1 x seen vars)))
                           (append (svexlist-subnodes x) (alist-keys seen))))
       :hints ('(:expand ((svexlist-collect-vars1 x seen vars)
                          (svexlist-subnodes x))
                 :in-theory (enable svexlist-seenlist-invariant-necc))
               (acl2::witness :ruleset svexlist-seenlist-invariant-witnessing)
               ;; (acl2::witness :ruleset svexlist-seenlist-invariant-example)
               )
       :flag svexlist-collect-vars1))


   (defthm svex-collect-vars1-preserves-seenlist-invar
     (implies (and (svex-seenlist-invariant y (alist-keys seen))
                   (svex-seenlist-invariant x (alist-keys seen)))
              (svex-seenlist-invariant
               y (alist-keys
                  (mv-nth 0 (svex-collect-vars1 x seen vars)))))
     :hints (("goal" :in-theory (enable svex-seenlist-invariant-necc))
             (acl2::witness :ruleset svex-seenlist-invariant-witnessing)))

   (defthm svex-collect-vars1-preserves-seenlist-list-invar
     (implies (and (svexlist-seenlist-invariant y (alist-keys seen))
                   (svex-seenlist-invariant x (alist-keys seen)))
              (svexlist-seenlist-invariant
               y (alist-keys
                  (mv-nth 0 (svex-collect-vars1 x seen vars)))))
     :hints (("goal" :in-theory (enable svexlist-seenlist-invariant-necc))
             (acl2::witness :ruleset svexlist-seenlist-invariant-witnessing)))

   (defthm svexlist-collect-vars1-preserves-seenlist-invar
     (implies (and (svex-seenlist-invariant y (alist-keys seen))
                   (svexlist-seenlist-invariant x (alist-keys seen)))
              (svex-seenlist-invariant
               y (alist-keys
                  (mv-nth 0 (svexlist-collect-vars1 x seen vars)))))
     :hints (("goal" :in-theory (enable svex-seenlist-invariant-necc))
             (acl2::witness :ruleset svex-seenlist-invariant-witnessing)))

   (defthm svexlist-collect-vars1-preserves-seenlist-list-invar
     (implies (and (svexlist-seenlist-invariant y (alist-keys seen))
                   (svexlist-seenlist-invariant x (alist-keys seen)))
              (svexlist-seenlist-invariant
               y (alist-keys
                  (mv-nth 0 (svexlist-collect-vars1 x seen vars)))))
     :hints (("goal" :in-theory (enable svexlist-seenlist-invariant-necc))
             (acl2::witness :ruleset svexlist-seenlist-invariant-witnessing)))


   (local (Defthm set-difference-of-append
            (equal (set-difference$ (append x y) z)
                   (append (set-difference$ x z)
                           (set-difference$ y z)))
            :hints(("Goal" :in-theory (enable set-difference$ append)))))

   ;; (local (defthm rewrite-svex-collect-vars-under-set-equiv
   ;;          (implies (and (set-equiv (mv-nth 1 (svex-collect-vars1 x seen vars)) y)
   ;;                        (syntaxp (not (case-match y
   ;;                                        (('mv-nth ''1 ('svex-collect-vars1 . &)) t)
   ;;                                        (& nil)))))
   ;;                   (set-equiv (mv-nth 1 (svex-collect-vars1 x seen vars)) y))))

   (defthm rewrite-member-of-append-under-set-equiv
     (implies (set-equiv x (append y z))
              (iff (member k x)
                   (or (member k y)
                       (member k z)))))
   

   

   (local (defthm set-diff-of-nil
            (equal (set-difference$ nil x)
                   nil)
            :hints(("Goal" :in-theory (enable set-difference$)))))

   (defthm intersection-of-append
     (equal (intersection$ (append a b) c)
            (append (intersection$ a c)
                    (intersection$ b c)))
     :hints(("Goal" :in-theory (enable intersection$))))

   (defthm intersection-of-append-2
     (set-equiv (intersection$ c (append a b))
                (append (intersection$ c a)
                        (intersection$ c b)))
     :hints ((acl2::set-reasoning)))


   (defthm member-svexlist-vars-of-intersection
     (implies (not (member v (svexlist-vars x)))
              (not (member v (svexlist-vars (intersection$ x y)))))
     :hints(("Goal" :in-theory (enable intersection$ svexlist-vars))))

   (defthm member-svexlist-vars-of-intersection-2
     (implies (not (member v (svexlist-vars y)))
              (not (member v (svexlist-vars (intersection$ x y)))))
     :hints(("Goal" :in-theory (enable intersection$ svexlist-vars))))


   (define member-svexlist-vars-witness (k x)
     :verify-guards nil
     (if (atom x)
         nil
       (if (member k (svex-vars (car x)))
           (car x)
         (member-svexlist-vars-witness k (cdr x))))
     ///
     (defthm member-svexlist-vars-witness-when-member-svexlist-vars
       (implies (member k (svexlist-vars x))
                (let ((elt (member-svexlist-vars-witness k x)))
                  (and (member elt x)
                       (member k (svex-vars elt)))))
       :hints(("Goal" :in-theory (enable svexlist-vars)))))

   (defthm svex-var-member-of-intersection-when-member-both
     (implies (and (member (svex-var k) x)
                   (member (svex-var k) y)
                   (svar-p k))
              (member k (svexlist-vars (intersection$ x y))))
     :hints(("Goal" :in-theory (enable intersection$ member))))

   (defthm svar-p-when-member-svex-vars
     (implies (member k (svex-vars x))
              (svar-p k))
     :rule-classes :forward-chaining)

   (defthm svar-p-when-member-svexlist-vars
     (implies (member k (svexlist-vars x))
              (svar-p k))
     :rule-classes :forward-chaining)

   (defthm member-vars-of-svex-intersection-under-svex-invar
     (implies (and (svex-seenlist-invariant x seen)
                   ;; (member k (svex-vars x))
                   )
              (iff (member k (svexlist-vars (intersection$ (svex-subnodes x) seen)))
                   (and (member k (svex-vars x))
                        (member (svex-var k) seen))))
     :hints ((and stable-under-simplificationp
                  '(:use ((:instance svex-seenlist-invariant-necc
                           (y (member-svexlist-vars-witness
                               k (intersection$ (svex-subnodes x) seen)))
                           (z (svex-var k)))
                          (:instance member-svexlist-vars-witness-when-member-svexlist-vars
                           (x (intersection$ (svex-subnodes x) seen))))
                    :in-theory (disable member-svexlist-vars-witness-when-member-svexlist-vars)
                    :do-not-induct t)))
     :otf-flg t)

   (defthm member-vars-of-svexlist-intersection-under-svexlist-invar
     (implies (svexlist-seenlist-invariant x seen)
              (iff (member k (svexlist-vars (intersection$ (svexlist-subnodes x) seen)))
                   (and (member k (svexlist-vars x))
                        (member (svex-var k) seen))))
     :hints ((and stable-under-simplificationp
                  '(:use ((:instance svexlist-seenlist-invariant-necc
                           (y (member-svexlist-vars-witness
                               k (intersection$ (svexlist-subnodes x) seen)))
                           (z (svex-var k)))
                          (:instance member-svexlist-vars-witness-when-member-svexlist-vars
                           (x (intersection$ (svexlist-subnodes x) seen))))
                    :in-theory (disable member-svexlist-vars-witness-when-member-svexlist-vars)
                    :do-not-induct t)))
     :otf-flg t)


   ;; (defthm member-vars-of-svex-intersection-under-svexlist-invar
   ;;   (implies (and (svexlist-seenlist-invariant x seen)
   ;;                 (member y (svexlist-subnodes x))
   ;;                 (member k (svex-vars y)))
   ;;            (iff (member k (svexlist-vars (intersection$ (svex-subnodes y) seen)))
   ;;                 (member (svex-var k) seen)))
   ;;   :hints (("goal" :use ((:instance svexlist-seenlist-invariant-necc
   ;;                          (y (member-svexlist-vars-witness
   ;;                              k (intersection$ (svex-subnodes y) seen)))
   ;;                          (z (svex-var k)))
   ;;                         (:instance member-svexlist-vars-witness-when-member-svexlist-vars
   ;;                          (x (intersection$ (svex-subnodes y) seen))))
   ;;            :in-theory (disable member-svexlist-vars-witness-when-member-svexlist-vars)
   ;;            :do-not-induct t))
   ;;   :otf-flg t)




   ;; (defthm member-vars-of-svexlist-intersection-under-svexlist-invar
   ;;   (implies (and (svexlist-seenlist-invariant x seen)
   ;;                 (member k (svexlist-vars x)))
   ;;            (iff (member k (svexlist-vars (intersection$ (svexlist-subnodes x) seen)))
   ;;                 (member (svex-var k) seen)))
   ;;   :hints (("goal" :use ((:instance svexlist-seenlist-invariant-necc
   ;;                          (y (member-svexlist-vars-witness
   ;;                              k (intersection$ (svexlist-subnodes x) seen)))
   ;;                          (z (svex-var k)))
   ;;                         (:instance member-svexlist-vars-witness-when-member-svexlist-vars
   ;;                          (x (intersection$ (svexlist-subnodes x) seen))))
   ;;            :in-theory (disable member-svexlist-vars-witness-when-member-svexlist-vars)
   ;;            :do-not-induct t))
   ;;   :otf-flg t)

   (defthm svexlist-seenlist-invariant-of-svex-subnodes
     (svexlist-seenlist-invariant x (svex-subnodes y))
     :hints ((acl2::witness)))

   (defthm svex-seenlist-invariant-of-svex-subnodes
     (svex-seenlist-invariant x (svex-subnodes y))
     :hints ((acl2::witness)))

   (defthm svexlist-seenlist-invariant-of-svexlist-subnodes
     (svexlist-seenlist-invariant x (svex-subnodes y))
     :hints ((acl2::witness)))

   (defthm svex-seenlist-invariant-of-svexlist-subnodes
     (svex-seenlist-invariant x (svex-subnodes y))
     :hints ((acl2::witness)))

   (defthm member-self-of-svex-subnodes
     (implies (member k (svex-vars x))
              (member (svex-fix x) (svex-subnodes x)))
     :hints (("goal" :expand ((svex-subnodes x)))))

   (defthm seen-invariant-implies-vars-subset
     (implies (and (svex-seenlist-invariant x seen)
                   (member (svex-fix x) seen)
                   (member k (svex-vars x)))
              (member (svex-var k) seen))
     :hints (("goal" :use ((:instance svex-seenlist-invariant-necc
                            (y (svex-fix x)) (z (svex-var k)))))))


   (local (defthmd hons-assoc-equal-iff-member-alist-keys
            (iff (hons-assoc-equal k x)
                 (member k (alist-keys x)))
            :hints(("Goal" :in-theory (enable member-alist-keys)))))

   (defthm-svex-collect-vars1-flag
     (defthm svex-collect-vars1-result
       (implies (svex-seenlist-invariant x (alist-keys seen))
                (set-equiv (mv-nth 1 (svex-collect-vars1 x seen vars))
                           (append (set-difference$ (svex-vars x)
                                                    (svexlist-vars
                                                     (intersection-equal
                                                      (svex-subnodes x)
                                                      (alist-keys seen))))
                                   (svarlist-fix vars))))
       :hints ('(:expand ((svex-collect-vars1 x seen vars)
                          (svex-vars x)
                          (:free (a b) (alist-keys (cons a b))))
                 :in-theory (enable hons-assoc-equal-iff-member-alist-keys))
               (acl2::witness :ruleset (acl2::set-equiv-witnessing
                                        acl2::subsetp-witnessing)))
       :flag svex-collect-vars1)
     (defthm svexlist-collect-vars1-result
       (implies (svexlist-seenlist-invariant x (alist-keys seen))
                (set-equiv (mv-nth 1 (svexlist-collect-vars1 x seen vars))
                           (append (set-difference$ (svexlist-vars x)
                                                    (svexlist-vars
                                                     (intersection-equal
                                                      (svexlist-subnodes x)
                                                      (alist-keys seen))))
                                   (svarlist-fix vars))))
       :hints ('(:expand ((svexlist-collect-vars1 x seen vars)
                          (svexlist-vars x)
                          (svexlist-subnodes x)))
               (acl2::witness :ruleset (acl2::set-equiv-witnessing
                                        acl2::subsetp-witnessing))
               ;; (acl2::witness :ruleset svexlist-seenlist-invariant-witnessing)
               )
       :flag svexlist-collect-vars1))))



(defsection seenlist-invariant

  ;; (acl2::defquant svex-seenlist-invariant (x seen)
  ;;   (forall (y z)
  ;;           (implies (and (member y (svex-subnodes x))
  ;;                         (member y seen)
  ;;                         (not (member z seen)))
  ;;                    (not (member z (svex-subnodes y)))))
  ;;   :rewrite :direct)

  ;; (acl2::defquant svex-varlist-invariant (a seen vars)
  ;;   (forall (v x)
  ;;           (implies (and (member x (svex-subnodes a))
  ;;                         (member x seen)
  ;;                         (not (member v (svarlist-fix vars))))
  ;;                    (not (member v (svex-vars x)))))
  ;;   :rewrite :direct)

  (acl2::defquant svex-collect-seen-invariant (seen)
    ;; Seenlist and varlist invariants for all X
    (forall (y z)
            (implies (and (member y seen)
                          (not (member z seen)))
                     (not (member z (svex-subnodes y)))))
    :rewrite :direct)


  (local (in-theory (enable svex-collect-seen-invariant-necc)))

  (local
   (progn
     (defthm svex-seenlist-invariant-when-collect-seen-invariant
       (implies (svex-collect-seen-invariant seen)
                (svex-seenlist-invariant x seen))
       :hints ((acl2::witness)))

     (defthm svexlist-seenlist-invariant-when-collect-seen-invariant
       (implies (svex-collect-seen-invariant seen)
                (svexlist-seenlist-invariant x seen))
       :hints ((acl2::witness)))))

  (defthm svex-collect-seen-invariant-of-empty
    (svex-collect-seen-invariant nil)
    :hints(("Goal" :in-theory (enable svex-collect-seen-invariant))))


  (defthm svex-collect-vars1-preserves-svex-collect-seen-invariant
    (b* (((mv seen1 ?vars1) (svex-collect-vars1 x seen vars)))
      (implies (svex-collect-seen-invariant (alist-keys seen))
               (svex-collect-seen-invariant (alist-keys seen1))))
    :hints ((acl2::witness)))

  (defthm svexlist-collect-vars1-preserves-svex-collect-seen-invariant
    (b* (((mv seen1 ?vars1) (svexlist-collect-vars1 x seen vars)))
      (implies (svex-collect-seen-invariant (alist-keys seen))
               (svex-collect-seen-invariant (alist-keys seen1))))
    :hints ((acl2::witness)))


  (defthm svex-collect-vars1-seenlist
    (implies (svex-collect-seen-invariant (alist-keys seen))
             (set-equiv (alist-keys (mv-nth 0 (svex-collect-vars1 x seen vars)))
                        (append (svex-subnodes x) (alist-keys seen)))))


  (defthm svexlist-collect-vars1-seenlist
    (implies (svex-collect-seen-invariant (alist-keys seen))
             (set-equiv (alist-keys (mv-nth 0 (svexlist-collect-vars1 x seen vars)))
                        (append (svexlist-subnodes x) (alist-keys seen)))))


  (local
   (defthm member-svexlist-vars-when-member-svex-var
     (implies (and (member (svex-var k) x)
                   (svar-p k))
              (member k (svexlist-vars x)))
     :hints(("Goal" :induct (len x)
             :expand ((svexlist-vars x))))))

  (local (defthm svex-collect-seen-invariant-implies-member-svex-var
           (implies (svex-collect-seen-invariant seen)
                    (iff (member (svex-var k) seen)
                         (member (svar-fix k) (svexlist-vars seen))))
           :hints (("goal" :use ((:instance svex-collect-seen-invariant-necc
                                  (y (member-svexlist-vars-witness
                                      (svar-fix k) seen))
                                  (z (svex-var k))))
                    :in-theory (disable svex-collect-seen-invariant-necc)))))



  (local
   (defthm svex-collect-correct-lemma
     (IMPLIES
      (SVEX-COLLECT-SEEN-INVARIANT (ALIST-KEYS SEEN))
      (SET-EQUIV
       (SET-DIFFERENCE-EQUAL
        (SVEX-VARS X)
        (SVEXLIST-VARS (INTERSECTION-EQUAL (SVEX-SUBNODES X)
                                           (ALIST-KEYS SEEN))))
       (SET-DIFFERENCE-EQUAL (SVEX-VARS X)
                             (SVEXLIST-VARS (ALIST-KEYS SEEN)))))
     :hints ((acl2::set-reasoning)
             (and stable-under-simplificationp
                  '(:use ((:instance svex-seenlist-invariant-when-collect-seen-invariant
                           (seen (alist-keys seen))))
                    :in-theory (disable svex-seenlist-invariant-when-collect-seen-invariant))))
     :otf-flg t))

  (local
   (defthm svexlist-collect-correct-lemma
     (IMPLIES
      (SVEX-COLLECT-SEEN-INVARIANT (ALIST-KEYS SEEN))
      (SET-EQUIV
       (SET-DIFFERENCE-EQUAL
        (SVEXlist-VARS X)
        (SVEXLIST-VARS (INTERSECTION-EQUAL (SVEXlist-SUBNODES X)
                                           (ALIST-KEYS SEEN))))
       (SET-DIFFERENCE-EQUAL (SVEXlist-VARS X)
                             (SVEXLIST-VARS (ALIST-KEYS SEEN)))))
     :hints ((acl2::set-reasoning)
             (and stable-under-simplificationp
                  '(:use ((:instance svexlist-seenlist-invariant-when-collect-seen-invariant
                           (seen (alist-keys seen))))
                    :in-theory (disable svexlist-seenlist-invariant-when-collect-seen-invariant))))
     :otf-flg t))


  (defthm svex-collect-vars1-correct
    (implies (svex-collect-seen-invariant (alist-keys seen))
             (set-equiv (mv-nth 1 (svex-collect-vars1 x seen vars))
                        (append (set-difference$ (svex-vars x)
                                                 (svexlist-vars (alist-keys seen)))
                                (svarlist-fix vars)))))

  (defthm svexlist-collect-vars1-correct
    (implies (svex-collect-seen-invariant (alist-keys seen))
             (set-equiv (mv-nth 1 (svexlist-collect-vars1 x seen vars))
                        (append (set-difference$ (svexlist-vars x)
                                                 (svexlist-vars (alist-keys seen)))
                                (svarlist-fix vars))))))

  



(defthm svex-collect-vars-correct
  (set-equiv (svex-collect-vars x)
             (svex-vars x))
  :hints(("Goal" :in-theory (enable svex-collect-vars))
         (acl2::set-reasoning)))

(defthm svexlist-collect-vars-correct
  (set-equiv (svexlist-collect-vars x)
             (svexlist-vars x))
  :hints(("Goal" :in-theory (enable svexlist-collect-vars))
         (acl2::set-reasoning)))
