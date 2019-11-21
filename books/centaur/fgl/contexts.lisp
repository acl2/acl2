; FGL - A Symbolic Simulation Framework for ACL2
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

(in-package "FGL")

(include-book "centaur/meta/congruence" :dir :system)
(include-book "logicman")
(include-book "centaur/misc/starlogic" :dir :system)

(local (std::add-default-post-define-hook :fix))

(table equiv-ev-fgl-ev-functional-subst)
(table equiv-ev-fgl-ev-functional-subst 'cmr::equiv-ev 'fgl-ev)
(table equiv-ev-fgl-ev-functional-subst 'cmr::equiv-ev-list 'fgl-ev-list)

(defmacro add-equiv-ev-fgl-ev-functional-subst (cmr-name fgl-name)
  `(table equiv-ev-fgl-ev-functional-subst ',cmr-name ',fgl-name))

(local (defun equiv-ev-fgl-ev-functional-subst-hint-fn (formula world other-hints subst)
         `(,@other-hints
             :use ((:instance
                    (:functional-instance ,formula
                     . ,(let ((a (table-alist 'equiv-ev-fgl-ev-functional-subst world)))
                          (pairlis$ (strip-cars a) (pairlis$ (strip-cdrs a) nil))))
                    . ,subst)))))

(local (defmacro equiv-ev-fgl-ev-functional-subst-hint (formula &key other-hints subst)
         `(equiv-ev-fgl-ev-functional-subst-hint-fn ',formula world ',other-hints ',subst)))

(local (defmacro equiv-ev-fgl-ev-record-functional-subst (name formula &key other-hints)
         `(defthm ,name
            t
            :rule-classes nil
            :hints ((equiv-ev-fgl-ev-functional-subst-hint ,formula :other-hints ,other-hints)))))


(local (equiv-ev-fgl-ev-record-functional-subst
        fgl-ev-func-inst cmr::equiv-ev-of-fncall-args
        :other-hints (:in-theory (enable fgl-ev-of-fncall-args))))



;; The reflexive closure of the OR of the equivalences.
(define fgl-ev-context-equiv-base ((ctx equiv-contextsp) x y)
  (if (atom ctx)
      (equal x y)
    (or (and (fgl-ev (pseudo-term-fncall (car ctx)
                                           (list (pseudo-term-quote x)
                                                 (pseudo-term-quote y)))
                       nil)
             t)
        (fgl-ev-context-equiv-base (cdr ctx) x y)))
  ///
  (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-context-equiv-base fgl-ev-context-equiv-base)
  (local (equiv-ev-fgl-ev-record-functional-subst
          fgl-ev-context-equiv-base-func-inst
          cmr::equiv-ev-context-equiv-base)))

;; The symmetric/reflexiv closure of the OR of the equivalences.
(define fgl-ev-context-equiv-symm ((ctx equiv-contextsp) x y)
  (or (fgl-ev-context-equiv-base ctx x y)
      (fgl-ev-context-equiv-base ctx y x))
  ///
  (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-context-equiv-symm fgl-ev-context-equiv-symm)
  (local (equiv-ev-fgl-ev-record-functional-subst
          fgl-ev-context-equiv-symm-func-inst
          cmr::equiv-ev-context-equiv-symm)))


(define fgl-ev-context-equiv-trace ((ctx equiv-contextsp) (trace true-listp))
  (if (atom (cdr trace))
      t
    (and (fgl-ev-context-equiv-symm ctx (car trace) (cadr trace))
         (fgl-ev-context-equiv-trace ctx (cdr trace))))
  ///
  (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-context-equiv-trace fgl-ev-context-equiv-trace)
  (local (equiv-ev-fgl-ev-record-functional-subst
          fgl-ev-context-equiv-trace-func-inst
          cmr::equiv-ev-context-equiv-trace)))


(defsection fgl-ev-context-equiv
  (defun-sk fgl-ev-context-equiv1 (ctx x y)
    (exists trace
            (and (consp trace)
                 (true-listp trace)
                 (equal (car trace) x)
                 (equal (car (last trace)) y)
                 (fgl-ev-context-equiv-trace ctx trace))))

  (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-context-equiv1 fgl-ev-context-equiv1)
  (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-context-equiv1-witness fgl-ev-context-equiv1-witness)
  (local (equiv-ev-fgl-ev-record-functional-subst
          fgl-ev-context-equiv1-func-inst
          cmr::equiv-ev-context-equiv1))

  (in-theory (disable fgl-ev-context-equiv1
                      fgl-ev-context-equiv1-suff))

  (define fgl-ev-context-equiv-witness ((ctx equiv-contextsp)
                                        x y)
    :returns (trace (and (consp trace) (true-listp trace)) :rule-classes :type-prescription)
    (let ((trace (true-list-fix (ec-call (fgl-ev-context-equiv1-witness (equiv-contexts-fix ctx) x y)))))
      (if (consp trace)
          trace
        (list x)))
    ///
    (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-context-equiv-witness fgl-ev-context-equiv-witness)
    (local (equiv-ev-fgl-ev-record-functional-subst
            fgl-ev-context-equiv-witness-func-inst
            cmr::equiv-ev-context-equiv-witness)))

  (define fgl-ev-context-equiv ((ctx equiv-contextsp)
                                  x y)
    (let ((trace (fgl-ev-context-equiv-witness ctx x y)))
      (and (equal (car trace) x)
           (equal (car (last trace)) y)
           (fgl-ev-context-equiv-trace ctx trace)))
    ///
    (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-context-equiv fgl-ev-context-equiv)
    (local (equiv-ev-fgl-ev-record-functional-subst
            fgl-ev-context-equiv-func-inst
            cmr::equiv-ev-context-equiv))))


(define fgl-ev-context-equiv-list ((contexts equiv-contextslist-p)
                                    (x true-listp)
                                    (y true-listp))
  (if (atom contexts)
      (acl2::nth-equiv-exec x y)
    (and (fgl-ev-context-equiv (car contexts) (car x) (car y))
         (fgl-ev-context-equiv-list (cdr contexts) (cdr x) (cdr y))))
    ///
    (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-context-equiv-list fgl-ev-context-equiv-list)
    (local (equiv-ev-fgl-ev-record-functional-subst
            fgl-ev-context-equiv-list-func-inst
            cmr::equiv-ev-context-equiv-list))

    (defthm fgl-ev-context-equiv-list-of-nil
      (equal (fgl-ev-context-equiv-list nil x y)
             (acl2::nth-equiv x y))))





(local (defthm kwote-lst-redef
         (equal (kwote-lst x)
                (if (atom x)
                    nil
                  (cons (pseudo-term-quote (car x))
                        (kwote-lst (cdr x)))))
         :hints(("Goal" :in-theory (enable kwote-lst pseudo-term-quote)))
         :rule-classes ((:definition :controller-alist ((kwote-lst t))))))

(local (defthm pseudo-term-listp-of-kwote-lst
         (pseudo-term-listp (kwote-lst x))))

(local (in-theory (disable (:d kwote-lst))))

(defsection fgl-ev-congruence-correct-p

  (defun-sk fgl-ev-congruence-correct-p1 (ctx fn arg-ctxs arity)
    (forall (args1 args2)
            (implies (and (fgl-ev-context-equiv-list arg-ctxs args1 args2)
                          (equal (len args1) (nfix arity))
                          (equal (len args2) (nfix arity)))
                     (fgl-ev-context-equiv ctx
                                             (fgl-ev (pseudo-term-fncall fn (kwote-lst args1)) nil)
                                             (fgl-ev (pseudo-term-fncall fn (kwote-lst args2)) nil))))
    :rewrite :direct)

  (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-congruence-correct-p1-witness
                                        fgl-ev-congruence-correct-p1-witness)
  (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-congruence-correct-p1 fgl-ev-congruence-correct-p1)
  (local (equiv-ev-fgl-ev-record-functional-subst
          fgl-ev-congruence-correct-p1-func-inst
          cmr::equiv-ev-congruence-correct-p1
          :other-hints
          (:computed-hint-replacement
           ((and stable-under-simplificationp
                 '(:in-theory (enable fgl-ev-congruence-correct-p1))))
           :in-theory (disable fgl-ev-congruence-correct-p1
                               fgl-ev-of-pseudo-term-fncall
                               fgl-ev-when-pseudo-term-fncall))))

  (in-theory (disable fgl-ev-congruence-correct-p1
                      fgl-ev-congruence-correct-p1-necc))


  (define fgl-ev-congruence-correct-p-witness ((ctx equiv-contextsp)
                                         (fn pseudo-fnsym-p)
                                         (arg-ctxs equiv-contextslist-p)
                                         (arity natp))
    :returns (mv (args1 true-listp :rule-classes :type-prescription)
                 (args2 true-listp :rule-classes :type-prescription))
    (b* (((mv args1 args2) (ec-call (fgl-ev-congruence-correct-p1-witness
                                     (equiv-contexts-fix ctx)
                                     (pseudo-fnsym-fix fn)
                                     (equiv-contextslist-fix arg-ctxs)
                                     (lnfix arity)))))
      (mbe :logic (mv (take arity args1)
                      (take arity args2))
           :exec (mv (take arity (true-list-fix args1))
                     (take arity (true-list-fix args2)))))
    ///
    (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-congruence-correct-p-witness fgl-ev-congruence-correct-p-witness)
    (local (equiv-ev-fgl-ev-record-functional-subst
            fgl-ev-congruence-correct-p-witness-func-inst
            cmr::equiv-ev-congruence-correct-p-witness))

    (defret len-of-<fn>
      (and (equal (len args1) (nfix arity))
           (equal (len args2) (nfix arity)))))

  (define fgl-ev-congruence-correct-p ((ctx equiv-contextsp)
                                         (fn pseudo-fnsym-p)
                                         (arg-ctxs equiv-contextslist-p)
                                         (arity natp))
    (b* (((mv args1 args2) (fgl-ev-congruence-correct-p-witness ctx fn arg-ctxs arity)))
      (implies (fgl-ev-context-equiv-list arg-ctxs args1 args2)
               (fgl-ev-context-equiv ctx
                                       (fgl-ev (pseudo-term-fncall fn (kwote-lst args1)) nil)
                                       (fgl-ev (pseudo-term-fncall fn (kwote-lst args2)) nil))))
    ///
    (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-congruence-correct-p fgl-ev-congruence-correct-p)
    (local (equiv-ev-fgl-ev-record-functional-subst
            fgl-ev-congruence-correct-p-func-inst
            cmr::equiv-ev-congruence-correct-p))))


(define fgl-ev-congruence-rule-correct-p ((rule cmr::congruence-rule-p))
  (b* (((cmr::congruence-rule rule)))
    (and (<= (len rule.arg-contexts) rule.arity)
         (ec-call (fgl-ev-congruence-correct-p (list rule.equiv-req)
                                               rule.fn rule.arg-contexts rule.arity))))
    ///
    (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-congruence-rule-correct-p fgl-ev-congruence-rule-correct-p)
    (local (equiv-ev-fgl-ev-record-functional-subst
            fgl-ev-congruence-rule-correct-p-func-inst
            cmr::equiv-ev-congruence-rule-correct-p)))


(defthm fgl-ev-congruence-correct-p-of-join-equiv-contextslists
  (let ((arg-ctxs (cmr::join-equiv-contextslists arg-ctxs1 arg-ctxs2)))
    (implies (and (fgl-ev-congruence-correct-p ctx fn arg-ctxs1 arity)
                  (fgl-ev-congruence-correct-p ctx fn arg-ctxs2 arity)
                  (<= (len arg-ctxs) (nfix arity)))
             (fgl-ev-congruence-correct-p ctx fn arg-ctxs arity)))
  :hints ((equiv-ev-fgl-ev-functional-subst-hint
           cmr::equiv-ev-congruence-correct-p-of-join-equiv-contextslists
           :subst ((fn fn) (arg-ctxs1 arg-ctxs1) (arg-ctxs2 arg-ctxs2)))))

(add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-falsify fgl-ev-falsify)
(add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-meta-extract-global-badguy fgl-ev-meta-extract-global-badguy)
(local (equiv-ev-fgl-ev-record-functional-subst fgl-ev-falsify-func-inst cmr::equiv-ev-falsify
                                                :other-hints (:computed-hint-replacement
                                                              ((and stable-under-simplificationp
                                                                    '(:use fgl-ev-falsify))))))
(local (equiv-ev-fgl-ev-record-functional-subst fgl-ev-meta-extract-global-badguy-func-inst
                                                cmr::equiv-ev-meta-extract-global-badguy
                                                :other-hints (:computed-hint-replacement
                                                              ((and stable-under-simplificationp
                                                                    '(:use fgl-ev-meta-extract-global-badguy))))))

(defret fgl-ev-congruence-rule-correct-p-of-<fn>
  (implies (and (fgl-ev-theoremp x)
                (fgl-ev-meta-extract-global-facts)
                (equal w (w state))
                (not cmr::errmsg))
           (fgl-ev-congruence-rule-correct-p cmr::rule))
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-congruence-rule-correct-p-of-<fn>))
  :fn cmr::parse-congruence-rule)





(defthm equiv-rel-term-of-unequiv
  (fgl-ev (cmr::equiv-rel-term 'unequiv) a)
  :hints(("Goal" :in-theory (enable cmr::equiv-rel-term))))

(defthm equiv-rel-term-of-iff
  (fgl-ev (cmr::equiv-rel-term 'iff) a)
  :hints(("Goal" :in-theory (enable cmr::equiv-rel-term))))



(defsection fgl-ev-context-fix

  (defchoose fgl-ev-context-fix1 (rep) (contexts x)
    (fgl-ev-context-equiv contexts x rep)
    :strengthen t)

  (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-context-fix1 fgl-ev-context-fix1)
  (local (equiv-ev-fgl-ev-record-functional-subst
          fgl-ev-context-fix1-func-inst
          cmr::equiv-ev-context-fix1
          :other-hints (:computed-hint-replacement
                        ('(:use ((:instance fgl-ev-context-fix1
                                  (contexts cmr::contexts)
                                  (contexts1 cmr::contexts1)
                                  (rep cmr::rep))))))))

  (define fgl-ev-context-fix ((contexts equiv-contextsp) x)
    :non-executable t
    (fgl-ev-context-fix1 (equiv-contexts-fix contexts) x)
    ///
    (in-theory (disable (fgl-ev-context-fix)))
    (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-context-fix fgl-ev-context-fix)
    (local (equiv-ev-fgl-ev-record-functional-subst
            fgl-ev-context-fix-func-inst
            cmr::equiv-ev-context-fix))))



(defsection fgl-ev-context-fix-list

  (defchoose fgl-ev-context-fix-list1 (rep) (contexts x)
    (fgl-ev-context-equiv-list contexts x rep)
    :strengthen t)

  (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-context-fix-list1 fgl-ev-context-fix-list1)
  (local (equiv-ev-fgl-ev-record-functional-subst
          fgl-ev-context-fix-list1-func-inst
          cmr::equiv-ev-context-fix-list1
          :other-hints (:computed-hint-replacement
                        ('(:use ((:instance fgl-ev-context-fix-list1
                                  (contexts cmr::contexts)
                                  (contexts1 cmr::contexts1)
                                  (rep cmr::rep))))))))

  (define fgl-ev-context-fix-list ((contexts equiv-contextslist-p) (x true-listp))
    :non-executable t
    (true-list-fix (fgl-ev-context-fix-list1 (equiv-contextslist-fix contexts) (true-list-fix x)))
    ///
    (in-theory (disable (fgl-ev-context-fix-list)))
    (add-equiv-ev-fgl-ev-functional-subst cmr::equiv-ev-context-fix-list fgl-ev-context-fix-list)
    (local (equiv-ev-fgl-ev-record-functional-subst
            fgl-ev-context-fix-list-func-inst
            cmr::equiv-ev-context-fix-list))))


(defsection fgl-ev-context-equiv
  (defthm fgl-ev-context-equiv-self
    (fgl-ev-context-equiv contexts x x)
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-context-equiv-reflexive
          :subst ((ctx contexts)))))

  (defthm fgl-ev-context-equiv-symmetric
    (implies (fgl-ev-context-equiv contexts x y)
             (fgl-ev-context-equiv contexts y x))
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-context-equiv-symmetric
          :subst ((ctx contexts)))))

  (defthm fgl-ev-context-equiv-trans
    (implies (and (fgl-ev-context-equiv contexts x y)
                  (fgl-ev-context-equiv contexts y z))
             (fgl-ev-context-equiv contexts x z))
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-context-equiv-transitive
          :subst ((ctx contexts)))))

  (defthmd fgl-ev-context-equiv-of-singleton
    (implies (fgl-ev-theoremp (cmr::equiv-rel-term equiv))
             (iff (fgl-ev-context-equiv (list equiv) x y)
                  (fgl-ev (pseudo-term-fncall equiv (list (pseudo-term-quote x)
                                                            (pseudo-term-quote y)))
                            nil)))
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-context-equiv-of-singleton
          :subst ((equiv equiv)))))

  (defthmd fgl-ev-context-equiv-when-singleton
    (implies (fgl-ev (pseudo-term-fncall equiv (list (pseudo-term-quote x)
                                                       (pseudo-term-quote y)))
                       nil)
             (fgl-ev-context-equiv (list equiv) x y))
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-context-equiv-when-singleton
          :subst ((equiv equiv)))))

  (defthm fgl-ev-context-equiv-equal
    (equal (fgl-ev-context-equiv nil x y)
           (equal x y))
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-context-equiv-equal)))

  (defthm fgl-ev-context-equiv-iff
    (equal (fgl-ev-context-equiv '(iff) x y)
           (iff* x y))
    :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-of-singleton))))

  (defthm fgl-ev-context-equiv-unequiv
    (equal (fgl-ev-context-equiv '(unequiv) x y)
           t)
    :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-of-singleton))))

  (defthm fgl-ev-context-equiv-list-equal
    (equal (fgl-ev-context-equiv '(equal) x y)
           (equal x y))
    :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-of-singleton))))

  (defthmd fgl-ev-context-equiv-by-singleton
    (implies (and (fgl-ev-context-equiv (list equiv) x y)
                  (member (pseudo-fnsym-fix equiv) (equiv-contexts-fix ctx)))
             (fgl-ev-context-equiv ctx x y))
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-context-equiv-by-singleton
          :subst ((equiv equiv)))))

  (defthm fgl-ev-context-equiv-when-member-iff
    (implies (and (member 'iff (equiv-contexts-fix contexts))
                  (iff* x y))
             (equal (fgl-ev-context-equiv contexts x y) t))
    :hints (("goal" :use ((:instance fgl-ev-context-equiv-by-singleton
                           (equiv 'iff) (ctx contexts))))))

  (defthm fgl-ev-context-equiv-when-member-unequiv
    (implies (member 'unequiv (equiv-contexts-fix contexts))
             (equal (fgl-ev-context-equiv contexts x y)
                    t))
    :hints (("goal" :use ((:instance fgl-ev-context-equiv-by-singleton
                           (equiv 'unequiv) (ctx contexts)))))))




(defsection fgl-ev-context-fix
  
  (defthm fgl-ev-context-fix-equiv
    (fgl-ev-context-equiv contexts x (fgl-ev-context-fix contexts x))
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-context-fix-equiv
          :subst ((contexts contexts)))))

  (defthm fgl-ev-context-fix-strengthen
    (implies (fgl-ev-context-equiv contexts x y)
             (equal (fgl-ev-context-fix contexts x) (fgl-ev-context-fix contexts y)))
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-context-fix-strengthen
          :subst ((contexts contexts))))
    :rule-classes nil)

  (defthm fgl-ev-context-fix-equiv-rev
    (fgl-ev-context-equiv contexts (fgl-ev-context-fix contexts x) x)
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-context-fix-equiv-rev
          :subst ((contexts contexts)))))

  (defthmd equal-of-fgl-ev-context-fix
    (iff (equal (fgl-ev-context-fix contexts x) (fgl-ev-context-fix contexts y))
         (fgl-ev-context-equiv contexts x y))
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equal-of-equiv-ev-context-fix
          :subst ((contexts contexts)))))

  (defthmd fgl-ev-context-equiv-is-equal-of-fixes
    (iff (fgl-ev-context-equiv contexts x y)
         (equal (fgl-ev-context-fix contexts x) (fgl-ev-context-fix contexts y)))
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-context-equiv-is-equal-of-fixes
          :subst ((contexts contexts)))))


  (defthm fgl-ev-context-fix-of-fgl-ev-context-fix
    (equal (fgl-ev-context-fix contexts (fgl-ev-context-fix contexts x))
           (fgl-ev-context-fix contexts x))
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-context-fix-of-equiv-ev-context-fix
          :subst ((contexts contexts)))))

  (defthm fgl-ev-context-fix-under-fgl-ev-context-equiv-1
    (equal (fgl-ev-context-equiv contexts (fgl-ev-context-fix contexts x) y)
           (fgl-ev-context-equiv contexts x y))
    :hints((equiv-ev-fgl-ev-functional-subst-hint
            cmr::equiv-ev-context-fix-under-equiv-ev-context-equiv-1
            :subst ((contexts contexts)))))

  (defthm fgl-ev-context-fix-under-fgl-ev-context-equiv-2
    (equal (fgl-ev-context-equiv contexts x (fgl-ev-context-fix contexts y))
           (fgl-ev-context-equiv contexts x y))
    :hints((equiv-ev-fgl-ev-functional-subst-hint
            cmr::equiv-ev-context-fix-under-equiv-ev-context-equiv-2
            :subst ((contexts contexts)))))

  (defthm fgl-ev-context-fix-of-equal
    (equal (fgl-ev-context-fix nil x) x)
    :hints((equiv-ev-fgl-ev-functional-subst-hint
            cmr::equiv-ev-context-fix-of-nil)))

  (defthm fgl-ev-context-fix-of-iff
    (iff (fgl-ev-context-fix '(iff) x) x)
    :hints (("goal" :use ((:instance fgl-ev-context-fix-equiv (contexts '(iff))))
             :in-theory (disable fgl-ev-context-fix-equiv
                                 fgl-ev-context-fix-equiv-rev
                                 fgl-ev-context-fix-under-fgl-ev-context-equiv-1
                                 fgl-ev-context-fix-under-fgl-ev-context-equiv-2))))

  (defthm fgl-ev-context-fix-iff-congruence
    (implies (iff x y)
             (equal (fgl-ev-context-fix '(iff) x)
                    (fgl-ev-context-fix '(iff) y)))
    :hints (("goal" :use ((:instance fgl-ev-context-equiv-is-equal-of-fixes
                           (contexts '(iff))))))
    :rule-classes :congruence)

  (defthm fgl-ev-context-fix-iff-of-nil
    (equal (fgl-ev-context-fix '(iff) nil) nil))



  (defthm fgl-ev-context-fix-of-unequiv
    (implies (syntaxp (not (equal x ''nil)))
             (equal (fgl-ev-context-fix '(unequiv) x)
                    (fgl-ev-context-fix '(unequiv) nil)))
    :hints (("goal" :use ((:instance fgl-ev-context-equiv-is-equal-of-fixes (contexts '(unequiv)) (y nil))))))

  (defthm fgl-ev-context-fix-when-member-unequiv
    (implies (and (syntaxp (not (equal x ''nil)))
                  (member 'unequiv (equiv-contexts-fix contexts)))
             (equal (fgl-ev-context-fix contexts x)
                    (fgl-ev-context-fix contexts nil)))
    :hints (("goal" :use ((:instance fgl-ev-context-equiv-is-equal-of-fixes (y nil))))))


  (defthm fgl-ev-context-fix-when-member-iff-nonnil
    (implies (and (syntaxp (not (equal x ''t)))
                  (member 'iff (equiv-contexts-fix contexts))
                  x)
             (equal (fgl-ev-context-fix contexts x)
                    (fgl-ev-context-fix contexts t)))
    :hints (("goal" :use ((:instance fgl-ev-context-equiv-is-equal-of-fixes (y t))))))

  (defthm fgl-ev-context-fix-when-member-iff-equiv
    (implies (and (member 'iff (equiv-contexts-fix contexts))
                  (iff* x y))
             (equal (equal (fgl-ev-context-fix contexts x)
                           (fgl-ev-context-fix contexts y))
                    t))
    :hints (("goal" :use ((:instance fgl-ev-context-equiv-is-equal-of-fixes))))))






(defthmd fgl-ev-congruence-correct-p-necc
  (implies (and (fgl-ev-congruence-correct-p ctx fn arg-ctxs arity)
                (fgl-ev-context-equiv-list arg-ctxs args1 args2)
                (equal (len args1) (nfix arity))
                (equal (len args2) (nfix arity)))
           (fgl-ev-context-equiv ctx
                                 (fgl-ev (pseudo-term-fncall fn (kwote-lst args1)) nil)
                                 (fgl-ev (pseudo-term-fncall fn (kwote-lst args2)) nil)))
  :hints((equiv-ev-fgl-ev-functional-subst-hint
          cmr::equiv-ev-congruence-correct-p-necc
          :subst ((fn fn) (arg-ctxs arg-ctxs)
                  (args1 args1) (args2 args2)))))




(define equiv-argcontexts-p (x)
  (or (eq x t) (equiv-contextslist-p x))
  ///
  (define equiv-argcontexts-fix ((x equiv-argcontexts-p))
    :returns (new-x equiv-argcontexts-p)
    (mbe :logic (if (eq x t) t (equiv-contextslist-fix x))
         :exec x)
    ///
    (defret equiv-argcontexts-fix-when-equiv-argcontexts-p
      (implies (equiv-argcontexts-p x)
               (equal (equiv-argcontexts-fix x) x)))

    (fty::deffixtype equiv-argcontexts
      :pred equiv-argcontexts-p
      :fix equiv-argcontexts-fix
      :equiv equiv-argcontexts-equiv
      :define t)))




(define equiv-argcontexts-first ((contexts equiv-argcontexts-p))
  :returns (first equiv-contextsp)
  :prepwork ((local (in-theory (enable equiv-argcontexts-p
                                       equiv-argcontexts-fix))))
  (if (eq contexts t) '(unequiv) (equiv-contexts-fix (car contexts))))

(define equiv-argcontexts-rest ((contexts equiv-argcontexts-p))
  :returns (rest equiv-argcontexts-p)
  :prepwork ((local (in-theory (enable equiv-argcontexts-p
                                       equiv-argcontexts-fix))))
  (if (eq contexts t) t (equiv-contextslist-fix (cdr contexts))))


(define fgl-ev-argcontexts-equiv ((contexts equiv-argcontexts-p) (x true-listp) (y true-listp))
  :prepwork ((local (in-theory (enable equiv-argcontexts-p
                                       equiv-argcontexts-fix))))
  :hooks nil
  (if (eq contexts t)
      t
    (fgl-ev-context-equiv-list contexts x y))
  ///
  (local (defthm nth-equiv-of-atoms
           (implies (and (atom x) (atom y))
                    (acl2::nth-equiv x y))
           :hints(("Goal" :in-theory (enable acl2::nth-equiv-recursive)))))

  (local (defthm fgl-ev-context-equiv-list-when-atoms
           (implies (and (atom x) (atom y))
                    (fgl-ev-context-equiv-list contexts x y))
           :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-list)))))

  (deffixequiv fgl-ev-argcontexts-equiv)

  (defthm fgl-ev-argcontexts-equiv-recursive
    (equal (fgl-ev-argcontexts-equiv contexts x y)
           (if (and (atom x) (atom y))
               t
             (and (fgl-ev-context-equiv (equiv-argcontexts-first contexts) (car x) (car y))
                  (fgl-ev-argcontexts-equiv (equiv-argcontexts-rest contexts) (cdr x) (cdr y)))))
    :hints(("Goal" :in-theory (enable fgl-ev-context-equiv-list
                                      equiv-argcontexts-first
                                      equiv-argcontexts-rest
                                      acl2::nth-equiv-recursive)))
    :rule-classes ((:definition :controller-alist ((fgl-ev-argcontexts-equiv nil t t)))))

  (defthm fgl-ev-argcontexts-equiv-when-not-t
    (implies (not (equal contexts t))
             (equal (fgl-ev-argcontexts-equiv contexts x y)
                    (fgl-ev-context-equiv-list contexts x y)))))





(defsection fgl-ev-argcontext-congruence-correct-p

  (defun-sk fgl-ev-argcontext-congruence-correct-p1 (ctx fn arg-ctxs arity)
    (forall (args1 args2)
            (implies (and (fgl-ev-argcontexts-equiv arg-ctxs args1 args2)
                          (equal (len args1) (nfix arity))
                          (equal (len args2) (nfix arity)))
                     (fgl-ev-context-equiv ctx
                                             (fgl-ev (pseudo-term-fncall fn (kwote-lst args1)) nil)
                                             (fgl-ev (pseudo-term-fncall fn (kwote-lst args2)) nil))))
    :rewrite :direct)

  (in-theory (disable fgl-ev-argcontext-congruence-correct-p1
                      fgl-ev-argcontext-congruence-correct-p1-necc))


  (define fgl-ev-argcontext-congruence-correct-p-witness ((ctx equiv-contextsp)
                                                           (fn pseudo-fnsym-p)
                                                           (arg-ctxs equiv-argcontexts-p)
                                                           (arity natp))
    :returns (mv (args1 true-listp :rule-classes :type-prescription)
                 (args2 true-listp :rule-classes :type-prescription))
    (b* (((mv args1 args2) (ec-call (fgl-ev-argcontext-congruence-correct-p1-witness
                                     (equiv-contexts-fix ctx)
                                     (pseudo-fnsym-fix fn)
                                     (equiv-argcontexts-fix arg-ctxs)
                                     (lnfix arity)))))
      (mbe :logic (mv (take arity args1)
                      (take arity args2))
           :exec (mv (take arity (true-list-fix args1))
                     (take arity (true-list-fix args2)))))
    ///
    (defret len-of-<fn>
      (and (equal (len args1) (nfix arity))
           (equal (len args2) (nfix arity)))))

  
  (local (defthm len-equal-0
           (equal (Equal (len x) 0)
                  (not (consp x)))))

  (local (defthm take-of-len-gen
           (implies (equal (nfix n) (len x))
                    (equal (take n x)
                           (true-list-fix x)))))

  (local (defthm kwote-lst-of-true-list-fix
           (Equal (kwote-lst (true-list-fix x)) (kwote-lst x))))

  (define fgl-ev-argcontext-congruence-correct-p ((ctx equiv-contextsp)
                                                  (fn pseudo-fnsym-p)
                                                  (arg-ctxs equiv-argcontexts-p)
                                                  (arity natp))
    (b* (((mv args1 args2) (fgl-ev-argcontext-congruence-correct-p-witness ctx fn arg-ctxs arity)))
      (implies (fgl-ev-argcontexts-equiv arg-ctxs args1 args2)
               (fgl-ev-context-equiv ctx
                                     (fgl-ev (pseudo-term-fncall fn (kwote-lst args1)) nil)
                                     (fgl-ev (pseudo-term-fncall fn (kwote-lst args2)) nil))))
    ///
    
    (defthmd fgl-ev-argcontext-congruence-correct-p-necc
      (implies (and (fgl-ev-argcontext-congruence-correct-p ctx fn arg-ctxs arity)
                    (fgl-ev-argcontexts-equiv arg-ctxs args1 args2)
                    (equal (len args1) (nfix arity))
                    (equal (len args2) (nfix arity)))
               (fgl-ev-context-equiv ctx
                                     (fgl-ev (pseudo-term-fncall fn (kwote-lst args1)) nil)
                                     (fgl-ev (pseudo-term-fncall fn (kwote-lst args2)) nil)))
      :hints(("Goal" :in-theory (enable fgl-ev-argcontext-congruence-correct-p-witness
                                        fgl-ev-argcontext-congruence-correct-p1)
              :use ((:instance fgl-ev-argcontext-congruence-correct-p1-necc
                     (args1 args1)
                     (args2 args2)
                     (fn (pseudo-fnsym-fix fn))
                     (arg-ctxs (equiv-argcontexts-fix arg-ctxs))
                     (arity (len args1))
                     (ctx (equiv-contexts-fix ctx))))
              :do-not-induct t))
      :otf-flg t))

  (defthm fgl-ev-argcontext-congruence-correct-p-when-not-t
    (implies (not (equal arg-ctxs t))
             (iff (fgl-ev-argcontext-congruence-correct-p ctx fn arg-ctxs arity)
                  (fgl-ev-congruence-correct-p ctx fn arg-ctxs arity)))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (or (assoc 'fgl-ev-argcontext-congruence-correct-p clause)
                               (assoc 'fgl-ev-congruence-correct-p clause))))
                   `(:expand (,lit)
                     :use ((:instance fgl-ev-argcontext-congruence-correct-p-necc
                            (args1 (mv-nth 0 (fgl-ev-congruence-correct-p-witness . ,(cdr lit))))
                            (args2 (mv-nth 1 (fgl-ev-congruence-correct-p-witness . ,(cdr lit)))))
                           (:instance fgl-ev-congruence-correct-p-necc
                            (args1 (mv-nth 0 (fgl-ev-argcontext-congruence-correct-p-witness . ,(cdr lit))))
                            (args2 (mv-nth 1 (fgl-ev-argcontext-congruence-correct-p-witness . ,(cdr lit))))))))))))

(define join-equiv-argcontexts ((ctx1 equiv-argcontexts-p)
                                (ctx2 equiv-argcontexts-p))
  :returns (ctx equiv-argcontexts-p)
  :prepwork ((local (in-theory (enable equiv-argcontexts-p equiv-argcontexts-fix))))
  (if (or (eq ctx1 t) (eq ctx2 t))
      t
    (cmr::join-equiv-contextslists ctx1 ctx2))
  ///
  (defthm fgl-ev-argcontext-congruence-correct-p-of-join-equiv-argcontexts
    (let ((arg-ctxs (join-equiv-argcontexts arg-ctxs1 arg-ctxs2)))
      (implies (and (fgl-ev-argcontext-congruence-correct-p ctx fn arg-ctxs1 arity)
                    (fgl-ev-argcontext-congruence-correct-p ctx fn arg-ctxs2 arity)
                    (<= (len arg-ctxs) (nfix arity)))
               (fgl-ev-argcontext-congruence-correct-p ctx fn arg-ctxs arity)))))
