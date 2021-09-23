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
(include-book "rewrite-base")
;; (local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (std::add-default-post-define-hook :fix))



(local (defthm svex-lookup-of-cons
         (equal (svex-lookup key (cons (cons var val) rest))
                (if (and (svar-p var)
                         (equal (svar-fix key) var))
                    (svex-fix val)
                  (svex-lookup key rest)))
         :hints(("Goal" :in-theory (enable svex-lookup)))))



(defcong set-equiv svex-alist-eval-equiv (svex-alist-reduce vars al) 1
  :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))


(local (defthm svex-alist-eval-equiv-of-cons
         (implies (svex-eval-equiv val1 val2)
                  (svex-alist-eval-equiv (cons (cons key val1) rest)
                                         (cons (cons key val2) rest)))
         :hints (("goal" :in-theory (enable svex-alist-eval-equiv
                                            svex-lookup)))
         :rule-classes :congruence))

(defsection netcomp-p-of-cons-compose

  (defthm netcomp-p-of-nil
    (netcomp-p nil network)
    :hints (("goal" :use ((:instance netcomp-p-suff
                           (comp nil) (decomp network)
                           (ordering nil)))
             :in-theory (enable neteval-ordering-compile))))

  (local (defthm svex-lookup-when-eval-equiv-compile
           (implies (and (svex-alist-eval-equiv network
                                                (neteval-ordering-compile order network1))
                         (svex-lookup var network))
                    (svex-eval-equiv (svex-lookup var network)
                                     ;; (svex-compose (svex-lookup var network1)
                                     (neteval-sigordering-compile
                                      (cdr (hons-assoc-equal (svar-fix var) order))
                                      var 0
                                      network1)))))

  

  (local (defthm svex-compose-of-svex-compose
           (svex-eval-equiv (svex-compose (svex-compose x al1) al2)
                            (svex-compose x (append (svex-alist-compose al1 al2) al2)))
           :hints(("Goal" :in-theory (enable svex-eval-equiv)))))

  (defthm netcomp-p-of-singleton-lookup
    (implies (and (netcomp-p lookup-network network1)
                  (svar-p var)
                  (svex-lookup var lookup-network))
             (netcomp-p (list (cons var (svex-lookup var lookup-network)))
                        network1))
    :hints (("goal" :use ((:instance netcomp-p-of-svex-alist-reduce
                           (keys (list var))
                           (x lookup-network)
                           (y network1)))
             :expand ((svex-alist-reduce (list var) lookup-network)
                      (svex-alist-reduce nil lookup-network))
             :in-theory (disable netcomp-p-of-svex-alist-reduce))))

  (local (defthm netcomp-p-of-singleton-compose
           (implies (and (netcomp-p compose-network network1)
                         (netcomp-p lookup-network network1)
                         (svar-p var)
                         (svex-lookup var lookup-network))
                    (netcomp-p (list (cons var (svex-compose (svex-lookup var lookup-network)
                                                             compose-network)))
                               network1))
           :hints (("goal" :use ((:instance netcomp-p-of-singleton-lookup
                                  (lookup-network (svex-alist-compose lookup-network compose-network))))
                    :in-theory (disable netcomp-p-of-singleton-lookup)))))

  (local (defthm cons-bad-pair-under-svex-alist-eval-equiv
           (implies (not (svar-p var))
                    (svex-alist-eval-equiv (cons (cons var val) rest) rest))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv svex-lookup)))))

  (defthm netcomp-p-of-cons-lookup
    (implies (and (netcomp-p lookup-network network1)
                  (netcomp-p rest-network network1)
                  (svex-lookup var lookup-network)
                  (svar-equiv var var1))
             (netcomp-p (cons (cons var (svex-lookup var1 lookup-network))
                              rest-network)
                        network1))
    :hints (("goal" :use ((:instance netcomp-p-of-append
                           (x (list (cons var (svex-lookup var lookup-network))))
                           (y rest-network)
                           (network network1)))
             :cases ((svar-p var)))))

  (defthm netcomp-p-of-cons-compose
    (implies (and (netcomp-p compose-network network1)
                  (netcomp-p lookup-network network1)
                  (netcomp-p rest-network network1)
                  (svex-lookup var lookup-network)
                  (svar-equiv var var1))
             (netcomp-p (cons (cons var (svex-compose (svex-lookup var1 lookup-network)
                                                      compose-network))
                              rest-network)
                        network1))
    :hints (("goal" :use ((:instance netcomp-p-of-append
                           (x (list (cons var (svex-compose (svex-lookup var lookup-network)
                                                            compose-network))))
                           (y rest-network)
                           (network network1)))
             :cases ((svar-p var)))))

  (defthm netcomp-p-of-svex-acons-lookup
    (implies (and (netcomp-p lookup-network network1)
                  (netcomp-p rest-network network1)
                  (svex-lookup var lookup-network))
             (netcomp-p (svex-acons var (svex-lookup var lookup-network)
                                    rest-network)
                        network1))
    :hints(("Goal" :in-theory (enable svex-acons))))

  (defthm netcomp-p-of-svex-acons-compose
    (implies (and (netcomp-p compose-network network1)
                  (netcomp-p lookup-network network1)
                  (netcomp-p rest-network network1)
                  (svex-lookup var lookup-network))
             (netcomp-p (svex-acons var (svex-compose (svex-lookup var lookup-network)
                                                      compose-network)
                                    rest-network)
                        network1))
    :hints(("Goal" :in-theory (enable svex-acons)))))



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

  ;; (defret svex-network-join-envs-of-<fn>
  ;;   (implies (svex-lookup var network)
  ;;            (svex-envs-equivalent (svex-network-join-envs new-network env1 env2)
  ;;                                  (svex-network-join-envs network env1 env2)))
  ;;   :hints(("Goal" :in-theory (enable svex-envs-equivalent))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-network-compose-step var composed-var network) 3
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong set-equiv svex-alist-eval-equiv (svex-network-compose-step var composed-var network) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret netcomp-p-of-<fn>
    (implies (and (netcomp-p network network1)
                  (svex-lookup var network))
             (netcomp-p new-network network1))))





(defthm svex-env-reduce-keys-of-alist-eval
  (svex-envs-equivalent (svex-env-reduce (svex-alist-keys network)
                                         (svex-alist-eval network env))
                        (svex-alist-eval network env))
  :hints(("Goal" :in-theory (enable svex-envs-equivalent))))


(define svex-network-compose-multistep ((vars svarlist-p)
                                        (composed-vars svarlist-p)
                                        (network svex-alist-p))
  :returns (new-network svex-alist-p)
  (append (svex-alist-compose (svex-alist-reduce vars network)
                              (svex-alist-reduce composed-vars network))
          (svex-alist-fix network))
  ///
  (defret svex-lookup-of-<fn>
    (equal (svex-lookup key new-network)
           (if (and (member-equal (svar-fix key) (svarlist-fix vars))
                    (svex-lookup key network))
               (svex-compose (svex-lookup key network)
                             (svex-alist-reduce composed-vars network))
             (svex-lookup key network))))

  ;; (defret svex-network-join-envs-of-<fn>
  ;;   (svex-envs-equivalent (svex-network-join-envs new-network env1 env2)
  ;;                         (svex-network-join-envs network env1 env2))
  ;;   :hints(("Goal" :in-theory (enable svex-envs-equivalent))))


  (defcong svex-alist-eval-equiv svex-alist-eval-equiv
    (svex-network-compose-multistep vars composed-var network) 3
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong set-equiv svex-alist-eval-equiv
    (svex-network-compose-multistep vars composed-var network) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong set-equiv svex-alist-eval-equiv
    (svex-network-compose-multistep vars composed-var network) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret netcomp-p-of-<fn>
    (implies (netcomp-p network network1)
             (netcomp-p new-network network))))



(defcong svex-alist-eval-equiv svex-alist-eval-equiv (append x y) 1
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))

(defcong svex-alist-eval-equiv svex-alist-eval-equiv (append x y) 2
  :hints ((and stable-under-simplificationp `(:expand (,(car (last clause)))))))


(define svex-network-compose-combostep ((var svar-p)
                                        (update-composed-vars svarlist-p)
                                        (network-composed-vars svarlist-p)
                                        (updates svex-alist-p)
                                        (network svex-alist-p))
  :guard (svex-lookup var network)
  :returns (new-network svex-alist-p)
  (cons (cons (svar-fix var)
              (svex-compose (svex-lookup var network)
                            (append (svex-alist-reduce update-composed-vars updates)
                                    (svex-alist-reduce network-composed-vars network))))
        (svex-alist-fix updates))
  ///
  (defret svex-lookup-of-<fn>
    (equal (svex-lookup key new-network)
           (if (equal (svar-fix key) (svar-fix var))
               (svex-compose (svex-lookup var network)
                             (append (svex-alist-reduce update-composed-vars updates)
                                     (svex-alist-reduce network-composed-vars network)))
             (svex-lookup key updates)))
    :hints(("Goal" :in-theory (enable svex-lookup))))

  ;; (defret svex-network-join-envs-of-<fn>
  ;;   (implies (svex-lookup var network)
  ;;            (svex-envs-equivalent (svex-network-join-envs new-network env1 env2)
  ;;                                  (svex-network-join-envs network env1 env2)))
  ;;   :hints(("Goal" :in-theory (enable svex-envs-equivalent))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv
    (svex-network-compose-combostep var update-composed-vars network-composed-vars updates network) 5
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv
    (svex-network-compose-combostep var update-composed-vars network-composed-vars updates network) 4
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong set-equiv svex-alist-eval-equiv
    (svex-network-compose-combostep var update-composed-vars network-composed-vars updates network) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong set-equiv svex-alist-eval-equiv
    (svex-network-compose-combostep var update-composed-vars network-composed-vars updates network) 3
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret netcomp-p-of-<fn>
    (implies (and (netcomp-p updates network1)
                  (netcomp-p network network1)
                  (svex-lookup var network))
             (netcomp-p new-network network1))))


;; Suppose A is the variables of the regular svex alist.  B is an isomorphic
;; set of variables, e.g., some of the variables of B are the same as the
;; variables of A, but some are disjoint part-selects of variables of A that
;; cover them, such that each variable of A can be expressed as some
;; concatenation of variables of B.  A->B has keys which are variables of A and
;; values which are the corresponding concatenations.  B->A has keys which are
;; variables of B and values which are the corresponding part-selects of
;; variables of A.

(deftagsum svar-decomp
  (:segment ((width posp :rule-classes :type-prescription)
             (var svar-p)
             (rest svar-decomp-p)))
  (:remainder ((var svar-p))))


(fty::defmap svar-decomptable :key-type svar :val-type svar-decomp :true-listp t)

(define svar-decomp-vars ((x svar-decomp-p))
  :measure (svar-decomp-count x)
  :returns (vars svarlist-p)
  (svar-decomp-case x
    :segment (cons x.var (svar-decomp-vars x.rest))
    :remainder (list x.var)))

(define svar-decomptable-vars ((x svar-decomptable-p))
  :returns (vars svarlist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable-vars (cdr x))))
    (append (svar-decomp-vars (cdar x))
            (svar-decomptable-vars (cdr x))))
  ///
  (local (in-theory (enable svar-decomptable-fix))))

(define svar-decomp-eval ((x svar-decomp-p)
                          (env svex-env-p))
  :returns (val 4vec-p)
  :measure (svar-decomp-count x)
  :verify-guards :after-returns
  (svar-decomp-case x
    :segment (4vec-concat
              (2vec x.width)
              (svex-env-lookup x.var env)
              (svar-decomp-eval x.rest env))
    :remainder (svex-env-lookup x.var env))
  ///
  (defthm svar-decomp-eval-of-acons-non-member
    (implies (not (member-equal (svar-fix var) (svar-decomp-vars x)))
             (equal (svar-decomp-eval x (svex-env-acons var val rest))
                    (svar-decomp-eval x rest)))
    :hints(("Goal" :in-theory (enable svar-decomp-vars))))

  (local (defthm member-alist-keys
           (iff (member k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defthm svar-decomp-eval-of-append-superset
    (implies (subsetp-equal (svar-decomp-vars x) (alist-keys (svex-env-fix env1)))
             (equal (svar-decomp-eval x (append env1 env2))
                    (svar-decomp-eval x env1)))
    :hints(("Goal" :in-theory (enable svar-decomp-vars svex-env-boundp))))

  (defthm svar-decomp-eval-of-append-non-intersecting
    (implies (not (intersectp-equal (svar-decomp-vars x) (alist-keys (svex-env-fix env1))))
             (equal (svar-decomp-eval x (append env1 env2))
                    (svar-decomp-eval x env2)))
    :hints(("Goal" :in-theory (enable svar-decomp-vars svex-env-boundp))))

  (defret <fn>-of-append-when-subsetp-first
    (implies (subsetp-equal (svar-decomp-vars x) (alist-keys (svex-env-fix env)))
             (equal (svar-decomp-eval x (append env env2))
                    val))
    :hints(("Goal" :in-theory (enable svar-decomp-vars)))))

(define svar-decomptable-eval ((x svar-decomptable-p)
                               (env svex-env-p))
  :returns (eval svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable-eval (cdr x) env)))
    (svex-env-acons (caar x) (svar-decomp-eval (cdar x) env)
                    (svar-decomptable-eval (cdr x) env)))
  ///
  (defthm svar-decomptable-eval-of-acons-non-member
    (implies (not (member-equal (svar-fix var) (svar-decomptable-vars x)))
             (equal (svar-decomptable-eval x (svex-env-acons var val rest))
                    (svar-decomptable-eval x rest)))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars))))

  (local (defthm member-alist-keys
           (iff (member k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defthm svar-decomptable-eval-of-append-superset
    (implies (subsetp-equal (svar-decomptable-vars x) (alist-keys (svex-env-fix env1)))
             (equal (svar-decomptable-eval x (append env1 env2))
                    (svar-decomptable-eval x env1)))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars svex-env-boundp))))

  (defthm svar-decomptable-eval-of-append-non-intersecting
    (implies (not (intersectp-equal (svar-decomptable-vars x) (alist-keys (svex-env-fix env1))))
             (equal (svar-decomptable-eval x (append env1 env2))
                    (svar-decomptable-eval x env2)))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars svex-env-boundp))))

  (local (in-theory (enable svar-decomptable-fix))))

(define svar-decomp->svex ((x svar-decomp-p))
  :returns (svex svex-p)
  :measure (svar-decomp-count x)
  :verify-guards :after-returns
  (svar-decomp-case x
    :segment (svcall concat
                     (svex-quote (2vec x.width))
                     (svex-var x.var)
                     (svar-decomp->svex x.rest))
    :remainder (svex-var x.var))
  ///
  (defret eval-of-<fn>
    (equal (svex-eval svex env)
           (svar-decomp-eval x env))
    :hints(("Goal" :in-theory (enable svar-decomp-eval svex-apply)
            :expand ((:free (x) (svex-eval (svex-var x) env))))))

  (defret svex-vars-of-<fn>
    (set-equiv (svex-vars svex)
               (svar-decomp-vars x))
    :hints(("Goal" :in-theory (enable svex-vars svar-decomp-vars)))))

(define svar-decomptable->subst ((x svar-decomptable-p))
  :returns (subst svex-alist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable->subst (cdr x))))
    (cons (cons (caar x) (svar-decomp->svex (cdar x)))
          (svar-decomptable->subst (cdr x))))
  ///
  (defret eval-of-<fn>
    (equal (svex-alist-eval subst env)
           (svar-decomptable-eval x env))
    :hints(("Goal" :in-theory (enable svar-decomptable-eval
                                      svex-env-acons
                                      svex-alist-eval)
            :induct t)))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys subst)
           (alist-keys (svar-decomptable-fix x)))
    :hints(("Goal" :in-theory (enable svex-alist-keys svar-decomptable-fix alist-keys))))

  (defret svex-lookup-of-<fn>
    (equal (svex-lookup v subst)
           (b* ((look (hons-assoc-equal (svar-fix v) x)))
             (and look
                  (svar-decomp->svex (cdr look))))))

  (local (in-theory (enable svar-decomptable-fix)))

  (defret svex-alist-vars-of-<fn>
    (set-equiv (svex-alist-vars subst)
               (svar-decomptable-vars x))
    :hints(("Goal" :in-theory (enable svex-alist-vars svar-decomptable-vars)))))



(define svar-decomp-extract ((x svar-decomp-p)
                             (env svex-env-p))
  :returns (new-env svex-env-p)
  :measure (svar-decomp-count x)
  :verify-guards :after-returns
  (svar-decomp-case x
    :segment (svex-env-acons x.var (4vec-zero-ext
                                    (2vec x.width)
                                    (svex-env-lookup x.var env))
                             (svar-decomp-extract x.rest env))
    :remainder (svex-env-acons x.var (svex-env-lookup x.var env) nil))
  ///
  (local (defthm 4vec-concat-of-4vec-zero-ext
           (equal (4vec-concat w (4vec-zero-ext w x) y)
                  (4vec-concat w x y))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-zero-ext)))))

  (defret svar-decomp-eval-of-<fn>
    (implies (no-duplicatesp-equal (svar-decomp-vars x))
             (equal (svar-decomp-eval x new-env)
                    (svar-decomp-eval x env)))
    :hints(("Goal" :in-theory (enable svar-decomp-eval svar-decomp-vars))))

  (defret alist-keys-of-<fn>
    (equal (alist-keys (svar-decomp-extract x env))
           (svar-decomp-vars x))
    :hints(("Goal" :in-theory (enable svar-decomp-vars svex-env-acons alist-keys)))))

(local (defthm alist-keys-of-append
         (equal (alist-keys (append x y))
                (append (alist-keys x) (alist-keys y)))
         :hints(("Goal" :in-theory (enable alist-keys)))))


(define svar-decomptable-extract ((x svar-decomptable-p)
                                  (env svex-env-p))
  :returns (new-env svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable-extract (cdr x) env)))
    (append (svar-decomp-extract (cdar x) env)
            (svar-decomptable-extract (cdr x) env)))
  ///

  (defret svar-decomptable-eval-of-<fn>
    (implies (no-duplicatesp-equal (svar-decomptable-vars x))
             (equal (svar-decomptable-eval x new-env)
                    (svar-decomptable-eval x env)))
    :hints(("Goal" :in-theory (enable svar-decomptable-eval svar-decomptable-vars))))

  (defret alist-keys-of-<fn>
    (equal (alist-keys (svar-decomptable-extract x env))
           (svar-decomptable-vars x))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars))))

  (local (in-theory (enable svar-decomptable-fix))))

;; (defprod svar-decomp-varspec
;;   ;; Look up a variable in the range of an svar-decomptable and get the
;;   ;; corresponding domain variable, position, and width
;;   ((domainvar svar-p)
;;    (pos natp :rule-classes :type-prescription)
;;    (width posp :rule-classes :type-prescription))
;;   :layout :list)


(define svar-decomp-has-var ((key svar-p)
                             (x svar-decomp-p))
  :returns (has-var (iff has-var
                         (member-equal (svar-fix key) (svar-decomp-vars x)))
                    :hints(("Goal" :induct <call>
                            :expand ((svar-decomp-vars x)))))
  :measure (svar-decomp-count x)
  (svar-decomp-case x
    :segment (or (equal (svar-fix key) x.var)
                 (svar-decomp-has-var key x.rest))
    :remainder (equal (svar-fix key) x.var)))

(define svar-decomptable-find-domainvar ((key svar-p)
                                         (x svar-decomptable-p))
  :returns (domainvar (iff (svar-p domainvar) domainvar))
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable-find-domainvar key (cdr x))))
    (if (svar-decomp-has-var key (cdar x))
        (caar x)
      (svar-decomptable-find-domainvar key (cdr x))))
  ///
  (local (in-theory (enable svar-decomptable-vars)))
  (defret <fn>-under-iff
    (iff domainvar
         (member-equal (svar-fix key) (svar-decomptable-vars x))))

  (defret lookup-exists-of-<fn>
    (implies domainvar
             (hons-assoc-equal domainvar x)))

  (local (defthm member-alist-keys
           (iff (member k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defret member-svar-decomp-vars-of-<fn>
    (implies (and (equal key1 (svar-fix key))
                  domainvar
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix x))))
             (member-equal key1 (svar-decomp-vars
                                 (cdr (hons-assoc-equal domainvar x)))))
    :hints(("Goal" :in-theory (enable svar-decomptable-fix alist-keys))))

  (local (defthm intersectp-when-member-both
           (implies (and (member-equal k y)
                         (member-equal k x))
                    (intersectp-equal x y))))

  (local (defthm member-svar-decomptable-vars-when-member-svar-decomp-vars-of-lookup
           (implies (and (svar-p k)
                         (hons-assoc-equal k decomp)
                         (member-equal key
                                       (svar-decomp-vars (cdr (hons-assoc-equal k decomp)))))
                    (member-equal key (svar-decomptable-vars decomp)))
           :hints(("Goal" :in-theory (enable svar-decomptable-vars)))))

  (defret member-svar-decomp-vars-of-<fn>-when-no-duplicate-vars
    (implies (and (svar-p key)
                  (hons-assoc-equal var (svar-decomptable-fix x))
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix x)))
                  (no-duplicatesp-equal (svar-decomptable-vars x)))
             (iff (member-equal key (svar-decomp-vars
                                      (cdr (hons-assoc-equal var x))))
                  (and domainvar
                       (equal var domainvar))))
    :hints(("Goal" :in-theory (enable svar-decomptable-fix alist-keys)
            :induct <call>
            :expand ((svar-decomptable-vars x)))))

  (local (in-theory (enable svar-decomptable-fix))))
  


(define svar-decomp-lookup ((key svar-p)
                            (x svar-decomp-p)
                            (position natp)
                            (val 4vec-p))
  :measure (svar-decomp-count x)
  :returns (new-val (iff (4vec-p new-val) new-val))
  (svar-decomp-case x
    :segment (if (equal (svar-fix key) x.var)
                 (4vec-part-select (2vec (lnfix position))
                                   (2vec x.width)
                                   val)
               (svar-decomp-lookup key x.rest (+ x.width (lnfix position)) val))
    :remainder (and (equal (svar-fix key) x.var)
                    (4vec-rsh (2vec (lnfix position)) val)))
  ///
  (defret <fn>-under-iff
    (iff new-val (member-equal (svar-fix key) (svar-decomp-vars x)))
    :hints(("Goal" 
            :induct <call>
            :expand ((svar-decomp-vars x)))))

  ;; (local (Defthm 4vec-part-select-of-x
  ;;          (implies (or (not (2vec-p pos))
  ;;                       (<= 0 (2vec->val pos)))
  ;;                   (equal (4vec-part-select pos width (4vec-x))
  ;;                          (4vec-x)))
  ;;          :hints(("Goal" :in-theory (enable 4vec-part-select
  ;;                                            4vec-rsh
  ;;                                            4vec-zero-ext)))))

  ;; (defthm svar-decomp-lookup-of-x
  ;;   (equal (svar-decomp-lookup key x pos (4vec-x))
  ;;          (and (member-equal (svar-fix key) (svar-decomp-vars x))
  ;;               (4vec-x)))
  ;;   :hints(("Goal" :in-theory (enable svar-decomp-vars))))
  )

(define svar-decomptable-lookup ((key svar-p)
                                 (x svar-decomptable-p)
                                 (env svex-env-p))
  :returns (new-val (iff (4vec-p new-val) new-val))
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable-lookup key (cdr x) env)))
    (or (svar-decomp-lookup key (cdar x) 0 (svex-env-lookup (caar x) env))
        (svar-decomptable-lookup key (cdr x) env)))
  ///
  (defret <fn>-under-iff
    (iff new-val (member-equal (svar-fix key) (svar-decomptable-vars x)))
    :hints(("Goal" 
            :induct <call>
            :expand ((svar-decomptable-vars x)))))

  (defthm svar-decomptable-lookup-of-acons-non-key
    (implies (not (hons-assoc-equal (svar-fix v) (svar-decomptable-fix decomp)))
             (equal (svar-decomptable-lookup key decomp (cons (cons v val) env))
                    (svar-decomptable-lookup key decomp env)))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

  (local (defthm member-alist-keys
           (iff (member k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defthm svar-decomptable-lookup-of-acons-when-key-not-in-new-var-decomp
    (implies (or (not (svar-p v))
                 (and (not (member-equal (svar-fix key)
                                         (svar-decomp-vars (cdr (hons-assoc-equal v decomp)))))
                      (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))))
             (equal (svar-decomptable-lookup key decomp (cons (cons v val) env))
                    (svar-decomptable-lookup key decomp env)))
    :hints(("Goal" :in-theory (enable svex-env-lookup alist-keys svar-decomptable-fix))))

  ;; (defthm svar-decomptable-lookup-empty-env
  ;;   (Equal (svar-decomptable-lookup key decomp nil)
  ;;          (and (member-equal (svar-fix key) (svar-decomptable-vars decomp))
  ;;               (4vec-x)))
  ;;   :hints(("Goal" :in-theory (enable svar-decomptable-vars))))

  (local (in-theory (enable svar-decomptable-fix)))


  (local (defthm svex-env-boundp-by-member-alist-keys
           (implies (member (svar-fix key) (alist-keys (svex-env-fix env)))
                    (svex-env-boundp key env))
           :hints(("Goal" :in-theory (enable svex-env-boundp alist-keys)))))

  (defthm svar-decomptable-lookup-of-append-env-when-alist-keys-subsetp
    (implies (subsetp-equal (alist-keys (svar-decomptable-fix x)) (alist-keys (svex-env-fix env)))
             (equal (svar-decomptable-lookup key x (append env rest))
                    (svar-decomptable-lookup key x env)))
    :hints(("Goal" :in-theory (e/d (alist-keys) (member-alist-keys))))))
  

(define svar-decomp-inverse-env ((x svar-decomp-p)
                                 (position natp)
                                 (val 4vec-p))
  :measure (svar-decomp-count x)
  :returns (env svex-env-p)
  :verify-guards :after-returns
  :prepwork ()
  (svar-decomp-case x
    :segment (svex-env-acons x.var (4vec-part-select
                                    (2vec (lnfix position))
                                    (2vec x.width)
                                    val)
                             (svar-decomp-inverse-env x.rest
                                                      (+ x.width (lnfix position))
                                                      val))
    :remainder (svex-env-acons x.var (4vec-rsh (2vec (lnfix position)) val) nil))
  ///
  (local (defthm concat-part-select-rsh
           (implies (and (natp pos)
                         (natp w))
                    (equal (4vec-concat (2vec w) (4vec-part-select (2vec pos) (2vec w) val) (4vec-rsh (2vec (+ pos w)) val))
                           (4vec-rsh (2vec pos) val)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-part-select 4vec-rsh 4vec-zero-ext 4vec-shift-core))
                  (bitops::logbitp-reasoning))))

  (defret svar-decomp-eval-with-<fn>
    (implies (no-duplicatesp-equal (svar-decomp-vars x))
             (equal (svar-decomp-eval x env)
                    (4vec-rsh (2vec (lnfix position)) val)))
    :hints(("Goal" :in-theory (enable svar-decomp-eval no-duplicatesp-equal svar-decomp-vars))))

  (local (defthm concat-of-part-select
           (implies (and (natp width)
                         (integerp position)
                         (<= width position))
                    (equal (4vec-part-select (2vec position) (2vec width1) (4vec-concat (2vec width) val1 val2))
                           (4vec-part-select (2vec (- position width)) (2vec width1) val2)))
           :hints(("Goal" :in-theory (enable 4vec-part-select 4vec-concat 4vec-zero-ext 4vec-shift-core 4vec-rsh)))))
                           
           

  (defthm svar-decomp-inverse-env-of-concat
    (implies (and (natp width)
                  (integerp position)
                  (<= width position))
             (equal (svar-decomp-inverse-env x position (4vec-concat (2vec width) val1 val2))
                    (svar-decomp-inverse-env x (- position width) val2))))
           
  (local (defthm equal-of-4vec-concat-strong
           (implies (natp w)
                    (equal (equal val (4vec-concat (2vec w) val1 val2))
                           (and (4vec-p val)
                                (equal (4vec-zero-ext (2vec w) val)
                                       (4vec-zero-ext (2vec w) val1))
                                (equal (4vec-rsh (2vec w) val)
                                       (4vec-fix val2)))))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-zero-ext 4vec-shift-core 4vec-rsh))
                  (bitops::logbitp-reasoning))))
                                        

  (defret <fn>-of-svar-decomp-eval
    ;; :pre-bind ((val (svar-decomp-eval x env1)))
    (implies (and (no-duplicatesp-equal (svar-decomp-vars x))
                  (equal (4vec-rsh (2vec (nfix position)) val)
                         (svar-decomp-eval x env1)))
             (equal env (svar-decomp-extract x env1)))
    :hints(("Goal" :in-theory (enable svar-decomp-eval no-duplicatesp-equal svar-decomp-vars
                                      svar-decomp-extract)
            :induct <call>
            :expand ((:free (val) <call>)))
           (and stable-under-simplificationp
                '(:in-theory (enable svex-env-acons 4vec-part-select)))))

  (defret <fn>-of-svar-decomp-eval-0
    :pre-bind ((val (svar-decomp-eval x env1))
               (position 0))
    (implies (no-duplicatesp-equal (svar-decomp-vars x))
             (equal env (svar-decomp-extract x env1)))
    :hints (("goal" :use ((:instance <fn>-of-svar-decomp-eval
                           (position 0)
                           (val (svar-decomp-eval x env1)))))))

  (defret alist-keys-of-<fn>
    (equal (alist-keys env)
           (svar-decomp-vars x))
    :hints(("Goal" :in-theory (enable svar-decomp-vars alist-keys svex-env-acons))))

  (defret lookup-in-<fn>
    (equal (svex-env-lookup key env)
           (if (member-equal (svar-fix key) (svar-decomp-vars x))
               (svar-decomp-lookup key x position val)
             (4vec-x)))
    :hints(("Goal" :in-theory (enable svar-decomp-lookup
                                      svar-decomp-vars)))))


(define svar-decomptable-inverse-env ((x svar-decomptable-p)
                                      (env svex-env-p))
  :returns (new-env svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable-inverse-env (cdr x) env)))
    (append (svar-decomp-inverse-env (cdar x) 0 (svex-env-lookup (caar x) env))
            (svar-decomptable-inverse-env (cdr x) env)))
  ///

  (defret svar-decomptable-eval-with-<fn>
    (implies (no-duplicatesp-equal (svar-decomptable-vars x))
             (equal (svar-decomptable-eval x new-env)
                    (svex-env-extract (alist-keys (svar-decomptable-fix x)) env)))
    :hints(("Goal" :in-theory (enable svar-decomptable-eval svar-decomptable-vars alist-keys
                                      svex-env-extract svex-env-acons)
            :induct <call>
            :expand ((svar-decomptable-fix x)))))
                           
  (defthm svar-decomptable-inverse-env-of-svex-env-acons-non-member
    (implies (not (member (svar-fix v) (alist-keys (svar-decomptable-fix x))))
             (equal (svar-decomptable-inverse-env x (svex-env-acons v val env))
                    (svar-decomptable-inverse-env x env)))
    :hints(("Goal" :in-theory (enable svar-decomptable-fix alist-keys))))

  (defret <fn>-of-svar-decomptable-eval
    :pre-bind ((env (svar-decomptable-eval x env1)))
    (implies (and (no-duplicatesp-equal (svar-decomptable-vars x))
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix x))))
             (equal new-env (svar-decomptable-extract x env1)))
    :hints(("Goal" :in-theory (enable svar-decomptable-eval
                                      svar-decomptable-vars
                                      svar-decomptable-extract
                                      svar-decomptable-fix
                                      alist-keys))))

  (defret alist-keys-of-<fn>
    (equal (alist-keys new-env)
           (svar-decomptable-vars x))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars))))

  

  (local (defthm member-alist-keys
           (iff (member k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (local (defthm svex-env-boundp-is-member-alist-keys
           (iff (svex-env-boundp key x)
                (member-equal (svar-fix key) (alist-keys (svex-env-fix x))))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))

  (defret lookup-in-<fn>
    (equal (svex-env-lookup key new-env)
           (if (member-equal (svar-fix key) (svar-decomptable-vars x))
               (svar-decomptable-lookup key x env)
             (4vec-x)))
    :hints(("Goal" :in-theory (enable svar-decomptable-lookup
                                      svar-decomptable-vars))))

  (local (in-theory (enable svar-decomptable-fix))))
  

(define svar-decomp->inverse ((x svar-decomp-p)
                              (position natp)
                              (val svex-p))
  :returns (alist svex-alist-p)
  :measure (svar-decomp-count x)
  (svar-decomp-case x
    :segment (cons (cons x.var (svcall partsel
                                       (svex-quote (2vec (lnfix position)))
                                       (svex-quote (2vec x.width))
                                       val))
                   (svar-decomp->inverse x.rest
                                         (+ x.width (lnfix position))
                                         val))
    :remainder (list (cons x.var (svcall rsh (svex-quote (2vec (lnfix position))) val))))
  ///
  (defret eval-of-<fn>
    (equal (svex-alist-eval alist env)
           (svar-decomp-inverse-env x position (svex-eval val env)))
    :hints(("Goal" :in-theory (enable svar-decomp-inverse-env svex-apply svex-alist-eval
                                      svex-env-acons))))

  (defthm svar-decomp-svex-of-inverse
    (implies (no-duplicatesp-equal (svar-decomp-vars x))
             (svex-eval-equiv (svex-compose (svar-decomp->svex x) (svar-decomp->inverse x position val))
                              (svcall rsh (svex-quote (2vec (nfix position))) val)))
    :hints(("Goal" :in-theory (enable svex-eval-equiv svex-apply))))

  (defret svex-lookup-under-iff-of-<fn>
    (iff (svex-lookup key alist)
         (member-equal (svar-fix key) (svar-decomp-vars x)))
    :hints(("Goal" :in-theory (enable svar-decomp-vars))))
  
  (defret eval-lookup-of-<fn>
    (equal (svex-eval (svex-lookup key alist) env)
           (if (member-equal (svar-fix key) (svar-decomp-vars x))
               (svar-decomp-lookup key x position (svex-eval val env))
             (4vec-x)))
    :hints (("goal" :use ((:instance svex-env-lookup-of-svex-alist-eval
                           (k key)
                           (x alist)))
             :in-theory (disable svex-env-lookup-of-svex-alist-eval)
             :do-not-induct t)))

  (local (Defthm cdr-hons-assoc-equal-when-svex-alist-p
           (implies (svex-alist-p x)
                    (iff (cdr (hons-assoc-equal k x))
                         (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable svex-alist-p)))))

  (local (defthm svar-p-when-lookup-in-svex-alist
           (implies (and (hons-assoc-equal k x)
                         (svex-alist-p x))
                    (svar-p k))))

  (defret hons-assoc-equal-of-<fn>
    (iff (hons-assoc-equal key alist)
         (and (svar-p key)
              (member-equal key (svar-decomp-vars x))))
    :hints (("goal" :use svex-lookup-under-iff-of-<fn>
             :in-theory (e/d (svex-lookup)
                             (svex-lookup-under-iff-of-<fn>))
             :do-not-induct t)))

  (local (defthm not-hons-assoc-equal-when-not-svar-p
           (implies (and (svex-alist-p x)
                         (not (svar-p k)))
                    (not (hons-assoc-equal k x)))))
  

  (defret svex-eval-cdr-hons-assoc-equal-of-<fn>
    (equal (svex-eval (cdr (hons-assoc-equal key alist)) env)
           (if (and (svar-p key)
                    (member-equal key (svar-decomp-vars x)))
               (svar-decomp-lookup key x position (svex-eval val env))
             (4vec-x)))
    :hints (("goal" :use eval-lookup-of-<fn>
             :in-theory (e/d (svex-lookup)
                             (eval-lookup-of-<fn>))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:cases ((svar-p key))))))

  (defret svex-alist-keys-of-<fn>
    (equal (Svex-alist-keys alist)
           (svar-decomp-vars x))
    :hints(("Goal" :in-theory (enable svar-decomp-vars svex-alist-keys)))))


(defthm svex-alist-keys-of-append
  (equal (svex-alist-keys (append x y))
         (append (svex-alist-keys x)
                 (svex-alist-keys y)))
  :hints(("Goal" :in-theory (enable svex-alist-keys))))

(define svar-decomptable->inverse ((x svar-decomptable-p))
  :returns (alist svex-alist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svar-decomptable->inverse (cdr x))))
    (append (svar-decomp->inverse (cdar x) 0 (svex-var (caar x)))
            (svar-decomptable->inverse (cdr x))))
  ///
  (defret eval-of-<fn>
    (equal (svex-alist-eval alist env)
           (svar-decomptable-inverse-env x env))
    :hints(("Goal" :in-theory (enable svar-decomptable-inverse-env svex-alist-eval)
            :induct <call>
            :expand ((:free (v) (svex-eval (svex-var v) env))))))

  (local (defthm svex-alist-eval-of-pairlis$-vars
           (implies (svarlist-p vars)
                    (equal (svex-alist-eval (pairlis$ vars (svarlist->svexes vars)) env)
                           (svex-env-extract vars env)))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-extract svarlist->svexes svex-eval)))))

  (local (defthm svarlist-p-keys-of-svar-decomptable
           (implies (svar-decomptable-p x)
                    (svarlist-p (alist-keys x)))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defthm svar-decomptable-svex-of-inverse
    (implies (no-duplicatesp-equal (svar-decomptable-vars x))
             (svex-alist-eval-equiv (svex-alist-compose (svar-decomptable->subst x) (svar-decomptable->inverse x))
                                    (svex-identity-subst (alist-keys (svar-decomptable-fix x)))))
    :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent)
            :do-not-induct t)))

  (defret svex-lookup-under-iff-of-<fn>
    (iff (svex-lookup key alist)
         (member-equal (svar-fix key) (svar-decomptable-vars x)))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars))))

  (defret eval-lookup-of-<fn>
    (equal (svex-eval (svex-lookup key alist) env)
           (if (member-equal (svar-fix key) (svar-decomptable-vars x))
               (svar-decomptable-lookup key x env)
             (4vec-x)))
    :hints (("goal" :use ((:instance svex-env-lookup-of-svex-alist-eval
                           (k key)
                           (x alist)))
             :in-theory (disable svex-env-lookup-of-svex-alist-eval)
             :do-not-induct t)))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys alist)
           (svar-decomptable-vars x))
    :hints(("Goal" :in-theory (enable svar-decomptable-vars))))

  (local (in-theory (enable svar-decomptable-fix))))



(local (defthm member-alist-keys
         (iff (member k (alist-keys x))
              (hons-assoc-equal k x))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(local (Defthm svex-lookup-when-subsetp-alist-keys
         (implies (and (subsetp set (svex-alist-keys x))
                       (member-equal (svar-fix key) set))
                  (svex-lookup key x))
         :hints(("Goal" :in-theory (enable svex-alist-keys svex-lookup)))))

(define svex-alist-decomptable-decompose ((x svex-alist-p)
                                          (decomp svar-decomptable-p))
  ;; Just affects the keys, not the values
  :returns (new-x svex-alist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svex-alist-decomptable-decompose (cdr x) decomp))
       ((cons var val) (car x))
       (look (hons-assoc-equal var (svar-decomptable-fix decomp)))
       ((unless look)
        (cons (cons var (svex-fix val))
              (svex-alist-decomptable-decompose (cdr x) decomp))))
    (append (svar-decomp->inverse (cdr look) 0 val)
            (svex-alist-decomptable-decompose (cdr x) decomp)))
  ///
  (local (defthm svex-p-lookup-in-svex-alist
           (implies (and (svex-alist-p x)
                         (hons-assoc-equal k x))
                    (svex-p (cdr (hons-assoc-equal k x))))
           :hints(("Goal" :in-theory (enable svex-alist-p)))))

  (local (defthm hons-assoc-equal-of-append
           (equal (hons-assoc-equal k (append x y))
                  (or (hons-assoc-equal k x)
                      (hons-assoc-equal k y)))))

  (local (defthm intersectp-when-member-both
           (implies (and (member-equal k y)
                         (member-equal k x))
                    (intersectp-equal x y))))

  (local (defthm member-svar-decomptable-vars-when-member-svar-decomp-vars-of-lookup
           (implies (and (svar-p k)
                         (hons-assoc-equal k decomp)
                         (member-equal key
                                       (svar-decomp-vars (cdr (hons-assoc-equal k decomp)))))
                    (member-equal key (svar-decomptable-vars decomp)))
           :hints(("Goal" :in-theory (enable svar-decomptable-vars)))))

  (local (defthm svar-decomptable-lookup-when-var-in-look
           (implies (and (svar-p k)
                         (hons-assoc-equal k decomp)
                         ;; (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))
                         (member-equal (svar-fix key)
                                       (svar-decomp-vars (cdr (hons-assoc-equal k decomp))))
                         (no-duplicatesp-equal (svar-decomptable-vars decomp)))
                    (equal (svar-decomptable-lookup key decomp env)
                           (svar-decomp-lookup key (cdr (hons-assoc-equal k decomp))
                                               0 (svex-env-lookup k env))))
           :hints(("Goal" :in-theory (enable svar-decomptable-lookup svar-decomptable-vars
                                             svar-decomptable-fix alist-keys)))))

  (local (defthm svex-env-lookup-of-cons
           (equal (svex-env-lookup k (cons (cons key val) env))
                  (if (and (svar-p key) (equal (svar-fix k) key))
                      (4vec-fix val)
                    (svex-env-lookup k env)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))
                        

  (defret eval-svex-lookup-of-<fn>
    (implies (and (not (intersectp-equal (svex-alist-keys x)
                                         (svar-decomptable-vars decomp)))
                  (no-duplicatesp-equal (svar-decomptable-vars decomp))
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp))))
             (equal (svex-eval (svex-lookup key new-x) env)
                    (cond ((member-equal (svar-fix key) (svar-decomptable-vars decomp))
                           (if (svex-lookup (svar-decomptable-find-domainvar key decomp)
                                            x)
                               (svar-decomptable-lookup key decomp (svex-alist-eval x env))
                             (4vec-x)))
                          ((member-equal (svar-fix key) (alist-keys (svar-decomptable-fix decomp)))
                           (4vec-x))
                          (t (svex-eval (svex-lookup key x) env)))))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-keys svex-alist-eval))))

  (local (defthm cdr-hons-assoc-equal-under-iff-in-svex-alist
           (implies (svex-alist-p x)
                    (iff (cdr (hons-assoc-equal k x))
                         (hons-assoc-equal k x)))))

  (defret svex-lookup-under-iff-of-<fn>
    (implies (and (not (intersectp-equal (svex-alist-keys x)
                                         (svar-decomptable-vars decomp)))
                  (no-duplicatesp-equal (svar-decomptable-vars decomp))
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp))))
             (iff (svex-lookup key new-x)
                  (cond ((member-equal (svar-fix key) (svar-decomptable-vars decomp))
                         (svex-lookup (svar-decomptable-find-domainvar key decomp)
                                      x))
                        ((member-equal (svar-fix key) (alist-keys (svar-decomptable-fix decomp)))
                         nil)
                        (t (svex-lookup key x)))))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-keys svex-alist-eval))))




  (defthm alist-keys-of-svex-alist-eval
    (equal (alist-keys (svex-alist-eval x env))
           (svex-alist-keys x))
    :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-eval alist-keys))))

  (defret <fn>-in-terms-of-svar-decomptable->inverse
    (implies (and (not (intersectp-equal (svex-alist-keys x)
                                         (svar-decomptable-vars decomp)))
                  (no-duplicatesp-equal (svar-decomptable-vars decomp))
                  (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))
                  (subsetp-equal (alist-keys (svar-decomptable-fix decomp))
                                 (svex-alist-keys x)))
             (svex-alist-eval-equiv new-x
                                    (append (svex-alist-compose (svar-decomptable->inverse decomp) x)
                                            (svex-alist-removekeys (alist-keys (svar-decomptable-fix decomp)) x))))
    :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                      svex-eval-equiv)
            :do-not-induct t)))

  (local (in-theory (enable svex-alist-fix))))




(defthm svex-alist-eval-equiv-of-compose-nil
  (svex-alist-eval-equiv (svex-alist-compose x nil) x)
  :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent
                                    svex-alist-eval))))


(defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-removekeys keys x) 2
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))

(defthm svex-alist-compose-nil
  (equal (svex-alist-compose nil a) nil)
  :hints(("Goal" :in-theory (enable svex-alist-compose))))

(defthm svex-alist-removekeys-of-nil
  (equal (svex-alist-removekeys keys nil) nil)
  :hints(("Goal" :in-theory (enable svex-alist-removekeys))))

(define svex-alist-to-decomp ((x svex-alist-p)
                              (decomp svar-decomptable-p))
  :returns (new-x svex-alist-p)
  (svex-alist-decomptable-decompose (svex-alist-compose x (svar-decomptable->subst decomp)) decomp))


(define svex-alist-decomptable-recompose ((x svex-alist-p)
                                          (decomp svar-decomptable-p))
  :returns (new-x svex-alist-p)
  (append (svex-alist-removekeys (svar-decomptable-vars decomp) x)
          (svex-alist-compose (svar-decomptable->subst decomp) x))
  ///
  (defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-decomptable-recompose x decomp) 1)
  (defthm svex-alist-decomptable-recompose-of-nil
    (svex-alist-eval-equiv (svex-alist-decomptable-recompose nil decomp)
                           (svar-decomptable->subst decomp))))


(define svex-alist-from-decomp ((x svex-alist-p)
                                (decomp svar-decomptable-p))
  :returns (new-x svex-alist-p)
  (svex-alist-decomptable-recompose (svex-alist-compose x (svar-decomptable->inverse decomp))
                                    decomp)
  ///
  (defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-from-decomp x decomp) 1)
  (defthm svex-alist-from-decomp-of-nil
    (svex-alist-eval-equiv (svex-alist-from-decomp nil decomp)
                           (svar-decomptable->subst decomp))))
  

(defthm svex-alist-keys-of-svex-alist-compose
  (Equal (svex-alist-keys (svex-alist-compose x a))
         (svex-alist-keys x))
  :hints(("Goal" :in-theory (enable svex-alist-compose
                                    svex-alist-keys))))

(defthm svex-alist-compose-of-append
  (equal (svex-alist-compose (append x y) a)
         (append (svex-alist-compose x a)
                 (svex-alist-compose y a)))
  :hints(("Goal" :in-theory (enable svex-alist-compose svex-acons))))

;; (local
;;  (defthm svex-alist-removekeys-of-cons-member
;;    (implies (or (member-equal (car pair) (svarlist-fix vars))
;;                 (not (consp pair))
;;                 (not (svar-p (car pair))))
;;             (equal (svex-alist-removekeys vars (cons pair y))
;;                    (svex-alist-removekeys vars y)))
;;    :hints(("Goal" :in-theory (enable svex-alist-removekeys)))))

(defthm svex-alist-removekeys-of-append-subset
  (implies (subsetp-equal (svex-alist-keys x) (svarlist-fix vars))
           (equal (svex-alist-removekeys vars (append x y))
                  (svex-alist-removekeys vars y)))
  :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-removekeys))))

(defthm svex-alist-removekeys-of-non-intersect
  (implies (not (intersectp-equal (svex-alist-keys x) (svarlist-fix vars)))
           (equal (svex-alist-removekeys vars x)
                  (svex-alist-fix x)))
  :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-removekeys
                                    svex-alist-fix))))

;; (local (defthm consp-hons-assoc-equal
;;          (iff (consp (hons-assoc-equal k a))
;;               (hons-assoc-equal k a))))



(std::defret-mutual svex-eval-of-append-when-subsetp-first
  (defret <fn>-of-append-when-subsetp-first
    (implies (subsetp-equal (svex-vars x) (alist-keys (svex-env-fix env)))
             (equal (svex-eval x (append env env2))
                    val))
    :hints ('(:expand ((:free (env) <call>)
                       (svex-vars x)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-boundp))))
    :fn svex-eval)
  (defret <fn>-of-append-when-subsetp-first
    (implies (subsetp-equal (svexlist-vars x) (alist-keys (svex-env-fix env)))
             (equal (svexlist-eval x (append env env2))
                    vals))
    :hints ('(:expand ((:free (env) <call>)
                       (svexlist-vars x))))
    :fn svexlist-eval)
  :mutual-recursion svex-eval)

(local
 (std::defret-mutual svex-eval-of-special-append
   (defret <fn>-of-special-append
     (implies (not (intersectp-equal (alist-keys (svex-env-fix env2)) (svex-vars x)))
              (equal (svex-eval x (append (svex-env-extract keys env) env2 env))
                     val))
     :hints ('(:expand ((:free (env) <call>)
                        (svex-vars x)))
             (and stable-under-simplificationp
                  '(:in-theory (enable svex-env-boundp))))
     :fn svex-eval)
   (defret <fn>-of-special-append
     (implies (not (intersectp-equal (alist-keys (svex-env-fix env2)) (svexlist-vars x)))
              (equal (svexlist-eval x (append (svex-env-extract keys env) env2 env))
                     vals))
     :hints ('(:expand ((:free (env) <call>)
                        (svexlist-vars x))))
     :fn svexlist-eval)
   :mutual-recursion svex-eval))


(defret <fn>-of-special-append
  (implies (not (intersectp-equal (alist-keys (svex-env-fix env2)) (svex-alist-vars x)))
           (equal (svex-alist-eval x (append (svex-env-extract keys env) env2 env))
                  result))
  :hints (("goal" :in-theory (enable svex-alist-eval svex-alist-vars)))
  :fn svex-alist-eval)

(defthm svex-alist-eval-of-append-when-subsetp-first
  (implies (subsetp (svex-alist-vars x) (alist-keys (svex-env-fix a)))
           (equal (svex-alist-eval x (append a b))
                  (svex-alist-eval x a)))
  :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vars))))
  

(defthm svex-alist-compose-of-append-when-subsetp-first
  (implies (subsetp (svex-alist-vars x) (svex-alist-keys a))
           (svex-alist-eval-equiv (svex-alist-compose x (append a b))
                                  (svex-alist-compose x a)))
  :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent))))

(defthm svex-alist-eval-of-svex-alist-removekeys
  (equal (svex-alist-eval (svex-alist-removekeys vars x) a)
         (svex-env-removekeys vars (svex-alist-eval x a)))
  :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-removekeys svex-env-removekeys))))


(defthm from-decomp-of-to-decomp
  (implies (and (not (intersectp-equal (svex-alist-keys x)
                                       (svar-decomptable-vars decomp)))
                (not (intersectp-equal (svex-alist-vars x)
                                       (svar-decomptable-vars decomp)))
                (no-duplicatesp-equal (svar-decomptable-vars decomp))
                (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))
                (subsetp-equal (alist-keys (svar-decomptable-fix decomp))
                               (svex-alist-keys x)))
           (svex-alist-eval-equiv (svex-alist-from-decomp (svex-alist-to-decomp x decomp) decomp)
                                  x))
  :hints(("Goal" :in-theory (enable svex-alist-from-decomp svex-alist-to-decomp
                                    svex-alist-decomptable-recompose))
         (and stable-under-simplificationp
              '(:computed-hint-replacement
                ((let ((env (acl2::find-call-lst 'SVEX-ALIST-EVAL-EQUIV-ENVS-EQUIVALENT-WITNESS clause)))
                   `(:clause-processor (acl2::generalize-with-alist-cp clause '((,env . env))))))
                :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent)))
         (and stable-under-simplificationp
              '(:computed-hint-replacement
                ((let ((key (acl2::find-call-lst 'svex-envs-equivalent-witness clause)))
                   `(:clause-processor (acl2::generalize-with-alist-cp clause '((,key . key))))))
                :in-theory (enable svex-envs-equivalent)))))


#||
;; Composition steps.
;; 1: compose original network (orig) via dfs, resulting in comp1.  We have (netcomp-p comp1 orig).
;; 2: apply svex-alist-to-decomp to comp1, resulting in compdec1.
;; 3: compose compdec1 via dfs, resulting in compdec2.  We have (netcomp-p compdec2 compdec1).
;; 4. apply svex-alist-from-decomp to compdec2, resulting in comp2.
;;     --- Can we conclude (netcomp-p comp2 comp1)?
;;
(defthm from-decomp-of-to-decomp-preserves-netcomp-p
  (implies (and (not (intersectp-equal (svex-alist-keys comp1)
                                       (svar-decomptable-vars decomp)))
                (not (intersectp-equal (svex-alist-vars comp1)
                                       (svar-decomptable-vars decomp)))
                (no-duplicatesp-equal (svar-decomptable-vars decomp))
                (no-duplicatesp-equal (alist-keys (svar-decomptable-fix decomp)))
                (subsetp-equal (alist-keys (svar-decomptable-fix decomp))
                               (svex-alist-keys comp1))
                (netcomp-p compdec2 (svex-alist-to-decomp comp1 decomp)))
           (netcomp-p (svex-alist-from-decomp compdec2 decomp) comp1))
  :hints ('(:computed-hint-replacement
            ((and stable-under-simplificationp
                  (let ((ordering (acl2::find-call-lst 'netcomp-p-witness clause)))
                    `(:clause-processor (acl2::generalize-with-alist-cp clause '((,ordering . ordering)))))))
            :expand ((netcomp-p compdec2 (svex-alist-to-decomp comp1 decomp))))))

;; this reduces to:
(IMPLIES
 (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                             (SVEX-ALIST-KEYS COMP1)))
      (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                             (SVEX-ALIST-VARS COMP1)))
      (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
      (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
      (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                     (SVEX-ALIST-KEYS COMP1)))
 (NETCOMP-P
  (SVEX-ALIST-FROM-DECOMP
   (NETEVAL-ORDERING-COMPILE ORDERING
                             (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
   DECOMP)
  COMP1))
;; so we have to construct (from-to-decomp-ordering ordering decomp)
;; for which:

(IMPLIES
 (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                             (SVEX-ALIST-KEYS COMP1)))
      (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                             (SVEX-ALIST-VARS COMP1)))
      (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
      (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
      (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                     (SVEX-ALIST-KEYS COMP1)))
 (svex-alist-eval-equiv
  (SVEX-ALIST-FROM-DECOMP
   (NETEVAL-ORDERING-COMPILE ORDERING
                             (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
   DECOMP)
  (neteval-ordering-compile (from-decomp-ordering ordering decomp) COMP1)))

||#

(defthm neteval-ordering-compile-of-nil
  (equal (neteval-ordering-compile nil network) nil)
  :hints(("Goal" :in-theory (enable neteval-ordering-compile))))

(local
 (defthm svex-alist-removekeys-when-superset
   (implies (subsetp (svex-alist-keys a) (svarlist-fix keys))
            (equal (svex-alist-removekeys keys a) nil))
   :hints(("Goal" :in-theory (enable svex-alist-removekeys svex-alist-keys svex-alist-fix)))))

(local
 (defthm svex-alist-keys-of-svex-alist-removekeys
   (equal (svex-alist-keys (svex-alist-removekeys vars alist))
          (set-difference-equal (svex-alist-keys alist) (svarlist-fix vars)))
   :hints(("Goal" :in-theory (enable svex-alist-removekeys svex-alist-keys set-difference-equal)))))

(local (defthm subsetp-set-difference
         (subsetp-equal (set-difference-equal a b) a)
         :hints(("goal" :in-theory (enable acl2::subsetp-witness-rw)))))

(local (defthm subsetp-keys-of-svex-alist-reduce
         (implies (svarlist-p vars)
                  (subsetp-equal (svex-alist-keys (svex-alist-reduce vars alist)) vars))
         :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-reduce)))))




(local
 (define svex-pair-eval-equiv (x y)
   :verify-guards nil
   (and (iff (consp x) (consp y))
        (implies (consp x)
                 (and (equal (car x) (car y))
                      (svex-eval-equiv (cdr x) (cdr y)))))
   ///
   (defequiv svex-pair-eval-equiv)
   (defcong svex-pair-eval-equiv svex-alist-eval-equiv (cons pair rest) 1
     :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                       svex-lookup))))

   (defcong svex-eval-equiv svex-pair-eval-equiv (cons key val) 2)))


(local
 (defthm svex-compose-of-rsh-under-eval-equiv
   (svex-eval-equiv (svex-compose (svex-rsh offset x) a)
                    (svex-rsh offset (svex-compose x a)))
   :hints(("Goal" :in-theory (enable svex-eval-equiv)))))

(local
 (defthm svex-compose-of-concat-under-eval-equiv
   (svex-eval-equiv (svex-compose (svex-concat offset x y) a)
                    (svex-concat offset (svex-compose x a) (svex-compose y a)))
   :hints(("Goal" :in-theory (enable svex-eval-equiv)))))

(local (defthm svex-compose-of-compose
         (svex-eval-equiv (svex-compose (svex-compose x a) b)
                          (svex-compose x (append (svex-alist-compose a b) b)))
         :hints(("Goal" :in-theory (enable svex-eval-equiv)))))

(local (defthm svex-alist-compose-of-svex-alist-compose
         (svex-alist-eval-equiv (svex-alist-compose (svex-alist-compose x a) b)
                                (svex-alist-compose x (append (svex-alist-compose a b) b)))
         :hints(("Goal" :in-theory (enable svex-alist-eval-equiv)))))



(local (defthm svex-alist-removekeys-of-append-removekeys
         (equal (svex-alist-removekeys vars (append (svex-alist-removekeys vars x) y))
                (svex-alist-removekeys vars (append x y)))
         :hints(("Goal" :in-theory (enable svex-alist-removekeys)))))


(local (defthm svex-alist-removekeys-of-append
         (Equal (svex-alist-removekeys vars (append a b))
                (append (svex-alist-removekeys vars a)
                        (svex-alist-removekeys vars b)))
         :hints(("Goal" :in-theory (enable svex-alist-removekeys)))))


(local
 (std::defret-mutual svex-eval-of-append-reduce-superset
   (defret <fn>-of-append-reduce-superset
     :pre-bind ((env (append a b c)))
     (implies (subsetp-equal (svex-vars x) (svarlist-fix vars))
              (equal (svex-eval x (append a (svex-env-reduce vars b) c))
                     val))
     :hints ('(:expand ((:free (env) <call>)
                        (svex-vars x)))
             (and stable-under-simplificationp
                  '(:in-theory (enable svex-env-boundp))))
     :fn svex-eval)
   (defret <fn>-of-append-reduce-superset
     :pre-bind ((env (append a b c)))
     (implies (subsetp-equal (svexlist-vars x) (svarlist-fix vars))
              (equal (svexlist-eval x (append a (svex-env-reduce vars b) c))
                     vals))
     :hints ('(:expand ((:free (env) <call>)
                        (svexlist-vars x))))
     :fn svexlist-eval)
   :mutual-recursion svex-eval))

(local (defthm svex-alist-eval-append-reduce-superset
         (implies (subsetp-equal (svex-alist-vars x) (svarlist-fix vars))
                  (equal (svex-alist-eval x (append a (svex-env-reduce vars b) c))
                         (svex-alist-eval x (append a b c))))
         :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vars)))))

(local (defthm svex-alist-compose-append-reduce-superset
         (implies (subsetp-equal (svex-alist-vars x) (svarlist-fix vars))
                  (svex-alist-eval-equiv (svex-alist-compose x (append a (svex-alist-reduce vars b)))
                                         (svex-alist-compose x (append a b))))
         :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent)))))


(local
 (encapsulate nil
   (local (defthmd svex-env-boundp-is-member-alist-keys
           (iff (svex-env-boundp key x)
                (member-equal (svar-fix key) (alist-keys (svex-env-fix x))))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))
   (local (defthm svex-env-lookup-when-not-boundp
            (implies (not (svex-env-boundp key x))
                     (equal (svex-env-lookup key x) (4vec-x)))
            :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-boundp)))))

   (defthm svex-envs-equivalent-append-removekeys-set-equiv
     (implies (acl2::set-equiv (alist-keys (svex-env-fix a)) (svarlist-fix vars))
              (svex-envs-equivalent (append (svex-env-removekeys vars b) a)
                                    (append a b)))
     :hints(("Goal" :in-theory (enable svex-envs-equivalent))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (svex-env-boundp-is-member-alist-keys)
                                   (member-alist-keys))))))

   (defthm svex-alist-eval-equiv-append-removekeys-set-equiv
     (implies (acl2::set-equiv (svex-alist-keys a) (svarlist-fix vars))
              (svex-alist-eval-equiv (append (svex-alist-removekeys vars b) a)
                                     (append a b)))
     :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent))))))




(defines from-decomp-ordering
    ;; The ordering is in terms of decomposed variables.  We want to create one
    ;; in terms of the non-decomposed variables.  To do this for the decomposed
    ;; variables, we go through the decomptable and for each non-decomp
    ;; variable bound, we create a neteval-sigordering based on its
    ;; decomposition.  But we also need to translate the part involving the
    ;; non-decomposed variables.
  :ruler-extenders :lambdas
  (define from-decomp-ordering ((x neteval-ordering-p)
                                (decomp svar-decomptable-p))
    :measure (nat-list-measure (list (neteval-ordering-count x) 2 0))
    :returns (new-x neteval-ordering-p)
    :verify-guards nil
    (append (from-decomp-ordering-decomp-vars x decomp decomp)
            (from-decomp-ordering-non-decomp-vars x decomp)))
  
  (define from-decomp-ordering-decomp-vars ((x neteval-ordering-p)
                                            (decomp svar-decomptable-p)
                                            (full-decomp svar-decomptable-p))
    :measure (nat-list-measure (list (neteval-ordering-count x) 1 (len decomp)))
    :returns (new-x neteval-ordering-p)
    (b* (((when (Atom decomp)) nil)
         ((unless (and (consp (car decomp))
                       (svar-p (caar decomp))))
          (from-decomp-ordering-decomp-vars x (cdr decomp) full-decomp))
         ((cons var dec) (car decomp)))
      (cons (cons var (from-decomp-ordering-decomp-vars-decomp-sigordering dec x full-decomp))
            (from-decomp-ordering-decomp-vars x (cdr decomp) full-decomp))))

  (define from-decomp-ordering-decomp-vars-decomp-sigordering ((dec svar-decomp-p)
                                                               (x neteval-ordering-p)
                                                               (decomp svar-decomptable-p))
    :measure (nat-list-measure (list (neteval-ordering-count x) 0 (svar-decomp-count dec)))
    :returns (new-x neteval-sigordering-p)
    (b* ((var (svar-decomp-case dec
                :segment dec.var
                :remainder dec.var))
         (sigord (cdr (hons-assoc-equal var x)))
         (new-sigord (if sigord
                         (from-decomp-ordering-sigord sigord decomp)
                       (make-neteval-sigordering-remainder :ord (make-neteval-ordering-or-null-null)))))
      (svar-decomp-case dec
        :segment (neteval-sigordering-concat
                  dec.width new-sigord
                  (from-decomp-ordering-decomp-vars-decomp-sigordering dec.rest x decomp))
        :remainder new-sigord)))

  (define from-decomp-ordering-sigord ((x neteval-sigordering-p)
                                       (decomp svar-decomptable-p))
    :measure (nat-list-measure (list (neteval-sigordering-count x) 0 0))
    :returns (new-x neteval-sigordering-p)
    (neteval-sigordering-case x
      :segment (make-neteval-sigordering-segment
                :width x.width
                :ord (from-decomp-ordering-ordering-or-null x.ord decomp)
                :rest (from-decomp-ordering-sigord x.rest decomp))
      :remainder (make-neteval-sigordering-remainder
                  :ord (from-decomp-ordering-ordering-or-null x.ord decomp))))

  (define from-decomp-ordering-ordering-or-null ((x neteval-ordering-or-null-p)
                                                 (decomp svar-decomptable-p))
    :measure (nat-list-measure (list (neteval-ordering-or-null-count x) 0 0))
    :returns (new-x neteval-ordering-or-null-p)
    (neteval-ordering-or-null-case x
      :null (make-neteval-ordering-or-null-null)
      :ordering (make-neteval-ordering-or-null-ordering
                 :ord (from-decomp-ordering x.ord decomp))))
                
  (define from-decomp-ordering-non-decomp-vars ((x neteval-ordering-p)
                                                (decomp svar-decomptable-p))
    :measure (nat-list-measure (list (neteval-ordering-count x) 0 0))
    :returns (new-x neteval-ordering-p)
    (b* ((x (neteval-ordering-fix x))
         ((when (atom x)) nil)
         ((cons signal sigordering) (car x))
         ((when (or (member-equal signal (svar-decomptable-vars decomp))
                    (hons-assoc-equal signal (svar-decomptable-fix decomp))))
          (from-decomp-ordering-non-decomp-vars (cdr x) decomp)))
      (cons (cons signal (from-decomp-ordering-sigord sigordering decomp))
            (from-decomp-ordering-non-decomp-vars (cdr x) decomp))))
  ///
  (verify-guards from-decomp-ordering)


  (defun-sk from-decomp-ordering-sigord-prop (x comp1 decomp-net decomp)
    (forall (signal offset)
            (implies (svex-lookup signal comp1)
                     (svex-eval-equiv
                      (svex-compose
                       (NETEVAL-sigORDERING-COMPILE x signal offset decomp-net)
                       (svar-decomptable->inverse decomp))
                      (neteval-sigordering-compile (from-decomp-ordering-sigord x decomp) signal offset COMP1))))
    :rewrite :direct)

  (local (in-theory (disable from-decomp-ordering-sigord-prop)))

  (defun-sk from-decomp-ordering-ordering-or-null-prop (x comp1 decomp-net decomp)
    (forall (signal)
            (implies (svex-lookup signal comp1)
                     (svex-eval-equiv
                      (svex-compose
                       (NETEVAL-ordering-or-null-COMPILE x signal decomp-net)
                       (svar-decomptable->inverse decomp))
                      (neteval-ordering-or-null-compile (from-decomp-ordering-ordering-or-null x decomp) signal COMP1))))
    :rewrite :direct)

  (local (in-theory (disable from-decomp-ordering-ordering-or-null-prop)))

  (local (in-theory (disable append acl2::consp-of-append)))

  (local (in-theory (disable from-decomp-ordering
                             from-decomp-ordering-decomp-vars
                             from-decomp-ordering-non-decomp-vars
                             from-decomp-ordering-sigord
                             from-decomp-ordering-ordering-or-null
                             from-decomp-ordering-decomp-vars-decomp-sigordering)))

  (std::defret-mutual <fn>-correct
    (defret <fn>-correct
      (IMPLIES
       (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                   (SVEX-ALIST-KEYS COMP1)))
            (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                   (SVEX-ALIST-VARS COMP1)))
            (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
            (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
            (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                           (SVEX-ALIST-KEYS COMP1)))
       (svex-alist-eval-equiv
        (SVEX-ALIST-FROM-DECOMP
         (append (NETEVAL-ORDERING-COMPILE x
                                           (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
                 (svex-identity-subst (svar-decomptable-vars decomp)))
         DECOMP)
        (neteval-ordering-compile new-x COMP1)))
      :hints ('(:expand ((:free (net) (neteval-ordering-compile x net))
                         ;; (:free (net) (neteval-ordering-compile new-x net))
                         ))
              ;; (and stable-under-simplificationp
              ;;      '(:expand ((:free (x) <call>))))
              )
      :fn from-decomp-ordering)
    (defret <fn>-correct
      (IMPLIES
       (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                   (SVEX-ALIST-KEYS COMP1)))
            (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                   (SVEX-ALIST-VARS COMP1)))
            (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
            (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
            (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                           (SVEX-ALIST-KEYS COMP1)))
       (svex-alist-eval-equiv
        (svex-alist-reduce (alist-keys (svar-decomptable-fix decomp))
                           (SVEX-ALIST-FROM-DECOMP
                            (append (NETEVAL-ORDERING-COMPILE x
                                                              (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
                                    (svex-identity-subst (svar-decomptable-vars decomp)))
                            DECOMP))
        (neteval-ordering-compile new-x COMP1)))
      :hints ('(:expand (;; (:free (net) (neteval-ordering-compile x net))
                         <call>
                         ;; (:free (net) (neteval-ordering-compile new-x net))
                         ))
              ;; (and stable-under-simplificationp
              ;;      '(:expand ((:free (x) <call>))))
              )
      :fn from-decomp-ordering-decomp-vars)
    (defret <fn>-correct
      (IMPLIES
       (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                   (SVEX-ALIST-KEYS COMP1)))
            (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                   (SVEX-ALIST-VARS COMP1)))
            (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
            (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
            (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                           (SVEX-ALIST-KEYS COMP1)))
       (svex-alist-eval-equiv
        (svex-alist-removekeys
         (alist-keys (svar-decomptable-fix decomp))
         (svex-alist-removekeys
          (svar-decomptable-vars decomp)
          (SVEX-ALIST-FROM-DECOMP
           (append (NETEVAL-ORDERING-COMPILE x
                                             (SVEX-ALIST-TO-DECOMP COMP1 DECOMP))
                   (svex-identity-subst (svar-decomptable-vars decomp)))
           DECOMP)))
        (neteval-ordering-compile new-x COMP1)))
      :hints ('(:expand ((:free (net) (neteval-ordering-compile x net))
                         <call>
                         (:free (vars a b) (svex-alist-removekeys vars (cons a b)))
                         (:free (x y a) (svex-alist-compose (cons x y) a))
                         ;; (:free (net) (neteval-ordering-compile new-x net))
                         )
                :in-theory (enable svex-alist-from-decomp
                                   svex-alist-to-decomp
                                   svex-alist-decomptable-recompose
                                   svex-acons)
                :do-not-induct t)
              ;; (and stable-under-simplificationp
              ;;      '(:expand ((:free (x) <call>))))
              )
      :fn from-decomp-ordering-non-decomp-vars)
    (defret <fn>-correct
      (IMPLIES
       (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                   (SVEX-ALIST-KEYS COMP1)))
            (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                   (SVEX-ALIST-VARS COMP1)))
            (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
            (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
            (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                           (SVEX-ALIST-KEYS COMP1)))
       (from-decomp-ordering-sigord-prop x comp1
                                         (svex-alist-to-decomp comp1 decomp)
                                         decomp))
      :hints ((and stable-under-simplificationp
                   `(:computed-hint-replacement
                     ((let ((wit (acl2::find-call-lst 'from-decomp-ordering-sigord-prop-witness clause)))
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '(((mv-nth '0 ,wit) . signal)
                                                                                     ((mv-nth '1 ,wit) . offset))))))
                     :expand (,(car (last clause))
                              (:free (net signal offset) (neteval-sigordering-compile x signal offset net))
                              <call>
                              (:free (ord signal offset net)
                               (neteval-sigordering-compile
                                (neteval-sigordering-remainder ord) signal offset net))
                              (:free (width ord rest signal offset net)
                               (neteval-sigordering-compile
                                (neteval-sigordering-segment width ord rest) signal offset net))
                              )))
              (and stable-under-simplificationp
                   '(:expand (<call>))))
      :fn from-decomp-ordering-sigord)

    (defret <fn>-correct
      (IMPLIES
       (AND (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                   (SVEX-ALIST-KEYS COMP1)))
            (NOT (INTERSECTP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP)
                                   (SVEX-ALIST-VARS COMP1)))
            (NO-DUPLICATESP-EQUAL (SVAR-DECOMPTABLE-VARS DECOMP))
            (NO-DUPLICATESP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP)))
            (SUBSETP-EQUAL (ALIST-KEYS (SVAR-DECOMPTABLE-FIX DECOMP))
                           (SVEX-ALIST-KEYS COMP1)))
       (from-decomp-ordering-ordering-or-null-prop x comp1
                                                   (svex-alist-to-decomp comp1 decomp)
                                                   decomp))
      :hints ((and stable-under-simplificationp
                   `(:computed-hint-replacement
                     ((let ((wit (acl2::find-call-lst 'from-decomp-ordering-ordering-or-null-prop-witness clause)))
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '((,wit . signal))))))
                     :expand (,(car (last clause))
                              (:free (net signal) (neteval-ordering-or-null-compile x signal net))
                              <call>
                              (:free (net signal)
                               (neteval-ordering-or-null-compile
                                '(:null) signal net))
                              (:free (ord net signal)
                               (neteval-ordering-or-null-compile
                                (neteval-ordering-or-null-ordering ord) signal net))
                              (svex-compose (svex-var signal) (svar-decomptable->inverse decomp))
                              )))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-alist-to-decomp
                                        svex-alist-decomptable-recompose
                                        svex-alist-from-decomp))))
      :fn from-decomp-ordering-ordering-or-null)
    :skip-others t))
         



     
(defstub from-to-decomp-ordering (ordering decomp) nil)


(defines from-to-decomp-ordering
  (define svex-alist-

(defthm from-decomp-preserves-netcomp-p
  (implies (netcomp-p comp network)
           (netcomp-p (svex-alist-from-decomp comp)
                      (svex-alist-from-decomp network))))




