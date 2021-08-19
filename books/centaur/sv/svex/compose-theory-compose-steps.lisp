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
                                      (svex-lookup var network1)
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
    :hints(("Goal" :in-theory (enable svar-decomp-vars svex-env-boundp)))))

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
            :expand ((:free (x) (svex-eval (svex-var x) env)))))))

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

  (local (in-theory (enable svar-decomptable-fix))))



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

  (local (in-theory (enable svar-decomptable-fix))))
  

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
                 '(:cases ((svar-p key)))))))


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
                                    (pairlis$ (alist-keys (svar-decomptable-fix x))
                                              (svarlist->svexes (alist-keys (svar-decomptable-fix x))))))
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

  (local (in-theory (enable svar-decomptable-fix))))

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

  (local (defthm member-alist-keys
           (iff (member k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))

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


  (local (Defthm svex-lookup-when-subsetp-alist-keys
           (implies (and (subsetp set (svex-alist-keys x))
                         (member-equal (svar-fix key) set))
                    (svex-lookup key x))
           :hints(("Goal" :in-theory (enable svex-alist-keys svex-lookup)))))

  

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

(define svex-alist-to-decomp ((x svex-alist-p)
                              (decomp svar-decomptable-p))
  :returns (new-x svex-alist-p)
  (svex-alist-decomptable-decompose (svex-alist-compose x (svar-decomptable->subst decomp)) decomp))


(define svex-alist-decomptable-recompose ((x svex-alist-p)
                                          (decomp svar-decomptable-p))
  :returns (new-x svex-alist-p)
  (append (svex-alist-compose (svar-decomptable->subst decomp) x)
          (svex-alist-removekeys (svar-decomptable-vars decomp) x)))


(define svex-alist-from-decomp ((x svex-alist-p)
                                (decomp svar-decomptable-p))
  :returns (new-x svex-alist-p)
  (svex-alist-decomptable-recompose (svex-alist-compose x (svar-decomptable->inverse decomp))
                                    decomp))
  










(defthm netcomp-p-of-bijective-composition
  (implies (and (svex-alist-equiv (svex-alist-compose a->b b->a)
                                  (pairlis$ (svex-alist-keys a->b)
                                            (svarlist->svexes (svex-alist-keys a->b))))
                (svex-alist-equiv (svex-alist-compose b->a a->b)
                                  (pairlis$ (svex-alist-keys b->a)
                                            (svarlist->svexes (svex-alist-keys b->a))))
                (netcomp-p new (svex-alist-compose b->a (svex-alist-compose old a->b))))
