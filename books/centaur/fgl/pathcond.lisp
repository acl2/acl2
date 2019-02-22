; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(include-book "logicman")
(include-book "pathcond-base")
(local (include-book "theory"))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "std/util/termhints" :dir :system))



(define logicman-pathcond-p (pathcond &optional (logicman 'logicman))
  (declare (xargs :non-executable t))
  :no-function t
  :verify-guards nil
  (prog2$ (acl2::throw-nonexec-error 'logicman-pathcond-p-fn (list pathcond logicman))
          (lbfr-case
            :aignet (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                               (ans)
                               (stobj-let ((aignet (logicman->aignet logicman)))
                                          (ans)
                                          (aignet::aignet-pathcond-p aignet-pathcond aignet)
                                          ans)
                               ans)
            :otherwise t))
  ///
  (defthm logicman-pathcond-p-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (logicman-pathcond-p pathcond old))
             (logicman-pathcond-p pathcond new))
    :hints(("Goal" :in-theory (enable logicman-extension-p)))))
                       


(define logicman-pathcond-eval (env pathcond &optional (logicman 'logicman))
  (declare (xargs :non-executable t))
  :no-function t
  :verify-guards nil
  (prog2$ (acl2::throw-nonexec-error 'logicman-pathcond-eval-fn (list env pathcond logicman))
          (lbfr-case
            :bdd (b* ((pathcond-bdd (mbe :logic (acl2::ubdd-fix (pathcond-bdd pathcond))
                                         :exec (pathcond-bdd pathcond))))
                   (bfr-eval pathcond-bdd env))
            :aig (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                            (ans)
                            (calist-eval calist-stobj env)
                            ans)
            :aignet (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                               (ans)
                               (stobj-let ((aignet   (logicman->aignet logicman)))
                                          (ans)
                                          (aignet::aignet-pathcond-eval
                                           aignet aignet-pathcond
                                           (alist-to-bitarr (aignet::num-ins aignet) env nil)
                                           nil)
                                          ans)
                               ans)))
  ///
  #!aignet
  (local (defthm aignet-pathcond-eval-of-alist-to-bitarr-aignet-extension
           (implies (and (syntaxp (not (equal new old)))
                         (aignet-extension-p new old))
                    (equal (aignet-pathcond-eval old nbalist (fgl::alist-to-bitarr
                                                              (stype-count :pi new) env bitarr)
                                                 regvals)
                           (aignet-pathcond-eval old nbalist (fgl::alist-to-bitarr
                                                              (stype-count :pi old) env bitarr)
                                                 regvals)))
           :hints (("goal" :Cases ((aignet-pathcond-eval old nbalist (fgl::alist-to-bitarr
                                                              (stype-count :pi new) env bitarr)
                                                 regvals)))
                   (and stable-under-simplificationp
                        (let ((lit (assoc 'aignet-pathcond-eval clause)))
                          `(:expand (,lit)))))))

  (defthm logicman-pathcond-eval-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (logicman-pathcond-p pathcond old))
             (equal (logicman-pathcond-eval env pathcond new)
                    (logicman-pathcond-eval env pathcond old)))
    :hints(("Goal" :in-theory (enable logicman-pathcond-p logicman-extension-p))
           (acl2::use-termhint
            (lbfr-case old
              :bdd '(:in-theory (enable bfr-eval bfr-fix))
              :otherwise nil)))))
                                  


(define logicman-pathcond-implies-aignet-base ((x lbfr-p) pathcond
                                               &optional (logicman 'logicman))
  :prepwork ((local (in-theory (enable bfr->aignet-lit bfr-p aignet::aignet-idp))))
  :guard (lbfr-mode-is :aignet)
  :enabled t
  :returns (mv (ans acl2::maybe-bitp :rule-classes ((:type-prescription :typed-term ans)))
               (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
  (b* ((bfrstate (logicman->bfrstate))
       (lit (bfr->aignet-lit x))
       (pathcond (pathcond-fix pathcond)))
    (stobj-let ((aignet   (logicman->aignet logicman)))
               (ans pathcond)
               (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                          (ans aignet-pathcond)
                          (aignet-pathcond-implies (aignet::lit->var lit) aignet aignet-pathcond)
                          (mv (and ans (b-xor (aignet::lit->neg lit) ans)) pathcond))
               (mv ans pathcond))))

(defthm bounded-lit-fix-of-fanin-count
  (equal (bounded-lit-fix x (aignet::fanin-count aignet))
         (aignet::aignet-lit-fix x aignet))
  :hints(("Goal" :in-theory (enable bounded-lit-fix aignet::aignet-lit-fix
                                    aignet::aignet-idp
                                    aignet::aignet-id-fix))))

(define logicman-pathcond-implies ((x lbfr-p)
                                   pathcond
                                   &optional (logicman 'logicman))
  :returns (mv (ans acl2::maybe-bitp :rule-classes :type-prescription)
               (new-pathcond (equal new-pathcond (pathcond-fix pathcond))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable bfr-p))))
  :prepwork ((local (in-theory (disable (force)))))
  :guard-debug t
  (b* ((x (lbfr-fix x))
       (pathcond (pathcond-fix pathcond)))
    (lbfr-case
      :bdd (b* ((pathcond-bdd (pathcond-bdd pathcond))
                (pathcond-bdd (mbe :logic (acl2::ubdd-fix pathcond-bdd) :exec pathcond-bdd))
                ((when (acl2::q-and-is-nil pathcond-bdd x)) (mv 0 pathcond))
                ((when (acl2::q-and-is-nilc2 pathcond-bdd x)) (mv 1 pathcond)))
             (mv nil pathcond))
      :aig (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                      (ans)
                      (calist-implies x (calist-stobj-access calist-stobj))
                      (mv ans pathcond))
      :aignet (mbe :logic (non-exec
                           (b* (((mv ans ?new-pathcond)
                                 (logicman-pathcond-implies-aignet-base x pathcond)))
                             (mv ans pathcond)))
                   :exec (logicman-pathcond-implies-aignet-base x pathcond))))
  ///
  ;; (local (defthm backchaining-hack
  ;;          (implies (not (equal (aignet::aignet-pathcond-implies-logic x aignet pathcond) b))
  ;;                   (not (equal (aignet::aignet-pathcond-implies-logic x aignet pathcond) b)))))
  ;; (local (acl2::use-trivial-ancestors-check))

  (defret eval-when-logicman-pathcond-implies
    (implies (and (logicman-pathcond-eval env pathcond)
                  ans)
             (equal ans (bool->bit (bfr-eval x env))))
    :hints(("Goal" :in-theory (enable logicman-pathcond-eval bfr-eval bfr-fix bfr->aignet-lit aignet-lit->bfr
                                      aignet::lit-eval-of-aignet-lit-fix
                                      aignet::aignet-lit-fix aignet::aignet-id-fix
                                      aignet::aignet-idp)
            :expand ((:free (invals regvals aignet) (aignet::lit-eval x invals regvals aignet)))
            :do-not-induct t)
           (and stable-under-simplificationp
                (let ((lit (assoc 'acl2::q-binary-and clause)))
                  (and lit
                       `(:use ((:instance acl2::eval-bdd-of-q-and
                                (x ,(second lit)) (y ,(third lit))
                                (values env)))
                         :in-theory (disable acl2::eval-bdd-of-q-and))))))
    :otf-flg t)

  (defret logicman-pathcond-implies-not-equal-negation
    (implies (and (logicman-pathcond-eval env pathcond)
                  (equal b (b-not (bool->bit (bfr-eval x env)))))
             (not (equal ans b)))
    :hints (("goal" :use eval-when-logicman-pathcond-implies))))


(define logicman-pathcond-depends-on ((v natp)
                                      pathcond
                                      &optional (logicman 'logicman))
  (lbfr-case
    :bdd (ec-call (nth v (acl2::ubdd-deps (acl2::ubdd-fix (pathcond-bdd pathcond)))))
    :aig (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                    (dep)
                    (calist-depends-on v (calist-stobj-access calist-stobj))
                    dep)
    :aignet (stobj-let ((aignet (logicman->aignet logicman)))
                       (dep)
                       (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                                  (dep)
                                  (non-exec
                                   (ec-call (aignet::nbalist-depends-on
                                             v aignet-pathcond aignet)))
                                  dep)
                       dep))
  ///

  (local #!acl2
         (defthm eval-bdd-of-update-when-not-dependent-fix
           (implies (not (nth n (ubdd-deps (ubdd-fix x))))
                    (equal (eval-bdd x (update-nth n v env))
                           (eval-bdd x env)))
           :hints (("goal" :use ((:instance eval-bdd-of-update-when-not-dependent
                                  (x (ubdd-fix x))))
                    :in-theory (disable eval-bdd-of-update-when-not-dependent)))))

    (local (defthm alist-to-bitarr-of-cons
           (acl2::bits-equiv (alist-to-bitarr max (cons (cons var val) alist) bitarr)
                             (if (and (natp var)
                                      (< var (nfix max)))
                                 (update-nth var (bool->bit val) (alist-to-bitarr max alist bitarr))
                               (alist-to-bitarr max alist bitarr)))
           :hints(("Goal" :in-theory (enable acl2::bits-equiv)))))
           

  (defthm logicman-pathcond-eval-of-set-var-when-not-depends-on
    (implies (and (not (logicman-pathcond-depends-on v pathcond)))
             (equal (logicman-pathcond-eval (bfr-set-var v val env) pathcond)
                    (logicman-pathcond-eval env pathcond)))
    :hints(("Goal" :in-theory (enable logicman-pathcond-eval bfr-eval bfr-fix
                                      bfr-set-var bfr-varname-p bfr-nvars))))

  (defthm logicman-pathcond-depends-on-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (logicman-pathcond-p pathcond old)
                  (not (logicman-pathcond-depends-on v pathcond old)))
             (not (logicman-pathcond-depends-on v pathcond new)))
    :hints(("Goal" :in-theory (enable logicman-extension-p logicman-pathcond-p)))))


(define logicman-pathcond-assume ((x lbfr-p)
                                  pathcond
                                  &optional (logicman 'logicman))
  :returns (mv contradictionp
               new-pathcond)
  :guard-hints (("goal" :in-theory (enable bfr-p bfr->aignet-lit aignet::aignet-idp)))
  (b* ((x (lbfr-fix x)))
    (lbfr-case
      :bdd (b* ((pathcond (pathcond-fix pathcond))
                (pathcond-bdd (pathcond-bdd pathcond))
                (pathcond-bdd (mbe :logic (acl2::ubdd-fix pathcond-bdd)
                                   :exec pathcond-bdd))
                (new-pathcond-bdd (acl2::q-and pathcond-bdd x))
                ((when (eq new-pathcond-bdd nil))
                 (mv t pathcond))
                (pathcond (update-pathcond-bdd new-pathcond-bdd pathcond)))
             (mv nil pathcond))
      :aig (b* ((pathcond (pathcond-fix pathcond)))
             (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                        (contra calist-stobj)
                        (calist-assume x calist-stobj)
                        (mv contra pathcond)))
      :aignet (b* ((bfrstate (logicman->bfrstate logicman))
                   (x (bfr->aignet-lit x)))
                (stobj-let ((aignet (logicman->aignet logicman)))
                           (contra pathcond)
                           (b* ((pathcond (pathcond-fix pathcond)))
                             (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                                        (contra aignet-pathcond)
                                        (aignet-pathcond-assume x aignet aignet-pathcond)
                                        (mv contra pathcond)))
                           (mv contra pathcond)))))
  ///
  ;; (defret logicman-get-of-logicman-pathcond-assume
  ;;   (implies (not (equal (logicman-field-fix key) :pathcond))
  ;;            (equal (logicman-get key new-logicman)
  ;;                   (logicman-get key logicman))))

  ;; (defret logicman-extension-p-of-logicman-pathcond-assume
  ;;   (logicman-extension-p new-logicman logicman))
  

  (defret logicman-pathcond-assume-correct
    (implies (and (logicman-pathcond-eval env pathcond)
                  (bfr-eval x env))
             (and (not contradictionp)
                  (logicman-pathcond-eval env new-pathcond)))
    :hints(("Goal" :in-theory (enable bfr-eval bfr-fix bfr-p bfr->aignet-lit
                                      logicman-pathcond-eval))
           (and stable-under-simplificationp
                (let ((lit (assoc 'acl2::q-binary-and clause)))
                  (and lit
                       `(:use ((:instance acl2::eval-bdd-of-q-and
                                (x ,(second lit)) (y ,(third lit))
                                (values env)))
                         :in-theory (disable acl2::eval-bdd-of-q-and))))))
    :otf-flg t)

  (defret logicman-pathcond-assume-eval-new
    (implies (not contradictionp)
             (equal (logicman-pathcond-eval env new-pathcond)
                    (and (logicman-pathcond-eval env pathcond)
                         (bfr-eval x env))))
    :hints(("Goal" :in-theory (enable bfr-eval bfr-fix bfr->aignet-lit logicman-pathcond-eval))))

  (defret logicman-pathcond-assume-contradictionp-correct
    (implies (and contradictionp
                  (bfr-eval x env))
             (not (logicman-pathcond-eval env pathcond)))
    :hints (("goal" :use logicman-pathcond-assume-correct)))

  (local (in-theory (disable (force))))

  (defret pathcond-rewindable-of-logicman-pathcond-assume
    (implies (equal (bfr-mode-fix bfr-mode) (lbfr-mode))
             (pathcond-rewindable bfr-mode new-pathcond pathcond))
    :hints(("Goal" :in-theory (enable pathcond-rewindable bfr-fix))))

  ;; (local
  ;;  #!aignet
  ;;  (Defthm depends-on-of-aignet-lit-fix
  ;;    (equal (depends-on (aignet-lit-fix lit aignet) ci-id aignet)
  ;;           (depends-on lit ci-id aignet))
  ;;    :hints (("goal" :expand ((depends-on (aignet-lit-fix lit aignet)
  ;;                                         ci-id aignet)
  ;;                             (depends-on lit ci-id aignet))))))

  (defret logicman-pathcond-depends-on-of-logicman-pathcond-assume
    (implies (and (not (logicman-pathcond-depends-on v pathcond))
                  (not (bfr-depends-on v x ))
                  (bfr-varname-p v))
             (not (logicman-pathcond-depends-on v new-pathcond)))
    :hints(("Goal" :in-theory (enable logicman-pathcond-depends-on
                                      bfr-depends-on
                                      bfr-varname-p
                                      bfr-fix
                                      bfr-nvars
                                      bfr->aignet-lit)))))


                                  


    
