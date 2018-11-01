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

(define logicman-pathcond-checkpoint-p (x &optional (logicman 'logicman))
  :enabled t
  (b* ((bfr-mode (bfr-mode)))
    (stobj-let ((pathcond (logicman->pathcond logicman)))
               (ok)
               (pathcond-checkpoint-p x bfr-mode pathcond)
               ok))
  ;; ///
  ;; (def-updater-independence-thm logicman-pathcond-checkpoint-p-updater-independence
  ;;   (implies (and (equal (logicman->pathcond new)
  ;;                        (logicman->pathcond old))
  ;;                 (equal (logicman->mode new)
  ;;                        (logicman->mode old)))
  ;;            (equal (logicman-pathcond-checkpoint-p x new)
  ;;                   (logicman-pathcond-checkpoint-p x old))))
  )

(define logicman-pathcond-checkpoint (&optional (logicman 'logicman))
  :enabled t
  (b* ((bfr-mode (bfr-mode)))
    (stobj-let ((pathcond (logicman->pathcond logicman)))
               (chp)
               (pathcond-checkpoint bfr-mode pathcond)
               chp))
  ;; ///
  ;; (def-updater-independence-thm logicman-pathcond-checkpoint-updater-independence
  ;;   (implies (and (equal (logicman->pathcond new)
  ;;                        (logicman->pathcond old))
  ;;                 (equal (logicman->mode new)
  ;;                        (logicman->mode old)))
  ;;            (equal (logicman-pathcond-checkpoint new)
  ;;                   (logicman-pathcond-checkpoint old))))
  )

(define logicman-pathcond-rewindable (new old)
  :non-executable t
  :verify-guards nil
  :enabled t
  (b* ((bfr-mode (bfr-mode old)))
    (and (equal (bfr-mode new) bfr-mode)
         (pathcond-rewindable bfr-mode (logicman->pathcond new) (logicman->pathcond old))))
  ;; ///
  ;; (defthm logicman-pathcond-checkpoint-p-when-rewindable
  ;;   (implies (and (logicman-pathcond-rewindable new old)
  ;;                 (logicman-pathcond-checkpoint-p chp old))
  ;;            (logicman-pathcond-checkpoint-p chp new))
  ;;   :hints(("Goal" :in-theory (enable logicman-pathcond-checkpoint-p))))

  ;; (defthm logicman-pathcond-checkpoint-rewindable-of-self
  ;;   (logicman-pathcond-rewindable x x))

  ;; (def-updater-independence-thm logicman-pathcond-rewindable-updater-independence
  ;;   (implies (and (equal (logicman->pathcond new)
  ;;                        (logicman->pathcond old))
  ;;                 (equal (logicman->mode new)
  ;;                        (logicman->mode old)))
  ;;            (equal (logicman-pathcond-rewindable new x)
  ;;                   (logicman-pathcond-rewindable old x))))
  )

(define logicman-pathcond-rewind ((chp logicman-pathcond-checkpoint-p)
                                  &optional (logicman 'logicman))
  :returns (new-logicman)
  :guard-hints (("goal" :in-theory (enable logicman-pathcond-checkpoint-p)))
  (b* ((bfr-mode (bfr-mode)))
    (stobj-let ((pathcond (logicman->pathcond logicman)))
               (pathcond)
               (pathcond-rewind chp bfr-mode pathcond)
               logicman))
  ///
  (defret logicman-get-of-logicman-pathcond-rewind
    (implies (not (equal (logicman-field-fix key) :pathcond))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  (defret logicman-extension-p-of-logicman-pathcond-rewind
    (logicman-extension-p new-logicman logicman))

  (defthm logicman-pathcond-rewind-when-rewindable
    (implies (and (logicman-pathcond-rewindable new old)
                  (equal bfr-mode (logicman->mode old)))
             (equal (logicman->pathcond (logicman-pathcond-rewind
                                         (pathcond-checkpoint bfr-mode (logicman->pathcond old))
                                         new))
                    (pathcond-fix (logicman->pathcond old))))))

(local (defthm bitp-when-maybe-bitp
         (implies (and x (acl2::maybe-bitp x))
                  (bitp x))))


(define logicman-pathcond-eval (env &optional (logicman 'logicman))
  (declare (xargs :non-executable t))
  :no-function t
  :verify-guards nil
  (prog2$ (acl2::throw-nonexec-error 'logicman-pathcond-eval-fn (list env logicman))
          (bfr-case
            :bdd (b* ((pathcond-bdd (stobj-let ((pathcond (logicman->pathcond logicman)))
                                               (bdd)
                                               (pathcond-bdd pathcond)
                                               (bfr-fix bdd))))
                   (bfr-eval pathcond-bdd env))
            :aig (stobj-let ((pathcond (logicman->pathcond logicman)))
                            (ans)
                            (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                                       (ans)
                                       (calist-eval calist-stobj env)
                                       ans)
                            ans)
            :aignet (stobj-let ((pathcond (logicman->pathcond logicman))
                                (aignet   (logicman->aignet logicman)))
                               (ans)
                               (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                                          (ans)
                                          (aignet::aignet-pathcond-eval
                                           aignet aignet-pathcond
                                           (alist-to-bitarr (aignet::num-ins aignet) env nil)
                                           nil)
                                          ans)
                               ans))))
                                  


(define logicman-pathcond-implies-aignet-base ((x bfr-p)
                                               &optional (logicman 'logicman))
  :prepwork ((local (in-theory (enable bfr->aignet-lit bfr-p aignet::aignet-idp))))
  :guard (eq (bfr-mode) :aignet)
  :enabled t
  (b* ((lit (bfr->aignet-lit x)))
    (stobj-let ((pathcond (logicman->pathcond logicman))
                (aignet   (logicman->aignet logicman)))
               (ans pathcond)
               (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                          (ans aignet-pathcond)
                          (aignet-pathcond-implies (aignet::lit->var lit) aignet aignet-pathcond)
                          (mv (and ans (b-xor (aignet::lit->neg lit) ans)) pathcond))
               (mv ans logicman))))

(define logicman-pathcond-implies ((x bfr-p)
                                   &optional (logicman 'logicman))
  :returns (mv (ans acl2::maybe-bitp :rule-classes :type-prescription)
               (new-logicman (equal new-logicman logicman)))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable bfr-p))))
  :prepwork ((local (in-theory (disable (force)))))
  (b* ((x (bfr-fix x)))
    (bfr-case
      :bdd (b* ((pathcond-bdd (stobj-let ((pathcond (logicman->pathcond logicman)))
                                         (bdd)
                                         (pathcond-bdd pathcond)
                                         (mbe :logic (acl2::ubdd-fix bdd) :exec bdd)))
                ((when (acl2::q-and-is-nil pathcond-bdd x)) (mv 0 logicman))
                ((when (acl2::q-and-is-nilc2 pathcond-bdd x)) (mv 1 logicman)))
             (mv nil logicman))
      :aig (stobj-let ((pathcond (logicman->pathcond logicman)))
                      (ans)
                      (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                                 (ans)
                                 (calist-implies x (calist-stobj-access calist-stobj))
                                 ans)
                      (mv ans logicman))
      :aignet (mbe :logic (non-exec
                           (b* (((mv ans ?new-logicman)
                                 (logicman-pathcond-implies-aignet-base x)))
                             (mv ans logicman)))
                   :exec (logicman-pathcond-implies-aignet-base x))))
  ///
  ;; (local (defthm backchaining-hack
  ;;          (implies (not (equal (aignet::aignet-pathcond-implies-logic x aignet pathcond) b))
  ;;                   (not (equal (aignet::aignet-pathcond-implies-logic x aignet pathcond) b)))))
  ;; (local (acl2::use-trivial-ancestors-check))

  (defret eval-when-logicman-pathcond-implies
    (implies (and (logicman-pathcond-eval env)
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
    (implies (and (logicman-pathcond-eval env)
                  (equal b (b-not (bool->bit (bfr-eval x env)))))
             (not (equal ans b)))
    :hints (("goal" :use eval-when-logicman-pathcond-implies))))


(define logicman-pathcond-depends-on ((v bfr-varname-p)
                                      &optional ((logicman logicman-nvars-ok) 'logicman))
  (bfr-case
    :bdd (stobj-let ((pathcond (logicman->pathcond logicman)))
                    (dep)
                    (ec-call (nth v (acl2::ubdd-deps (acl2::ubdd-fix (pathcond-bdd pathcond)))))
                    dep)
    :aig (stobj-let ((pathcond (logicman->pathcond logicman)))
                    (dep)
                    (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                               (dep)
                               (calist-depends-on v (calist-stobj-access calist-stobj))
                               dep)
                    dep)
    :aignet (stobj-let ((pathcond (logicman->pathcond logicman))
                        (aignet (logicman->aignet logicman)))
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
    (implies (and (not (logicman-pathcond-depends-on v))
                  (bfr-varname-p v))
             (equal (logicman-pathcond-eval (bfr-set-var v val env))
                    (logicman-pathcond-eval env)))
    :hints(("Goal" :in-theory (enable logicman-pathcond-eval bfr-eval bfr-fix
                                      bfr-set-var bfr-varname-p bfr-nvars)))))


(define logicman-pathcond-assume ((x bfr-p)
                                  &optional (logicman 'logicman))
  :returns (mv contradictionp
               new-logicman)
  :guard-hints (("goal" :in-theory (enable bfr-p bfr->aignet-lit aignet::aignet-idp)))
  (b* ((x (bfr-fix x)))
    (bfr-case
      :bdd (stobj-let ((pathcond (logicman->pathcond logicman)))
                      (contra pathcond)
                      (b* ((pathcond (pathcond-fix pathcond))
                           (pathcond-bdd (pathcond-bdd pathcond))
                           (pathcond-bdd (mbe :logic (acl2::ubdd-fix pathcond-bdd)
                                              :exec pathcond-bdd))
                           (new-pathcond-bdd (acl2::q-and pathcond-bdd x))
                           ((when (eq new-pathcond-bdd nil))
                            (mv t pathcond))
                           (pathcond (update-pathcond-bdd new-pathcond-bdd pathcond)))
                        (mv nil pathcond))
                      (mv contra logicman))
      :aig (stobj-let ((pathcond (logicman->pathcond logicman)))
                      (contra pathcond)
                      (b* ((pathcond (pathcond-fix pathcond)))
                        (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                                   (contra calist-stobj)
                                   (calist-assume x calist-stobj)
                                   (mv contra pathcond)))
                      (mv contra logicman))
      :aignet (b* ((x (bfr->aignet-lit x)))
                (stobj-let ((pathcond (logicman->pathcond logicman))
                            (aignet (logicman->aignet logicman)))
                           (contra pathcond)
                           (b* ((pathcond (pathcond-fix pathcond)))
                             (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                                        (contra aignet-pathcond)
                                        (aignet-pathcond-assume x aignet aignet-pathcond)
                                        (mv contra pathcond)))
                           (mv contra logicman)))))
  ///
  (defret logicman-get-of-logicman-pathcond-assume
    (implies (not (equal (logicman-field-fix key) :pathcond))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  (defret logicman-extension-p-of-logicman-pathcond-assume
    (logicman-extension-p new-logicman logicman))
  

  (defret logicman-pathcond-assume-correct
    (implies (and (logicman-pathcond-eval env)
                  (bfr-eval x env))
             (and (not contradictionp)
                  (logicman-pathcond-eval env new-logicman)))
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
             (equal (logicman-pathcond-eval env new-logicman)
                    (and (logicman-pathcond-eval env)
                         (bfr-eval x env))))
    :hints(("Goal" :in-theory (enable bfr-eval bfr-fix bfr->aignet-lit logicman-pathcond-eval))))

  (defret logicman-pathcond-assume-contradictionp-correct
    (implies (and contradictionp
                  (bfr-eval x env))
             (not (logicman-pathcond-eval env logicman)))
    :hints (("goal" :use logicman-pathcond-assume-correct)))

  (local (in-theory (disable (force))))

  (defret pathcond-rewindable-of-logicman-pathcond-assume
    (implies (equal (bfr-mode-fix bfr-mode) (bfr-mode))
             (pathcond-rewindable bfr-mode (logicman->pathcond new-logicman)  (logicman->pathcond logicman)))
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
    (implies (and (not (logicman-pathcond-depends-on v))
                  (not (bfr-depends-on v x ))
                  (bfr-varname-p v))
             (not (logicman-pathcond-depends-on v new-logicman)))
    :hints(("Goal" :in-theory (enable logicman-pathcond-depends-on
                                      bfr-depends-on
                                      bfr-varname-p
                                      bfr-fix
                                      bfr->aignet-lit)))))


                                  


    
