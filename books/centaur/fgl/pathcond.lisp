; FGL - A Symbolic Simulation Framework for ACL2
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
(include-book "pathcond-aignet-ipasir")
(include-book "centaur/misc/starlogic" :dir :system)
(local (include-book "theory"))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "std/util/termhints" :dir :system))



(define bfr-pathcond-p (pathcond &optional (bfrstate 'bfrstate))
  (declare (xargs :non-executable t))
  :no-function t
  :verify-guards nil
  (prog2$ (acl2::throw-nonexec-error 'bfr-pathcond-p-fn (list pathcond bfrstate))
          (bfrstate-case
            :aignet (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                               (ans)
                               (aignet::bounded-pathcond-p
                                (aignet::nbalist-fix aignet-pathcond)
                                (1+ (bfrstate->bound bfrstate)))
                               ans)
            :bdd (and (bfr-p (acl2::ubdd-fix (pathcond-bdd pathcond)))
                      (bfr-listp (ubdd-list-fix (pathcond-checkpoint-ubdds pathcond))))
            :aig (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                            (ans)
                            (bfr-listp (alist-keys (calist-stobj-access calist-stobj)))
                            ans)))
  ///
  (defmacro logicman-pathcond-p (pathcond &optional (logicman 'logicman))
    `(bfr-pathcond-p ,pathcond (logicman->bfrstate ,logicman)))

  (add-macro-alias logicman-pathcond-p bfr-pathcond-p-fn)

  (defthm logicman-pathcond-p-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (logicman-pathcond-p pathcond old))
             (logicman-pathcond-p pathcond new))
    :hints((and stable-under-simplificationp
                '(:in-theory (enable logicman-extension-p)))))

  (defthm logicman-pathcond-p-of-update-enabledp
    (equal (logicman-pathcond-p (update-nth *pathcond-enabledp* enp pathcond) logicman)
           (logicman-pathcond-p pathcond logicman)))


  (local (defthm bfr-listp-alist-keys-of-rewind-calist
           (implies (bfr-listp (alist-keys (calist-fix calist)))
                    (bfr-listp (alist-keys (rewind-calist n calist))))
           :hints(("Goal" :in-theory (enable rewind-calist alist-keys)))))

  (local (defthm ubdd-fix-preserves-bfr-p
           (implies (and (bfr-p x)
                         (bfrstate-mode-is :bdd))
                    (bfr-p (acl2::ubdd-fix x)))
           :hints(("Goal" :in-theory (enable bfr-p ubddp)))))

  (local (defthm ubdd-list-fix-preserves-bfr-listp
           (implies (and (bfr-listp x)
                         (bfrstate-mode-is :bdd))
                    (bfr-listp (ubdd-list-fix x)))
           :hints(("Goal" :in-theory (enable bfr-listp$ ubdd-list-fix)))))


  (defthm bfr-pathcond-p-of-pathcond-rewind
    (implies (and (bfr-pathcond-p x)
                  (equal (bfr-mode-fix bfr-mode)
                         (bfr-mode-fix (bfrstate->mode bfrstate))))
             (bfr-pathcond-p (pathcond-rewind bfr-mode x)))
    :hints(("Goal" :in-theory (e/d (pathcond-rewind)
                                   (aignet::nbalist-extension-of-nbalist-stobj-rewind
                                    aignet::bounded-pathcond-p-necc)))
           (and stable-under-simplificationp
                (let ((lit (car (last clause))))
                  `(:expand ((:with aignet::bounded-pathcond-p ,lit))
                    :use ((:instance aignet::bounded-pathcond-p-necc
                           (nbalist (aignet::nbalist-fix (nth *pathcond-aignet* x)))
                           (num-fanins (+ 1 (bfrstate->bound bfrstate)))
                           (id (aignet::bounded-pathcond-p-witness . ,(cdr lit))))
                          (:instance aignet::nbalist-extension-of-nbalist-stobj-rewind
                           (x (aignet::nbalist-fix (nth *pathcond-aignet* x)))
                           (len (car (nth *pathcond-checkpoint-ptrs* x))))
                          (:instance aignet::nbalist-extension-of-nbalist-stobj-rewind
                           (x (aignet::nbalist-fix (nth *pathcond-aignet* x)))
                           (len 0)))))))))






(local (defthm ubdd-fix-of-ubdd-fix
         (equal (ubdd-fix (acl2::ubdd-fix x) bound)
                (ubdd-fix x bound))
         :hints(("Goal" :in-theory (enable ubdd-fix)))))

(define logicman-pathcond-eval (env pathcond &optional (logicman 'logicman))
  (declare (xargs :non-executable t))
  :no-function t
  :verify-guards nil
  :hooks ((:fix :hints ((and stable-under-simplificationp
                             '(:in-theory (enable bfr-eval bfr-fix))))))
  (prog2$ (acl2::throw-nonexec-error 'logicman-pathcond-eval-fn (list env pathcond logicman))
          (if (pathcond-enabledp pathcond)
              (lbfr-case
                :bdd (b* ((pathcond-bdd (mbe :logic ;; (lbfr-fix (pathcond-bdd pathcond))
                                             (acl2::ubdd-fix (pathcond-bdd pathcond))
                                             :exec (pathcond-bdd pathcond))))
                       (acl2::eval-bdd pathcond-bdd env))
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
                                   ans))
            t))
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
                          `(:expand ((:with aignet-pathcond-eval ,lit))))))))

  (local (defthm bfr-nvars-of-logicman-extension-rw
           (implies (logicman-extension-p new old)
                    (<= (bfr-nvars old) (bfr-nvars new)))
           :hints (("goal" :use bfr-nvars-of-logicman-extension))))


  (local (defthm ubdd-fix-when-ubddp-of-ubdd-fix
           (implies (ubddp (acl2::ubdd-fix x) bound)
                    (equal (ubdd-fix x bound)
                           (acl2::ubdd-fix x)))
           :hints(("Goal" :in-theory (enable ubdd-fix ubddp)))))

  (defthm logicman-pathcond-eval-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (logicman-pathcond-p pathcond old))
             (equal (logicman-pathcond-eval env pathcond new)
                    (logicman-pathcond-eval env pathcond old)))
    :hints(("Goal" :in-theory (enable logicman-pathcond-p))
           (acl2::use-termhint
            (lbfr-case old
              :bdd '(:in-theory (enable bfr-eval bfr-fix bfr-p))
              :aignet '(:in-theory (enable logicman-extension-p))
              :otherwise nil))))

  (defthm logicman-pathcond-eval-when-not-enabled
    (implies (not (pathcond-enabledp pathcond))
             (equal (logicman-pathcond-eval env pathcond logicman)
                    t)))

  (defcong logicman-equiv equal (logicman-pathcond-eval pathcond env logicman) 3))
                                  


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
       (pathcond (pathcond-fix pathcond))
       ((when (not (pathcond-enabledp pathcond)))
        (mv nil pathcond)))
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


  (local (defthm ubddp-of-ubdd-fix
           (acl2::ubddp (ubdd-fix x bound))
           :hints(("Goal" :in-theory (enable ubdd-fix)))))

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


;; (define logicman-pathcond-depends-on ((v natp)
;;                                       pathcond
;;                                       &optional (logicman 'logicman))
;;   (lbfr-case
;;     :bdd (ec-call (nth v (acl2::ubdd-deps (acl2::ubdd-fix (pathcond-bdd pathcond)))))
;;     :aig (stobj-let ((calist-stobj (pathcond-aig pathcond)))
;;                     (dep)
;;                     (calist-depends-on v (calist-stobj-access calist-stobj))
;;                     dep)
;;     :aignet (stobj-let ((aignet (logicman->aignet logicman)))
;;                        (dep)
;;                        (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
;;                                   (dep)
;;                                   (non-exec
;;                                    (ec-call (aignet::nbalist-depends-on
;;                                              v aignet-pathcond aignet)))
;;                                   dep)
;;                        dep))
;;   ///

;;   (local #!acl2
;;          (defthm eval-bdd-of-update-when-not-dependent-fix
;;            (implies (not (nth n (ubdd-deps (ubdd-fix x))))
;;                     (equal (eval-bdd x (update-nth n v env))
;;                            (eval-bdd x env)))
;;            :hints (("goal" :use ((:instance eval-bdd-of-update-when-not-dependent
;;                                   (x (ubdd-fix x))))
;;                     :in-theory (disable eval-bdd-of-update-when-not-dependent)))))

;;     (local (defthm alist-to-bitarr-of-cons
;;            (acl2::bits-equiv (alist-to-bitarr max (cons (cons var val) alist) bitarr)
;;                              (if (and (natp var)
;;                                       (< var (nfix max)))
;;                                  (update-nth var (bool->bit val) (alist-to-bitarr max alist bitarr))
;;                                (alist-to-bitarr max alist bitarr)))
;;            :hints(("Goal" :in-theory (enable acl2::bits-equiv)))))
           

;;   (defthm logicman-pathcond-eval-of-set-var-when-not-depends-on
;;     (implies (and (not (logicman-pathcond-depends-on v pathcond)))
;;              (equal (logicman-pathcond-eval (bfr-set-var v val env) pathcond)
;;                     (logicman-pathcond-eval env pathcond)))
;;     :hints(("Goal" :in-theory (enable logicman-pathcond-eval bfr-eval bfr-fix
;;                                       bfr-set-var bfr-varname-p bfr-nvars))))

;;   (defthm logicman-pathcond-depends-on-of-logicman-extension
;;     (implies (and (bind-logicman-extension new old)
;;                   (logicman-pathcond-p pathcond old)
;;                   (not (logicman-pathcond-depends-on v pathcond old)))
;;              (not (logicman-pathcond-depends-on v pathcond new)))
;;     :hints(("Goal" :in-theory (enable logicman-extension-p logicman-pathcond-p)))))


(local (defthm ubddp-when-ubddp
         (implies (ubddp x bound)
                  (acl2::ubddp x))
         :hints(("Goal" :in-theory (enable ubddp)))))

(define logicman-pathcond-assume ((x lbfr-p)
                                  pathcond
                                  &optional (logicman 'logicman))
  :returns (mv contradictionp
               new-pathcond)
  :prepwork ((local (defthm len-of-calist-assume-fix
                      (<= (len (calist-fix calist)) (len (mv-nth 1 (calist-assume x calist))))
                      :hints(("Goal" :in-theory (enable calist-assume)))
                      :rule-classes :linear))

             (local (defthm len-of-aignet-pathcond-assume
                      (<= (len (aignet::nbalist-fix pc))
                          (len (mv-nth 1 (aignet::aignet-pathcond-assume-logic x aignet pc))))
                      :hints (("goal" :use ((:instance aignet::nbalist-extension-of-aignet-pathcond-assume-logic
                                             (nbalist-stobj pc) (lit x) (aignet aignet)))
                               :in-theory (disable aignet::nbalist-extension-of-aignet-pathcond-assume-logic)))
                      :rule-classes :linear)))
  :guard-hints (("goal" :in-theory (enable bfr-p bfr->aignet-lit aignet::aignet-idp)))
  (b* ((x (lbfr-fix x))
       (pathcond (pathcond-fix pathcond))
       ((unless (pathcond-enabledp pathcond))
        (mv nil pathcond)))
    (lbfr-case
      :bdd (b* ((pathcond-bdd (pathcond-bdd pathcond))
                (pathcond-bdd (mbe :logic (acl2::ubdd-fix pathcond-bdd)
                                   :exec pathcond-bdd))
                (new-pathcond-bdd (acl2::q-and pathcond-bdd x))
                ((when (eq new-pathcond-bdd nil))
                 (mv t pathcond))
                (stack (cons pathcond-bdd (pathcond-checkpoint-ubdds pathcond)))
                (pathcond (update-pathcond-checkpoint-ubdds stack pathcond))
                (pathcond (update-pathcond-bdd new-pathcond-bdd pathcond)))
             (mv nil pathcond))
      :aig (stobj-let ((calist-stobj (pathcond-aig pathcond)))
                      (len contra calist-stobj)
                      (b* ((len (calist-stobj-len calist-stobj))
                           ((mv contra calist-stobj) (calist-assume x calist-stobj))
                           ((when contra)
                            (b* ((calist-stobj (rewind-calist len calist-stobj)))
                              (mv len contra calist-stobj))))
                        (mv len contra calist-stobj))
                      (b* (((when contra) (mv contra pathcond))
                           (stack (cons len (pathcond-checkpoint-ptrs pathcond)))
                           (pathcond (update-pathcond-checkpoint-ptrs stack pathcond)))
                        (mv nil pathcond)))
      :aignet (b* ((bfrstate (logicman->bfrstate logicman))
                   (x (bfr->aignet-lit x)))
                (stobj-let ((aignet (logicman->aignet logicman)))
                           (contra pathcond)
                           (b* ((pathcond (pathcond-fix pathcond)))
                             (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                                        (len contra aignet-pathcond)
                                        (b* ((len (aignet-pathcond-len aignet-pathcond))
                                             ((mv contra aignet-pathcond)
                                              (aignet-pathcond-assume x aignet aignet-pathcond))
                                             ((when contra)
                                              (b* ((aignet-pathcond (aignet-pathcond-rewind len aignet-pathcond)))
                                                (mv len contra aignet-pathcond))))
                                          (mv len contra aignet-pathcond))
                                        (b* (((when contra) (mv contra pathcond))
                                             (stack (cons len (pathcond-checkpoint-ptrs pathcond)))
                                             (pathcond (update-pathcond-checkpoint-ptrs stack pathcond)))
                                          (mv nil pathcond))))
                           (mv contra pathcond)))))
  ///
  ;; (defret logicman-get-of-logicman-pathcond-assume
  ;;   (implies (not (equal (logicman-field-fix key) :pathcond))
  ;;            (equal (logicman-get key new-logicman)
  ;;                   (logicman-get key logicman))))

  ;; (defret logicman-extension-p-of-logicman-pathcond-assume
  ;;   (logicman-extension-p new-logicman logicman))
  
  (local (defthm nbalist-stobj-rewind-of-assume-logic
           (equal (aignet::nbalist-stobj-rewind
                   (len (aignet::nbalist-fix nbalist))
                   (mv-nth 1 (aignet::aignet-pathcond-assume-logic
                              lit aignet nbalist)))
                  (aignet::nbalist-fix nbalist))
           :hints (("goal" :use ((:instance aignet::nbalist-extension-of-aignet-pathcond-assume-logic
                                  (nbalist-stobj nbalist) (lit lit) (aignet aignet)))
                    :in-theory (disable aignet::nbalist-extension-of-aignet-pathcond-assume-logic)))))

  (local (defthm rewind-calist-of-calist-assume
           (equal (rewind-calist
                   (len (calist-fix calist))
                   (mv-nth 1 (calist-assume lit calist)))
                  (calist-fix calist))
           :hints (("goal" :use ((:instance calist-extension-p-of-calist-assume
                                  (calist-stobj calist) (x lit)))
                    :in-theory (disable calist-extension-p-of-calist-assume)))))


  (local (defun aig-listp (x bound)
           (if (atom x)
               t
             (and (aig-p (car x) bound)
                  (aig-listp (cdr x) bound)))))

  (local (defthmd bfr-listp-when-aig-mode
           (implies (bfrstate-mode-is :aig)
                    (equal (bfr-listp x)
                           (aig-listp x (bfrstate->bound bfrstate))))
           :hints(("Goal" :in-theory (enable bfr-listp bfr-p)))))

  (local (defthm aig-listp-of-calist-assume
           (implies (and (aig-listp (alist-keys (calist-fix calist)) bound)
                         (aig-p x bound))
                    (aig-listp (alist-keys (mv-nth 1 (calist-assume x calist))) bound))
           :hints(("Goal" :in-theory (enable calist-assume alist-keys)))))

  (local (defthm bfr-mode-fix-possibilities
           (or (bfr-mode-is :aig)
               (bfr-mode-is :bdd)
               (bfr-mode-is :aignet))
           :rule-classes ((:forward-chaining :trigger-terms ((bfr-mode-fix bfr-mode))))))

  (local (defthm bfr-listp-of-calist-assume
           (implies (and (bfr-listp (alist-keys (calist-fix calist)))
                         (bfr-p x)
                         (bfrstate-mode-is :aig))
                    (bfr-listp (alist-keys (mv-nth 1 (calist-assume x calist)))))
           :hints(("Goal" :in-theory (enable bfr-listp-when-aig-mode bfr-p)))))

  (defret logicman-pathcond-p-of-<fn>
    (implies (and (logicman-pathcond-p pathcond)
                  (lbfr-p x))
             (logicman-pathcond-p new-pathcond))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable logicman-pathcond-p)))
            (and stable-under-simplificationp
                 '(:in-theory (enable bfr-p)))))
  

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
    (implies (and (not contradictionp)
                  (pathcond-enabledp pathcond))
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

  (local (defthm update-nth-redundant
           (implies (and (equal val (nth n x))
                         (< (nfix n) (len x)))
                    (equal (update-nth n val x) x))
           :hints(("Goal" :in-theory (enable nth update-nth len)))))

  (local (defthm len-of-pathcond-fix
           (equal (len (pathcond-fix x)) 6)
           :hints(("Goal" :in-theory (enable pathcond-fix)))))

  ;; (local (defthm len-of-calist-assume
  ;;          (implies (calistp calist)
  ;;                   (<= (len calist) (len (mv-nth 1 (calist-assume x calist)))))
  ;;          :hints(("Goal" :in-theory (enable calist-assume)))
  ;;          :rule-classes :linear))
  

  (defret pathcond-rewind-of-logicman-pathcond-assume
    (implies (and (not contradictionp)
                  (equal (bfr-mode-fix bfr-mode) (bfr-mode-fix (lbfr-mode))))
             (equal (pathcond-rewind bfr-mode new-pathcond)
                    (pathcond-fix pathcond)))
    :hints(("Goal" :in-theory (enable pathcond-rewind bfr-fix))
           (and stable-under-simplificationp
                '(:in-theory (enable pathcond-fix update-nth)))))

  (defret logicman-pathcond-assume-unchanged-when-contradictionp
    (implies contradictionp
             (equal new-pathcond
                    (pathcond-fix pathcond))))

  ;; (defret pathcond-checkpoint-p-of-logicman-pathcond-assume
  ;;   (implies (pathcond-checkpoint-p chp (lbfr-mode) pathcond)
  ;;            (pathcond-checkpoint-p chp (lbfr-mode) new-pathcond))
  ;;   :hints (("goal" :use ((:instance pathcond-checkpoint-p-when-rewindable
  ;;                          (old pathcond)
  ;;                          (new new-pathcond)
  ;;                          (bfr-mode (lbfr-mode))))
  ;;            :in-theory (disable pathcond-checkpoint-p-when-rewindable
  ;;                                logicman-pathcond-assume))))
  ;; (local
  ;;  #!aignet
  ;;  (Defthm depends-on-of-aignet-lit-fix
  ;;    (equal (depends-on (aignet-lit-fix lit aignet) ci-id aignet)
  ;;           (depends-on lit ci-id aignet))
  ;;    :hints (("goal" :expand ((depends-on (aignet-lit-fix lit aignet)
  ;;                                         ci-id aignet)
  ;;                             (depends-on lit ci-id aignet))))))

  ;; (defret logicman-pathcond-depends-on-of-logicman-pathcond-assume
  ;;   (implies (and (not (logicman-pathcond-depends-on v pathcond))
  ;;                 (not (bfr-depends-on v x ))
  ;;                 (bfr-varname-p v))
  ;;            (not (logicman-pathcond-depends-on v new-pathcond)))
  ;;   :hints(("Goal" :in-theory (enable logicman-pathcond-depends-on
  ;;                                     bfr-depends-on
  ;;                                     bfr-varname-p
  ;;                                     bfr-fix
  ;;                                     bfr-nvars
  ;;                                     bfr->aignet-lit))))

  (defret pathcond-enabledp-of-<fn>
    (iff* (nth *pathcond-enabledp* new-pathcond)
          (nth *pathcond-enabledp* pathcond)))

  (defret pathcond-rewind-stack-len-of-<fn>
    (implies (and (not contradictionp)
                  (pathcond-enabledp pathcond)
                  (equal mode (lbfr-mode)))
             (equal (pathcond-rewind-stack-len mode new-pathcond)
                    (+ 1 (pathcond-rewind-stack-len mode pathcond))))
    :hints(("Goal" :in-theory (enable pathcond-rewind-stack-len)))))






                                  

(define maybe-cons (do-it val lst)
  :verify-guards nil
  (if do-it (cons val lst) lst)
  ///
  (defcong iff equal (maybe-cons do-it val lst) 1))

(define maybe-cdr (do-it lst)
  :verify-guards nil
  (if do-it (cdr lst) lst)
  ///
  (defcong iff equal (maybe-cdr do-it lst) 1)
  (defthm maybe-cdr-of-maybe-cons
    (equal (maybe-cdr do-it (maybe-cons do-it val lst))
           lst)
    :hints(("Goal" :in-theory (enable maybe-cons)))))

(define maybe-incr (do-it x)
  :verify-guards nil
  (if do-it (+ 1 (nfix x)) (nfix x))
  ///
  (defthm maybe-incr-equal-0
    (implies do-it
             (not (equal (maybe-incr do-it x) 0))))
  (defcong iff equal (maybe-incr do-it x) 1))

(define maybe-decr (do-it x)
  :verify-guards nil
  (if do-it (nfix (+ -1 (nfix x))) (nfix x))
  ///
  (defcong iff equal (maybe-decr do-it x) 1)

  (defthm maybe-decr-of-maybe-incr
    (equal (maybe-decr do-it (maybe-incr do-it x))
           (nfix x))
    :hints(("Goal" :in-theory (enable maybe-incr)))))



(defthm pathcond-rewind-stack-len-of-pathcond-rewind
  (equal (pathcond-rewind-stack-len mode (pathcond-rewind mode pathcond))
         (maybe-decr (nth *pathcond-enabledp* pathcond)
                     (pathcond-rewind-stack-len mode pathcond)))
  :hints(("Goal" :in-theory (enable maybe-decr pos-fix nfix))
         (and stable-under-simplificationp
              '(:in-theory (enable pathcond-rewind)))))

(defret pathcond-rewind-stack-len-of-logicman-pathcond-assume-maybe
  (implies (and (equal mode (logicman->mode logicman))
                (not contradictionp))
           (equal (pathcond-rewind-stack-len mode new-pathcond)
                  (maybe-incr (nth *pathcond-enabledp* pathcond)
                              (pathcond-rewind-stack-len mode pathcond))))
  :hints(("Goal" :in-theory (enable maybe-incr pos-fix nfix))
         (and stable-under-simplificationp
              '(:in-theory (enable logicman-pathcond-assume))))
  :fn logicman-pathcond-assume)


(defthm pathcond-enabledp-of-pathcond-rewind
  (iff (nth *pathcond-enabledp* (pathcond-rewind mode pathcond))
       (nth *pathcond-enabledp* pathcond))
  :hints(("Goal" :in-theory (e/d (pathcond-rewind) (nth-add1 nth update-nth)))))

(define logicman-pathcond-eval-checkpoints (env pathcond logicman)
  :non-executable t
  :no-function t
  :verify-guards nil
  :measure (pathcond-rewind-stack-len (lbfr-mode) pathcond)
  :hints(("goal" :in-theory (enable maybe-decr)))
  (if (or (zp (pathcond-rewind-stack-len (lbfr-mode) pathcond))
          (not (pathcond-enabledp pathcond)))
      nil
    (b* ((pathcond (pathcond-rewind (lbfr-mode) pathcond))
         (eval (logicman-pathcond-eval env pathcond logicman)))
      (cons eval (logicman-pathcond-eval-checkpoints env pathcond logicman))))
  ///
  (deffixequiv logicman-pathcond-eval-checkpoints)

  (defthm logicman-pathcond-eval-checkpoints-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (logicman-pathcond-p pathcond old))
             (equal (logicman-pathcond-eval-checkpoints env pathcond new)
                    (logicman-pathcond-eval-checkpoints env pathcond old))))


  (defret logicman-pathcond-eval-checkpoints-of-logicman-pathcond-assume
    (implies (and (not contradictionp)
                  (equal (logicman->mode logicman) (logicman->mode logicman1)))
             (equal (logicman-pathcond-eval-checkpoints env new-pathcond logicman1)
                    (maybe-cons (nth *pathcond-enabledp* pathcond)
                                (logicman-pathcond-eval env pathcond logicman1)
                                (logicman-pathcond-eval-checkpoints env pathcond logicman1))))
    :hints(("Goal" :in-theory (enable maybe-cons)))
    :fn logicman-pathcond-assume)

  (defret logicman-pathcond-eval-checkpoints-of-pathcond-rewind
    (implies (equal bfr-mode (lbfr-mode))
             (equal (logicman-pathcond-eval-checkpoints env new-pathcond logicman)
                    (maybe-cdr (nth *pathcond-enabledp* pathcond)
                               (logicman-pathcond-eval-checkpoints env pathcond logicman))))
    :hints(("Goal" :in-theory (enable maybe-cdr maybe-incr maybe-decr)
            :expand ((logicman-pathcond-eval-checkpoints env pathcond logicman)
                     (logicman-pathcond-eval-checkpoints env (pathcond-rewind (lbfr-mode) pathcond) logicman))))
    :fn pathcond-rewind)

  (defthm len-of-logicman-pathcond-eval-checkpoints
    (implies (nth *pathcond-enabledp* pathcond)
             (equal (len (logicman-pathcond-eval-checkpoints env pathcond logicman))
                    (pathcond-rewind-stack-len (lbfr-mode) pathcond)))
    :hints(("Goal" :in-theory (enable maybe-cdr maybe-decr))))

  (defcong logicman-equiv equal (logicman-pathcond-eval-checkpoints env pathcond logicman) 3
    :hints (("goal" :induct (logicman-pathcond-eval-checkpoints env pathcond logicman)
             :in-theory (enable maybe-cdr)
             :expand ((logicman-pathcond-eval-checkpoints env pathcond logicman))))))


(define logicman-pathcond-eval-checkpoints! (env pathcond logicman)
  :non-executable t
  :no-function t
  :verify-guards nil
  (b* ((pathcond (update-nth *pathcond-enabledp* t pathcond)))
    (cons (logicman-pathcond-eval env pathcond logicman)
          (logicman-pathcond-eval-checkpoints env pathcond logicman)))
  ///
  (deffixequiv logicman-pathcond-eval-checkpoints)

  (defthm update-pathcond-enabledp-under-pathcond-equiv
    (implies (iff* enabledp (pathcond-enabledp pathcond))
             (pathcond-equiv (update-nth *pathcond-enabledp* enabledp pathcond)
                             pathcond))
    :hints(("Goal" :in-theory (enable pathcond-fix))))

  (fty::deffixcong pathcond-equiv pathcond-equiv (update-nth n v x) x
    :hints(("Goal" :in-theory (enable pathcond-fix))))

  ;; (local (defthm logicman-pathcond-eval-checkpoints-of-update-pathcond-enabledp
  ;;          (implies (nth *pathcond-enabledp* pathcond)
  ;;                   (equal (logicman-pathcond-eval-checkpoints
  ;;                           env (update-nth *pathcond-enabledp* t pathcond) logicman)
  ;;                          (logicman-pathcond-eval-checkpoints
  ;;                           env pathcond logicman)))
  ;;          :hints(("Goal" :in-theory (e/d (logicman-pathcond-eval-checkpoints)
  ;;                                         (LOGICMAN-PATHCOND-EVAL-CHECKPOINTS-OF-PATHCOND-REWIND)))
  ;;                 (and (equal id (acl2::parse-clause-id "Subgoal *1/3'10'"))
  ;;                      '(:error t)))))

  (defthm logicman-pathcond-eval-checkpoints!-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (logicman-pathcond-p pathcond old))
             (equal (logicman-pathcond-eval-checkpoints! env pathcond new)
                    (logicman-pathcond-eval-checkpoints! env pathcond old))))

  (defret logicman-pathcond-eval-checkpoints!-of-logicman-pathcond-assume
    (implies (and (not contradictionp)
                  (equal (logicman->mode logicman) (logicman->mode logicman1)))
             (equal (logicman-pathcond-eval-checkpoints! env new-pathcond logicman1)
                    (maybe-cons (nth *pathcond-enabledp* pathcond)
                                (logicman-pathcond-eval env new-pathcond logicman1)
                                (logicman-pathcond-eval-checkpoints! env pathcond logicman1))))
    :hints(("Goal" :in-theory (enable maybe-cons))
           (and stable-under-simplificationp
                '(:in-theory (enable logicman-pathcond-assume))))
    :fn logicman-pathcond-assume)

  (defret logicman-pathcond-eval-checkpoints!-of-pathcond-rewind
    (implies (and (equal bfr-mode (lbfr-mode))
                  (pathcond-rewind-ok bfr-mode pathcond))
             (equal (logicman-pathcond-eval-checkpoints! env new-pathcond logicman)
                    (maybe-cdr (nth *pathcond-enabledp* pathcond)
                               (logicman-pathcond-eval-checkpoints! env pathcond logicman))))
    :hints(("Goal" :in-theory (enable maybe-cdr)
            :expand ((logicman-pathcond-eval-checkpoints env pathcond logicman)))
           (and stable-under-simplificationp
                '(:in-theory (enable pathcond-rewind pathcond-rewind-ok)))
           )
    :fn pathcond-rewind)

  (local (defthm update-nth-of-update-nth
           (equal (update-nth n a (update-nth n b x))
                  (update-nth n a x))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (defthm logicman-pathcond-eval-checkpoints!-of-update-pathcond-enabledp
    (equal (logicman-pathcond-eval-checkpoints! env (update-nth *pathcond-enabledp* v pathcond) logicman)
           (logicman-pathcond-eval-checkpoints! env pathcond logicman)))

  (defthm pathcond-rewind-stack-len-of-update-pathcond-enabledp
    (equal (pathcond-rewind-stack-len mode (update-nth *pathcond-enabledp* v pathcond))
           (pathcond-rewind-stack-len mode pathcond))
    :hints(("Goal" :in-theory (enable pathcond-rewind-stack-len))))

  (defthm len-of-logicman-pathcond-eval-checkpoints!
    (equal (len (logicman-pathcond-eval-checkpoints! env pathcond logicman))
           (+ 1 (pathcond-rewind-stack-len (lbfr-mode) pathcond))))

  (defcong logicman-equiv equal (logicman-pathcond-eval-checkpoints! env pathcond logicman) 3
    :hints (("goal"
             :expand ((logicman-pathcond-eval-checkpoints! env pathcond logicman))))))



      
                
(local (defthm cdr-of-nthcdr
         (equal (cdr (nthcdr n x))
                (nthcdr n (cdr x)))))
(local (defthm hons-assoc-equal-in-pairlis-numlist
         (implies (and (natp start) (natp n))
                  (equal (cdr (hons-assoc-equal n (pairlis$ (numlist start 1 k) (nthcdr start x))))
                         (and (< (- n start) (nfix k))
                              (<= start n)
                              (nth n x))))
         :hints(("Goal" :in-theory (enable car-of-nthcdr)
                 :induct (numlist start 1 k)))))

(local (defthm hons-assoc-equal-in-pairlis-numlist-base
         (implies (natp n)
                  (equal (cdr (hons-assoc-equal n (pairlis$ (numlist 0 1 k) x)))
                         (and (< n (nfix k))
                              (nth n x))))
         :hints(("Goal" :use ((:instance hons-assoc-equal-in-pairlis-numlist
                               (start 0)))
                 :in-theory (disable hons-assoc-equal-in-pairlis-numlist)))))
                          

(local
 (defthm nth-alist-to-bitarr-of-pairlis$
   (acl2::bit-equiv (nth n (alist-to-bitarr k (pairlis$ (acl2::numlist 0 1 k) bits) nil))
                    (if (< (nfix n) (nfix k))
                        (bool->bit (nth n bits))
                      0))))

(define bools->bits (x)
  :Returns (bits)
  (if (atom x)
      nil
    (cons (bool->bit (car x))
          (bools->bits (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len bits) (len x)))
  (defretd nth-of-<fn>
    (equal (nth n bits)
           (and (< (nfix n) (len x))
                (bool->bit (nth n x))))
    :hints(("Goal" :in-theory (enable nth)
            :induct (nth n x))))
  (defret nth-of-<fn>-under-bit-equiv
    (acl2::bit-equiv (nth n bits)
                     (bool->bit (nth n x)))
    :hints(("Goal" :in-theory (enable nth-of-bools->bits)))))

(define bits->bools (x)
  :Returns (bits)
  (if (atom x)
      nil
    (cons (bit->bool (car x))
          (bits->bools (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len bits) (len x)))
  (defret nth-of-<fn>
    (equal (nth n bits)
           (bit->bool (nth n x)))
    :hints(("Goal" :in-theory (enable nth)
            :induct (nth n x)))))

(local
 (defthm alist-to-bitarr-of-pairlis$-under-bits-equiv
   (acl2::bits-equiv (alist-to-bitarr k (pairlis$ (acl2::numlist 0 1 k) bools) nil)
                     (take k (bools->bits bools)))
   :hints(("Goal" :in-theory (enable acl2::bits-equiv)))))

(local
 (defthm bools->bits-of-bits->bools-under-bits-equiv
   (acl2::bits-equiv (bools->bits (bits->bools x)) x)
   :hints(("Goal" :in-theory (enable acl2::bits-equiv)))))


;; (defconst *logicman-empty-ipasir*
;;   (ipasir::make-ipasir$a :status :input :history '(ok)))

;; (define logicman-delete-ipasir (logicman)
;;   :non-executable t
;;   :verify-guards nil
;;   :returns new-logicman
;;   (update-logicman->ipasir *logicman-empty-ipasir* logicman)
;;   ///
;;   (defret logicman->ipasir-of-<fn>
;;     (equal (logicman->ipasir new-logicman)
;;            *logicman-empty-ipasir*))

;;   (defret logicman-get-of-<fn>
;;     (implies (not (equal (logicman-field-fix key) :ipasir))
;;              (equal (logicman-get key new-logicman)
;;                     (logicman-get key logicman))))

;;   (defret logicman-invar-of-<fn>
;;     (implies (logicman-invar logicman)
;;              (logicman-invar new-logicman))
;;     :hints(("Goal" :in-theory (enable logicman-invar)))))




(define logicman-pathcond-to-ipasir ((ipasir-index natp) pathcond logicman)
  :guard (and (ec-call (bfr-pathcond-p-fn pathcond (logicman->bfrstate)))
              (< ipasir-index (logicman->ipasir-length logicman))
              (logicman-invar logicman)
              (lbfr-mode-is :aignet)
              (stobj-let ((ipasir (logicman->ipasiri ipasir-index logicman)))
                         (ok)
                         (not (equal (ipasir-get-status ipasir) :undef))
                         ok)
              )
  :guard-hints (("goal" :in-theory (enable logicman-pathcond-p
                                           logicman-invar)))
  :returns (new-logicman)
  (b* (((unless (mbt (lbfr-mode-is :aignet)))
        (stobj-let ((ipasir (logicman->ipasiri ipasir-index logicman)))
                   (ipasir)
                   (ipasir::ipasir-input ipasir)
                   logicman))
       (logicman (logicman-update-refcounts logicman)))
    (stobj-let ((aignet (logicman->aignet logicman))
                (sat-lits (logicman->sat-litsi ipasir-index logicman))
                (ipasir (logicman->ipasiri ipasir-index logicman))
                (u32arr (logicman->aignet-refcounts logicman)))
               (sat-lits ipasir)
               (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                          (sat-lits ipasir)
                          (b* ((ipasir (ipasir::ipasir-input ipasir)))
                            (aignet::aignet-pathcond-to-ipasir
                             aignet-pathcond aignet sat-lits ipasir u32arr))
                          (mv sat-lits ipasir))
               logicman))
  ///

  ;;(local (in-theory (enable ipasir::ipasir-input$a)))
  (local (defret logicman-ipasir-sat-lits-invar-of-ipasir-input$a
           (implies (and (logicman-ipasir-sat-lits-invar logicman)
                         (< (nfix n) (logicman->ipasir-length logicman))
                         (not (equal (ipasir::ipasir$a->status (logicman->ipasiri n logicman)) :undef)))
                    (logicman-ipasir-sat-lits-invar
                     (update-logicman->ipasiri n
                                               (ipasir::ipasir-input$a (logicman->ipasiri n logicman))
                                               logicman)))
           :hints (("goal" :in-theory (enable ipasir::ipasir-input$a))
                   (and stable-under-simplificationp
                        (let ((lit (car (last clause))))
                          `(:expand (,lit)
                            :in-theory (enable logicman->ipasiri-of-update-logicman->ipasiri-split)))))))

  (local (defthm consp-history-of-ipasir-input$a
           (equal (ipasir::ipasir$a->history (ipasir::ipasir-input$a ipasir))
                  (ipasir::ipasir$a->history ipasir))
           :hints(("Goal" :in-theory (enable ipasir::ipasir-input$a)))))

  (local (defret logicman-ipasir-sat-lits-invar-of-<fn>
           (implies (and (logicman-ipasir-sat-lits-invar logicman)
                         (logicman-pathcond-p pathcond)
                         (< (nfix ipasir-index) (logicman->ipasir-length logicman))
                         (not (equal (ipasir::ipasir$a->status (logicman->ipasiri ipasir-index logicman)) :undef)))
                    (logicman-ipasir-sat-lits-invar new-logicman))
           :hints(("Goal" :in-theory (enable logicman-pathcond-p))
                  ;; (and stable-under-simplificationp
                  ;;      (let ((lit (car (last clause))))
                  ;;      `(:expand (,lit)
                  ;;        :use ((:instance logicman-ipasir-sat-lits-invar-necc
                  ;;               (n (logicman-ipasir-sat-lits-invar-witness . ,(cdr lit))))
                  ;;              (:instance logicman-ipasir-sat-lits-invar-necc
                  ;;               (n ipasir-index)))
                  ;;        :in-theory (e/d (logicman->ipasiri-of-update-logicman->ipasiri-split
                  ;;                         logicman->sat-litsi-of-update-logicman->sat-litsi-split)
                  ;;                        (logicman-ipasir-sat-lits-invar-necc)))))
                  )))

  (defret logicman-invar-of-<fn>
    (implies (and (logicman-invar logicman)
                  (logicman-pathcond-p pathcond)
                  (< (nfix ipasir-index) (logicman->ipasir-length logicman))
                  (not (equal (ipasir::ipasir$a->status (logicman->ipasiri ipasir-index logicman)) :undef)))
             (logicman-invar new-logicman))
    :hints(("Goal" :in-theory (e/d (logicman-invar
                                    logicman-pathcond-p)
                                   (logicman-ipasir-sat-lits-invar-of-logicman-pathcond-to-ipasir))
            :use logicman-ipasir-sat-lits-invar-of-logicman-pathcond-to-ipasir)))

  (local (defthm eval-cube-of-append
           (equal (satlink::eval-cube (append x y) env)
                  (b-and (satlink::eval-cube x env)
                         (satlink::eval-cube y env)))
           :hints(("Goal" :in-theory (enable satlink::eval-cube)))))

  (local (defthm eval-formula-of-append
           (equal (satlink::eval-formula (append x y) env)
                  (b-and (satlink::eval-formula x env)
                         (satlink::eval-formula y env)))
           :hints(("Goal" :in-theory (enable satlink::eval-formula)))))

  (defret logicman-ipasir-assumption-of-<fn>
    (implies (and (logicman-invar logicman)
                  (logicman-pathcond-p pathcond)
                  (equal (satlink::eval-formula
                          (ipasir::ipasir$a->formula (logicman->ipasiri ipasir-index new-logicman))
                          env)
                         1)
                  (lbfr-mode-is :aignet)
                  (nth *pathcond-enabledp* pathcond)
                  (< (nfix ipasir-index) (logicman->ipasir-length logicman))
                  (not (equal (ipasir::ipasir$a->status (logicman->ipasiri ipasir-index logicman)) :undef)))
             (equal (satlink::eval-cube
                     (ipasir::ipasir$a->assumption (logicman->ipasiri ipasir-index new-logicman))
                     env)
                    (b-and (satlink::eval-cube (ipasir::ipasir$a->assumption (logicman->ipasiri ipasir-index logicman)) env)
                           (b* ((vals (aignet::cnf->aignet-invals
                                       nil env (logicman->sat-litsi ipasir-index new-logicman)
                                       (logicman->aignet logicman))))
                             (bool->bit (logicman-pathcond-eval (pairlis$
                                                                 (acl2::numlist 0 1
                                                                                (aignet::num-ins (logicman->aignet logicman)))
                                                                 (bits->bools vals))
                                                                pathcond logicman))))))
    :hints(("Goal" :in-theory (enable logicman-invar logicman-pathcond-p
                                      logicman-pathcond-eval))))

  (defret logicman-equiv-of-<fn>
    (logicman-equiv new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-equiv))))

  (defret logicman-get-of-<fn>
    (implies (and (not (equal (logicman-field-fix key) :sat-lits))
                  (not (equal (logicman-field-fix key) :ipasir))
                  (not (equal (logicman-field-fix key) :refcounts-index))
                  (not (equal (logicman-field-fix key) :aignet-refcounts)))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

  ;; (defret ipasir-formula-norm-of-<fn>
  ;;   (implies (and (equal ipasir (logicman->ipasir logicman))
  ;;                 (syntaxp (and (quotep ipasir)
  ;;                               (equal (unquote ipasir) *logicman-empty-ipasir*))))
  ;;            (equal
  ;;             (ipasir::ipasir$a->formula (logicman->ipasir new-logicman))
  ;;             (append (ipasir::ipasir$a->formula (logicman->ipasir
  ;;                                                 (logicman-pathcond-to-ipasir
  ;;                                                  pathcond (logicman-delete-ipasir logicman))))
  ;;                     (ipasir::ipasir$a->formula ipasir))))
  ;;   :hints(("Goal" :in-theory (enable logicman-delete-ipasir
  ;;                                     logicman-update-refcounts))))
  ;; (defret ipasir-assumption-norm-of-<fn>
  ;;   (implies (and (equal ipasir (logicman->ipasir logicman))
  ;;                 (syntaxp (and (quotep ipasir)
  ;;                               (equal (unquote ipasir) *logicman-empty-ipasir*))))
  ;;            (equal
  ;;             (ipasir::ipasir$a->assumption (logicman->ipasir new-logicman))
  ;;             (append (ipasir::ipasir$a->assumption (logicman->ipasir
  ;;                                                    (logicman-pathcond-to-ipasir
  ;;                                                     pathcond (logicman-delete-ipasir logicman))))
  ;;                     (ipasir::ipasir$a->assumption ipasir))))
  ;;   :hints(("Goal" :in-theory (enable logicman-delete-ipasir
  ;;                                     logicman-update-refcounts))))

  ;; (defret sat-lits-norm-of-<fn>
  ;;   (implies (and (equal ipasir (logicman->ipasir logicman))
  ;;                 (syntaxp (and (quotep ipasir)
  ;;                               (equal (unquote ipasir) *logicman-empty-ipasir*))))
  ;;            (equal
  ;;             (logicman->sat-lits new-logicman)
  ;;             (logicman->sat-lits
  ;;              (logicman-pathcond-to-ipasir
  ;;               pathcond (logicman-delete-ipasir logicman)))))
  ;;   :hints(("Goal" :in-theory (enable logicman-delete-ipasir
  ;;                                     logicman-update-refcounts))))

  (defret sat-lit-extension-p-of-<fn>
    (implies (equal sat-lits (logicman->sat-litsi ipasir-index logicman))
             (aignet::sat-lit-extension-p (logicman->sat-litsi ipasir-index new-logicman) sat-lits)))


  (defret nbalist-has-sat-lits-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  (logicman-invar logicman)
                  (logicman-pathcond-p pathcond logicman)
                  (< (nfix ipasir-index) (logicman->ipasir-length logicman))
                  (not (equal (ipasir::ipasir$a->status (logicman->ipasiri ipasir-index logicman)) :undef)))
             (aignet::nbalist-has-sat-lits
              (nth *pathcond-aignet* pathcond)
              (logicman->sat-litsi ipasir-index new-logicman)))
    :hints(("Goal" :in-theory (enable logicman-invar logicman-pathcond-p))))

  (defret ipasir-status-of-<fn>
    (equal (ipasir::ipasir$a->status (logicman->ipasiri ipasir-index new-logicman))
           :input))

  (defret ipasirs-length-of-<fn>
    (implies (< (nfix ipasir-index) (logicman->ipasir-length logicman))
             (equal (logicman->ipasir-length new-logicman)
                    (logicman->ipasir-length logicman))))

  (defret sat-lits-length-of-<fn>
    (implies (< (nfix ipasir-index) (logicman->sat-lits-length logicman))
             (equal (logicman->sat-lits-length new-logicman)
                    (logicman->sat-lits-length logicman))))

  (defret other-ipasir-of-<fn>
    (implies (and (< (nfix ipasir-index) (logicman->ipasir-length logicman))
                  (not (equal (nfix n) (nfix ipasir-index))))
             (equal (logicman->ipasiri n new-logicman)
                    (logicman->ipasiri n logicman))))

  (defret other-sat-lits-of-<fn>
    (implies (and (< (nfix ipasir-index) (logicman->sat-lits-length logicman))
                  (not (equal (nfix n) (nfix ipasir-index))))
             (equal (logicman->sat-litsi n new-logicman)
                    (logicman->sat-litsi n logicman)))))


(define logicman-pathcond-to-cnf (pathcond logicman
                                           sat-lits
                                           (cnf satlink::lit-list-listp)
                                           (cube satlink::lit-listp))
  :guard (and (ec-call (bfr-pathcond-p-fn pathcond (logicman->bfrstate)))
              (lbfr-mode-is :aignet)
              (stobj-let ((aignet (logicman->aignet logicman)))
                         (ok)
                         (aignet::sat-lits-wfp sat-lits aignet)
                         ok))
  :guard-hints (("goal" :in-theory (enable logicman-pathcond-p
                                           logicman-invar)))
  :returns (mv new-logicman
               new-sat-lits
               (new-cnf satlink::lit-list-listp)
               (new-cube satlink::lit-listp))
  (b* (((unless (mbt (lbfr-mode-is :aignet)))
        (mv logicman
            sat-lits
            (satlink::lit-list-list-fix cnf)
            (satlink::lit-list-fix cube)))
       (logicman (logicman-update-refcounts logicman)))
    (stobj-let ((aignet (logicman->aignet logicman))
                (u32arr (logicman->aignet-refcounts logicman)))
               (sat-lits cnf cube)
               (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                          (sat-lits cnf cube)
                          (aignet::aignet-pathcond-to-cnf
                           aignet-pathcond aignet sat-lits cnf cube u32arr)
                          (mv sat-lits cnf cube))
               (mv logicman sat-lits cnf cube)))
  ///
  (defret sat-lit-listp-of-<fn>
    (implies (and (aignet::sat-lits-wfp sat-lits (logicman->aignet logicman))
                  (logicman-pathcond-p pathcond logicman))
             (and (implies (aignet::sat-lit-list-listp cnf sat-lits)
                           (aignet::sat-lit-list-listp new-cnf new-sat-lits))
                  (implies (aignet::sat-lit-listp cube sat-lits)
                           (aignet::sat-lit-listp new-cube new-sat-lits))
                  (implies (equal aignet (logicman->aignet logicman))
                           (aignet::sat-lits-wfp new-sat-lits aignet))))
    :hints(("Goal" :in-theory (enable logicman-pathcond-p))))

  (defret cnf-for-aignet-of-<fn>
    (implies (and (equal aignet (logicman->aignet logicman))
                  (aignet::cnf-for-aignet aignet cnf sat-lits)
                  (aignet::sat-lits-wfp sat-lits (logicman->aignet logicman))
                  (logicman-pathcond-p pathcond logicman)
                  (aignet::sat-lit-list-listp cnf sat-lits))
             (aignet::cnf-for-aignet aignet new-cnf new-sat-lits))
    :hints(("Goal" :in-theory (e/d (logicman-pathcond-p)
                                   (aignet::nbalist-to-cnf-normalize-cnf)))))

  (local (defthm eval-cube-of-append
           (equal (satlink::eval-cube (append x y) env)
                  (b-and (satlink::eval-cube x env)
                         (satlink::eval-cube y env)))
           :hints(("Goal" :in-theory (enable satlink::eval-cube)))))

  (local (defthm eval-formula-of-append
           (equal (satlink::eval-formula (append x y) env)
                  (b-and (satlink::eval-formula x env)
                         (satlink::eval-formula y env)))
           :hints(("Goal" :in-theory (enable satlink::eval-formula)))))

  (defret eval-cube-of-<fn>
    (implies (and (aignet::sat-lit-list-listp cnf sat-lits)
                  (aignet::sat-lit-listp cube sat-lits)
                  (aignet::sat-lits-wfp sat-lits (logicman->aignet logicman))
                  (aignet::cnf-for-aignet (logicman->aignet logicman) cnf sat-lits)
                  (logicman-pathcond-p pathcond)
                  (equal (satlink::eval-formula new-cnf env) 1)
                  (lbfr-mode-is :aignet)
                  (equal (aignet::stype-count :reg (logicman->aignet logicman)) 0)
                  (nth *pathcond-enabledp* pathcond))
             (equal (satlink::eval-cube new-cube env)
                    (b-and (satlink::eval-cube cube env)
                           (b* ((vals (aignet::cnf->aignet-invals
                                       nil env new-sat-lits
                                       (logicman->aignet logicman))))
                             (bool->bit (logicman-pathcond-eval (pairlis$
                                                                 (acl2::numlist 0 1
                                                                                (aignet::num-ins (logicman->aignet logicman)))
                                                                 (bits->bools vals))
                                                                pathcond logicman))))))
    :hints(("Goal" :in-theory (enable logicman-invar logicman-pathcond-p
                                      logicman-pathcond-eval))))

  ;; (defret ipasir-formula-norm-of-<fn>
  ;;   (implies (and (equal ipasir (logicman->ipasir logicman))
  ;;                 (syntaxp (and (quotep ipasir)
  ;;                               (equal (unquote ipasir) *logicman-empty-ipasir*))))
  ;;            (equal
  ;;             (ipasir::ipasir$a->formula (logicman->ipasir new-logicman))
  ;;             (append (ipasir::ipasir$a->formula (logicman->ipasir
  ;;                                                 (logicman-pathcond-to-ipasir
  ;;                                                  pathcond (logicman-delete-ipasir logicman))))
  ;;                     (ipasir::ipasir$a->formula ipasir))))
  ;;   :hints(("Goal" :in-theory (enable logicman-delete-ipasir
  ;;                                     logicman-update-refcounts))))
  ;; (defret ipasir-assumption-norm-of-<fn>
  ;;   (implies (and (equal ipasir (logicman->ipasir logicman))
  ;;                 (syntaxp (and (quotep ipasir)
  ;;                               (equal (unquote ipasir) *logicman-empty-ipasir*))))
  ;;            (equal
  ;;             (ipasir::ipasir$a->assumption (logicman->ipasir new-logicman))
  ;;             (append (ipasir::ipasir$a->assumption (logicman->ipasir
  ;;                                                    (logicman-pathcond-to-ipasir
  ;;                                                     pathcond (logicman-delete-ipasir logicman))))
  ;;                     (ipasir::ipasir$a->assumption ipasir))))
  ;;   :hints(("Goal" :in-theory (enable logicman-delete-ipasir
  ;;                                     logicman-update-refcounts))))

  ;; (defret sat-lits-norm-of-<fn>
  ;;   (implies (and (equal ipasir (logicman->ipasir logicman))
  ;;                 (syntaxp (and (quotep ipasir)
  ;;                               (equal (unquote ipasir) *logicman-empty-ipasir*))))
  ;;            (equal
  ;;             (logicman->sat-lits new-logicman)
  ;;             (logicman->sat-lits
  ;;              (logicman-pathcond-to-ipasir
  ;;               pathcond (logicman-delete-ipasir logicman)))))
  ;;   :hints(("Goal" :in-theory (enable logicman-delete-ipasir
  ;;                                     logicman-update-refcounts))))

  
  (defret logicman-equiv-of-<fn>
    (logicman-equiv new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-equiv))))

  (defret logicman-get-of-<fn>
    (implies (and (not (equal (logicman-field-fix key) :refcounts-index))
                  (not (equal (logicman-field-fix key) :aignet-refcounts)))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

  (defret sat-lit-extension-p-of-<fn>
    (aignet::sat-lit-extension-p new-sat-lits sat-lits))


  (defret nbalist-has-sat-lits-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  (logicman-pathcond-p pathcond logicman)
                  (aignet::sat-lits-wfp sat-lits (logicman->aignet logicman)))
             (aignet::nbalist-has-sat-lits
              (nth *pathcond-aignet* pathcond)
              new-sat-lits))
    :hints(("Goal" :in-theory (enable logicman-invar logicman-pathcond-p)))))

(define bfr-cube-eval ((x lbfr-listp) env logicman)
  (if (atom x)
      t
    (and (bfr-eval (car x) env)
         (bfr-cube-eval (cdr x) env logicman)))
  ///
  (defthm bfr-cube-eval-of-cons
    (equal (bfr-cube-eval (cons x y) env logicman)
           (and (bfr-eval x env)
                (bfr-cube-eval y env logicman))))

  (defthm bfr-cube-eval-of-append
    (equal (bfr-cube-eval (append x y) env logicman)
           (and (bfr-cube-eval x env logicman)
                (bfr-cube-eval y env logicman)))))

(local (defthm lit-listp-of-rev
         (implies (satlink::lit-listp x)
                  (satlink::lit-listp (rev x)))
         :hints(("Goal" :in-theory (enable rev)))))

(define pathcond-to-cube (pathcond
                          (cube satlink::lit-listp))
  :returns (new-cube satlink::lit-listp)
  (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
             (cube)
             (aignet::aignet-pathcond-to-cube aignet-pathcond cube)
             cube)
  ///
  (local (defthm aignet-eval-conjunction-of-append
           (equal (aignet::aignet-eval-conjunction (append x y) invals regvals aignet)
                  (b-and (aignet::aignet-eval-conjunction x invals regvals aignet)
                         (aignet::aignet-eval-conjunction y invals regvals aignet)))
           :hints(("Goal" :in-theory (enable aignet::aignet-eval-conjunction)))))

  (local (defthm aignet-eval-conjunction-of-rev
           (equal (aignet::aignet-eval-conjunction (rev x) invals regvals aignet)
                  (aignet::aignet-eval-conjunction x invals regvals aignet))
           :hints(("Goal" :in-theory (enable rev aignet::aignet-eval-conjunction)))))

  (defret pathcond-eval-of-<fn>-free
    (implies (and (lbfr-mode-is :aignet)
                  (equal invals (alist-to-bitarr (aignet::num-ins (logicman->aignet logicman)) env nil))
                  (nth *pathcond-enabledp* pathcond))
             (equal (aignet::aignet-eval-conjunction
                     new-cube invals nil (logicman->aignet logicman))
                    (b-and (bool->bit (logicman-pathcond-eval env pathcond))
                           (aignet::aignet-eval-conjunction
                            cube invals nil (logicman->aignet logicman)))))
    :hints(("Goal" :in-theory (enable logicman-pathcond-eval))))

  (defret pathcond-eval-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  (nth *pathcond-enabledp* pathcond))
             (equal (aignet::aignet-eval-conjunction
                     new-cube
                     (alist-to-bitarr (aignet::stype-count :pi (logicman->aignet logicman)) env nil)
                     nil (logicman->aignet logicman))
                    (b-and (bool->bit (logicman-pathcond-eval env pathcond))
                           (aignet::aignet-eval-conjunction
                            cube
                            (alist-to-bitarr (aignet::stype-count :pi (logicman->aignet logicman)) env nil)
                            nil (logicman->aignet logicman)))))
    :hints(("Goal" :in-theory (enable logicman-pathcond-eval))))

  (local
   #!aignet
   (defthm aignet-lit-listp-of-append
     (implies (and (aignet-lit-listp a aignet)
                   (aignet-lit-listp b aignet))
              (aignet-lit-listp (append a b) aignet))))

  (local
   #!aignet
   (defthm aignet-lit-listp-of-rev
     (implies (aignet-lit-listp a aignet)
              (aignet-lit-listp (acl2::rev a) aignet))))

  (defret aignet-lit-listp-of-<fn>
    (implies (and (logicman-pathcond-p pathcond)
                  (lbfr-mode-is :aignet)
                  (aignet::aignet-lit-listp cube (logicman->aignet logicman)))
             (aignet::aignet-lit-listp new-cube (logicman->aignet logicman)))
    :hints(("Goal" :in-theory (enable logicman-pathcond-p)))))

             
                    
                  
