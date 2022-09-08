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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "SV")

;; (include-book "../svex/unroll")
(include-book "fsm-base")
(include-book "../svex/rewrite")
(include-book "centaur/sv/svex/alist-equiv" :dir :system)
(local (include-book "centaur/sv/svex/alist-thms" :dir :System))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (std::add-default-post-define-hook :fix))


(local (in-theory (disable acl2::nth-when-zp
                           nth update-nth)))

(defthm svex-alist-p-of-nth
  (implies (svex-alistlist-p x)
           (svex-alist-p (nth n x)))
  :hints(("Goal" :in-theory (enable svex-alistlist-p nth))))



(deffixcong svex-alistlist-equiv svex-alist-equiv (nth n x) x
  :hints(("Goal" :in-theory (enable svex-alistlist-fix nth))))

(defprod svtv-composedata
  ((simp svex-simpconfig-p)
   (nextstates svex-alistlist-p) ;; 0th is initst
   (input-substs svex-alistlist-p))
  :layout :tree)

(local (deffixcong svex-alist-equiv svex-alist-equiv (append x y) x))
(local (deffixcong svex-alist-equiv svex-alist-equiv (append x y) y))

;; (define svex-alist-compose-multistate-unroll ((x svex-alist-p)
;;                                               (phase natp)
;;                                               (states svex-alistlist-p)
;;                                               (inputs svex-alistlist-p))
;;   :Returns (compose svex-alist-p)
;;   :measure (nfix phase)
;;   :ruler-extenders :lambdas
;;   :verify-guards :after-returns
;;   (b* ((state-alist (nth phase states))
;;        (state-unroll (if (zp phase)
;;                          state-alist
;;                        (svex-alist-compose-multistate-unroll state-alist (1- phase) states inputs)))
;;        (compose-alist (append state-unroll (nth phase inputs))))
;;     (svex-alist-compose x compose-alist))
;;   ///
;;   (defret lookup-in-<fn>
;;     (equal (svex-lookup k compose)
;;            (and (svex-lookup k x)
;;                 (svex-compose (svex-lookup k x)
;;                               (b* ((state-alist (nth phase states))
;;                                    (state-unroll (if (zp phase)
;;                                                      state-alist
;;                                                    (svex-alist-compose-multistate-unroll state-alist (1- phase) states inputs))))
;;                                 (append state-unroll (nth phase inputs)))))))

;;   (defret <fn>-phase-0
;;     (implies (zp phase)
;;              (equal compose
;;                     (svex-alist-compose x (append (nth 0 states) (nth 0 inputs)))))))





(defthm svex-lookup-in-svex-alist-subst
  (equal (svex-lookup k (svex-alist-subst x a))
         (and (svex-lookup k x)
              (svex-subst (svex-lookup k x) a)))
  :hints(("Goal" :in-theory (enable svex-alist-subst svex-lookup svex-acons))))

(defthm svex-alist-keys-of-svex-alist-subst
  (equal (svex-alist-keys (svex-alist-subst x a))
         (svex-alist-keys x))
  :hints(("Goal" :in-theory (enable svex-alist-subst svex-alist-keys))))

(define svex-unroll-multistate-phase-state ((phase natp)
                                            (states svex-alistlist-p)
                                            (inputs svex-alistlist-p))
  :Returns (compose svex-alist-p)
  :measure (nfix phase)
  :ruler-extenders :lambdas
  :verify-guards :after-returns
  (b* ((state-alist (nth phase (svex-alistlist-fix states)))
       ((when (zp phase)) state-alist) ;; 0th phase is initial state
       (compose-alist (append (svex-unroll-multistate-phase-state (1- phase) states inputs)
                              (nth (1- phase) inputs))))
    (svex-alist-subst state-alist compose-alist))
  ///
  (defret lookup-in-<fn>
    (equal (svex-lookup k compose)
           (let ((state-look (svex-lookup k (nth phase states))))
             (if (zp phase)
                 state-look
               (and state-look
                    (svex-subst state-look
                                  (append (svex-unroll-multistate-phase-state (1- phase) states inputs)
                                          (nth (1- phase) inputs))))))))

  (defret <fn>-phase-0
    (implies (zp phase)
             (equal compose (svex-alist-fix (nth 0 states)))))

  ;; (local (defthm svex-alist-keys-of-svex-alist-compose
  ;;          (Equal (svex-alist-keys (svex-alist-compose x y))
  ;;                 (svex-alist-keys x))
  ;;          :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-compose)))))
  
  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys compose)
           (svex-alist-keys (nth phase states)))))


(local (in-theory (disable acl2::hons-dups-p)))

(local
 (encapsulate nil
   
   (local
    (defthm svex-alist-extract-when-car-unbound
      (implies (not (member-equal (caar x) (svarlist-fix vars)))
               (equal (svex-alist-extract vars x)
                      (svex-alist-extract vars (cdr x))))
      :hints(("Goal" :in-theory (enable svex-alist-extract
                                        svex-lookup-redef)))))

    (defthm svex-alist-extract-of-svex-alist-keys
         (implies (no-duplicatesp-equal (svex-alist-keys x))
                  (equal (svex-alist-extract (svex-alist-keys x) x)
                         (svex-alist-fix x)))
         :hints(("Goal" :in-theory (enable svex-alist-keys
                                           svex-alist-fix
                                           svex-lookup-redef
                                           svex-alist-extract))))))

;; move to alist-thms.lisp
(defthm svex-alist-keys-of-svex-alist-extract
  (equal (svex-alist-keys (svex-alist-extract keys x))
         (svarlist-fix keys))
  :hints(("Goal" :in-theory (enable svex-alist-extract svex-alist-keys))))

(define svex-unroll-phase-state ((phase natp)
                                 (nextstate svex-alist-p)
                                 (initst svex-alist-p)
                                 (inputs svex-alistlist-p))
  :Returns (compose svex-alist-p)
  :measure (nfix phase)
  :ruler-extenders :lambdas
  :verify-guards :after-returns
  :guard (and (equal (svex-alist-keys nextstate)
                     (svex-alist-keys initst))
              (not (acl2::hons-dups-p (svex-alist-keys initst))))
  (b* (((when (zp phase))
        (mbe :logic (svex-alist-extract (svex-alist-keys nextstate) initst)
             :exec initst))
       (compose-alist (append (svex-unroll-phase-state (1- phase) nextstate initst inputs)
                              (nth (1- phase) inputs))))
    (svex-alist-subst nextstate compose-alist))
  ///
  
  (defret lookup-in-<fn>
    (equal (svex-lookup k compose)
             (if (zp phase)
                 (and (svex-lookup k nextstate)
                      (or (svex-lookup k initst) (svex-x)))
               (b* ((state-look (svex-lookup k nextstate)))
                 (and state-look
                      (svex-subst state-look
                                    (append (svex-unroll-phase-state (1- phase) nextstate initst inputs)
                                            (nth (1- phase) inputs))))))))

  (defret <fn>-phase-0
    (implies (zp phase)
             (equal compose (svex-alist-extract (svex-alist-keys nextstate) initst))))

  ;; (local (defthm svex-alist-keys-of-svex-alist-compose
  ;;          (Equal (svex-alist-keys (svex-alist-compose x y))
  ;;                 (svex-alist-keys x))
  ;;          :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-compose)))))
  
  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys compose)
           (svex-alist-keys nextstate)))

  (local (defthm svex-envs-equivalent-of-svex-env-extract-keys
           (implies (equal keys (alist-keys (svex-env-fix x)))
                    (svex-envs-equivalent (svex-env-extract keys x) x))
           :hints(("Goal" :in-theory (enable svex-envs-equivalent
                                             svex-env-boundp-iff-member-alist-keys
                                             svex-env-lookup-when-not-boundp)))))

  (local (defun nth-of-base-fsm-eval-ind (n ins st fsm)
         (if (zp n)
             (list ins st fsm)
           (nth-of-base-fsm-eval-ind (1- n) (cdr ins)
                                     (base-fsm-step (car ins) st fsm)
                                     fsm))))

  (local (defthm base-fsm-final-state-of-take-n+1
           (implies (and (posp n)
                         ;; (no-duplicatesp-equal (svex-alist-keys (base-fsm->nextstate x)))
                         )
                    (svex-envs-equivalent
                     (base-fsm-final-state (take n ins) prev-st x)
                     (base-fsm-step (nth (1- n) ins)
                                    (base-fsm-final-state (take (1- n) ins) prev-st x)
                                    x)))
           :hints(("Goal" :in-theory (e/d (take nth base-fsm-final-state)
                                          (acl2::take-of-too-many
                                           acl2::take-when-atom))
                   :induct (nth-of-base-fsm-eval-ind n ins prev-st x)
                   :expand ((take 1 ins)))
                  (and stable-under-simplificationp
                       '(:in-theory (enable base-fsm-step))))))

  
  (defret eval-of-<fn>
    (svex-envs-equivalent (svex-alist-eval compose env)
                          (base-fsm-final-state (take phase (svex-alistlist-eval inputs env))
                                                (svex-alist-eval initst env)
                                                nextstate))
    :hints (("goal" :induct <call>
             :expand ((take phase inputs)
                      (:free (initst) (base-fsm-final-state nil initst nextstate))))
                  (and stable-under-simplificationp
                       '(:in-theory (enable base-fsm-step
                                            base-fsm-step-env))))))
                         

;; (define svex-alist-eval-multistate-unroll ((x svex-alist-p)
;;                                            (phase natp)
;;                                            (states svex-alistlist-p)
;;                                            (inputs svex-alistlist-p)
;;                                            (env svex-env-p))
;;   :Returns (compose svex-env-p)
;;   :measure (nfix phase)
;;   :ruler-extenders :lambdas
;;   :verify-guards :after-returns
;;   (b* ((state-alist (nth phase states))
;;        (state-unroll (if (zp phase)
;;                          (svex-alist-eval state-alist env)
;;                        (svex-alist-eval-multistate-unroll state-alist (1- phase) states inputs env)))
;;        (compose-alist (append state-unroll (svex-alist-eval (nth phase inputs) env))))
;;     (svex-alist-eval x (append compose-alist env)))
;;   ///
;;   (defthm eval-of-svex-alist-compose-multistate-unroll
;;     (equal (svex-alist-eval (svex-alist-compose-multistate-unroll x phase states inputs) env)
;;            (svex-alist-eval-multistate-unroll x phase states inputs env))
;;     :hints(("Goal" :in-theory (enable svex-alist-compose-multistate-unroll)))))


;; (define svex-eval-multistate-unroll ((x svex-p)
;;                                      (phase natp)
;;                                      (states svex-alistlist-p)
;;                                      (inputs svex-alistlist-p)
;;                                      (env svex-env-p))
;;   :Returns (val 4vec-p)
;;   :ruler-extenders :lambdas
;;   :verify-guards :after-returns
;;   (b* ((state-alist (nth phase states))
;;        (state-unroll (if (zp phase)
;;                          (svex-alist-eval state-alist env)
;;                        (svex-alist-eval-multistate-unroll state-alist (1- phase) states inputs env)))
;;        (compose-alist (append state-unroll (svex-alist-eval (nth phase inputs) env))))
;;     (svex-eval x (append compose-alist env))))




;; (defines svex-compose-unroll-multistate
;;   (define svex-compose-unroll-multistate ((x svex-p)
;;                                           (cycle natp)
;;                                           (nextstates svex-alistlist-p)
;;                                           (in-alists svex-alistlist-p))
;;     :guard (< cycle (len in-alists))
;;     :measure (two-nats-measure cycle (svex-count x))
;;     :returns (new-x svex-p)
;;     :verify-guards nil
;;     (b* ((x (svex-fix x)))
;;       (svex-case x
;;         :quote (svex-fix x)
;;         :var (b* ((look (svex-fastlookup x.name (nth cycle (sv::svex-alistlist-fix nextstates))))
;;                   ((when look)
;;                    ;; state var
;;                    (if (zp cycle)
;;                        look
;;                      (svex-compose-unroll-multistate look (1- cycle) nextstates in-alists))))
;;                ;; input var
;;                (or (svex-fastlookup x.name (nth cycle (svex-alistlist-fix in-alists)))
;;                    (svex-x)))
;;         :call (svex-call x.fn (svexlist-compose-unroll-multistate x.args cycle nextstates in-alists)))))
;;   (define svexlist-compose-unroll-multistate ((x svexlist-p)
;;                                          (cycle natp)
;;                                          (nextstates svex-alistlist-p)
;;                                          (in-alists svex-alistlist-p))
;;     :guard (< cycle (len in-alists))
;;     :measure (two-nats-measure cycle (svexlist-count x))
;;     :returns (new-x svexlist-p)
;;     (if (atom x)
;;         nil
;;       (cons (svex-compose-unroll-multistate (car x) cycle nextstates in-alists)
;;             (svexlist-compose-unroll-multistate (cdr x) cycle nextstates in-alists))))
;;   ///
;;   (verify-guards svex-compose-unroll-multistate)


;;   (local (defcong svexlist-eval-equiv svex-eval-equiv (svex-call fn args) 2))

;;   (local (defthm svex-subst-of-svex-call
;;            (implies (svex-case x :call)
;;                     (equal (svex-subst x a)
;;                            (svex-call (svex-call->fn x)
;;                                       (svexlist-subst (svex-call->args x) a))))
;;            :hints(("Goal" :expand ((svex-subst x a))))))

;;   (local (defthm svex-subst-of-svex-var
;;            (implies (svex-case x :var)
;;                     (equal (svex-subst x a)
;;                            (or (svex-lookup (svex-var->name x) a)
;;                                (svex-x))))
;;            :hints(("Goal" :expand ((svex-subst x a))))))

;;   (local (defthm svex-subst-of-svex-quote
;;            (implies (svex-case x :quote)
;;                     (equal (svex-subst x a)
;;                            (svex-fix x)))
;;            :hints(("Goal" :expand ((svex-subst x a))))))

;;   ;; (local (defthm hons-assoc-equal-of-append
;;   ;;          (equal (hons-assoc-equal k (append x y))
;;   ;;                 (or (hons-assoc-equal k x)
;;   ;;                     (hons-assoc-equal k y)))))
  
;;   ;; (local (defthm svex-lookup-of-append
;;   ;;          (equal (Svex-lookup v (append x y))
;;   ;;                 (or (svex-lookup v x)
;;   ;;                     (svex-lookup v y)))
;;   ;;          :hints(("Goal" :in-theory (enable svex-lookup)))))
  

;;   (std::defret-mutual svex-compose-unroll-multistate-in-terms-of-svex-alist-compose-multistate-unroll
;;     (defret <fn>-in-terms-of-svex-alist-eval-multistate-unroll
;;       (svex-eval-equiv new-x
;;                        (svex-subst x (append (svex-unroll-multistate-phase-state
;;                                                 cycle nextstates in-alists)
;;                                                (nth cycle in-alists))))
;;       :hints ('(:expand (<call>)))
;;       :fn svex-compose-unroll-multistate)

;;     (defret <fn>-in-terms-of-svex-alist-eval-multistate-unroll
;;       (svexlist-eval-equiv new-x
;;                            (svexlist-subst x (append (svex-unroll-multistate-phase-state
;;                                                         cycle nextstates in-alists)
;;                                                        (nth cycle in-alists))))
;;       :hints ('(:expand (<call>
;;                          (:free (a) (svexlist-subst x a)))))
;;       :fn svexlist-compose-unroll-multistate))

  
;;   ;; (std::defret-mutual svex-compose-unroll-multistate-in-terms-of-svex-alist-compose-multistate-unroll
;;   ;;   (defret <fn>-in-terms-of-svex-alist-eval-multistate-unroll
;;   ;;     (svex-eval-equiv new-x
;;   ;;                      (svex-compose x (append (if (zp cycle)
;;   ;;                                                  (nth 0 nextstates)
;;   ;;                                                (svex-alist-compose-multistate-unroll
;;   ;;                                                 (nth cycle nextstates)
;;   ;;                                                 (1- cycle) nextstates in-alists))
;;   ;;                                              (nth cycle in-alists))))
;;   ;;     :hints ('(:expand (<call>)))
;;   ;;     :fn svex-compose-unroll-multistate)

;;   ;;   (defret <fn>-in-terms-of-svex-alist-eval-multistate-unroll
;;   ;;     (svexlist-eval-equiv new-x
;;   ;;                          (svexlist-compose x (append (if (zp cycle)
;;   ;;                                                          (nth 0 nextstates)
;;   ;;                                                        (svex-alist-compose-multistate-unroll
;;   ;;                                                         (nth cycle nextstates)
;;   ;;                                                         (1- cycle) nextstates in-alists))
;;   ;;                                                      (nth cycle in-alists))))
;;   ;;     :hints ('(:expand (<call>
;;   ;;                        (:free (a) (svexlist-compose x a)))))
;;   ;;     :fn svexlist-compose-unroll-multistate))
;;   )

                       


(defprod svtv-precompose-data
  ((simp svex-simpconfig-p)
   (nextstate svex-alist-p)
   (input-substs svex-alistlist-p)
   (initst svex-alist-p)
   (pre-compose-inputs svarlist-p))
  :layout :tree)


;; (local (defthmd svex-lookup-of-cons
;;          (equal (svex-lookup var (cons (cons key val) rest))
;;                 (if (and (svar-p key) (equal (svar-fix var) key))
;;                     (svex-fix val)
;;                   (svex-lookup var rest)))
;;          :hints(("Goal" :in-theory (enable svex-lookup)))))

(define svtv-precompose-input-subst-alist ((pre-compose-inputs svarlist-p)
                                           (input-subst svex-alist-p))
  :returns (pre-subst svex-alist-p)
  (b* (((when (atom pre-compose-inputs)) nil)
       (var (svar-fix (car pre-compose-inputs)))
       (expr (svex-fastlookup var input-subst))
       ((unless (and expr (svex-case expr :quote)))
        (svtv-precompose-input-subst-alist (cdr pre-compose-inputs) input-subst)))
    (cons (cons var expr)
          (svtv-precompose-input-subst-alist (cdr pre-compose-inputs) input-subst)))
  ///
  
  
  (defret lookup-in-<fn>
    (equal (svex-lookup k pre-subst)
           (and (member-equal (svar-fix k) (svarlist-fix pre-compose-inputs))
                (b* ((expr (svex-lookup k input-subst)))
                  (and (svex-case expr :quote) expr))))
    :hints(("Goal" :in-theory (enable svex-lookup-of-cons))))


  (defret svex-alist-compose-of-<fn>
    (equal (svex-alist-compose pre-subst x) pre-subst)
    :hints(("Goal" :in-theory (enable svex-alist-compose svex-acons svex-compose))))

  (defret svex-alist-subst-of-<fn>
    (equal (svex-alist-subst pre-subst x) pre-subst)
    :hints(("Goal" :in-theory (enable svex-alist-subst svex-acons svex-subst))))

  (local (defthm svex-lookup-when-not-member
           (implies (not (member-equal (svar-fix v) (svex-alist-keys x)))
                    (not (svex-lookup v x)))
           :hints(("Goal" :in-theory (enable svex-alist-keys)))))
  
  (local (defthm svex-lookup-when-member-non-intersecting
           (implies (and (not (intersectp-equal vars (svex-alist-keys x)))
                         (member-equal (svar-fix v) vars))
                    (not (svex-lookup v x)))))
  
  (defret svex-alist-reduce-of-append-<fn>
    (implies (not (intersectp-equal (svarlist-fix pre-compose-inputs) (svex-alist-keys sts)))
             (equal (svex-alist-reduce vars (append pre-subst sts input-subst))
                    (svex-alist-reduce vars (append sts input-subst))))
    :hints(("Goal" :in-theory (e/d ()
                                   (<fn>))
            :induct (len vars)
            :expand ((:free (x) (svex-alist-reduce vars x)))))))

(define svtv-precompose-inputs-compose ((x svex-alist-p)
                                        (substconfig svex-substconfig-p))
  :enabled t
  (b* ((- (cw "svtv-precompose-inputs-compose: input opcount ~x0~%" (svexlist-opcount (svex-alist-vals x))))
       ; (- (cw "svtv-precompose-inputs-compose: subst: ~x0~%" substconfig))
       (ans (svex-alist-compose-rw x substconfig))
       (- (cw "svtv-precompose-inputs-compose: output opcount ~x0~%" (svexlist-opcount (svex-alist-vals ans)))))
    ans)
  ///
  (memoize 'svtv-precompose-inputs-compose))


(local (defthm svex-lookup-under-iff-of-svex-alist-compose-rw
         (iff (svex-lookup k (svex-alist-compose-rw x subst))
              (svex-lookup k x))
         :hints(("Goal" :in-theory (enable svex-alist-compose-rw svex-lookup)))))

(local (defthm svex-alist-compose-rw-under-svex-alist-eval-equiv
         (svex-alist-eval-equiv (svex-alist-compose-rw x subst)
                                (svex-alist-compose x (svex-substconfig->alist subst)))
         :hints(("Goal" :in-theory (enable svex-envs-equivalent-implies-alist-eval-equiv)))))


(defcong svex-alist-eval-equiv svex-alist-eval-equiv (svex-alist-subst x a) 1
  :hints(("Goal" :in-theory (enable svex-envs-equivalent-implies-alist-eval-equiv))))



(defthm svex-alist-subst-of-svex-alist-compose
  (svex-alist-eval-equiv!
   (svex-alist-subst (svex-alist-compose x a1) a2)
   (svex-alist-subst x (append (svex-alist-subst a1 a2) a2)))
  :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent
                                    svex-alist-eval-equiv!-when-svex-alist-eval-equiv))))



(defcong svex-alist-eval-equiv! svex-alist-eval-equiv! (svex-alist-subst x a) 1
  :hints(("Goal" :in-theory (enable svex-envs-equivalent-implies-alist-eval-equiv
                                    svex-alist-eval-equiv!-when-svex-alist-eval-equiv))))

(defthm svex-alist-compose-rw-under-svex-alist-eval-equiv!
  (svex-alist-eval-equiv! (svex-alist-compose-rw x subst)
                          (svex-alist-compose x (svex-substconfig->alist subst)))
  :hints(("Goal" :in-theory (e/d (svex-alist-eval-equiv!-when-svex-alist-eval-equiv)
                                 (SVEX-ALIST-COMPOSE-RW-UNDER-SVEX-ALIST-EVAL-EQUIV))
          :use SVEX-ALIST-COMPOSE-RW-UNDER-SVEX-ALIST-EVAL-EQUIV)))


(define svtv-precompose-phase ((pre-compose-inputs svarlist-p)
                               (input-subst svex-alist-p)
                               (x svex-alist-p)
                               (simp svex-simpconfig-p))
  :returns (new-x svex-alist-p)
  (b* (((unless (consp pre-compose-inputs)) (svex-alist-fix x)) ;; optimization
       (subst (make-fast-alist (hons-copy (svtv-precompose-input-subst-alist pre-compose-inputs input-subst))))
       (subst-config (make-svex-substconfig :alist subst :simp simp)))
    (svtv-precompose-inputs-compose x (hons-copy subst-config)))
  ///

  
  (defret lookup-under-iff-in-<fn>
    (iff (svex-lookup key new-x)
         (svex-lookup key x)))

  (local
   (encapsulate nil
     (local (defthm svex-alist-compose-eval-equiv-when-extract-vars-similar-lemma
              (implies (svex-alist-eval-equiv (svex-alist-reduce vars a1)
                                              (svex-alist-reduce vars a2))
                       (equal (svex-envs-similar
                               (svex-env-extract vars (SVEX-ALIST-EVAL A1 env))
                               (svex-env-extract vars (SVEX-ALIST-EVAL A2 env)))
                              t))
              :hints(("Goal" :in-theory (e/d (svex-envs-similar svex-eval)
                                             (svex-alist-eval-equiv-necc
                                              SVEX-ALIST-EVAL-EQUIV-IMPLIES-SVEX-EVAL-EQUIV-SVEX-LOOKUP-2))
                      :use ((:instance svex-alist-eval-equiv-necc
                             (var (svex-envs-similar-witness
                                   (svex-env-extract vars (SVEX-ALIST-EVAL A1 env))
                                   (svex-env-extract vars (SVEX-ALIST-EVAL A2 env))))
                             (x (svex-alist-reduce vars a1))
                             (y (svex-alist-reduce vars a2))))))))
     (defthmd svex-alist-subst-eval-equiv-when-extract-vars-similar
       (implies (svex-alist-eval-equiv (svex-alist-reduce (svex-alist-vars x) a1)
                                       (svex-alist-reduce (svex-alist-vars x) a2))
                (equal (svex-alist-eval-equiv! (svex-alist-subst x a1)
                                               (svex-alist-subst x a2))
                       t))
       :hints(("Goal" :in-theory (enable svex-alist-eval-equivalent-when-extract-vars-similar
                                         svex-alist-eval-equiv!-when-svex-alist-eval-equiv)
               :expand ((:with svex-alist-eval-equiv-in-terms-of-envs-equivalent
                         (svex-alist-eval-equiv (svex-alist-subst x a1)
                                                (svex-alist-subst x a2)))))))))

  
  
  (defret <fn>-compose-correct
    (implies (not (intersectp-equal (svex-alist-keys sts)
                                    (svarlist-fix pre-compose-inputs)))
             (svex-alist-eval-equiv! (svex-alist-subst new-x
                                                      (append sts input-subst))
                                    (svex-alist-subst x (append sts input-subst))))
    :hints (("goal" :do-not-induct t
             :in-theory (enable SVEX-ALIST-subst-EVAL-EQUIV-WHEN-EXTRACT-VARS-SIMILAR)))
    :otf-flg t))


(local (include-book "std/lists/sets" :dir :System))



(defcong svex-alist-eval-equiv svex-alist-eval-equiv! (svex-alist-subst x a) 2
  :hints (("goal" :in-theory (enable svex-envs-equivalent-implies-alist-eval-equiv
                                     svex-alist-eval-equiv!-when-svex-alist-eval-equiv))))

(define svtv-precompose-phases-rec ((phase natp)
                                    (nphases natp)
                                    (data svtv-precompose-data-p))
  :guard (<= phase nphases)
  :measure (nfix (- (nfix nphases) (nfix phase)))
  :returns (nextstates svex-alistlist-p)
  (b* (((when (mbe :logic (zp (- (nfix nphases) (nfix phase)))
                   :exec (eql phase nphases)))
        nil)
       ((svtv-precompose-data data)))
    (cons (svtv-precompose-phase data.pre-compose-inputs
                                 (nth phase data.input-substs)
                                 data.nextstate
                                 data.simp)
          (svtv-precompose-phases-rec (1+ (lnfix phase)) nphases data)))
  ///
  (local (defun nth-of-ind (n phase nphases)
           (declare (xargs :measure (nfix (- (nfix nphases) (nfix phase)))))
           (if (zp (- (nfix nphases) (nfix phase)))
               n
             (nth-of-ind (1- (nfix n)) (1+ (nfix phase)) nphases))))
  
  (defret nth-of-<fn>
    (b* (((svtv-precompose-data data)))
      (equal (nth n nextstates)
             (and (< (+ (nfix n) (nfix phase)) (nfix nphases))
                  (svtv-precompose-phase data.pre-compose-inputs
                                         (nth (+ (nfix n) (nfix phase)) data.input-substs)
                                         data.nextstate
                                         data.simp))))
    :hints(("Goal" :in-theory (enable nth)
            :expand ((:free (a b) (nth n (cons a b))))
            :induct (nth-of-ind n phase nphases))))




  (defret svex-unroll-multistate-phase-state-of-<fn>
    :pre-bind ((phase 0))
    (b* (((svtv-precompose-data data)))
      (implies (and (< (nfix ph) (nfix nphases))
                    (not (intersectp-equal (svex-alist-keys data.nextstate)
                                           (svarlist-fix data.pre-compose-inputs)))
                    (equal initst (svex-alist-extract (svex-alist-keys data.nextstate) data.initst)))
               (svex-alist-eval-equiv! (svex-unroll-multistate-phase-state
                                        ph (cons initst nextstates)
                                        data.input-substs)
                                      (svex-unroll-phase-state
                                       ph data.nextstate data.initst data.input-substs))))
    :hints(("Goal" :in-theory (enable (:i svex-unroll-phase-state))
            :induct (svex-unroll-phase-state ph
                                             (svtv-precompose-data->nextstate data)
                                             (svtv-precompose-data->initst data)
                                             (svtv-precompose-data->input-substs data))
            :expand ((:free (states input-substs)
                      (svex-unroll-multistate-phase-state ph states input-substs))
                     (:free (nextstate initst input-substs)
                      (svex-unroll-phase-state ph nextstate initst input-substs))
                     (:free (a b) (nth ph (cons a b))))))))
                    



(define svtv-precompose-phases ((nphases natp)
                                (data svtv-precompose-data-p))
  :returns (compose-data svtv-composedata-p)
  :guard (b* (((svtv-precompose-data data))
              (st-keys (svex-alist-keys data.nextstate)))
           (and (equal (svex-alist-keys data.initst) st-keys)
                (not (acl2::hons-dups-p st-keys))))
  (b* ((nextstates (svtv-precompose-phases-rec 0 nphases data))
       ((svtv-precompose-data data)))
    (make-svtv-composedata
     :simp data.simp
     :nextstates (make-fast-alists
                  (cons (mbe :logic (svex-alist-extract (svex-alist-keys data.nextstate) data.initst)
                             :exec data.initst)
                        nextstates))
     :input-substs data.input-substs))
  ///
  (defret input-substs-of-<fn>
    (equal (svtv-composedata->input-substs compose-data)
           (svtv-precompose-data->input-substs data)))

  (defret svex-unroll-multistate-phase-state-of-<fn>
    (b* (((svtv-composedata compose-data))
         ((svtv-precompose-data data)))
      (implies (and (< (nfix phase) (nfix nphases))
                    (not (intersectp-equal (svex-alist-keys data.nextstate)
                                           (svarlist-fix data.pre-compose-inputs))))
               (svex-alist-eval-equiv! (svex-unroll-multistate-phase-state
                                        phase compose-data.nextstates data.input-substs)
                                       (svex-unroll-phase-state
                                        phase data.nextstate data.initst data.input-substs))))))
  


(local
 (defthm svex-call-simp-under-svex-eval-equiv
   (Svex-eval-equiv (svex-call-simp fn args simp)
                    (svex-call fn args))
   :hints(("Goal" :in-theory (enable svex-eval-equiv)))))


(defines svex-compose-svtv-phases
  :ruler-extenders :lambdas
  (define svex-compose-svtv-phases ((x svex-p)
                                    (phase natp)
                                    (data svtv-composedata-p))
    :measure (acl2::nat-list-measure (list phase (svex-count x) 1))
    :returns (new-x svex-p)
    :verify-guards nil
    (b* ((x (svex-fix x)))
      (svex-case x
        :quote x
        :var (b* (((svtv-composedata data))
                  (look (svex-fastlookup x.name (nth phase data.nextstates)))
                  ((when look)
                   ;; state var
                   (if (zp phase)
                       look
                     (svex-compose-svtv-phases look (1- phase) data))))
               ;; input var
               (b* ((inalist (nth phase (svex-alistlist-fix data.input-substs)))
                    (look (svex-fastlookup x.name inalist)))
                 (or look (svex-x)
                     ;; (svex-var (svex-phase-var x.name phase))
                     )))
        :call (svex-compose-svtv-phases-call x phase data))))

  (define svex-compose-svtv-phases-call ((x svex-p)
                                         (phase natp)
                                         (data svtv-composedata-p))
    :measure (acl2::nat-list-measure (list phase (svex-count x) 0))
    :returns (new-x svex-p)
    :guard (svex-case x :call)
    (b* (((unless (mbt (svex-case x :call))) (svex-fix x))
         ((svex-call x))
         (args (mbe :logic (svexlist-compose-svtv-phases x.args phase data)
                    :exec (rev (svexlist-compose-svtv-phases-tailrec x.args phase data nil)))))
      (svex-call-simp x.fn args (svtv-composedata->simp data))))

  (define svexlist-compose-svtv-phases ((x svexlist-p)
                                        (phase natp)
                                        (data svtv-composedata-p))
    :measure (acl2::nat-list-measure (list phase (svexlist-count x) 1))
    :returns (new-x svexlist-p)
    (if (atom x)
        nil
      (cons (svex-compose-svtv-phases (car x) phase data)
            (svexlist-compose-svtv-phases (cdr x) phase data))))

  (define svexlist-compose-svtv-phases-tailrec ((x svexlist-p)
                                                (phase natp)
                                                (data svtv-composedata-p)
                                                (acc svexlist-p))
    :measure (acl2::nat-list-measure (list phase (svexlist-count x) 1))
    :returns (new-x (equal new-x (revappend (svexlist-compose-svtv-phases x phase data) (svexlist-fix acc)))
                    :hints('(:in-theory (enable svex-compose-svtv-phases))))
    (if (atom x)
        (svexlist-fix acc)
      (b* ((new-x1 (b* ((x (svex-fix (car x))))
                     (svex-case x
                       :quote x
                       :var (b* (((svtv-composedata data))
                                 (look (svex-fastlookup x.name (nth phase data.nextstates)))
                                 ((when look)
                                  ;; state var
                                  (if (zp phase)
                                      look
                                    (svex-compose-svtv-phases look (1- phase) data))))
                              ;; input var
                              (b* ((inalist (nth phase (svex-alistlist-fix data.input-substs)))
                                   (look (svex-fastlookup x.name inalist)))
                                (or look (svex-x)
                                    ;; (svex-var (svex-phase-var x.name phase))
                                    )))
                       :call (svex-compose-svtv-phases-call x phase data)))))
        (svexlist-compose-svtv-phases-tailrec
         (cdr x) phase data
         (cons new-x1
               (svexlist-fix acc))))))
  ///
  (verify-guards svex-compose-svtv-phases)
  (memoize 'svex-compose-svtv-phases-call)

  (local (defthm svex-subst-of-svex-call
           (implies (svex-case x :call)
                    (equal (svex-subst x a)
                           (svex-call (svex-call->fn x)
                                      (svexlist-subst (svex-call->args x) a))))
           :hints(("Goal" :expand ((svex-subst x a))))))

  (local (defthm svex-subst-of-svex-var
           (implies (svex-case x :var)
                    (equal (svex-subst x a)
                           (or (svex-lookup (svex-var->name x) a)
                               (svex-x))))
           :hints(("Goal" :expand ((svex-subst x a))))))

  (local (defthm svex-subst-of-svex-quote
           (implies (svex-case x :quote)
                    (equal (svex-subst x a)
                           (svex-fix x)))
           :hints(("Goal" :expand ((svex-subst x a))))))

  (defthm-svex-compose-svtv-phases-flag
    (defthm svex-compose-svtv-phases-correct
      (svex-eval-equiv (svex-compose-svtv-phases x phase data)
                       (b* (((svtv-composedata data)))
                         (svex-subst x
                                     (append (svex-unroll-multistate-phase-state phase data.nextstates data.input-substs)
                                             (nth phase data.input-substs)))))
      :hints ('(:expand ((svex-compose-svtv-phases x phase data)))
              ;; (and stable-under-simplificationp
              ;;      '(:in-theory (enable svex-eval)))
              )
      :flag svex-compose-svtv-phases)
    (defthm svex-compose-svtv-phases-call-correct
      (implies (svex-case x :call)
               (svex-eval-equiv (svex-compose-svtv-phases-call x phase data)
                                (b* (((svtv-composedata data)))
                                  (svex-subst x
                                              (append (svex-unroll-multistate-phase-state phase data.nextstates data.input-substs)
                                                      (nth phase data.input-substs))))))
      :hints ('(:expand ((svex-compose-svtv-phases-call x phase data))))
      :flag svex-compose-svtv-phases-call)
    (defthm svexlist-compose-svtv-phases-correct
      (svexlist-eval-equiv (svexlist-compose-svtv-phases x phase data)
                           (b* (((svtv-composedata data)))
                             (svexlist-subst x
                                             (append (svex-unroll-multistate-phase-state phase data.nextstates data.input-substs)
                                                     (nth phase data.input-substs)))))
      :hints ('(:expand ((svexlist-compose-svtv-phases x phase data)
                         (:free (a) (svexlist-subst x a)))))
      :flag svexlist-compose-svtv-phases)
    :skip-others t)

  (deffixequiv-mutual svex-compose-svtv-phases
    :hints(("Goal" :in-theory (disable return-type-of-svexlist-compose-svtv-phases-tailrec.new-x)))))

(define svex-alist-compose-svtv-phases ((x svex-alist-p)
                                        (phase natp)
                                        (data svtv-composedata-p))
  :returns (new-x svex-alist-p)
  :hooks nil
  (if (atom x)
      nil
    (if (mbt (and (consp (car x)) (svar-p (caar x))))
        (cons (cons (caar x) (svex-compose-svtv-phases (cdar x) phase data))
              (svex-alist-compose-svtv-phases (cdr x) phase data))
      (svex-alist-compose-svtv-phases (cdr x) phase data)))
  ///
  (defretd svex-alist-compose-svtv-phases-correct
    (equal new-x
           (pairlis$ (svex-alist-keys x)
                     (svexlist-compose-svtv-phases (svex-alist-vals x) phase data)))
    :hints(("Goal" :in-theory (enable svexlist-compose-svtv-phases svex-alist-keys svex-alist-vals))))

  (deffixequiv svex-alist-compose-svtv-phases :hints(("Goal" :in-theory (enable svex-alist-fix)))))









       
  
