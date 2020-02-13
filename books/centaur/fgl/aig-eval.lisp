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

(include-book "primitives")
(include-book "centaur/aignet/from-hons-aig" :dir :system)
(local (include-book "primitive-lemmas"))
(local (std::add-default-post-define-hook :fix))



(def-formula-checks aig-eval-formula-checks
  (acl2::aig-eval-list))


(define fgl-object-alist-to-varmap ((x fgl-object-alist-p)
                                   (bfrstate bfrstate-p)
                                   (acc alistp))
  :guard (and (bfrstate-mode-is :aignet)
              (bfr-listp (fgl-object-alist-bfrlist x)))
  :returns (mv err varmap)
  (if (atom x)
      (mv nil acc)
    (if (and (mbt (consp (car x)))
             (acl2::aig-var-p (caar x))
             (not (hons-get (caar x) acc)))
        (b* (((mv ok obj) (gobj-syntactic-boolean-fix (cdar x)))
             ((unless ok)
              (mv (msg "Bad symbolic value for key: ~x0~%" (caar x)) nil)))
          (fgl-object-alist-to-varmap
           (cdr x) bfrstate
           (hons-acons (caar x)
                       (bfr->aignet-lit (gobj-syntactic-boolean->bool obj) bfrstate)
                       acc)))
      (fgl-object-alist-to-varmap (cdr x) bfrstate acc)))
  ///
  (defthm good-varmap-p-of-fgl-object-alist-to-varmap
    (b* (((mv ?err varmap) (fgl-object-alist-to-varmap x (logicman->bfrstate) acc)))
      (implies (and (bfrstate-mode-is :aignet (logicman->bfrstate))
                    (lbfr-listp (fgl-object-alist-bfrlist x))
                    (aignet::good-varmap-p acc (logicman->aignet logicman)))
               (aignet::good-varmap-p varmap (logicman->aignet logicman))))
    :hints(("Goal" :in-theory (enable aignet::good-varmap-p))))

  ;; (defret lookup-preserved-in-<fn>
  ;;   (implies (and (not err)
  ;;                 (equal acc-pair (hons-assoc-equal key acc))
  ;;                 acc-pair)
  ;;            (equal (hons-assoc-equal key varmap)
  ;;                   acc-pair)))

  ;; (defret lookup-exists-in-fgl-object-alist-to-varmap
  ;;   (implies (and (not err)
  ;;                 (acl2::aig-var-p key)
  ;;                 (hons-assoc-equal key x))
  ;;            (hons-assoc-equal key varmap)))

  (defret lookup-exists-in-fgl-object-alist-to-varmap-split
    (implies (not err)
             (iff (hons-assoc-equal key varmap)
                  (or (hons-assoc-equal key acc)
                      (and (acl2::aig-var-p key)
                           (hons-assoc-equal key x))))))
  
  (defret lookup-in-fgl-object-alist-to-varmap
    (implies (and (not err)
                  (hons-assoc-equal key varmap))
             (equal (hons-assoc-equal key varmap)
                    (or (hons-assoc-equal key acc)
                        (and (acl2::aig-var-p key)
                             (cons key
                                   (bfr->aignet-lit (gobj-syntactic-boolean->bool
                                                     (mv-nth 1 (gobj-syntactic-boolean-fix
                                                                (cdr (hons-assoc-equal key x)))))
                                                    bfrstate))))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defret gobj-syntactic-boolean-fix-when-fgl-object-alist-to-varmap
    (implies (and (not err)
                  (hons-assoc-equal key varmap)
                  (not (hons-assoc-equal key acc)))
             (mv-nth 0 (gobj-syntactic-boolean-fix (cdr (hons-assoc-equal key x))))))

  (local (in-theory (enable fgl-object-alist-fix))))



(define lit-list-max-var+1 ((x aignet::lit-listp))
  :returns (max-var natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (max (+ 1 (satlink::lit->var (car x)))
         (lit-list-max-var+1 (cdr x))))
  ///
  (defthm lit-list-max-var+1-when-aignet-lit-listp
    (implies (aignet::aignet-lit-listp x aignet)
             (<= (lit-list-max-var+1 x) (+ 1 (aignet::fanin-count aignet))))
    :hints(("Goal" :in-theory (enable aignet::aignet-idp))))

  (defthm lit-list-max-var+1-of-aiglist-to-aignet
    (b* (((mv lits & & new-aignet) (aignet::aiglist-to-aignet aigs xmemo varmap gatesimp strash aignet)))
      (implies (and (aignet::good-varmap-p varmap aignet)
                    (aignet::xmemo-well-formedp xmemo aignet))
               (<= (lit-list-max-var+1 lits) (+ 1 (aignet::fanin-count new-aignet)))))
    :hints (("goal" :use ((:instance lit-list-max-var+1-when-aignet-lit-listp
                           (x (mv-nth 0 (aignet::aiglist-to-aignet aigs xmemo varmap gatesimp strash aignet)))
                           (aignet (mv-nth 3 (aignet::aiglist-to-aignet aigs xmemo varmap gatesimp strash aignet)))))
             :in-theory (disable lit-list-max-var+1-when-aignet-lit-listp
                                 lit-list-max-var+1)))
    :rule-classes :linear))

(encapsulate nil
  (define aignet-lit->bool ((x satlink::litp)
                            (bfrstate bfrstate-p))
    :guard (and (bfrstate-mode-is :aignet)
                (<= (satlink::lit->var x) (bfrstate->bound bfrstate)))
    :returns (obj fgl-object-p)
    (mk-g-boolean (aignet-lit->bfr x bfrstate))
    ///
    (defret bfr-listp-of-aignet-lit->bool
      (implies (and (bfrstate-mode-is :aignet)
                    (<= (satlink::lit->var x) (bfrstate->bound bfrstate)))
               (bfr-listp (fgl-object-bfrlist obj))))

    (defret fgl-object-eval-of-<fn>
      (implies (lbfr-mode-is :aignet)
               (equal (fgl-object-eval (aignet-lit->bool x (logicman->bfrstate)) env)
                      (b* ((aignet (logicman->aignet logicman)))
                        (bit->bool
                         (aignet::lit-eval x
                                           (alist-to-bitarr (aignet::num-ins aignet)
                                                            (fgl-env->bfr-vals env) nil)
                                           ;; (alist-to-bitarr (aignet::num-regs aignet) nil nil)
                                           nil
                                           aignet)))))
      :hints(("Goal" :in-theory (enable gobj-bfr-eval bfr-eval)))))
  ;; (local (set-default-hints
  ;;         '((and stable-under-simplificationp
  ;;                '(:expand ((lit-list-max-var+1 x)))))))
  (local (in-theory (enable lit-list-max-var+1
                            satlink::lit-listp)))

  ;; (define fgl-objectlist-to-object ((x fgl-objectlist-p))
  ;;   :returns (new-x fgl-object-p)
  ;;   (if (atom x)
  ;;       nil
  ;;     (g-cons (car x)
  ;;             (fgl-objectlist-to-object (cdr x))))
  ;;   ///
  ;;   (defret fgl-object-eval-of-<fn>
  ;;     (equal (fgl-object-eval new-x env)
  ;;            (fgl-objectlist-eval x env)))

  ;;   (defret fgl-objectlist-bfrlist-of-<fn>
  ;;     (implies (not (member v (fgl-objectlist-bfrlist x)))
  ;;              (not (member v (fgl-object-bfrlist new-x))))))

  ;; (define fgl-objectlist-accumulate-to-object ((x fgl-objectlist-p)
  ;;                                             (acc fgl-object-p))
  ;;   :returns (new-x fgl-object-p)
  ;;   (if (atom x)
  ;;       (fgl-object-fix acc)
  ;;     (fgl-objectlist-accumulate-to-object
  ;;      (cdr x)
  ;;      (g-cons (car x) acc)))
  ;;   )

  ;; (define aignet-lit-list->bools-aux ((x aignet::lit-listp)
  ;;                                     (bfrstate bfrstate-p)
  ;;                                     (acc fgl-objectlist-p))
  ;;   :returns (obj fgl-object-p)
  ;;   (if (Atom x)
  ;;       (fgl-objectlist-accumulate-to-object acc nil)
  ;;     (aignet-lit-list->bools-aux
  ;;      (cdr x) bfrstate (cons (aignet-lit->bool (car x) bfrstate acc)))))

  (define aignet-lit-list->bools ((x aignet::lit-listp)
                                  (bfrstate bfrstate-p))
    :returns (new-x fgl-object-p)
    :guard (and (bfrstate-mode-is :aignet)
                (<= (lit-list-max-var+1 x) (+ 1 (bfrstate->bound bfrstate))))
    :guard-debug t
    ;; :verify-guards nil
    (if (atom x)
        nil
      (mk-g-cons (aignet-lit->bool (car x) bfrstate)
                 (aignet-lit-list->bools (cdr x) bfrstate)))
    ///
    ;; (verify-guards aignet-lit-list->bfrs-nrev
    ;;   :hints(("Goal" :in-theory (enable lit-list-max-var+1))))
    ;; (verify-guards aignet-lit-list->bfrs
    ;;   :hints(("Goal" :in-theory (enable lit-list-max-var+1))))
    
    (defthm bfr-listp-of-aignet-lit-list->bools
      (implies (and (<= (lit-list-max-var+1 x) (+ 1 (bfrstate->bound bfrstate)))
                    (bfrstate-mode-is :aignet))
               (bfr-listp (fgl-object-bfrlist (aignet-lit-list->bools x bfrstate))))
      :hints(("Goal" :in-theory (enable aignet-lit-list->bools
                                        lit-list-max-var+1))))
    (defthm fgl-object-eval-of-aignet-lit-list->bools
      (implies (lbfr-mode-is :aignet)
               (equal (fgl-object-eval (aignet-lit-list->bools x (logicman->bfrstate)) env)
                      (b* ((aignet (logicman->aignet logicman)))
                        (bits->bools
                         (aignet::lit-eval-list x
                                                (alist-to-bitarr (aignet::num-ins aignet)
                                                                 (fgl-env->bfr-vals env) nil)
                                                nil
                                                aignet)))))
      :hints(("Goal" :in-theory (enable bits->bools))))))


(set-ignore-ok t)

(local (defthm good-varmap-p-nil
         (aignet::good-varmap-p nil aignet)
         :hints(("Goal" :in-theory (enable aignet::good-varmap-p)))))

;; (local (defthm logicman->bfrstate-of-update-logicman->aignet
;;          (implies (lbfr-mode-is :aignet)
;;                   (equal (logicman->bfrstate (update-logicman->aignet aignet logicman))
;;                          (bfrstate (lbfr-mode)
;;                                    (aignet::fanin-count aignet))))
;;          :hints(("Goal" :in-theory (enable logicman->bfrstate)))))

(local (defthm logicman-extension-p-of-update
         (implies (and (equal (logicman->aignet new) (logicman->aignet old))
                       (equal (logicman->mode new) (logicman->mode old)))
                  (logicman-extension-p new old))
         :hints(("Goal" :in-theory (enable logicman-extension-p)))))

(local (defthm logicman-extension-p-of-update-aignet
         (implies (and (aignet::aignet-extension-p new-aignet (logicman->aignet old))
                       (equal (aignet::num-regs new-aignet) (aignet::num-regs (logicman->aignet old))))
                  (logicman-extension-p (update-logicman->aignet new-aignet old) old))
         :hints(("Goal" :in-theory (enable logicman-extension-p)))))
         
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

(local (defthm boolean-listp-of-aig-eval-list
         (boolean-listp (acl2::aig-eval-list x env))))

(local (defthm bits->bools-of-bools->bits
         (implies (boolean-listp x)
                  (equal (bits->bools (aignet::bools->bits x)) x))
         :hints(("Goal" :in-theory (enable aignet::bools->bits bits->bools)))))

(local (defun-sk aig-env-equiv (x y)
         (forall v
                 (implies (acl2::aig-var-p v)
                          (equal (acl2::aig-env-lookup v x)
                                 (acl2::aig-env-lookup v y))))
         :rewrite :direct))

(local (in-theory (disable aig-env-equiv)))

(local (defthm aig-env-equiv-self
         (aig-env-equiv x x)
         :hints(("Goal" :in-theory (enable aig-env-equiv)))))

(local (defthm aig-env-equiv-symm
         (implies (aig-env-equiv x y)
                  (aig-env-equiv y x))
         :hints(("Goal" :expand ((aig-env-equiv y x))
                 :in-theory (disable acl2::aig-env-lookup)))))

(local (defthm aig-env-equiv-trans
         (implies (and (aig-env-equiv x y)
                       (aig-env-equiv y z))
                  (aig-env-equiv x z))
         :hints(("Goal" :expand ((aig-env-equiv x z))
                 :in-theory (disable acl2::aig-env-lookup)))))

(local (defequiv aig-env-equiv))

(local (in-theory (disable aig-env-equiv
                           aig-env-equiv-symm
                           aig-env-equiv-necc)))

;; (local (defcong aig-env-equiv equal (acl2::aig-env-lookup v x) 2
;;          :hints(("Goal" :in-theory (disable acl2::aig-env-lookup)
;;                  :use ((:instance aig-env-equiv-necc
;;                         (y x-equiv)))))))

(local (defcong aig-env-equiv equal (acl2::aig-eval v x) 2
         :hints(("Goal" :in-theory (disable acl2::aig-env-lookup)
                 :induct (acl2::aig-eval v x))
                (and stable-under-simplificationp
                     '(:use ((:instance aig-env-equiv-necc
                              (y x-equiv))))))))

(local (defcong aig-env-equiv equal (acl2::aig-eval-list v x) 2
         :hints(("Goal" :in-theory (disable acl2::aig-env-lookup)))))

(local (defthm lookup-exists-of-fgl-object-alist-eval
         (iff (hons-assoc-equal k (fgl-object-alist-eval x env))
              (hons-assoc-equal k x))
         :hints(("Goal" :in-theory (enable fgl-object-alist-eval hons-assoc-equal)))))

(local (defthm lookup-of-fgl-object-alist-eval
         (equal (cdr (hons-assoc-equal k (fgl-object-alist-eval x env)))
                (fgl-object-eval (cdr (hons-assoc-equal k x)) env))
         :hints(("Goal" :in-theory (enable fgl-object-alist-eval hons-assoc-equal)))))

(local (defthm lit-eval-bfr->aignet-lit-is-bfr-eval
         (implies (lbfr-mode-is :Aignet)
                  (equal (aignet::lit-eval
                          (bfr->aignet-lit x (logicman->bfrstate))
                          (alist-to-bitarr (aignet::stype-count :pi (logicman->aignet logicman))
                                           (fgl-env->bfr-vals env) nil)
                          nil
                          (logicman->aignet logicman))
                         (bool->bit (gobj-bfr-eval x env))))
         :hints(("Goal" :in-theory (enable bfr-eval gobj-bfr-eval)))))


(local (defthm aig-env-equiv-of-aignet-eval-to-env
         (b* (((mv err varmap) (FGL-OBJECT-ALIST-TO-VARMAP
                                           alist
                                           (logicman->bfrstate)
                                           NIL)))
           (implies (and (lbfr-mode-is :aignet)
                         (not err))
                    (aig-env-equiv (AIGNET::AIGNET-EVAL-TO-ENV
                                    varmap
                                    (ALIST-TO-BITARR
                                     (AIGNET::STYPE-COUNT :PI (logicman->aignet logicman))
                                     (FGL-ENV->BFR-VALS ENV)
                                     NIL)
                                    NIL
                                    (logicman->aignet logicman))
                                   (fgl-object-alist-eval alist env))))
         :hints(("Goal" :in-theory (e/d (aig-env-equiv
                                         lookup-exists-in-fgl-object-alist-to-varmap-split))))))



(def-fgl-primitive acl2::aig-eval-list (x a)
  (fgl-object-case x
    :g-concrete (fgl-object-case a
                  :g-map (stobj-let ((logicman (interp-st->logicman interp-st)))
                                    (ok val logicman)
                                    (b* ((bfrstate (logicman->bfrstate))
                                         ((unless (bfrstate-mode-is :aignet))
                                          (mv nil nil logicman))
                                         ((mv err varmap) (fgl-object-alist-to-varmap a.alist bfrstate nil))
                                         ((when err)
                                          (cw "~x0 primitive error: ~@1" 'acl2::aig-eval-list err)
                                          (mv nil nil logicman)))
                                      (stobj-let ((aignet (logicman->aignet logicman))
                                                  (strash (logicman->strash logicman)))
                                                 (lits aignet strash)
                                                 (b* (((mv lits xmemo strash aignet)
                                                       (aignet::aiglist-to-aignet
                                                        x.val nil varmap (aignet::default-gatesimp)
                                                        strash aignet)))
                                                   (fast-alist-free xmemo)
                                                   (mv lits aignet strash))
                                                 (b* ((bfrstate (logicman->bfrstate)))
                                                   (mv t
                                                       (aignet-lit-list->bools lits bfrstate)
                                                       logicman))))
                                    (mv ok val interp-st))
                  :otherwise (mv nil nil interp-st))
    :otherwise (mv nil nil interp-st))
  :returns (mv successp ans interp-st)
  :formula-check aig-eval-formula-checks)


