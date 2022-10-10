; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
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


(in-package "SV")
(include-book "expand")
(include-book "fsm-base")
(include-book "../svex/rewrite-base")
(include-book "../svex/alist-thms")
(include-book "std/alists/alist-defuns" :dir :system)
(include-book "name-lhs-map-inverse")
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/osets/element-list" :dir :system))
(local (deflist svarlist
         :elt-type svar
         :true-listp t
         :elementp-of-nil nil))
(local (std::add-default-post-define-hook :fix))


(local (in-theory (disable hons-dups-p)))




(define svtv-namemap->lhsmap ((x svtv-namemap-p
                                 "User-provided mapping.  An alist where the keys
                                  are arbitary names (svars, typically symbols)
                                  and the values are SystemVerilog-syntax hierarchical
                                  names (strings).")
                              (modidx natp)
                              (moddb moddb-ok)
                              (aliases))
  :parents (svtv-name-lhs-map)
  :short "Processes a list of nicknames for SystemVerilog-syntax signals into an internal form."
  :long "<p></p>"
  :guard (svtv-mod-alias-guard modidx moddb aliases)
  :returns (mv errs
               (lhses svtv-name-lhs-map-p))
  (b* (((when (atom x)) (mv nil nil))
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svtv-namemap->lhsmap (cdr x) modidx moddb aliases))
       ((mv err1 first) (svtv-wire->lhs! (cdar x) modidx moddb aliases))
       ((mv errs rest) (svtv-namemap->lhsmap (cdr x) modidx moddb aliases))
       ((when err1) (mv (append-without-guard err1 errs) rest)))
    (mv errs (cons (cons (caar x) first) rest)))
  ///
  (local (in-theory (enable svtv-namemap-fix))))


;; (define lhs-value/mask-to-svtv-assigns ((lhs lhs-p)
;;                                         (val 4vec-p)
;;                                         (mask 4vec-p)
;;                                         (updates svex-alist-p))
;;   :returns (assigns 4vec-assigns-p)
;;   (b* (((when (atom lhs))
;;         nil)
;;        ((lhrange x) (lhrange-fix (car lhs))))
;;     (lhatom-case x.atom
;;       :z (lhs-value-to-svtv-assigns (cdr lhs)
;;                                     (svex-rsh x.w val)
;;                                     updates)
;;       :var (b* ((overridep (svex-lookup x.atom.name updates))
;;                 ((unless overridep)
;;                  (cons (cons (list x)
;;                              (make-4vec-driver :value val))
;;                        (lhs-value/mask-to-svtv-assigns (cdr lhs)
;;                                                        (4vec-rsh x.w val)
;;                                                        updates))))
;;              (cons (cons (list (change-lhrange
;;                                 x
;;                                 :atom (change-lhatom-var
;;                                        x.atom
;;                                        :name (change-svar x.atom.name :override-test t))))
;;                          (make-driver :value -1))
;;                    (cons (cons (list (change-lhrange
;;                                       x
;;                                       :atom (change-lhatom-var
;;                                              x.atom
;;                                              :name (change-svar x.atom.name :override-val t))))
;;                                (make-driver :value val))
;;                          (lhs-value-to-svtv-assigns (cdr lhs)
;;                                                   (svex-rsh x.w val)
;;                                                   updates)))))))

(local (defthmd equal-of-svar->name
         (implies (and (svar-p x)
                       (svar-p y)
                       (equal (svar->delay x) (svar->delay y))
                       (equal (svar->nonblocking x) (svar->nonblocking y))
                       (equal (svar->override-val x) (svar->override-val y))
                       (equal (svar->override-test x) (svar->override-test y)))
                  (equal (equal (svar->name x) (svar->name y))
                         (equal x y)))
         :hints (("goal" :use ((:instance svar-fix-redef (x x))
                               (:instance svar-fix-redef (x y)))
                  :in-theory (disable svar-of-fields
                                      equal-of-svar)))))



;; (local (Defthm svtv-name-lhs-map-p-of-fast-alist-clean

(local (in-theory (disable fast-alist-clean)))
;; (local (include-book "std/alists/abstract" :dir :System))
;; (local (fty::defmap svtv-name-lhs-map :key-type svar :val-type lhs :true-listp t))


(defsection svtv-name-lhs-map-p-of-fal-extract
  (local (defthm lookup-when-not-svar-p-of-svtv-name-lhs-map
           (implies (and (svtv-name-lhs-map-p x)
                         (not (svar-p k)))
                    (not (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))
  (local (defthm car-of-hons-assoc-equal
           (equal (car (hons-assoc-equal k x))
                  (and (hons-assoc-equal k x) k))))
  (defthm svtv-name-lhs-map-p-of-fal-extract
    (implies (svtv-name-lhs-map-p x)
             (svtv-name-lhs-map-p (fal-extract keys x)))
    :hints(("Goal" :in-theory (enable fal-extract svtv-name-lhs-map-p)))))


(define svtv-fsm-env-inversemap ((keys svarlist-p)
                                 (map svtv-name-lhs-map-p))
  :returns (inverse-map svtv-name-lhs-map-p)
  (b* (((mv ?collision inverse-map)
        (svtv-name-lhs-map-inverse
         (acl2::fal-extract (svarlist-fix keys) (svtv-name-lhs-map-fix map)))))
    ;; error when collision??
    (and collision
         (er hard? 'svtv-fsm-env-inversemap
             "Collision while assigning input variables for keys ~x0 -- colliding ranges: ~x1~%"
             (svarlist-fix keys) collision))
    (fast-alist-free (fast-alist-clean inverse-map))))

;; (define svtv-fsm-values-inversemap ((keys svarlist-p)
;;                                     (map svtv-name-lhs-map-p)
;;                                     (updates svex-alist-p))
;;   :Returns (value-inverse-map svtv-name-lhs-map-p)
;;   (svtv-name-lhs-map-keys-to-overridevals
;;    (svtv-fsm-env-inversemap keys map) updates)
;;   ///
;;   (defret override-test-var-of-<fn>
;;     (implies (svar->override-test v)
;;              (not (hons-assoc-equal v value-inverse-map))))
  
;;   (defcong svex-alist-same-keys equal (svtv-fsm-values-inversemap keys map updates) 3))

;; (define svtv-fsm-tests-inversemap ((keys svarlist-p)
;;                                     (map svtv-name-lhs-map-p)
;;                                     (updates svex-alist-p))
;;   :Returns (test-inverse-map svtv-name-lhs-map-p)
;;   (svtv-name-lhs-map-keys-to-overridetests
;;    (svtv-fsm-env-inversemap keys map) updates)
;;   ///
;;   (defret override-test-var-of-<fn>
;;     (implies (or (not (svar->override-test v))
;;                  (svar->override-val v))
;;              (not (hons-assoc-equal v test-inverse-map))))
  
;;   (defcong svex-alist-same-keys equal (svtv-fsm-tests-inversemap keys map updates) 3))
  






(define svtv-fsm-phase-inputs ((inputs svex-env-p)
                               (override-vals svex-env-p)
                               (override-tests svex-env-p)
                               (map svtv-name-lhs-map-p))
  :returns (phase-env svex-env-p)
  (b* ((in-env (with-fast-alist inputs
                 (svtv-name-lhs-map-eval-x
                  (svtv-name-lhs-map-keys-change-override
                   (svtv-fsm-env-inversemap (alist-keys (svex-env-fix inputs))
                                            map)
                   nil)
                  inputs)))
       (val-env (with-fast-alist inputs
                 (svtv-name-lhs-map-eval-x
                  (svtv-name-lhs-map-keys-change-override
                   (svtv-fsm-env-inversemap (alist-keys (svex-env-fix override-vals))
                                            map)
                   :val)
                  override-vals)))
       (test-env (with-fast-alist inputs
                 (svtv-name-lhs-map-eval-x
                  (svtv-name-lhs-map-keys-change-override
                   (svtv-fsm-env-inversemap (alist-keys (svex-env-fix override-tests))
                                            map)
                   :test)
                  override-tests))))
    (append test-env val-env in-env)))


(define lhatom-subst-x ((x lhatom-p) (subst svex-alist-p))
  :returns (val svex-p)
  (lhatom-case x
    :z (svex-x)
    :var (svex-rsh x.rsh
                   (or (svex-lookup x.name subst) (svex-x))))
  ///
  (defret eval-of-<fn>
    (equal (svex-eval val env)
           (lhatom-eval-x x (svex-alist-eval subst env)))
    :hints(("Goal" :in-theory (enable svex-apply lhatom-eval-x)))))
                      
(define lhs-subst-x ((x lhs-p) (subst svex-alist-p))
  :returns (val svex-p)
  (if (atom x)
      (svex-x)
    (b* (((lhrange x1) (car x)))
      (svex-concat x1.w
                   (lhatom-subst-x x1.atom subst)
                   (lhs-subst-x (cdr x) subst))))
  ///
  (defret eval-of-<fn>
    (equal (svex-eval val env)
           (lhs-eval-x x (svex-alist-eval subst env)))
    :hints(("Goal" :in-theory (enable svex-apply lhs-eval-x lhrange-eval)))))

(define svtv-name-lhs-map-subst-x ((x svtv-name-lhs-map-p) (subst svex-alist-p))
  :returns (res svex-alist-p)
    (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svtv-name-lhs-map-subst-x (cdr x) subst)))
    (cons (cons (caar x) (lhs-subst-x (cdar x) subst))
          (svtv-name-lhs-map-subst-x (cdr x) subst)))
  ///
  (defret lookup-in-<fn>
    (equal (svex-lookup var res)
           (let ((pair (hons-assoc-equal (svar-fix var) (svtv-name-lhs-map-fix x))))
             (and pair
                  (lhs-subst-x (cdr pair) subst))))
    :hints(("Goal" :in-theory (enable svex-lookup))))

  (defret eval-of-<fn>
    (equal (svex-alist-eval res env)
           (svtv-name-lhs-map-eval-x x (svex-alist-eval subst env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval
                                      svtv-name-lhs-map-eval-x))))

  (local (in-theory (enable svtv-name-lhs-map-fix))))



(define svtv-fsm-phase-inputsubst ((inputs svex-alist-p)
                                   (override-vals svex-alist-p)
                                   (override-tests svex-alist-p)
                                   (map svtv-name-lhs-map-p))
  :returns (phase-subst svex-alist-p)
  (b* ((in-subst (with-fast-alist inputs
                   (svtv-name-lhs-map-subst-x
                    (svtv-name-lhs-map-keys-change-override
                     (svtv-fsm-env-inversemap (svex-alist-keys inputs)
                                              map)
                     nil)
                    inputs)))
       (val-subst (with-fast-alist inputs
                    (svtv-name-lhs-map-subst-x
                     (svtv-name-lhs-map-keys-change-override
                      (svtv-fsm-env-inversemap (svex-alist-keys override-vals)
                                               map)
                      :val)
                     override-vals)))
       (test-subst (with-fast-alist inputs
                     (svtv-name-lhs-map-subst-x
                      (svtv-name-lhs-map-keys-change-override
                       (svtv-fsm-env-inversemap (svex-alist-keys override-tests)
                                                map)
                       :test)
                      override-tests))))
    (append test-subst val-subst in-subst))
  ///
  (defret eval-of-<fn>
    (equal (svex-alist-eval phase-subst env)
           (svtv-fsm-phase-inputs (svex-alist-eval inputs env)
                                  (svex-alist-eval override-vals env)
                                  (svex-alist-eval override-tests env)
                                  map))
    :hints(("Goal" :in-theory (enable svtv-fsm-phase-inputs)))))





(define svtv-fsm-step-env ((inputs svex-env-p)
                           (override-vals svex-env-p)
                           (override-tests svex-env-p)
                           (prev-st svex-env-p)
                           (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (env svex-env-p)
  (base-fsm-step-env (svtv-fsm-phase-inputs inputs override-vals override-tests
                                            (svtv-fsm->namemap x))
                     prev-st (svtv-fsm->nextstate x))
  ///
  (defret svtv-fsm-step-env-of-extract-states
    (equal (svtv-fsm-step-env
            inputs override-vals override-tests
            (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x))) prev-st)
            x)
           env))

  (defcong svtv-fsm-eval/namemap-equiv svex-envs-equivalent (svtv-fsm-step-env inputs override-vals override-tests prev-st x) 5)
  
  (defcong svex-envs-similar svex-envs-equivalent
    (svtv-fsm-step-env inputs override-vals override-tests prev-st x) 4))
    



(define lhatom-subst-zero ((x lhatom-p) (subst svex-alist-p))
  :returns (val svex-p)
  (lhatom-case x
    :z (svex-quote 0)
    :var (svex-rsh x.rsh
                   (or (svex-lookup x.name subst) (svex-x))))
  ///
  (defret eval-of-<fn>
    (equal (svex-eval val env)
           (lhatom-eval-zero x (svex-alist-eval subst env)))
    :hints(("Goal" :in-theory (enable svex-apply lhatom-eval-zero)))))
                      
(define lhs-subst-zero ((x lhs-p) (subst svex-alist-p))
  :returns (val svex-p)
  (if (atom x)
      (svex-quote 0)
    (b* (((lhrange x1) (car x)))
      (svex-concat x1.w
                   (lhatom-subst-zero x1.atom subst)
                   (lhs-subst-zero (cdr x) subst))))
  ///
  (defret eval-of-<fn>
    (equal (svex-eval val env)
           (lhs-eval-zero x (svex-alist-eval subst env)))
    :hints(("Goal" :in-theory (enable svex-apply lhs-eval-zero lhrange-eval)))))

(define svtv-name-lhs-map-subst ((x svtv-name-lhs-map-p) (subst svex-alist-p))
  :returns (res svex-alist-p)
    (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svtv-name-lhs-map-subst (cdr x) subst)))
    (cons (cons (caar x) (lhs-subst-zero (cdar x) subst))
          (svtv-name-lhs-map-subst (cdr x) subst)))
  ///
  (defret lookup-in-<fn>
    (equal (svex-lookup var res)
           (let ((pair (hons-assoc-equal (svar-fix var) (svtv-name-lhs-map-fix x))))
             (and pair
                  (lhs-subst-zero (cdr pair) subst))))
    :hints(("Goal" :in-theory (enable svex-lookup))))

  (defret eval-of-<fn>
    (equal (svex-alist-eval res env)
           (svtv-name-lhs-map-eval x (svex-alist-eval subst env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval
                                      svtv-name-lhs-map-eval))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys res)
           (alist-keys (svtv-name-lhs-map-fix x)))
    :hints(("Goal" :in-theory (enable svex-alist-keys alist-keys svtv-name-lhs-map-fix))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv!
    (svtv-name-lhs-map-subst x subst) 2
    :hints (("goal" :use ((:instance svex-envs-equivalent-implies-alist-eval-equiv
                           (x (svtv-name-lhs-map-subst x subst))
                           (y (svtv-name-lhs-map-subst x subst-equiv))))
             :in-theory (enable svex-alist-eval-equiv!-when-svex-alist-eval-equiv)
             :do-not-induct t)))

  (local (in-theory (enable svtv-name-lhs-map-fix))))



(define lhatom-compose-zero ((x lhatom-p) (compose svex-alist-p))
  :returns (val svex-p)
  (lhatom-case x
    :z (svex-quote 0)
    :var (svex-rsh x.rsh
                   (or (svex-fastlookup x.name compose)
                       (svex-var x.name))))
  ///
  (local (defthm svex-eval-of-svex-var
           (equal (svex-eval (svex-var name) env)
                  (svex-env-lookup name env))
           :hints(("Goal" :in-theory (enable svex-eval)))))

  (defret eval-of-<fn>
    (equal (svex-eval val env)
           (lhatom-eval-zero x (append (svex-alist-eval compose env) env)))
    :hints(("Goal" :in-theory (enable svex-apply lhatom-eval-zero)))))
                      
(define lhs-compose-zero ((x lhs-p) (compose svex-alist-p))
  :returns (val svex-p)
  (if (atom x)
      (svex-quote 0)
    (b* (((lhrange x1) (car x)))
      (svex-concat x1.w
                   (lhatom-compose-zero x1.atom compose)
                   (lhs-compose-zero (cdr x) compose))))
  ///
  (defret eval-of-<fn>
    (equal (svex-eval val env)
           (lhs-eval-zero x (append (svex-alist-eval compose env) env)))
    :hints(("Goal" :in-theory (enable svex-apply lhs-eval-zero lhrange-eval)))))

(define svtv-name-lhs-map-compose ((x svtv-name-lhs-map-p) (subst svex-alist-p))
  :returns (res svex-alist-p)
    (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svtv-name-lhs-map-compose (cdr x) subst)))
    (cons (cons (caar x) (lhs-compose-zero (cdar x) subst))
          (svtv-name-lhs-map-compose (cdr x) subst)))
  ///
  (defret lookup-in-<fn>
    (equal (svex-lookup var res)
           (let ((pair (hons-assoc-equal (svar-fix var) (svtv-name-lhs-map-fix x))))
             (and pair
                  (lhs-compose-zero (cdr pair) subst))))
    :hints(("Goal" :in-theory (enable svex-lookup))))

  (defret eval-of-<fn>
    (equal (svex-alist-eval res env)
           (svtv-name-lhs-map-eval x (append (svex-alist-eval subst env) env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval
                                      svtv-name-lhs-map-eval))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys res)
           (alist-keys (svtv-name-lhs-map-fix x)))
    :hints(("Goal" :in-theory (enable svex-alist-keys alist-keys svtv-name-lhs-map-fix))))

  (defcong svex-alist-eval-equiv svex-alist-eval-equiv!
    (svtv-name-lhs-map-compose x subst) 2
    :hints (("goal" :use ((:instance svex-envs-equivalent-implies-alist-eval-equiv
                           (x (svtv-name-lhs-map-compose x subst))
                           (y (svtv-name-lhs-map-compose x subst-equiv))))
             :in-theory (enable svex-alist-eval-equiv!-when-svex-alist-eval-equiv)
             :do-not-induct t)))

  (local (in-theory (enable svtv-name-lhs-map-fix))))



(define svtv-fsm->renamed-fsm ((x svtv-fsm-p))
  :returns (base-fsm base-fsm-p)
  (b* (((svtv-fsm x))
       (renamed-values
        (with-fast-alist x.values
          (svtv-name-lhs-map-subst x.namemap x.values))))
    (make-base-fsm :nextstate x.nextstate :values renamed-values))
  ///
  (memoize 'svtv-fsm->renamed-fsm)

  (defcong svtv-fsm-eval/namemap-equiv base-fsm-eval-equiv
    (svtv-fsm->renamed-fsm x) 1
    :hints(("Goal" :in-theory (enable svtv-fsm-eval/namemap-equiv
                                      base-fsm-eval-equiv)))))

(define svtv-fsm->renamed-values ((x svtv-fsm-p))
  :returns (res svex-alist-p)
  :enabled t
  (base-fsm->values (svtv-fsm->renamed-fsm x)))

(define svtv-name-lhs-map-to-svex-alist ((x svtv-name-lhs-map-p))
  :returns (alist svex-alist-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x))
                          (svar-p (caar x)))))
        (svtv-name-lhs-map-to-svex-alist (cdr x))))
    (cons (cons (caar x)
                (lhs->svex-zero (cdar x)))
          (svtv-name-lhs-map-to-svex-alist (cdr x))))
  ///
  (defret lookup-in-<fn>
    (equal (svex-lookup var alist)
           (b* ((look (hons-assoc-equal (svar-fix var) x)))
             (and look
                  (lhs->svex-zero (cdr look)))))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))

  (defret svex-alist-eval-of-<fn>
    (equal (svex-alist-eval alist env)
           (svtv-name-lhs-map-eval x env))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval svex-alist-eval))))

  (local (in-theory (enable svtv-name-lhs-map-fix))))

(encapsulate nil
  (local (defthm svar-p-when-lookup-in-name-svex-alist
           (implies (and (svex-alist-p x)
                         (not (svar-p key)))
                    (not (hons-assoc-equal key x)))))
  (local (defthm svar-p-when-lookup-in-name-svtv-name-lhs-map
           (implies (and (svtv-name-lhs-map-p x)
                         (not (svar-p key)))
                    (not (hons-assoc-equal key x)))))
  (local (defthm car-of-hons-assoc-equal
           (equal (car (hons-assoc-equal k x))
                  (and (hons-assoc-equal k x)
                       k))))
  (defthm svex-alist-p-of-fal-extract
    (implies (svex-alist-p x)
             (svex-alist-p (fal-extract keys x)))
    :hints(("Goal" :in-theory (enable fal-extract))))

  (defthm svtv-name-lhs-map-p-of-fal-extract
    (implies (svtv-name-lhs-map-p x)
             (svtv-name-lhs-map-p (fal-extract keys x)))
    :hints(("Goal" :in-theory (enable fal-extract))))

  (local (defthm hons-assoc-equal-of-fal-extract
           (equal (hons-assoc-equal key (fal-extract keys al))
                  (and (member-equal key keys)
                       (hons-assoc-equal key al)))
           :hints(("Goal" :in-theory (enable fal-extract hons-assoc-equal)))))

  (defthm svex-lookup-of-fal-extract
    (equal (svex-lookup var (fal-extract vars alist))
           (and (member-equal (svar-fix var) vars)
                (svex-lookup var alist)))
    :hints(("Goal" :in-theory (enable svex-lookup)
            :do-not-induct t))))


;; (defines svex-subst-fal
;;   :verify-guards nil
;;   (define svex-subst-fal
;;     :parents (svex-subst)
;;     :short "Substitution for @(see svex)es, identical to @(see svex-subst),
;; except that we memoize the results."
;;     ((pat svex-p)
;;      (al  svex-alist-p "Need not be fast; we still use slow lookups."))
;;     :returns (x (equal x (svex-subst pat al))
;;                 :hints ((and stable-under-simplificationp
;;                              '(:expand ((svex-subst pat al))))))
;;     :measure (svex-count pat)
;;     (svex-case pat
;;       :var (or (svex-fastlookup pat.name al)
;;                (svex-quote (4vec-x)))
;;       :quote (svex-fix pat)
;;       :call (svex-call pat.fn (svexlist-subst-fal pat.args al))))
;;   (define svexlist-subst-fal ((pat svexlist-p) (al svex-alist-p))
;;     :returns (x (equal x (svexlist-subst pat al))
;;                 :hints ((and stable-under-simplificationp
;;                              '(:expand ((svexlist-subst pat al))))))
;;     :measure (svexlist-count pat)
;;     (if (atom pat)
;;         nil
;;       (cons (svex-subst-fal (car pat) al)
;;             (svexlist-subst-fal (cdr pat) al))))
;;   ///
;;   (verify-guards svex-subst-fal))

;; (define svex-alist-subst-fal-nrev ((x svex-alist-p)
;;                                  (a svex-alist-p)
;;                                  (nrev))
;;   :hooks nil
;;   (if (atom x)
;;       (acl2::nrev-fix nrev)
;;     (if (mbt (and (consp (car x)) (svar-p (caar x))))
;;         (b* ((nrev (acl2::nrev-push (cons (caar x) (svex-subst-fal (cdar x) a)) nrev)))
;;           (svex-alist-subst-fal-nrev (cdr x) a nrev))
;;       (svex-alist-subst-fal-nrev (cdr x) a nrev))))

;; (define svex-alist-subst-fal ((x svex-alist-p) (a svex-alist-p))
;;   :prepwork ((local (in-theory (enable svex-alist-p))))
;;   :returns (xx)
;;   :verify-guards nil
;;   (if (atom x)
;;       nil
;;     (acl2::with-local-nrev
;;       (svex-alist-subst-fal-nrev x a acl2::nrev)))
;;   ///
;;   (local (defthm svex-alist-subst-fal-nrev-elim
;;            (equal (svex-alist-subst-fal-nrev x a nrev)
;;                   (append nrev (svex-alist-subst x a)))
;;            :hints(("Goal" :in-theory (e/d (svex-alist-subst-fal-nrev
;;                                            svex-alist-subst
;;                                            acl2::rcons
;;                                            svex-acons))))))
;;   (defret svex-alist-subst-fal-is-svex-alist-subst
;;     (equal xx (svex-alist-subst x a))
;;     :hints(("Goal" :in-theory (enable svex-alist-subst))))
;;   (verify-guards svex-alist-subst-fal))






(define svtv-fsm-outexprs ((outvars svarlist-p)
                                   (x svtv-fsm-p))
  :returns (outs svex-alist-p)
  (svex-alist-extract outvars (svtv-fsm->renamed-values x))
  ///
  ;; (local (defthm svex-lookup-of-svex-alist-subst+
  ;;          (equal (svex-lookup var (svex-alist-subst x subst))
  ;;                 (b* ((look (svex-lookup var x)))
  ;;                   (and look
  ;;                        (svex-subst look subst))))
  ;;          :hints(("Goal" :in-theory (enable svex-alist-subst svex-lookup svex-acons)))))

  (local (defcong svex-envs-similar equal (lhs-eval-zero x env) 2
           :hints(("Goal" :in-theory (enable lhs-eval-zero lhrange-eval lhatom-eval)))))


  (defcong svtv-fsm-eval/namemap-equiv svex-alist-eval-equiv
    (svtv-fsm-outexprs outvars x) 2
    :hints ((witness) (witness))))




(define svtv-fsm-step ((inputs svex-env-p)
                       (override-vals svex-env-p)
                       (override-tests svex-env-p)
                       (prev-st svex-env-p)
                       (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (nextstate svex-env-p)
  (b* ((env (svtv-fsm-step-env inputs override-vals override-tests prev-st x)))
    (with-fast-alist env
      (svex-alist-eval (svtv-fsm->nextstate x) env)))
  ///
  (defret alist-keys-of-<fn>
    (equal (alist-keys nextstate)
           (svex-alist-keys (svtv-fsm->nextstate x))))

  (defret svtv-fsm-step-of-extract-states
    (equal (svtv-fsm-step
            inputs override-vals override-tests
            (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x))) prev-st)
            x)
           nextstate))

  (defcong svtv-fsm-eval/namemap-equiv svex-envs-equivalent
    (svtv-fsm-step inputs override-vals override-tests prev-st x) 5)

  (defcong svex-envs-similar svex-envs-equivalent
    (svtv-fsm-step inputs override-vals override-tests prev-st x) 4))




(define svtv-fsm-step-outs ((inputs svex-env-p)
                            (override-vals svex-env-p)
                            (override-tests svex-env-p)
                            (prev-st svex-env-p)
                            (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (outs svex-env-p)
  (b* ((env (svtv-fsm-step-env inputs override-vals override-tests prev-st x)))
    (with-fast-alist env
      (svex-alist-eval
       (svtv-fsm->renamed-values x) env)))
  ///
  (defret svtv-fsm-step-outs-of-extract-states
    (equal (svtv-fsm-step-outs
            inputs override-vals override-tests
            (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x))) prev-st)
            x)
           outs)))

(define svtv-fsm-step-extracted-outs ((inputs svex-env-p)
                                      (override-vals svex-env-p)
                                      (override-tests svex-env-p)
                                      (outvars svarlist-p)
                                      (prev-st svex-env-p)
                                      (x svtv-fsm-p))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :returns (outs svex-env-p)
  (b* ((env (svtv-fsm-step-env inputs override-vals override-tests prev-st x)))
    (with-fast-alist env
      (svex-alist-eval
       (svtv-fsm-outexprs outvars x)
       env)))
  ///
  (defret svtv-fsm-step-extracted-outs-of-extract-states
    (equal (svtv-fsm-step-extracted-outs
            inputs override-vals override-tests outvars
            (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x))) prev-st)
            x)
           outs))

  (defcong svtv-fsm-eval/namemap-equiv svex-envs-equivalent
    (svtv-fsm-step-extracted-outs inputs override-vals override-tests outvars prev-st x) 6)

  (defcong svex-envs-similar svex-envs-equivalent
    (svtv-fsm-step-extracted-outs inputs override-vals override-tests outvars prev-st x) 5)

  (defretd <fn>-in-terms-of-full-outs
    (equal outs
           (svex-env-extract outvars (svtv-fsm-step-outs inputs override-vals override-tests prev-st x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-step-outs svtv-fsm-outexprs)))))


;; (define svtv-fsm-step-output-signals ((outvars svarlist-p)
;;                                               (x svtv-fsm-p))
;;   :prepwork ((local (defthm len-equal-const
;;                       (implies (syntaxp (quotep n))
;;                                (equal (equal (len x) n)
;;                                       (if (atom x)
;;                                           (equal n 0)
;;                                         (and (posp n)
;;                                              (equal (len (cdr x)) (1- n))))))))
;;              (local (in-theory (disable len)))
             
;;              (local (defthm vars-of-svex-concat
;;                       (implies (and (posp w)
;;                                     (not (svex-case x
;;                                            :call (or (eq x.fn 'concat)
;;                                                      (eq x.fn 'signx)
;;                                                      (eq x.fn 'zerox))
;;                                            :otherwise nil)))
;;                                (set-equiv (svex-vars (svex-concat w x y))
;;                                           (append (svex-vars x) (svex-vars y))))
;;                       :hints(("Goal" :in-theory (enable svex-concat
;;                                                         svexlist-vars
;;                                                         match-concat
;;                                                         match-ext)))))
;;              ;; BOZO replace vars-of-lhs->svex with this
;;              (local (defthm vars-of-lhs->svex-strict
;;                       (set-equiv (svex-vars (lhs->svex-zero x))
;;                                  (lhs-vars x))
;;                       :hints(("Goal" :in-theory (enable svex-vars lhs->svex-zero lhs-vars
;;                                                         lhatom-vars lhatom->svex svex-rsh
;;                                                         match-concat match-ext match-rsh)
;;                               :induct (lhs->svex-zero x)
;;                               ;; :expand ((SVEX-CONCAT (LHRANGE->W (CAR X))
;;                               ;;                       '(0 . -1)
;;                               ;;                       (LHS->SVEX (CDR X))))
;;                               ;; :expand ((:free (x y) (svex-rsh x y)))
;;                               ;; :expand
;;                               ;; ((:free (w x y) (svex-concat w x y)))
;;                               ))))

;;              (local (defthm equal-of-mergesort
;;                       (equal (equal (mergesort x) y)
;;                              (and (setp y)
;;                                   (set-equiv x y)))))

;;              (local (defthm svex-alist-vars-of-svtv-name-lhs-map-to-svex-alist
;;                       (set-equiv (svex-alist-vars (svtv-name-lhs-map-to-svex-alist x))
;;                                  (lhslist-vars (alist-vals (svtv-name-lhs-map-fix x))))
;;                       :hints(("Goal" :in-theory (enable svtv-name-lhs-map-to-svex-alist
;;                                                         svtv-name-lhs-map-fix
;;                                                         svex-alist-vars
;;                                                         lhslist-vars
;;                                                         alist-vals)))))

;;              )
;;   :returns (signals svarlist-p)
;;   (b* (((svtv-fsm x))
;;        (out-alist1 (acl2::fal-extract (svarlist-fix outvars) x.namemap)))
;;     (mbe :logic (set::mergesort (svex-alist-vars (svtv-name-lhs-map-to-svex-alist out-alist1)))
;;          :exec (set::mergesort (lhslist-vars (alist-vals out-alist1))))))


;; (define svtv-fsm-step-extract-outs ((outvars svarlist-p)
;;                                             (full-outs svex-env-p)
;;                                             (x svtv-fsm-p))
;;   :returns (outs svex-env-p)
;;   (b* (((svtv-fsm x))
;;        (out-alist1 (acl2::fal-extract (svarlist-fix outvars) x.namemap)))
;;     (with-fast-alist full-outs
;;       (svex-alist-eval
;;        (svtv-name-lhs-map-to-svex-alist out-alist1) full-outs)))
;;   ///
;;   (defthmd svtv-fsm-step-extracted-outs-is-extract-of-full-outs
;;     (equal (svtv-fsm-step-extracted-outs inputs override-tests outvars prev-st x)
;;            (svtv-fsm-step-extract-outs outvars
;;                                                (svtv-fsm-step-outs
;;                                                 inputs override-tests prev-st x)
;;                                                x))
;;     :hints(("Goal" :in-theory (enable svtv-fsm-step-outs
;;                                       svtv-fsm-step-extracted-outs
;;                                       svtv-fsm-outexprs))))

;;   (local (defthm svexlist-vars-of-svex-alist-vals
;;            (equal (svexlist-vars (svex-alist-vals x))
;;                   (svex-alist-vars x))
;;            :hints(("Goal" :in-theory (enable svex-alist-vals svex-alist-vars
;;                                              svexlist-vars)))))

;;   (defthmd svtv-fsm-step-extracted-outs-is-extract-of-step-outs
;;     (equal (svtv-fsm-step-extracted-outs inputs override-tests outvars prev-st x)
;;            (svtv-fsm-step-extract-outs
;;             outvars
;;             (svex-env-extract (svtv-fsm-step-output-signals outvars x)
;;                               (base-fsm-step-outs (svtv-fsm-env inputs override-tests x)
;;                                                   prev-st (svtv-fsm->base-fsm x)))
;;             x))
;;     :hints(("Goal" :in-theory (enable svtv-fsm-step-output-signals
;;                                       base-fsm-step-outs
;;                                       svtv-fsm-step-env
;;                                       svtv-fsm-step-extracted-outs
;;                                       svtv-fsm-outexprs))))

;;   (local (defthm car-of-hons-assoc-equal
;;            (equal (car (hons-assoc-equal key x))
;;                   (and (hons-assoc-equal key x)
;;                        key))))

;;   (local (defthm hons-assoc-equal-of-fal-extract
;;            (equal (hons-assoc-equal key (fal-extract vars al))
;;                   (and (member-equal key vars)
;;                        (hons-assoc-equal key al)))
;;            :hints(("Goal" :in-theory (enable fal-extract hons-assoc-equal)))))

;;   (defretd lookup-of-<fn>
;;     (equal (svex-env-lookup var outs)
;;            (let ((look (hons-assoc-equal (svar-fix var) (svtv-fsm->namemap x))))
;;              (if (and (member-equal (svar-fix var) (svarlist-fix outvars))
;;                       look)
;;                  (lhs-eval-zero (cdr look) full-outs)
;;                (4vec-x))))))




(define svtv-fsm-to-base-fsm-inputs ((inputs svex-envlist-p)
                                     (override-vals svex-envlist-p)
                                     (override-tests svex-envlist-p)
                                     (map svtv-name-lhs-map-p))
  :returns (phase-envs svex-envlist-p)
  (if (atom inputs)
      nil
    (cons (svtv-fsm-phase-inputs (car inputs) (car override-vals) (car override-tests) map)
          (svtv-fsm-to-base-fsm-inputs (cdr inputs) (cdr override-vals) (cdr override-tests) map)))
  ///

  (defret len-of-<fn>
    (equal (len phase-envs) (len inputs))))
  

(define svtv-fsm-to-base-fsm-inputsubsts ((inputs svex-alistlist-p)
                                          (override-vals svex-alistlist-p)
                                          (override-tests svex-alistlist-p)
                                          (map svtv-name-lhs-map-p))
  :returns (substs svex-alistlist-p)
  (if (atom inputs)
      nil
    (cons (svtv-fsm-phase-inputsubst (car inputs) (car override-vals) (car override-tests) map)
          (svtv-fsm-to-base-fsm-inputsubsts (cdr inputs) (cdr override-vals) (cdr override-tests) map)))
  ///
  (defret eval-of-<fn>
    (equal (svex-alistlist-eval substs env)
           (svtv-fsm-to-base-fsm-inputs
            (svex-alistlist-eval inputs env)
            (svex-alistlist-eval override-vals env)
            (svex-alistlist-eval override-tests env)
            map))
    :hints(("Goal" :in-theory (enable svtv-fsm-to-base-fsm-inputs
                                      svex-alistlist-eval
                                      svex-alist-eval)))))




(define svtv-fsm-final-state ((inputs svex-envlist-p)
                              (prev-st svex-env-p)
                              (x svtv-fsm-p)
                              &key
                              ((override-vals svex-envlist-p) 'nil)
                              ((override-tests svex-envlist-p) 'nil))
  :returns (final-st svex-env-p)
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  (if (atom inputs)
      (mbe :logic (svex-env-extract (svex-alist-keys (svtv-fsm->nextstate x)) prev-st)
           :exec prev-st)
    (svtv-fsm-final-state (cdr inputs)
                          (svtv-fsm-step (car inputs)
                                         (car override-vals)
                                         (car override-tests)
                                         prev-st x)
                          x
                          :override-vals (cdr override-vals)
                          :override-tests (cdr override-tests)))
  ///
  (defretd <fn>-is-svtv-fsm-final-state-of-input-envs
    (equal final-st
           (base-fsm-final-state (svtv-fsm-to-base-fsm-inputs inputs override-vals override-tests (svtv-fsm->namemap x))
                                 prev-st (svtv-fsm->nextstate x)))
    :hints(("Goal" :in-theory (enable base-fsm-final-state
                                      svtv-fsm-to-base-fsm-inputs
                                      svtv-fsm-step
                                      svtv-fsm-step-env
                                      base-fsm-step))))

  (defret svtv-fsm-final-state-of-extract-states
    (equal (svtv-fsm-final-state
            inputs
            (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x))) prev-st)
            x :override-vals override-vals :override-tests override-tests)
           final-st))

  (defretd svtv-fsm-final-state-open-rev
    (implies (and (consp inputs)
                  (no-duplicatesp (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x)))))
             (equal final-st
                    (b* ((len (len inputs)))
                      (svtv-fsm-step (nth (+ -1 len) inputs)
                                     (nth (+ -1 len) override-vals)
                                     (nth (+ -1 len) override-tests)
                                     (svtv-fsm-final-state
                                      (take (+ -1 len) inputs)
                                      prev-st x
                                      :override-vals (take (+ -1 len) override-vals)
                                      :override-tests (take (+ -1 len) override-tests))
                                     x))))
    :hints(("Goal" :in-theory (enable svtv-fsm-final-state
                                      ;; svtv-fsm-eval
                                      take acl2::default-car
                                      )
            :expand ((len inputs))
            :induct <call>)
           (and stable-under-simplificationp
                '(:expand ((nth (len (cdr inputs)) inputs)))))))


;; (defsection svtv-fsm-open-nth
;;   (local (defun svtv-fsm-ind (n ins overrides initst svtv)
;;            (if (zp n)
;;                (list ins initst)
;;              (svtv-fsm-ind (1- n) (cdr ins) (cdr overrides)
;;                            (svtv-fsm-step (car ins) (car overrides) initst svtv)
;;                            svtv))))

;;   ;; (defthm svtv-fsm-step-outs-of-env-extract
;;   ;;   (equal (svtv-fsm-step-outs ins overrides
;;   ;;                                           (svex-env-extract
;;   ;;                                                (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm svtv)))
;;   ;;                                                prev-st)
;;   ;;                                           svtv)
;;   ;;          (svtv-fsm-step-outs ins overrides prev-st svtv))
;;   ;;   :hints(("Goal" :in-theory (enable svtv-fsm-step-outs))))

;;   ;; (defthm svtv-fsm-step-of-env-extract
;;   ;;   (equal (svtv-fsm-step ins overrides
;;   ;;                                 (svex-env-extract
;;   ;;                                  (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm svtv)))
;;   ;;                                  prev-st)
;;   ;;                         svtv)
;;   ;;          (svtv-fsm-step ins overrides prev-st svtv))
;;   ;;   :hints(("Goal" :in-theory (enable svtv-fsm-step))))

;;   (defthm env-extract-of-svtv-fsm-step
;;     (implies (no-duplicatesp (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm svtv))))
;;              (equal (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm svtv)))
;;                                       (svtv-fsm-step ins overrides prev-st svtv))
;;                     (svtv-fsm-step ins overrides prev-st svtv)))
;;     ;; :hints(("Goal" :in-theory (enable svtv-fsm-step)))
;;     )

;;   (defthmd svtv-fsm-eval-open-nth
;;     (implies (< (nfix n) (len ins))
;;              (equal (nth n (svtv-fsm-eval ins overrides initst svtv))
;;                     (svtv-fsm-step-outs
;;                      (nth n ins)
;;                      (nth n overrides)
;;                      (svtv-fsm-final-state (take n ins) (take n overrides) initst svtv)
;;                      svtv)))
;;     :hints(("Goal" :in-theory (enable svtv-fsm-final-state
;;                                       svtv-fsm-eval  ;; -when-consp-ins
;;                                       take)
;;             :expand ((len ins)
;;                      (:free (a b) (nth n (cons a b))))
;;             :induct (svtv-fsm-ind n ins overrides initst svtv))))

;;   (defthmd svtv-fsm-final-state-open-rev
;;     (implies (and (consp ins)
;;                   (no-duplicatesp (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm svtv)))))
;;              (equal (svtv-fsm-final-state ins overrides initst svtv)
;;                     (svtv-fsm-step (nth (+ -1 (len ins)) ins)
;;                                            (nth (+ -1 (len ins)) overrides)
;;                                            (svtv-fsm-final-state
;;                                             (take (+ -1 (len ins)) ins)
;;                                             (take (+ -1 (len ins)) overrides)
;;                                             initst svtv)
;;                                            svtv)))
;;     :hints(("Goal" :in-theory (enable svtv-fsm-final-state
;;                                       ;; svtv-fsm-eval
;;                                       take acl2::default-car
;;                                       )
;;             :expand ((len ins))
;;             :induct (svtv-fsm-final-state ins overrides initst svtv))
;;            (and stable-under-simplificationp
;;                 '(:expand ((nth (len (cdr ins)) ins)))))))




          





(defsection nth-of-base-fsm-eval
  (local (defun nth-of-sfe-ind (n ins prev-st x)
           (if (atom ins)
               (list n prev-st)
             (nth-of-sfe-ind (1- n) (cdr ins)
                             (base-fsm-step (car ins) prev-st (base-fsm->nextstate x))
                             x))))
  (defthmd nth-of-base-fsm-eval
    (equal (nth n (base-fsm-eval ins prev-st x))
           (and (< (nfix n) (len ins))
                (b* ((st (base-fsm-final-state (take n ins) prev-st (base-fsm->nextstate x))))
                  (base-fsm-step-outs (nth n ins) st x))))
    :hints(("Goal" :in-theory (enable base-fsm-final-state
                                      base-fsm-eval nth)
            :induct (nth-of-sfe-ind n ins prev-st x)))))






(define svtv-fsm-eval ((inputs svex-envlist-p)
                       (prev-st svex-env-p)
                       (x svtv-fsm-p)
                       &key
                       ((override-vals svex-envlist-p) 'nil)
                       ((override-tests svex-envlist-p) 'nil))
  :returns (outs svex-envlist-p)
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svtv-fsm-step-extracted-outs
                                          svtv-fsm-step))))
  (if (atom inputs)
      nil
    (b* (((mv outs nextst)
          (mv (svtv-fsm-step-outs
               (car inputs)
               (car override-vals)
               (car override-tests)
               prev-st x)
              (svtv-fsm-step (car inputs)
                             (car override-vals)
                             (car override-tests)
                             prev-st x))))
      (cons outs
            (svtv-fsm-eval (cdr inputs)
                           nextst
                           x
                           :override-vals (cdr override-vals)
                           :override-tests (cdr override-tests)))))
  ///
  (defretd <fn>-is-svtv-fsm-eval-of-input-envs
    (equal outs
           (base-fsm-eval (svtv-fsm-to-base-fsm-inputs inputs override-vals override-tests
                                                       (svtv-fsm->namemap x))
                          prev-st
                          (svtv-fsm->renamed-fsm x)))
    :hints(("Goal" :in-theory (enable base-fsm-eval svtv-fsm-to-base-fsm-inputs
                                      svtv-fsm-step-outs
                                      svtv-fsm-step
                                      svtv-fsm->renamed-fsm
                                      base-fsm-step-env
                                      svtv-fsm-step-env
                                      base-fsm-step
                                      base-fsm-step-outs))))

  
  (defret <fn>-of-extract-states
    (equal (svtv-fsm-eval
            inputs
            (svex-env-extract (svex-alist-keys (base-fsm->nextstate (svtv-fsm->base-fsm x))) prev-st)
            x :override-vals override-vals :override-tests override-tests)
           outs))

  (local (defun svtv-fsm-ind (n ins override-vals override-tests initst svtv)
           (if (zp n)
               (list ins initst)
             (svtv-fsm-ind (1- n) (cdr ins) (cdr override-vals) (cdr override-tests)
                           (svtv-fsm-step (car ins) (car override-vals) (car override-tests) initst svtv)
                           svtv))))

  (defretd svtv-fsm-eval-open-nth
    (implies (< (nfix n) (len inputs))
             (equal (nth n outs)
                    (svtv-fsm-step-outs
                     (nth n inputs)
                     (nth n override-vals)
                     (nth n override-tests)
                     (svtv-fsm-final-state (take n inputs) prev-st x
                                           :override-vals  (take n override-vals)
                                           :override-tests (take n override-tests))
                     x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-final-state
                                      svtv-fsm-eval ;; -when-consp-ins
                                      take)
            :expand ((len inputs)
                     (:free (a b) (nth n (cons a b)))
                     <call>)
            :induct (svtv-fsm-ind n inputs override-vals override-tests prev-st x)))))

;; (define svtv-fsm-run-extract-outs ((outvars svarlist-list-p)
;;                                            (full-outs svex-envlist-p)
;;                                            (x svtv-fsm-p))
;;   :returns (outs svex-envlist-p)
;;   (if (atom outvars)
;;       nil
;;     (cons (svtv-fsm-step-extract-outs (car outvars) (car full-outs) x)
;;           (svtv-fsm-run-extract-outs (cdr outvars) (cdr full-outs) x)))
;;   ///
;;   (local (defun ind (n outvars full-outs)
;;            (if (zp n)
;;                (list outvars full-outs)
;;              (ind (1- n) (cdr outvars) (cdr full-outs)))))
;;   (defret nth-of-<fn>
;;     (equal (nth n outs)
;;            (svtv-fsm-step-extract-outs
;;             (nth n outvars) (nth n full-outs) x))
;;     :hints (("goal" :induct (ind n outvars full-outs) :in-theory (enable nth))
;;             (and stable-under-simplificationp
;;                  '(:in-theory (enable svtv-fsm-step-extract-outs fal-extract svex-alist-eval))))))

;; (define svtv-fsm-run-output-signals ((outvars svarlist-list-p)
;;                                              (x svtv-fsm-p))
;;   :returns (outs svarlist-list-p)
;;   (if (atom outvars)
;;       nil
;;     (cons (svtv-fsm-step-output-signals (car outvars) x)
;;           (svtv-fsm-run-output-signals (cdr outvars) x))))


(define svtv-fsm-run ((inputs svex-envlist-p)
                      (prev-st svex-env-p)
                      (x svtv-fsm-p)
                      (outvars svarlist-list-p)
                      &key
                      ((override-vals svex-envlist-p) 'nil)
                      ((override-tests svex-envlist-p) 'nil))
  :returns (outs svex-envlist-p)
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svtv-fsm-step-extracted-outs
                                          svtv-fsm-step))))
  (if (atom outvars)
      nil
    (b* (((mv outs nextst)
          (mbe :logic 
               (mv (svtv-fsm-step-extracted-outs (car inputs)
                                                 (car override-vals)
                                                 (car override-tests)
                                                 (car outvars)
                                                 prev-st x)
                   (svtv-fsm-step (car inputs)
                                  (car override-vals)
                                  (car override-tests)
                                  prev-st x))
               :exec
               (b* ((env (svtv-fsm-step-env (car inputs)
                                            (car override-vals)
                                            (car override-tests)
                                            prev-st x))
                    ((mv outs nextst)
                     (with-fast-alist env
                       (mv (svex-alist-eval
                            (svtv-fsm-outexprs (car outvars) x)
                            env)
                           (svex-alist-eval (svtv-fsm->nextstate x) env)))))
                 (fast-alist-free env)
                 (mv outs nextst)))))
      (cons outs
            (svtv-fsm-run (cdr inputs)
                          nextst
                          x
                          (cdr outvars)
                          :override-vals (cdr override-vals)
                          :override-tests (cdr override-tests)))))
  ///
  (local (defun nth-of-fn-induct (n inputs override-vals override-tests outvars prev-st x)
           (if (atom outvars)
               (list n inputs prev-st)
             (nth-of-fn-induct
              (1- n)
              (cdr inputs)
              (cdr override-vals)
              (cdr override-tests)
              (cdr outvars)
              (svtv-fsm-step (car inputs) (car override-vals) (car override-tests) prev-st x)
              x))))

  (local (defthm svtv-fsm-step-extracted-outs-of-no-outvars
           (equal (svtv-fsm-step-extracted-outs ins override-vals override-tests nil prev-st x)
                  nil)
           :hints(("Goal" :in-theory (enable svtv-fsm-step-extracted-outs
                                             svtv-fsm-outexprs
                                             svex-env-extract
                                             svex-alist-eval)))))
  

  (defretd nth-of-<fn>
    (equal (nth n outs)
           (b* ((st (svtv-fsm-final-state (take n inputs)
                                          prev-st x
                                          :override-vals (take n override-vals)
                                          :override-tests (take n override-tests))))
             (svtv-fsm-step-extracted-outs (nth n inputs)
                                           (nth n override-vals)
                                           (nth n override-tests)
                                           (nth n outvars)
                                           st x)))
    :hints(("Goal" :in-theory (enable svtv-fsm-final-state
                                      nth)
            :induct (nth-of-fn-induct n inputs override-vals override-tests outvars prev-st x))))

  ;; (local (defthm svex-alist-eval-of-fal-extract
  ;;          (equal (svex-alist-eval (fal-extract vars x) env)
  ;;                 (svex-env-extract

  (defretd <fn>-is-extract-of-eval
    (equal outs
           (svex-envlist-extract
            outvars
            (svtv-fsm-eval (take (len outvars) inputs) prev-st x
                           :override-vals override-vals
                           :override-tests override-tests)))
    :hints(("Goal" :in-theory (e/d (;; svtv-fsm-run-extract-outs
                                    svtv-fsm-eval
                                    svtv-fsm-step-extracted-outs
                                    svtv-fsm-step-outs
                                    svex-envlist-extract
                                    svtv-fsm-outexprs
                                    ;; svtv-fsm-step-extracted-outs-is-extract-of-full-outs
                                    )
                                   (acl2::take-of-too-many))
            :induct <call>)))

  (defret <fn>-of-extract-states
    (equal (svtv-fsm-run
            inputs
            (svex-env-extract (svex-alist-keys (svtv-fsm->nextstate x)) prev-st)
            x
            outvars
            :override-vals override-vals
            :override-tests override-tests)
           outs))


  (defretd <fn>-is-base-fsm-run
    (equal outs
           (base-fsm-run
            (svtv-fsm-to-base-fsm-inputs
             (take (len outvars) inputs)
             override-vals override-tests
             (svtv-fsm->namemap x))
            prev-st
            (svtv-fsm->renamed-fsm x)
            outvars))
    :hints(("Goal" :in-theory (enable base-fsm-run
                                      svex-envlist-extract
                                      base-fsm-eval
                                      base-fsm-step-env
                                      svtv-fsm->renamed-fsm
                                      ;; svtv-fsm-run-output-signals
                                      svtv-fsm-to-base-fsm-inputs
                                      ;; svtv-fsm-run-extract-outs
                                      ;; svtv-fsm-step-extracted-outs-is-extract-of-step-outs
                                      svtv-fsm-step
                                      svtv-fsm-step-extracted-outs
                                      svtv-fsm-outexprs
                                      base-fsm-step-outs
                                      base-fsm-step
                                      svtv-fsm-step-env)
            :induct <call>)))

  (defcong svex-envlists-equivalent svex-envlists-equivalent (cons a b) 2
    :hints ((witness)))

  (local (defun svtv-fsm-run-prev-st-cong-ind (inputs override-vals override-tests
                                                      prev-st prev-st-equiv
                                                      x outvars)
           (if (atom outvars)
               (list inputs override-vals override-tests prev-st prev-st-equiv x)
             (b* ((nextst1
                   (svtv-fsm-step (car inputs)
                                  (car override-vals)
                                  (car override-tests)
                                  prev-st x))
                  (nextst2
                   (svtv-fsm-step (car inputs)
                                  (car override-vals)
                                  (car override-tests)
                                  prev-st-equiv x)))
               (svtv-fsm-run-prev-st-cong-ind (cdr inputs)
                                              (cdr override-vals)
                                              (cdr override-tests)
                                              nextst1 nextst2
                                              x
                                              (cdr outvars))))))

  (defcong svex-envs-similar svex-envlists-equivalent
    (svtv-fsm-run inputs prev-st x outvars
                  :override-vals override-vals
                  :override-tests override-tests)
    2
    :hints (("goal" :induct (svtv-fsm-run-prev-st-cong-ind inputs override-vals override-tests prev-st prev-st-equiv x outvars)
             :expand ((:free (prev-st) (svtv-fsm-run inputs prev-st x outvars
                                                     :override-vals override-vals
                                                     :override-tests override-tests))))))

  (defcong svtv-fsm-eval/namemap-equiv svex-envlists-equivalent
    (svtv-fsm-run inputs prev-st x outvars
                  :override-vals override-vals
                  :override-tests override-tests) 3
    :hints (("goal" :induct (svtv-fsm-run inputs prev-st x outvars
                                          :override-vals override-vals
                                          :override-tests override-tests)
             :expand ((:free (x) (svtv-fsm-run inputs prev-st x outvars
                                               :override-vals override-vals
                                               :override-tests override-tests))))))

  (defret len-of-<fn>
    (equal (len outs) (len outvars))))


(define svtv-fsm-run-states ((inputs svex-envlist-p)
                              (prev-st svex-env-p)
                              (x svtv-fsm-p)
                              (statevars svarlist-list-p)
                              &key
                              ((override-vals svex-envlist-p) 'nil)
                              ((override-tests svex-envlist-p) 'nil))
  :returns (states svex-envlist-p)
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svtv-fsm-step-extracted-outs
                                          svtv-fsm-step))))
  (if (atom statevars)
      nil
    (b* ((nextst
          (svtv-fsm-step (car inputs)
                         (car override-vals)
                         (car override-tests)
                         prev-st x)))
      (cons (svex-env-extract (car statevars) nextst)
            (svtv-fsm-run-states (cdr inputs)
                                 nextst x
                                 (cdr statevars)
                                 :override-vals (cdr override-vals)
                                 :override-tests (cdr override-tests)))))
  ///
  
  (defretd <fn>-is-base-fsm-run-states
    (equal states
           (base-fsm-run-states
            (svtv-fsm-to-base-fsm-inputs
             (take (len statevars) inputs)
             override-vals override-tests (svtv-fsm->namemap x))
            prev-st
            (svtv-fsm->nextstate x)
            statevars))
    :hints(("Goal" :in-theory (enable base-fsm-run-states
                                      svex-envlist-extract
                                      base-fsm-eval
                                      base-fsm-step-env
                                      svtv-fsm->renamed-fsm
                                      ;; svtv-fsm-run-output-signals
                                      svtv-fsm-to-base-fsm-inputs
                                      ;; svtv-fsm-run-extract-outs
                                      ;; svtv-fsm-step-extracted-outs-is-extract-of-step-outs
                                      svtv-fsm-step
                                      svtv-fsm-step-extracted-outs
                                      svtv-fsm-outexprs
                                      base-fsm-step-outs
                                      base-fsm-step
                                      svtv-fsm-step-env)
            :induct <call>)))

  (defret len-of-<fn>
    (equal (len states) (len statevars))))


(define svtv-fsm-run-outs-and-states ((inputs svex-envlist-p)
                                      (prev-st svex-env-p)
                                      (x svtv-fsm-p)
                                      &key
                                      ((override-vals svex-envlist-p) 'nil)
                                      ((override-tests svex-envlist-p) 'nil)
                                      ((out-signals svarlist-list-p) 'nil)
                                      ((state-signals svarlist-list-p) 'nil))
  ;; :measure (Max (len out-signals) (len state-signals))
  :guard-hints (("goal" :in-theory (enable svtv-fsm-run svtv-fsm-run-states
                                           svtv-fsm-run-outs-and-states-fn)
                 :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-fsm-step-extracted-outs
                                          svtv-fsm-step))))
  :guard (and (equal (alist-keys prev-st) (svex-alist-keys (svtv-fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (svtv-fsm->nextstate x)))))
  :enabled t
  :returns (mv outs states)
  (mbe :logic (mv (svtv-fsm-run inputs prev-st x out-signals :override-vals override-vals :override-tests override-tests)
                  (svtv-fsm-run-states inputs prev-st x state-signals :override-vals override-vals :override-tests override-tests))
       :exec
       (if (and (atom out-signals) (atom state-signals))
           (mv nil nil)
         (b* (((mv outs nextst)
               (mbe :logic 
                    (mv (svtv-fsm-step-extracted-outs (car inputs)
                                                      (car override-vals)
                                                      (car override-tests)
                                                      (car out-signals)
                                                      prev-st x)
                        (svtv-fsm-step (car inputs)
                                       (car override-vals)
                                       (car override-tests)
                                       prev-st x))
                    :exec
                    (b* ((env (svtv-fsm-step-env (car inputs)
                                                 (car override-vals)
                                                 (car override-tests)
                                                 prev-st x))
                         ((mv outs nextst)
                          (with-fast-alist env
                            (mv (svex-alist-eval
                                 (svtv-fsm-outexprs (car out-signals) x)
                                 env)
                                (svex-alist-eval (svtv-fsm->nextstate x) env)))))
                      (fast-alist-free env)
                      (mv outs nextst))))
              ((mv rest-outs rest-states)
               (svtv-fsm-run-outs-and-states (cdr inputs)
                                             nextst x
                                             :out-signals (cdr out-signals)
                                             :state-signals (cdr state-signals)
                                             :override-vals (cdr override-vals)
                                             :override-tests (cdr override-tests))))
           (mv (and (consp out-signals) (cons outs rest-outs))
               (and (consp state-signals)
                    (cons (svex-env-extract (car state-signals) nextst)
                          rest-states))))))
  ///
  
  (local (defthm true-listp-when-svex-envlist-p-rewrite
           (implies (svex-envlist-p x)
                    (true-listp x))))

  (local (defthm take-of-same-len
           (implies (equal len (len x))
                    (equal (take len x) (true-list-fix x)))))

  (local (defthm take-of-svtv-fsm-to-base-fsm-inputs
           (implies (<= (nfix len) (len inputs))
                    (equal (take len (svtv-fsm-to-base-fsm-inputs inputs override-vals override-tests x))
                           (svtv-fsm-to-base-fsm-inputs (take len inputs) override-vals override-tests x)))
           :hints(("Goal" :in-theory (enable svtv-fsm-to-base-fsm-inputs)))))

  (local (defthmd base-fsm-run-when-outvars-Shorter-than-inputs-lemma
           (implies (<= (len outvars) (len inputs))
                    (equal (base-fsm-run inputs prev-st fsm outvars)
                           (base-fsm-run (take (len outvars) inputs) prev-st fsm outvars)))
           :hints(("Goal" :in-theory (enable base-fsm-run)))))

  (local (defthm base-fsm-run-when-outvars-Shorter-than-inputs
           (implies (and (equal outs-len (len outvars))
                         (<= outs-len (len inputs))
                         (equal inputs2 (take outs-len inputs))
                         (syntaxp (not (case-match inputs2
                                         (('take len &) (equal len outs-len))
                                         (&  (equal inputs2 inputs))))))
                    (equal (base-fsm-run inputs prev-st fsm outvars)
                           (base-fsm-run inputs2 prev-st fsm outvars)))
           :hints(("Goal" :in-theory (enable base-fsm-run-when-outvars-Shorter-than-inputs-lemma)))))

  (local (defthmd base-fsm-run-states-when-outvars-Shorter-than-inputs-lemma
           (implies (<= (len outvars) (len inputs))
                    (equal (base-fsm-run-states inputs prev-st fsm outvars)
                           (base-fsm-run-states (take (len outvars) inputs) prev-st fsm outvars)))
           :hints(("Goal" :in-theory (enable base-fsm-run-states)))))

  (local (defthm base-fsm-run-states-when-outvars-Shorter-than-inputs
           (implies (and (equal outs-len (len outvars))
                         (<= outs-len (len inputs))
                         (equal inputs2 (take outs-len inputs))
                         (syntaxp (not (case-match inputs2
                                         (('take len &) (equal len outs-len))
                                         (&  (equal inputs2 inputs))))))
                    (equal (base-fsm-run-states inputs prev-st fsm outvars)
                           (base-fsm-run-states inputs2 prev-st fsm outvars)))
           :hints(("Goal" :in-theory (enable base-fsm-run-states-when-outvars-Shorter-than-inputs-lemma)))))

  (local (defthm len-of-take
           (equal (len (take n x)) (nfix n))))

  (local (defthm base-fsm->nextstate-of-svtv-fsm->renamed-fsm
           (equal (base-fsm->nextstate (svtv-fsm->renamed-fsm x))
                  (svtv-fsm->nextstate x))
           :hints(("Goal" :in-theory (enable svtv-fsm->renamed-fsm)))))
  
  (defretd <fn>-is-base-fsm-run-outs-and-states
    (equal <call>
           (b* (((mv outs states)
                 (base-fsm-run-outs-and-states
                  (svtv-fsm-to-base-fsm-inputs
                   (take (max (len out-signals) (len state-signals)) inputs)
                   override-vals override-tests (svtv-fsm->namemap x))
                  prev-st
                  (svtv-fsm->renamed-fsm x)
                  :out-signals out-signals
                  :state-signals state-signals)))
             (mv (take (len out-signals) outs)
                 (take (len state-signals) states))))
    :hints(("Goal" :in-theory (enable svtv-fsm-run-is-base-fsm-run
                                      base-fsm-run-outs-and-states
                                      svtv-fsm-run-states-is-base-fsm-run-states)
            :do-not-induct t))
    :otf-flg t))





(define svtv-fsm-mod-alias-guard ((top modname-p)
                                  (moddb moddb-ok) aliases)
  :enabled t
  (b* ((modidx (moddb-modname-get-index top moddb)))
    (and modidx
         (svtv-mod-alias-guard modidx moddb aliases))))


(define svtv-fsm-add-names ((names svtv-namemap-p)
                            (x svtv-fsm-p)
                            &key
                            ((top modname-p) 'nil)
                            ((moddb moddb-ok) 'moddb)
                            (aliases 'aliases))
  :guard (svtv-fsm-mod-alias-guard top moddb aliases)
  :returns (mv err
               (new-fsm (implies (not err) (svtv-fsm-p new-fsm))))
  (b* (((svtv-fsm x))
       ((mv errs lhsmap)
        (svtv-namemap->lhsmap
         names 
         (moddb-modname-get-index top moddb)
         moddb aliases))
       ((when errs)
        (mv (msg-list errs) nil)))
    (mv nil
        (change-svtv-fsm x :namemap (append lhsmap x.namemap)))))



