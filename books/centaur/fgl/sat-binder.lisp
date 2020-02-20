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

(include-book "add-primitives")
(include-book "primitives-stub")
(include-book "sat-stub")
(include-book "sat-binder-defs")

(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))

(local (std::add-default-post-define-hook :fix))


#!aignet
(define invals-to-conjunction ((n natp)
                                  (in-lit litp)
                                  (bitarr)
                                  (gatesimp gatesimp-p)
                                  (strash)
                                  (aignet))
  :returns (mv (res-lit litp :rule-classes :type-prescription)
               (new-strash)
               (new-aignet))
  :guard (and (fanin-litp in-lit aignet)
              (<= n (num-ins aignet))
              (<= (num-ins aignet) (bits-length bitarr)))
  :measure (nfix (- (num-ins aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
                   :exec (eql n (num-ins aignet))))
        (b* ((in-lit (mbe :logic (non-exec (aignet-lit-fix in-lit aignet)) :exec in-lit))
             (aignet (mbe :logic (non-exec (node-list-fix aignet)) :exec aignet)))
          (mv in-lit strash aignet)))
       ((mv and-lit strash aignet)
        (aignet-hash-and in-lit
                         (make-lit (innum->id n aignet)
                                   (b-not (get-bit n bitarr)))
                         gatesimp
                         strash
                         aignet)))
    (invals-to-conjunction (1+ (lnfix n)) and-lit bitarr gatesimp strash aignet))
  ///
  (def-aignet-preservation-thms invals-to-conjunction)

  (defret stype-count-of-<fn>
    (and (equal (stype-count :pi new-aignet)
                (stype-count :pi aignet))
         (equal (stype-count :po new-aignet)
                (stype-count :po aignet))
         (equal (stype-count :reg new-aignet)
                (stype-count :reg aignet))
         (equal (stype-count :nxst new-aignet)
                (stype-count :nxst aignet))))

  (defret aignet-litp-of-<fn>
    (aignet-litp res-lit new-aignet))

  (defret eval-of-<fn>
    (equal (lit-eval res-lit invals regvals new-aignet)
           (b-and (lit-eval in-lit invals regvals aignet)
                  (bool->bit
                   (equal (bit-list-fix (nthcdr n (take (num-ins aignet) bitarr)))
                          (bit-list-fix (nthcdr n (take (num-ins aignet) invals)))))))
    :hints (("goal" :induct <call>)
            (and stable-under-simplificationp
                 '(:expand ((:free (x y) (lit-eval (make-lit x y) invals regvals aignet))
                            (:free (x) (id-eval x invals regvals aignet))
                            (:free (x) (bit-list-fix (nthcdr n x)))))))))


#!aignet
(define regvals-to-conjunction ((n natp)
                                (in-lit litp)
                                (bitarr)
                                (gatesimp gatesimp-p)
                                (strash)
                                (aignet))
  :returns (mv (res-lit litp :rule-classes :type-prescription)
               (new-strash)
               (new-aignet))
  :guard (and (fanin-litp in-lit aignet)
              (<= n (num-regs aignet))
              (<= (num-regs aignet) (bits-length bitarr)))
  :measure (nfix (- (num-regs aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql n (num-regs aignet))))
        (b* ((in-lit (mbe :logic (non-exec (aignet-lit-fix in-lit aignet)) :exec in-lit))
             (aignet (mbe :logic (non-exec (node-list-fix aignet)) :exec aignet)))
          (mv in-lit strash aignet)))
       ((mv and-lit strash aignet)
        (aignet-hash-and in-lit
                         (make-lit (regnum->id n aignet)
                                   (b-not (get-bit n bitarr)))
                         gatesimp
                         strash
                         aignet)))
    (regvals-to-conjunction (1+ (lnfix n)) and-lit bitarr gatesimp strash aignet))
  ///
  (def-aignet-preservation-thms regvals-to-conjunction)

  (defret stype-count-of-<fn>
    (and (equal (stype-count :pi new-aignet)
                (stype-count :pi aignet))
         (equal (stype-count :po new-aignet)
                (stype-count :po aignet))
         (equal (stype-count :reg new-aignet)
                (stype-count :reg aignet))
         (equal (stype-count :nxst new-aignet)
                (stype-count :nxst aignet))))

  (defret aignet-litp-of-<fn>
    (aignet-litp res-lit new-aignet))

  ;; (local (defthm car-of-nthcdr
  ;;          (equal (car (nthcdr n x))
  ;;                 (nth n x))))

  ;; (local (Defthm nthcdr-redef
  ;;          (implies (natp n)
  ;;                   (equal (nthcdr (+ 1 n) x)
  ;;                          (cdr (nthcdr n x))))))
  ;; (local (in-theory (disable nthcdr)))

  (defret eval-of-<fn>
    (equal (lit-eval res-lit invals regvals new-aignet)
           (b-and (lit-eval in-lit invals regvals aignet)
                  (bool->bit
                   (equal (bit-list-fix (nthcdr n (take (num-regs aignet) bitarr)))
                          (bit-list-fix (nthcdr n (take (num-regs aignet) regvals)))))))
    :hints (("goal" :induct <call>)
            (and stable-under-simplificationp
                 '(:expand ((:free (x y) (lit-eval (make-lit x y) invals regvals aignet))
                            (:free (x) (id-eval x invals regvals aignet))
                            (:free (x) (bit-list-fix (nthcdr n x)))))))))



#!aignet
(local (defthm lit->var-less-when-aignet-idp
         (implies (and (aignet-idp n aignet)
                       (natp n))
                  (<= n (fanin-count aignet)))
         :hints(("Goal" :in-theory (enable aignet-idp)))))


(local (defthm bit-listp-of-update-nth
         (implies (and (aignet::bit-listp x)
                       (< (nfix n) (len x))
                       (bitp val))
                  (aignet::bit-listp (update-nth n val x)))
         :hints(("Goal" :in-theory (enable update-nth aignet::bit-listp)))))

(local (defthm bit-listp-of-alist-to-bitarr-aux
         (implies (aignet::bit-listp bitarr)
                  (aignet::bit-listp (alist-to-bitarr-aux n alist bitarr)))
         :hints(("Goal" :in-theory (enable alist-to-bitarr-aux)))))


(local (defthm bit-listp-of-repeat
         (implies (bitp bit)
                  (aignet::bit-listp (acl2::repeat max bit)))
         :hints(("Goal" :in-theory (enable acl2::repeat)))))

(local (defthm bit-listp-of-alist-to-bitarr
         (implies (aignet::bit-listp bitarr)
                  (aignet::bit-listp (alist-to-bitarr max alist bitarr)))
         :hints(("Goal" :in-theory (enable alist-to-bitarr)))))


(local
 #!aignet
 (encapsulate nil
   (local (defun-sk aignet-vals->invals-iter-norm-cond (n vals aignet)
            (forall invals
                    (implies (syntaxp (not (equal invals ''nil)))
                             (equal (aignet-vals->invals-iter n invals vals aignet)
                                    (append (take n (aignet-vals->invals-iter n nil vals aignet))
                                            (nthcdr n invals)))))
            :rewrite :direct))
   (local (in-theory (disable aignet-vals->invals-iter-norm-cond)))

   ;; (local (defthm aignet-vals->invals-iter-norm-cond-of-repeat-one-more
   
   (local (defthm update-nth-of-append-take-one-less
            (equal (update-nth n val (append (take n x) y))
                   (append (take (+ 1 (nfix n)) (update-nth n val x)) (cdr y)))
            :hints(("Goal" :in-theory (enable update-nth take)))))

   (local (defthm cdr-nthcdr-n-minus-1
            (implies (posp n)
                     (equal (cdr (nthcdr (+ -1 n) x))
                            (nthcdr n x)))
            :hints(("Goal" :in-theory (enable nthcdr)))))

   (local (defthm aignet-vals->invals-iter-norm-lemma
            (aignet-vals->invals-iter-norm-cond n vals aignet)
            :hints(("Goal" :in-theory (enable aignet-vals->invals-iter)
                    :induct (aignet-vals->invals-iter n invals vals aignet))
                   (and stable-under-simplificationp
                        `(:expand (,(car (last clause))))))))
   

   (defthmd len-of-aignet-vals->invals-iter-of-lesser
     (implies (<= (len invals) (nfix n))
              (equal (len (aignet-vals->invals-iter n invals vals aignet))
                     (nfix n))))
     ;; :hints(("Goal" :use ((:instance aignet-vals->invals-iter-norm-lemma))
     ;;         :in-theory (disable aignet-vals->invals-iter-norm-lemma
     ;;                             aignet-vals->invals-iter-norm-cond-necc))))

   (defthmd aignet-vals->invals-iter-norm
     (implies (syntaxp (not (equal invals ''nil)))
              (equal (aignet-vals->invals-iter n invals vals aignet)
                     (append (aignet-vals->invals-iter n nil vals aignet)
                             (nthcdr n invals))))
     :hints(("Goal" :in-theory (enable len-of-aignet-vals->invals-iter-of-lesser))))))


(local
 #!aignet
 (defthm true-listp-of-aignet-vals->invals-iter
   (implies (true-listp invals)
            (true-listp (aignet-vals->invals-iter n invals vals aignet)))
   :hints(("Goal" :in-theory (enable aignet-vals->invals-iter-norm)))))

(local
 #!aignet
 (defthm bit-listp-of-append
   (implies (and (bit-listp x)
                 (Bit-listp y))
            (bit-listp (append x y)))
   :hints(("Goal" :in-theory (enable bit-listp)))))

(local
 #!aignet
 (defthm bit-listp-of-update-nth
   (implies (and (bit-listp x)
                 (bitp val)
                 (<= (nfix n) (len x)))
            (bit-listp (update-nth n val x)))
   :hints(("Goal" :in-theory (enable bit-listp update-nth)))))

(local
 #!aignet
 (defthm bit-listp-of-aignet-vals->invals-iter
   (implies (bit-listp invals)
            (bit-listp (aignet-vals->invals-iter n invals vals aignet)))
   :hints(("Goal" :in-theory (enable aignet-vals->invals-iter)
           :induct (aignet-vals->invals-iter n invals vals aignet))
          (and stable-under-simplificationp
               '(:in-theory (enable aignet-vals->invals-iter-norm
                                    len-of-aignet-vals->invals-iter-of-lesser))))))



(local (defthm nthcdr-when-len-greater-or-equal-and-true-listp
         (implies (and (<= (len x) (nfix n))
                       (true-listp x))
                  (equal (nthcdr n x) nil))))

#!aignet
(defthm aignet-vals->invals-norm
  (implies (and (syntaxp (not (equal invals ''nil)))
                (<= (len invals) (num-ins aignet))
                (true-listp invals))
           (equal (aignet-vals->invals invals vals aignet)
                  (aignet-vals->invals nil vals aignet)))
  :hints(("Goal" :in-theory (enable aignet-vals->invals
                                    aignet-vals->invals-iter-norm)
          :do-not-induct t)))

#!aignet
(defthm bit-listp-of-aignet-vals->invals
  (implies (bit-listp invals)
           (bit-listp (aignet-vals->invals invals vals aignet)))
  :hints(("Goal" :in-theory (enable aignet-vals->invals))))

#!aignet
(defthmd len-of-aignet-vals->invals-when-lesser
  (implies (and (<= (len invals) (num-ins aignet))
                (true-listp invals))
           (equal (len (aignet-vals->invals invals vals aignet))
                  (num-ins aignet)))
  :hints(("Goal" :in-theory (enable aignet-vals->invals
                                    len-of-aignet-vals->invals-iter-of-lesser)
          :do-not-induct t)))

(define bfr-env$-to-conjunction (env$ logicman)
  :guard (and (bfr-env$-p env$ (logicman->bfrstate))
              (bfrstate-mode-is :aignet (logicman->bfrstate)))
  :guard-hints (("goal" :in-theory (enable bfr-env$-p
                                           aignet::len-of-aignet-vals->invals-when-lesser)))
  :returns (mv (ans)
               (new-logicman))
  (stobj-let ((bitarr (env$->bitarr env$)))
             (bfr logicman)
             (stobj-let ((aignet (logicman->aignet logicman))
                         (strash (logicman->strash logicman)))
                        (conj strash aignet)
                        (b* (((acl2::local-stobjs aignet::invals aignet::regvals)
                              (mv conj strash aignet aignet::invals aignet::regvals))
                             (aignet::invals (resize-bits (aignet::num-ins aignet) aignet::invals))
                             (aignet::regvals (resize-bits (aignet::num-regs aignet) aignet::regvals))
                             (aignet::invals (aignet::aignet-vals->invals aignet::invals bitarr aignet))
                             (aignet::regvals (aignet::aignet-vals->regvals aignet::regvals bitarr aignet))
                             ((mv conj strash aignet)
                              (aignet::invals-to-conjunction
                               0 1 aignet::invals
                               (aignet::default-gatesimp) strash aignet))
                             ((mv conj strash aignet)
                              (aignet::regvals-to-conjunction
                               0 conj aignet::regvals
                               (aignet::default-gatesimp) strash aignet)))
                          (mv conj strash aignet aignet::invals aignet::regvals))
                        (b* ((bfrstate (logicman->bfrstate)))
                          (mv (aignet-lit->bfr conj) logicman)))
             (mv bfr logicman))
  ///
  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars new-logicman)
           (bfr-nvars logicman)))

  (defret logicman-get-of-<fn>
    (implies (and (not (equal (logicman-field-fix key) :strash))
                  (not (equal (logicman-field-fix key) :aignet)))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  (defret logicman-invar-of-<fn>
    (implies (logicman-invar logicman)
             (logicman-invar new-logicman))
    :hints(("Goal" :in-theory (enable logicman-invar))
           (and stable-under-simplificationp
                (let ((lit (car (last clause))))
                  (cond ((eq (car lit) 'logicman-ipasir-sat-lits-invar)
                         `(:expand (,lit)))
                        (t nil))))))

  ;; (defret bfrstate-of-<fn>
  ;;   (equal (logicman->bfrstate new-logicman)
  ;;          (logicman->bfrstate logicman)))

  (local (defstub foo (x) x))
  (defret eval-of-<fn>
    (implies (and (logicman-invar logicman)
                  (bfrstate-mode-is :aignet (logicman->bfrstate)))
             (equal (bfr-eval ans eval-env new-logicman)
                    (aignet::bit-list-equiv
                     (alist-to-bitarr (aignet::stype-count :pi (logicman->aignet logicman))
                                      eval-env nil)
                     (aignet::aignet-vals->invals nil (env$->bitarr env$) (logicman->aignet logicman)))))
    :hints(("Goal" :in-theory (enable bfr-eval
                                      aignet::len-of-aignet-vals->invals-when-lesser)
            :do-not-induct t))
    :otf-flg t)

  (defret bfr-p-of-<fn>
    (implies (and (logicman-invar logicman)
                  (bfrstate-mode-is :aignet (logicman->bfrstate)))
             (lbfr-p ans new-logicman))))




(def-formula-checks sat-formula-checks
  (sat-check-raw sat-check-with-witness-raw))


(local (include-book "primitive-lemmas"))      

(local (in-theory (disable w)))

(local (in-theory (disable fgl-ev-context-equiv-forall-extensions)))

(local (defthm fgl-ev-context-equv-forall-extensions-trivial
         (implies (acl2::rewriting-negative-literal
                   `(fgl-ev-context-equiv-forall-extensions ,contexts ,obj ,term ,eval-alist))
                  (iff (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)
                       (and 
                        (equal (fgl-ev-context-fix contexts (fgl-ev term eval-alist))
                               (fgl-ev-context-fix contexts obj))
                        (hide (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)))))
         :hints (("goal" :expand ((:free (x) (hide x)))
                  :use ((:instance fgl-ev-context-equiv-forall-extensions-necc
                         (ext eval-alist)))
                  :in-theory (disable fgl-ev-context-equiv-forall-extensions-necc)))))




(def-fgl-binder-meta sat-check-raw-binder
  (if (and (eq (pseudo-fnsym-fix fn) 'sat-check-raw)
           (eql (len args) 2))
      (b* (((list config x) args)
           ((unless (fgl-object-case config :g-concrete))
            (fgl-interp-error
             :msg (msg "~x0 called on non-concrete config object: ~x1" 'sat-check-raw
                       (fgl-object-fix config))
             :nvals 4))
           ((mv ok xbool) (gobj-syntactic-boolean-fix x))
           ((unless ok)
            (fgl-interp-error
             :msg (msg "~x0 called on object not yet converted to Boolean formula: ~x1"
                       'sat-check-raw (fgl-object-fix x))
             :nvals 4))
           ((mv ans interp-st state)
            (interp-st-sat-check (g-concrete->val config) (gobj-syntactic-boolean->bool xbool)
                                 interp-st state)))
        (mv t 'x
            (case ans
              (:sat '((x . :sat)))
              (:unsat '((x . :unsat)))
              (t '((x . :failed))))
            nil interp-st state))
    (mv nil nil nil nil interp-st state))
  :prepwork ((local (in-theory (enable sat-check-raw)))
             (local (defret fgl-object-eval-when-gobj-syntactic-boolean-fix
                      (implies okp
                               (iff (fgl-object-eval x env)
                                    (gobj-bfr-eval (gobj-syntactic-boolean->bool new-x) env)))
                      :fn gobj-syntactic-boolean-fix))
             (local (in-theory (disable fgl-object-eval-of-gobj-syntactic-boolean-fix))))
  :formula-check sat-formula-checks)

(add-fgl-binder-meta sat-check-raw sat-check-raw-binder)



(local (defthmd mv-nth-when-equal-cons
         (implies (and (syntaxp (quotep n))
                       (equal x (cons a b)))
                  (equal (mv-nth n x)
                         (if (zp n)
                             a
                           (mv-nth (1- n) b))))
         :hints(("Goal" :in-theory (enable mv-nth)))))

(def-fgl-binder-meta sat-check-with-witness-raw-binder
  (if (and (eq (pseudo-fnsym-fix fn) 'sat-check-with-witness-raw)
           (eql (len args) 2))
      (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
            (fgl-interp-error
             :msg (msg "~x0 only works in aignet mode" 'sat-check-with-witness-raw)
             :nvals 4))
           ((list config x) args)
           ((unless (fgl-object-case config :g-concrete))
            (fgl-interp-error
             :msg (msg "~x0 called on non-concrete config object: ~x1" 'sat-check-with-witness-raw
                       (fgl-object-fix config))
             :nvals 4))
           ((mv ok xbool) (gobj-syntactic-boolean-fix x))
           ((unless ok)
            (fgl-interp-error
             :msg (msg "~x0 called on object not yet converted to Boolean formula: ~x1"
                       'sat-check-with-witness-raw (fgl-object-fix x))
             :nvals 4))
           (config (g-concrete->val config))
           (bfr (gobj-syntactic-boolean->bool xbool))
           ((mv ans interp-st state)
            (interp-st-sat-check config bfr interp-st state))
           ((unless (eq ans :sat))
            (mv t 'x
                (case ans
                  (:unsat '((x . (:unsat nil))))
                  (t '((x . (:failed nil)))))
                nil interp-st state))
           ((mv err interp-st) (interp-st-sat-counterexample config interp-st state))
           ((when err)
            (fgl-interp-error
             :msg (msg "Error retrieving SAT witness: ~@0" err)
             :nvals 4))
           ((mv err ans interp-st)
            (stobj-let ((env$ (interp-st->ctrex-env interp-st))
                        (logicman (interp-st->logicman interp-st)))
                       (err ans logicman)
                       (b* ((bfrstate (logicman->bfrstate))
                            (ok (stobj-let ((bitarr (env$->bitarr env$)))
                                           (ok)
                                           (eql 1 (aignet::aignet-eval-lit
                                                   (bfr->aignet-lit bfr)
                                                   bitarr))
                                           ok))
                            ((unless ok)
                             (mv "Malformed SAT witness: the formula wasn't satisfied"
                                 nil logicman))
                            ((mv ans logicman)
                             (bfr-env$-to-conjunction env$ logicman)))
                         (mv nil ans logicman))
                       (mv err ans interp-st)))
           ((when err)
            (fgl-interp-error :msg err :nvals 4)))
        (mv t 'x `((x . ,(g-cons :sat (g-cons (mk-g-boolean ans) nil))))
            nil interp-st state))
    (mv nil nil nil nil interp-st state))
  :prepwork ((local (defret fgl-object-eval-when-gobj-syntactic-boolean-fix
                      (implies okp
                               (iff (fgl-object-eval x env)
                                    (gobj-bfr-eval (gobj-syntactic-boolean->bool new-x) env)))
                      :fn gobj-syntactic-boolean-fix))
             (local (in-theory (disable fgl-object-eval-of-gobj-syntactic-boolean-fix)))

             (local (defthm bfr-env$-p-of-interp-st-sat-counterexample-rw
                      (b* (((mv err new-interp-st) (interp-st-sat-counterexample params interp-st state)))
                        (implies (and (not err)
                                      (equal bfrstate (logicman->bfrstate (interp-st->logicman interp-st))))
                                 (bfr-env$-p (interp-st->ctrex-env new-interp-st) bfrstate)))))

             (local (defthm len-of-interp-st-sat-counterexample
                      (b* ((env$ (interp-st->ctrex-env interp-st)))
                        (implies (and (bfr-env$-p env$ (logicman->bfrstate (interp-st->logicman interp-st)))
                                      (bfr-mode-is :aignet (interp-st-bfr-mode interp-st)))
                                 (< (bfrstate->bound 
                                     (logicman->bfrstate (interp-st->logicman interp-st)))
                                    (len (env$->bitarr env$)))))
                      :hints(("Goal" :in-theory (enable bfr-env$-p)))
                      :rule-classes :linear))

             ;; (local (def-updater-independence-thm logicman-pathcond-eval-checkpoints!-of-logicman-extension2
             ;;          (implies (and (logicman-extension-p new old)
             ;;                        (logicman-pathcond-p pathcond (double-rewrite old)))
             ;;                   (equal (logicman-pathcond-eval-checkpoints! env pathcond new)
             ;;                          (logicman-pathcond-eval-checkpoints! env pathcond old)))))
             ;; (local (def-updater-independence-thm logicman-pathcond-eval-of-logicman-extension2
             ;;          (implies (and (logicman-extension-p new old)
             ;;                        (logicman-pathcond-p pathcond (double-rewrite old)))
             ;;                   (equal (logicman-pathcond-eval env pathcond new)
             ;;                          (logicman-pathcond-eval env pathcond old)))))
             (local (defthm bfrstate-of-interp-st-sat-check
                      (equal (logicman->bfrstate
                              (interp-st->logicman
                               (mv-nth 1 (interp-st-sat-check config bfr interp-st state))))
                             (logicman->bfrstate (interp-st->logicman interp-st)))))
             (local (include-book "tools/trivial-ancestors-check" :dir :system))
             (local (defthm mv-nth-of-equal-list
                      (implies (and (syntaxp (atom x))
                                    (equal x (cons a b)))
                               (equal (mv-nth n x)
                                      (mv-nth n (cons a b))))))
             (local (defthm bit-equiv-congruence-on-equal-1
                      (implies (acl2::bit-equiv x y)
                               (equal (equal 1 x) (equal 1 y)))
                      :rule-classes :congruence))
             (local (acl2::use-trivial-ancestors-check))

             (local (in-theory (enable gobj-bfr-eval ;; bfr-eval ;; aignet::lit-eval
                                       )))

             (local
              (defthm nth-of-of-interp-st-sat-counterexample
                (b* (((mv err new-interp-st) (interp-st-sat-counterexample params interp-st state))
                     (aignet  (logicman->aignet (interp-st->logicman interp-st)))
                     (vals  (env$->bitarr (interp-st->ctrex-env new-interp-st))))
                  (implies (and (not err)
                                (bfr-mode-is :aignet (interp-st-bfr-mode))
                                (aignet::aignet-idp n aignet)
                                (equal 0 (aignet::num-regs aignet)))
                           (acl2::bit-equiv (nth n vals)
                                            (aignet::id-eval
                                             n
                                             (aignet::aignet-vals->invals nil vals aignet)
                                             nil aignet))))
                :hints (("goal" :use aignet-vals-p-of-interp-st-sat-counterexample
                         :in-theory (e/d (aignet::nth-when-aignet-vals-p
                                          aignet::aignet-vals->regvals
                                          aignet::aignet-vals->regvals-iter)
                                         (aignet-vals-p-of-interp-st-sat-counterexample))))))

             (local
              #!aignet
              (defthm id-eval-of-lit->var
                (equal (id-eval (lit->var lit) invals regvals aignet)
                       (b-xor (lit->neg lit)
                              (lit-eval lit invals regvals aignet)))
                :hints(("Goal" :in-theory (enable lit-eval)))))

             (local (in-theory (disable member-equal)))

             (local (defthmd sat-check-with-witness-raw-fixes
                      (and (equal (sat-check-with-witness-raw '(:failed nil) config x) '(:failed nil))
                           (implies (not x)
                                    (equal (sat-check-with-witness-raw '(:unsat nil) config x)
                                           '(:unsat nil)))
                           (implies (and (equal rhs  (list :sat ctrex))
                                         (case-split (implies ctrex x)))
                                    (equal (sat-check-with-witness-raw rhs config x) rhs))
                           (implies (case-split (implies ctrex x))
                                    (equal (sat-check-with-witness-raw (list :sat ctrex) config x)
                                           (list :sat ctrex))))
                      :hints(("Goal" :in-theory (enable sat-check-with-witness-raw)))))

             (defcong iff equal (sat-check-with-witness-raw ans config x) 3
               :hints(("Goal" :in-theory (enable sat-check-with-witness-raw))))
             (local (set-default-hints
                     '((and stable-under-simplificationp
                            '(:in-theory (enable sat-check-with-witness-raw-fixes
                                                 bfr-eval
                                                 w-state-equal-forward)))))))
  :formula-check sat-formula-checks)

(add-fgl-binder-meta sat-check-with-witness-raw sat-check-with-witness-raw-binder)








