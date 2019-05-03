; GLMC -- Hardware model checking interface
; Copyright (C) 2017 Centaur Technology
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

(in-package "GL")

(include-book "bfr-mcheck")
(include-book "centaur/aignet/from-hons-aig" :dir :system)
(include-book "centaur/aignet/aiger" :dir :system)
(include-book "centaur/aignet/prune" :dir :system)
(include-book "centaur/aignet/abc" :dir :system)
(include-book "centaur/aignet/eval" :dir :system)
(include-book "centaur/aignet/transform-utils" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))

;; Attachable function to set the ABC script to run.
(encapsulate
  (((gl-abc-mcheck-script * *) => *
    :formals (input-fname ctrex-fname)
    :guard (and (stringp input-fname)
                (stringp ctrex-fname))))
  (local (defun gl-abc-mcheck-script (input-fname ctrex-fname)
           (declare (xargs :guard (and (stringp input-fname)
                                       (stringp ctrex-fname)))
                    (ignore input-fname ctrex-fname))
           ""))

  (defthm stringp-of-gl-abc-mcheck-script
    (stringp (gl-abc-mcheck-script input-fname ctrex-fname))
    :rule-classes :type-prescription))

(define gl-abc-mcheck-script-default ((input-fname stringp) (ctrex-fname stringp))
  :returns (script stringp :rule-classes :type-prescription)
  (concatenate 'string
               "&r " input-fname "
                &put
                dprove
                print_status
                write_cex " ctrex-fname))

(defattach gl-abc-mcheck-script gl-abc-mcheck-script-default)




(acl2::defstobj-clone aignet2 aignet::aignet :suffix "2")
(acl2::defstobj-clone initsts aignet::initsts :pkg GL::|GL::GL| :strsubst (("___" . "")))
(acl2::defstobj-clone bitarr acl2::bitarr :pkg GL::|GL::GL| :strsubst (("___" . "")))
(acl2::defstobj-clone frames aignet::frames :pkg GL::|GL::GL| :strsubst (("___" . "")))

(define aig-env-to-bitarr ((n natp) vars env bitarr)
  :guard (<= (+ n (len vars)) (bits-length bitarr))
  :returns (new-bitarr)
  (b* (((when (atom vars)) bitarr)
       (val (acl2::bool->bit (acl2::aig-env-lookup (car vars) env)))
       (bitarr (set-bit n val bitarr)))
    (aig-env-to-bitarr (1+ (lnfix n)) (cdr vars) env bitarr))
  ///
  (std::defret nth-of-aig-env-to-bitarr
    (equal (nth k new-bitarr)
           (if (and (< (nfix k) (+ (nfix n) (len vars)))
                    (<= (nfix n) (nfix k)))
               (acl2::bool->bit (acl2::aig-env-lookup (nth (- (nfix k) (nfix n)) vars) env))
              (nth k bitarr))))

  (std::defret len-of-aig-env-to-bitarr
    (<= (len bitarr) (len new-bitarr))
    :rule-classes :linear)

  (local (defthmd pairlis$-of-take
           (implies (equal (len x) (nfix n))
                    (equal (pairlis$ x (take n y))
                           (pairlis$ x y)))
           :hints(("Goal" :in-theory (enable pairlis$)))))

  (local (defun-nx aignet-bitarr-to-aig-env-of-aig-env-to-bitarr-ind (n vars vars1 env bitarr)
           (if (atom vars)
               (list n vars1)
             (aignet-bitarr-to-aig-env-of-aig-env-to-bitarr-ind (1+ (nfix n)) (cdr vars)
                                                                (append vars1 (list (car vars)))
                                                                env
                                                                (set-bit n (acl2::bool->bit (acl2::aig-env-lookup (car vars) env)) bitarr)))))

  (local (defthm pairlis$-of-append
           (equal (pairlis$ (append a b) c)
                  (append (pairlis$ a (take (len a) c))
                          (pairlis$ b (nthcdr (len a) c))))
           :hints(("Goal" :in-theory (enable pairlis$ append nthcdr)
                   :induct (pairlis$ a c)))))

  (local (include-book "std/lists/update-nth" :dir :system))
  (local (include-book "std/lists/nth" :dir :system))

  (local (in-theory (disable acl2::aig-env-lookup)))

  (local (defthm bits-to-bools-of-update-nth
           (equal (aignet::bits-to-bools (update-nth n v x))
                  (update-nth n (equal v 1) (aignet::bits-to-bools x)))
           :hints(("Goal" :in-theory (e/d (aignet::bits-to-bools default-cdr)
                                          (acl2::update-nth-when-atom
                                           acl2::update-nth-when-zp
                                           (aignet::bits-to-bools)))))))

  (local (std::defret aignet-bitarr-to-aig-env-of-aig-env-to-bitarr-gen
           (implies (equal (len vars1) (nfix n))
                    (equal (aignet::aignet-bitarr-to-aig-env (append vars1 vars) (aig-env-to-bitarr n vars env bitarr))
                           (append (pairlis$ vars1 (take n (aignet::bits-to-bools bitarr)))
                                   (acl2::aig-env-extract vars env))))
           :hints(("Goal" :in-theory (e/d* (aignet::aignet-bitarr-to-aig-env
                                            pairlis$ aignet::bits-to-bools
                                            acl2::aig-env-extract
                                            acl2::arith-equiv-forwarding)
                                           (acl2::take-of-cons
                                            acl2::take-of-too-many
                                            acl2::take-of-zero
                                            acl2::car-of-take
                                            acl2::take))
                   :induct (aignet-bitarr-to-aig-env-of-aig-env-to-bitarr-ind n vars vars1 env bitarr)
                   :expand ((aig-env-to-bitarr n vars env bitarr)))
                  (and stable-under-simplificationp
                       '(:in-theory (enable pairlis$-of-take))))))

  (std::defret aignet-bitarr-to-aig-env-of-aig-env-to-bitarr
    (equal (aignet::aignet-bitarr-to-aig-env vars (aig-env-to-bitarr 0 vars env bitarr))
           (acl2::aig-env-extract vars env))
    :hints (("goal" :use ((:instance aignet-bitarr-to-aig-env-of-aig-env-to-bitarr-gen
                           (vars1 nil) (n 0)))
             :in-theory (disable aignet-bitarr-to-aig-env-of-aig-env-to-bitarr-gen)))))

(local (defthm aig-var-listp-of-keys-when-bfr-updates-p
         (implies (and (bfr-updates-p x)
                       (bfr-mode))
                  (acl2::aig-var-listp (alist-keys x)))
         :hints(("Goal" :in-theory (enable bfr-updates-p alist-keys acl2::aig-var-listp bfr-varname-p)))))


(local (include-book "std/lists/resize-list" :dir :system))

(defthm aig-env-extract-of-aig-env-extract
  (implies (subsetp vars vars1)
           (equal (acl2::aig-env-extract vars (acl2::aig-env-extract vars1 x))
                  (acl2::aig-env-extract vars x)))
  :hints(("Goal" :in-theory (enable (:i acl2::aig-env-extract))
          :induct (acl2::aig-env-extract vars x)
          :expand ((:free (x) (acl2::aig-env-extract vars x))))))

(defthm aig-fsm-frame-env-of-aig-env-extract
  (equal (aignet::aig-fsm-frame-env updates (acl2::aig-env-extract (alist-keys updates) initst) in)
         (aignet::aig-fsm-frame-env updates initst in))
  :hints(("Goal" :in-theory (enable aignet::aig-fsm-frame-env))))


(defthm aig-fsm-states-of-aig-env-extract
  (equal (aignet::aig-fsm-states regs (acl2::aig-env-extract (alist-keys regs) curr-st) ins)
         (aignet::aig-fsm-states regs curr-st ins))
  :hints (("goal" :expand ((:free (curr-st) (aignet::aig-fsm-states regs curr-st ins)))
           :in-theory (enable aignet::aig-fsm-frame-nextst))))



(define aig-mcheck-to-aignet (prop
                              (updates bfr-updates-p)
                              init-st
                              aignet)
  :guard (bfr-mode) ;; AIG
  :returns (mv new-aignet invars)
  (b* (((acl2::local-stobjs aignet2 initsts)
        (mv aignet invars aignet2 initsts))
       ((mv aignet2 ?varmap invars regvars)
        (aignet::aig-fsm-to-aignet updates (list prop) 1000
                                   (aignet::make-gatesimp :hashp t :level 4)
                                   aignet2))
       (initsts (acl2::resize-bits (len regvars) initsts))
       (initsts (aig-env-to-bitarr 0 regvars init-st initsts))
       (aignet (aignet::aignet-copy-init aignet2 initsts :gatesimp (aignet::make-gatesimp :hashp nil :level 0)
                                         :aignet2 aignet)))
    ;; (aignet::aignet-print aignet)
    (mv aignet invars aignet2 initsts))
  ///
  (std::defret aig-mcheck-to-aignet-correct
    (implies (and (bfr-updates-p updates)
                  (bfr-mode)
                  (no-duplicatesp (alist-keys updates))
                  (< (nfix k) (len (stobjs::2darr->rows frames))))
             (equal (aignet::output-eval-seq k 0 frames nil new-aignet)
                    (acl2::bool->bit (nth 0 (nth k (aignet::aig-fsm-run
                                                    (list prop) updates init-st
                                                    (aignet::aignet-frames-to-aig-envs
                                                     frames invars)))))))
    :hints (("goal" :do-not-induct t
             :in-theory (e/d (aignet::output-eval-seq) (nth)))))

  (std::defret num-outs-of-aig-mcheck-to-aignet
    (equal (aignet::stype-count :po new-aignet) 1))

  (std::defret len-of-aig-mcheck-to-aignet-invars
    (equal (len invars)
           (aignet::num-ins new-aignet)))

  (std::defret type-of-aig-mcheck-to-aignet-invars
    (true-listp invars)
    :rule-classes :type-prescription)

  (local (defthm aig-vars-of-append-list
           (acl2::set-equiv (acl2::aiglist-vars (append a b))
                            (append (acl2::aiglist-vars a) (acl2::aiglist-vars b)))))

  (std::defret prop-vars-covered-of-aig-mcheck-to-aignet
    (subsetp (acl2::aig-vars prop) (append (alist-keys updates) invars))
    :hints (("goal" :expand ((:free (x) (acl2::aiglist-vars (list x)))))
            (acl2::set-reasoning)))

  (std::defret updates-vars-covered-of-aig-mcheck-to-aignet
    (subsetp (acl2::aiglist-vars (alist-vals updates)) (append (alist-keys updates) invars))
    :hints (("goal" :expand ((:free (x) (acl2::aiglist-vars (list x)))))
            (acl2::set-reasoning))))




(defthm bfr-updates-p-of-fast-alist-clean
  (implies (bfr-updates-p x)
           (bfr-updates-p (fast-alist-clean x)))
  :hints(("Goal" :in-theory (enable bfr-updates-p fast-alist-clean))))

(defun-sk aig-fsm-run-prop-ok (prop updates init-st ins)
  (forall n
          (implies (< (nfix n) (len ins))
                   (equal (nth 0 (nth n (aignet::aig-fsm-run (list prop)
                                                             (fast-alist-clean (bfr-updates-fix updates))
                                                             init-st ins)))
                          t)))
  :rewrite :direct)

(in-theory (disable aig-fsm-run-prop-ok-necc
                    aig-fsm-run-prop-ok))


#!aignet
(define aignet-check-ctrex (aignet frames)
  :guard (and (equal 1 (num-outs aignet))
              (<= (num-ins aignet) (frames-ncols frames)))
  :returns (out-bit bitp :rule-classes :type-prescription)
  (b* (((acl2::local-stobjs vals initsts)
        (mv ans vals initsts))
       (initsts (resize-bits (num-regs aignet) initsts))
       (vals (aignet-sim-frames vals frames initsts aignet))
       (out-fanin (outnum->fanin 0 aignet)))
    (mv (aignet-eval-lit out-fanin vals) vals initsts)))

(define abc-mcheck-simple (prop (updates bfr-updates-p) init-st)
  :returns (mv result ctrex)
  (bfr-case
    :bdd (prog2$ (er hard? 'bfr-mcheck-abc
                     "ABC model checking not supported in BDD mode")
                 (mv :failed nil))
    :aig (b* (((acl2::local-stobjs aignet aignet2 frames)
               (mv result ctrex aignet aignet2 frames))
              (updates (fast-alist-clean (bfr-updates-fix updates)))
              ((mv aignet in-vars) (aig-mcheck-to-aignet (bfr-not prop) updates init-st aignet))
              (- (aignet::print-aignet-stats "Abc-mcheck-simple initial aignet" aignet))
              (aignet2 (aignet::aignet-prune-seq aignet (aignet::make-gatesimp :hashp t :level 4) aignet2))
              (- (aignet::print-aignet-stats "Abc-mcheck-simple pruned aignet" aignet2))
              ((mv status ?aignet frames)
               (aignet::aignet-abc aignet2 aignet frames
                                   (gl-abc-mcheck-script "gl-abc-input.aig" "gl-abc-ctrex")
                                   :script-filename "gl-abc-script"
                                   :input-filename "gl-abc-input.aig"
                                   :ctrex-filename "gl-abc-ctrex"
                                   :force-status t
                                   :axiom :seq-prove))
              ((unless (eq status :refuted))
               (mv status nil aignet aignet2 frames))
              (- (if (equal 0 (aignet::aignet-check-ctrex aignet2 frames))
                     (std::raise
                      "Error: Counterexample from ABC was not confirmed on aignet~%")
                   (cw "Counterexample from ABC confirmed on aignet~%")))
              (ctrex-inputs (aignet::aignet-frames-to-aig-envs frames in-vars)))
           (mv :refuted ctrex-inputs aignet aignet2 frames)))
  ///
  (local (defthm len-of-aig-fsm-run
           (equal (len (aignet::aig-fsm-run outputs updates init-st ins))
                  (len ins))
           :hints(("Goal" :in-theory (enable aignet::aig-fsm-run)))))

  (local
   (encapsulate nil
     (local (include-book "std/lists/nth" :dir :system))
     (defthm booleanp-outputs-of-aig-fsm-run
       (booleanp (nth n (nth m (aignet::aig-fsm-run outputs updates init-st ins))))
       :hints (("goal" :cases ((< (nfix m) (len ins)))
                :do-not-induct t))
       :rule-classes :type-prescription)))

  (local (in-theory (disable fast-alist-clean)))

  (local (defthm no-duplicatesp-alist-keys-of-fast-alist-fork
           (implies (no-duplicatesp (alist-keys y))
                    (no-duplicatesp (alist-keys (fast-alist-fork x y))))
           :hints(("Goal" :in-theory (enable alist-keys fast-alist-fork)))))

  (local (defthm no-duplicatesp-of-cdr-last
           (no-duplicatesp (alist-keys (cdr (last x))))))

  (local (defthm no-duplicatesp-alist-keys-of-fast-alist-clean
           (no-duplicatesp (alist-keys (fast-alist-clean x)))
           :hints(("Goal" :in-theory (enable alist-keys fast-alist-clean)))))

  (local (defthm aig-fsm-run-of-negate-prop
           (implies (and (bfr-mode)
                         (< (nfix k) (len ins)))
                    (equal (nth 0 (nth k (aignet::aig-fsm-run (list (bfr-not prop))
                                                              updates init-st ins)))
                           (not (nth 0 (nth k (aignet::aig-fsm-run (list prop)
                                                                   updates init-st ins))))))
           :hints(("Goal" :in-theory (enable bfr-not nth)
                   :induct (nth k ins)
                   :expand ((:free (prrops) (aignet::aig-fsm-run prop updates init-st ins)))))))

  (local
   #!aignet
   (defthm rewrite-to-output-eval-seq
     (implies (< (nfix n) (num-outs aignet))
              (equal (lit-eval-seq k (fanin :co (lookup-stype n :po aignet))
                                   frames
                                   initsts
                                   aignet)
                     (output-eval-seq k n frames initsts aignet)))
     :hints(("Goal" :in-theory (enable output-eval-seq)))))

  (local (Defthm aiglist-vars-of-singleton
           (equal (acl2::aiglist-vars (list x))
                  (acl2::aig-vars x))
           :hints(("Goal" :in-theory (enable acl2::aiglist-vars)))))

  (std::defret aig-fsm-run-when-abc-mcheck-simple
    (implies (and (equal result :proved)
                  (< (nfix k) (len ins))
                  ;; (bfr-updates-p updates)
                  ;; (no-duplicatesp (alist-keys updates))
                  )
             (equal (nth 0 (nth k (aignet::aig-fsm-run (list prop)
                                                       (fast-alist-clean (bfr-updates-fix updates))
                                                       init-st ins)))
                    t))
    :hints(("Goal" :use ((:instance aignet::aignet-abc-seq-prove-correct
                          (input-aignet (aignet::aignet-prune-seq
                                         (mv-nth 0 (aig-mcheck-to-aignet (bfr-not prop) (fast-alist-clean (bfr-updates-fix updates)) init-st nil))
                                         (aignet::make-gatesimp :hashp t :level 4) aignet2))
                          (output-aignet nil)
                          (frames '(0))
                          (script (gl-abc-mcheck-script "gl-abc-input.aig" "gl-abc-ctrex"))
                          (script-filename "gl-abc-script")
                          (input-filename "gl-abc-input.aig")
                          (ctrex-filename "gl-abc-ctrex")
                          (output-filename nil)
                          (force-status t)
                          (quiet nil)
                          (k k)
                          (n 0)
                          (inframes
                           (b* ((vars (mv-nth 1 (aig-mcheck-to-aignet (bfr-not prop) (fast-alist-clean (bfr-updates-fix updates)) init-st nil))))
                             (stobjs::2darr (len vars)
                                            (aignet::envs-to-bitarrs vars ins))))))
            :in-theory (disable aignet::aignet-abc-seq-prove-correct nth-0-cons nth
                                aignet::nth-of-aig-fsm-run
                                aignet::aig-fsm-run-in-terms-of-aig-eval)
            :expand ((:free (prop) (nth 0 (list prop))))))))


(local (include-book "std/alists/fast-alist-clean" :dir :system))
(local (in-theory (disable fast-alist-clean)))

(defsection  aig-fsm-run-prop-ok-when-abc-mcheck-simple

  (local (defthm aig-fsm-frame-env-is-bfr-mc-env
           (implies (bfr-mode)
                    (bfr-env-equiv (aignet::aig-fsm-frame-env updates curr-st in)
                                   (bfr-mc-env updates curr-st in)))
           :hints(("Goal" :in-theory (enable bfr-env-equiv bfr-lookup)))))

  (local (defthm aig-eval-of-aig-fsm-frame-env
           (implies (bfr-mode)
                    (equal (acl2::aig-eval x (aignet::aig-fsm-frame-env updates curr-st in))
                           (acl2::aig-eval x (bfr-mc-env updates curr-st in))))
           :hints (("goal" :use ((:instance aig-eval-when-bfr-env-equiv
                                  (a (aignet::aig-fsm-frame-env updates curr-st in))
                                  (b (bfr-mc-env updates curr-st in))))))))

  (local (defthm set-equiv-of-bfr-updates->states-of-fast-alist-clean
           (acl2::set-equiv (bfr-updates->states (fast-alist-clean updates))
                            (bfr-updates->states updates))
           :hints(("Goal" :in-theory (enable acl2::set-unequal-witness-rw)))))

  (local (defthm aig-eval-of-bfr-mc-env-of-fast-alist-clean
           (implies (bfr-mode)
                    (equal (acl2::aig-eval x (bfr-env-override (bfr-updates->states (fast-alist-clean updates)) curr-st in))
                           (acl2::aig-eval x (bfr-mc-env updates curr-st in))))
           :hints (("goal" :use ((:instance aig-eval-when-bfr-env-equiv
                                  (a (bfr-mc-env (fast-alist-clean updates) curr-st in))
                                  (b (bfr-mc-env updates curr-st in))))))))

  (local (defthm hons-assoc-equal-of-bfr-eval-updates
           (implies (bfr-mode)
                    (equal (hons-assoc-equal v (bfr-eval-updates updates env))
                           (and (bfr-varname-p v)
                                (hons-assoc-equal v updates)
                                (cons v (bfr-eval (cdr (hons-assoc-equal v updates)) env)))))
           :hints(("Goal" :in-theory (enable bfr-eval-updates bfr-set-var)))))

  (local (defthm aig-eval-alist-is-bfr-eval-updates
           (implies (bfr-mode)
                    (bfr-env-equiv (acl2::aig-eval-alist alist env)
                                   (bfr-eval-updates alist env)))
           :hints(("Goal" :in-theory (enable bfr-env-equiv bfr-lookup bfr-eval)))))

  (local (defthmd aig-env-extract-when-bfr-env-equiv
           (implies (and (bfr-mode)
                         (bfr-env-equiv a b)
                         (acl2::aig-var-listp keys))
                    (equal (equal (acl2::aig-env-extract keys a) (acl2::aig-env-extract keys b)) t))
           :hints(("Goal" :in-theory (e/d (acl2::aig-env-extract
                                           acl2::aig-var-listp)
                                          (acl2::aig-env-lookup))
                   :induct t)
                  (and stable-under-simplificationp
                       '(:use ((:instance bfr-env-equiv-necc
                                (v (car keys))
                                (x a) (y b)))
                         :in-theory (e/d (bfr-lookup bfr-varname-p) ()))))))

  (local (defthmd aig-fsm-frame-env-when-bfr-env-equiv
           (implies (and (bfr-mode)
                         (bfr-env-equiv a b)
                         (bfr-updates-p regs))
                    (equal (aignet::aig-fsm-frame-env regs a ins) (aignet::aig-fsm-frame-env regs b ins)))
           :hints (("goal" :in-theory (enable aignet::aig-fsm-frame-env)
                    :use ((:instance aig-env-extract-when-bfr-env-equiv
                           (keys (alist-keys regs))))))))

  (local (defthmd aig-fsm-run-when-bfr-env-equiv
           (implies (and (bfr-mode)
                         (bfr-env-equiv a b)
                         (bfr-updates-p regs))
                    (equal (aignet::aig-fsm-run outs regs a ins) (aignet::aig-fsm-run outs regs b ins)))
           :hints (("goal" :expand ((:free (curr-st) (aignet::aig-fsm-run outs regs curr-st ins)))
                    :use ((:instance aig-fsm-frame-env-when-bfr-env-equiv
                           (ins (car ins))))))))

  (local (defthm aig-fsm-run-of-aig-eval-alist
           (implies (and (bfr-mode)
                         (bfr-updates-p regs))
                    (equal (aignet::aig-fsm-run outs regs (acl2::aig-eval-alist alist env) ins)
                           (aignet::aig-fsm-run outs regs (bfr-eval-updates alist env) ins)))
           :hints (("goal" :use ((:instance aig-fsm-run-when-bfr-env-equiv
                                  (a (acl2::aig-eval-alist alist env))
                                  (b (bfr-eval-updates alist env))))))))

  (local (defthm aig-fsm-run-of-bfr-eval-updates-of-fast-alist-clean
           (implies (and (bfr-mode)
                         (bfr-updates-p regs))
                    (equal (aignet::aig-fsm-run outs regs (bfr-eval-updates (fast-alist-clean alist) env) ins)
                           (aignet::aig-fsm-run outs regs (bfr-eval-updates alist env) ins)))
           :hints (("goal" :use ((:instance aig-fsm-run-when-bfr-env-equiv
                                  (a (bfr-eval-updates (fast-alist-clean alist) env))
                                  (b (bfr-eval-updates alist env))))))))



  (define bfr-mcrun-fail-cycle (prop (updates bfr-updates-p) curr-st ins)
    :returns (fail-cycle natp)
    :measure (len ins)
    (b* (((when (atom ins)) 0)
         (env (bfr-mc-env updates curr-st (car ins)))
         ((unless (bfr-eval prop env)) 0))
      (+ 1 (bfr-mcrun-fail-cycle prop updates (bfr-eval-updates updates env) (cdr ins)))))


  (encapsulate nil
    (local (defun bfr-mcrun-nth-aig-fsm-run-ind (n updates curr-st ins)
             (if (zp n)
                 (list updates curr-st ins)
               (bfr-mcrun-nth-aig-fsm-run-ind
                (1- n) updates
                (bfr-eval-updates updates (bfr-mc-env updates curr-st (car ins)))
                (cdr ins)))))

    (defthm bfr-mcrun-implies-nth-aig-fsm-run-ok
      (implies (and (bfr-mode)
                    (bfr-mcrun prop updates init-st ins)
                    (< (nfix n) (len ins)))
               (equal (nth 0 (nth n (aignet::aig-fsm-run (list prop)
                                                         (fast-alist-clean (bfr-updates-fix updates))
                                                         init-st ins)))
                      t))
      :hints (("goal" :induct (bfr-mcrun-nth-aig-fsm-run-ind n updates init-st ins)
               :expand ((nth n (aignet::aig-fsm-run (list prop) (fast-alist-clean (bfr-updates-fix updates)) init-st ins))
                        (bfr-mcrun prop updates init-st ins))
               :in-theory (e/d (nth aignet::aig-fsm-frame-outs
                                    aignet::aig-fsm-frame-nextst
                                    bfr-eval)
                               (aignet::aig-fsm-run-in-terms-of-aig-eval
                                aignet::nth-of-aig-fsm-run
                                fast-alist-clean)))))


    (defthm not-bfr-mcrun-implies-nth-aig-fsm-run-not-ok
      (implies (and (bfr-mode)
                    (not (bfr-mcrun prop updates init-st ins)))
               (let ((n (bfr-mcrun-fail-cycle prop updates init-st ins)))
                 (not (nth 0 (nth n (aignet::aig-fsm-run (list prop)
                                                         (fast-alist-clean (bfr-updates-fix updates))
                                                         init-st ins))))))
      :hints (("goal" :induct (bfr-mcrun-fail-cycle prop updates init-st ins)
               :expand ((:free (n) (nth (+ 1 n) (aignet::aig-fsm-run (list prop) (fast-alist-clean (bfr-updates-fix updates)) init-st ins)))
                        (bfr-mcrun prop updates init-st ins)
                        (bfr-mcrun-fail-cycle prop updates init-st ins))
               :in-theory (e/d (nth aignet::aig-fsm-frame-outs
                                    aignet::aig-fsm-frame-nextst
                                    bfr-eval
                                    (:i bfr-mcrun-fail-cycle))
                               (aignet::aig-fsm-run-in-terms-of-aig-eval
                                aignet::nth-of-aig-fsm-run
                                fast-alist-clean)))))

    (defthm bfr-mcrun-fail-cycle-less-than-len-ins
      (implies (not (bfr-mcrun prop updates init-st ins))
               (< (bfr-mcrun-fail-cycle prop updates init-st ins) (len ins)))
      :hints(("Goal" :in-theory (enable bfr-mcrun bfr-mcrun-fail-cycle))))



    (defthm aig-fsm-run-prop-ok-iff-bfr-mcrun
      (implies (bfr-mode)
               (iff (aig-fsm-run-prop-ok prop updates init-st ins)
                    (bfr-mcrun prop updates init-st ins)))
      :hints (("goal" :in-theory (disable aignet::nth-of-aig-fsm-run
                                          aignet::aig-fsm-run-in-terms-of-aig-eval
                                          nth fast-alist-clean))
              (and stable-under-simplificationp
                   (if (member-equal '(aig-fsm-run-prop-ok prop updates init-st ins) clause)
                       '(:expand ((aig-fsm-run-prop-ok prop updates init-st ins)))
                     '(:use ((:instance aig-fsm-run-prop-ok-necc
                              (n (bfr-mcrun-fail-cycle prop updates init-st ins))))))))))


  (defthm aig-fsm-run-prop-ok-when-abc-mcheck-simple
    (b* (((mv result ?ctrex) (abc-mcheck-simple prop updates init-st)))
      (implies (equal result :proved)
               (bfr-mcrun prop updates init-st ins)))
    :hints (("goal" :use ((:instance aig-fsm-run-prop-ok-iff-bfr-mcrun))
             :in-theory (disable aig-fsm-run-prop-ok-iff-bfr-mcrun
                                 aignet::nth-of-aig-fsm-run
                                 aignet::aig-fsm-run-in-terms-of-aig-eval
                                 fast-alist-clean)
             :expand ((aig-fsm-run-prop-ok prop updates init-st ins)))
            (and stable-under-simplificationp
                 '(:cases ((bfr-mode))))
            (and stable-under-simplificationp
                 '(:expand ((abc-mcheck-simple prop updates init-st)))))))


(define bfr-mcheck-abc-simple (prop constr (updates bfr-updates-p) initstp (max-bvar natp))
  :returns (mv result ctrex-initst ctrex-ins)
  :parents (glmc)
  :short "@(see Bfr-mcheck) interface for ABC model-checking"
  (b* (((unless (bfr-mode))
        (prog2$ (er hard? 'bfr-mcheck-abc
                    "ABC model checking not supported in BDD mode")
                (mv :failed nil nil)))
       ;; (- (cw "prop: ~x0~%constr: ~x1~%updates: ~x2~%initstp: ~x3~%"
       ;;        prop constr updates initstp))
       ((mv prop1 constr1 updates1 initst1 next-bvar)
        (bfrmc-set-initst-pred prop constr updates initstp max-bvar))
       ((mv prop2 updates2)
        (bfrmc-add-constraint prop1 constr1 updates1 next-bvar))
       (initst2 (bfr-set-var next-bvar nil initst1))

       ((mv status ctrex)
        (abc-mcheck-simple prop2 updates2 initst2))
       ((unless (and (eq status :refuted) (consp ctrex)))
        (mv status nil nil))
       (first-ins (make-fast-alist (car ctrex)))
       (ctrex-initst1 (bfr-ins-to-initst (acl2::hons-set-diff (bfr-updates->states updates)
                                                              (bfr-updates->states initst1))
                                         (+ 1 (lnfix max-bvar))
                                         first-ins))
       (ctrex-initst2 (hons-shrink-alist initst2 ctrex-initst1)))
    (fast-alist-free first-ins)
    (mv :refuted ctrex-initst2 ctrex))
  ///

  (defthm aig-fsm-run-prop-ok-when-abc-mcheck-simple-rw
    (b* (((mv result ?ctrex) (abc-mcheck-simple prop updates init-st)))
      (implies (bind-free '((ins . (bfrmc-set-initst-pred-inputs updates initstp max-bvar init-st ins))))
               (iff (equal result :proved)
                    (and (bfr-mcrun prop updates init-st ins)
                         (hide (equal result :proved))))))
    :hints (("goal" :use aig-fsm-run-prop-ok-when-abc-mcheck-simple
             :expand ((:free (x) (hide x))))))

  (local (defthm bfr-constrained-mcrun-when-atom-ins
           (implies (atom ins)
                    (bfr-constrained-mcrun prop constr updates init-st ins))
           :hints(("Goal" :in-theory (enable bfr-constrained-mcrun)))))

  (defthm not-member-vars-when-pbfr-list-vars-bounded
    (implies (and (pbfr-list-vars-bounded max-bvar t x)
                  (bfr-varname-p var)
                  (bfr-mode)
                  (or (not (natp var))
                      (<= (nfix max-bvar) var)))
             (not (member var (bfrlist-vars x))))
    :hints(("Goal" :in-theory (enable bfrlist-vars pbfr-list-vars-bounded))))

  ;; (local (defthm not-hons-assoc-equal-when-bfr-varlist-bounded
  ;;          (implies (and (pbfr-list-vars-bounded max-bvar t (alist-vals x))
  ;;                        (bfr-varname-p var)
  ;;                        (bfr-mode)
  ;;                        (or (not (natp var))
  ;;                            (<= (nfix max-bvar) var)))
  ;;                   (not (member var (bfrlist-vars x))))

  (local (defthm lookup-in-updates-when-bfr-varlist-bounded
           (implies (and (bfr-varlist-bounded max-bvar (bfr-updates->states updates))
                         (bfr-varname-p var)
                         (or (not (natp var))
                             (<= (nfix max-bvar) var)))
                    (not (hons-assoc-equal var updates)))
           :hints(("Goal" :in-theory (enable bfr-varlist-bounded bfr-updates->states hons-assoc-equal)))))

  (defthm bfr-mcheck-abc-simple-correct
    (b* (((mv result ?ctrex-initst ?ctrex-ins)
          (bfr-mcheck-abc-simple prop constr updates initstp max-bvar)))
      (implies (and (equal result :proved)
                    (bfr-eval initstp (bfr-env-override (bfr-updates->states updates)
                                                        init-st (car ins)))
                    (pbfr-vars-bounded max-bvar t prop)
                    (pbfr-vars-bounded max-bvar t constr)
                    (pbfr-vars-bounded max-bvar t initstp)
                    (pbfr-list-vars-bounded max-bvar t (alist-vals (bfr-updates-fix updates)))
                    (bfr-varlist-bounded max-bvar (bfr-updates->states updates)))
               (bfr-constrained-mcrun prop constr updates init-st ins)))
    :hints (("goal" :cases ((consp ins))
             :use bfrmc-set-initst-pred-vars-bounded
             :in-theory (disable bfrmc-set-initst-pred-vars-bounded)))))



(local (defattach bfr-mcheck bfr-mcheck-abc-simple))

(defmacro bfr-mcheck-use-abc-simple ()
  '(defattach bfr-mcheck bfr-mcheck-abc-simple))
