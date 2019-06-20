; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(include-book "pathcond")
(include-book "interp-st-bfrs-ok")
(include-book "sat-stub")
(local (std::add-default-post-define-hook :fix))
(local (include-book "std/lists/resize-list" :dir :system))

(defprod fgl-ipasir-config
  :parents (fgl-sat-check)
  :short "Configuration object for IPASIR SAT checks in the default FGL configuration."
  ((ignore-pathcond booleanp :default t)
   (ignore-constraint booleanp :default nil)
   (ipasir-callback-limit acl2::maybe-natp :default nil
                          "Limit on the number of callbacks in a single SAT ~
                           check after which the check fails.")
   (ipasir-recycle-callback-limit acl2::maybe-natp :default nil
                                  "Limit on the number of callbacks over the lifespan
                                   of a solver object, after which the solver is
                                   re-initialized."))
  :tag :fgl-ipasir-config)


(define logicman-maybe-recycle-ipasir ((config fgl-ipasir-config-p)
                                       logicman)
  :guard (and (logicman-invar logicman)
              (stobj-let ((ipasir (logicman->ipasir logicman)))
                         (ok)
                         (not (ipasir-get-assumption ipasir))
                         ok)
              (bfr-mode-is :aignet (logicman->mode logicman)))
  :prepwork ((local (in-theory (enable logicman-invar))))
  :returns new-logicman
  (b* (((fgl-ipasir-config config)))
    (stobj-let ((ipasir (logicman->ipasir logicman))
                (sat-lits (logicman->sat-lits logicman)))
               (ipasir sat-lits)
               (b* ((ipasir (ipasir::ipasir-cancel-new-clause ipasir))
                    (ipasir (ipasir::ipasir-cancel-assumption ipasir))
                    (ipasir (ipasir::ipasir-input ipasir))
                    (count (ipasir-callback-count ipasir))
                    ((when (or (not config.ipasir-recycle-callback-limit)
                               (< count config.ipasir-recycle-callback-limit)))
                     (b* ((ipasir (ipasir-set-limit ipasir config.ipasir-callback-limit)))
                       (mv ipasir sat-lits)))
                    (ipasir (ipasir-release ipasir))
                    (ipasir (ipasir-reinit ipasir))
                    (sat-lits (aignet::sat-lits-empty (aignet::aignet->sat-length sat-lits) sat-lits))
                    (ipasir (ipasir-set-limit ipasir config.ipasir-callback-limit)))
                 (mv ipasir sat-lits))
               logicman))
  ///
  (defret logicman-get-of-<fn>
    (implies (and (not (equal (logicman-field-fix key) :ipasir))
                  (not (equal (logicman-field-fix key) :sat-lits)))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  (defret logicman-invar-of-<fn>
    (implies (logicman-invar logicman)
             (logicman-invar new-logicman))
    :hints(("Goal" :in-theory (enable ipasir::ipasir-input$a
                                      ipasir::ipasir-cancel-assumption
                                      ipasir::ipasir-cancel-new-clause
                                      ipasir::ipasir-release$a
                                      ipasir::ipasir-reinit$a
                                      ipasir::ipasir-set-limit$a))))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

  (defret ipasir-assumption-of-<fn>
    (implies (equal (ipasir::ipasir$a->assumption (logicman->ipasir logicman)) nil)
             (equal (ipasir::ipasir$a->assumption (logicman->ipasir new-logicman)) nil))))


(local
 (defsection logicman->aignet->ipasir-lemmas

   (defthm cdr-of-nthcdr
     (equal (cdr (nthcdr n x))
            (nthcdr n (cdr x))))

   (defthm hons-assoc-equal-in-pairlis-numlist
     (implies (and (natp start) (natp n))
              (equal (cdr (hons-assoc-equal n (pairlis$ (numlist start 1 k) (nthcdr start x))))
                     (and (< (- n start) (nfix k))
                          (<= start n)
                          (nth n x))))
     :hints(("Goal" :in-theory (enable car-of-nthcdr)
             :induct (numlist start 1 k))))

   (defthm hons-assoc-equal-in-pairlis-numlist-base
     (implies (natp n)
              (equal (cdr (hons-assoc-equal n (pairlis$ (numlist 0 1 k) x)))
                     (and (< n (nfix k))
                          (nth n x))))
     :hints(("Goal" :use ((:instance hons-assoc-equal-in-pairlis-numlist
                           (start 0)))
             :in-theory (disable hons-assoc-equal-in-pairlis-numlist))))

   (local (include-book "theory"))
   
   (defthm nth-alist-to-bitarr-of-pairlis$
     (acl2::bit-equiv (nth n (alist-to-bitarr k (pairlis$ (acl2::numlist 0 1 k) bits) nil))
                      (if (< (nfix n) (nfix k))
                          (bool->bit (nth n bits))
                        0)))
   
   (defthm alist-to-bitarr-of-pairlis$-under-bits-equiv
     (acl2::bits-equiv (alist-to-bitarr k (pairlis$ (acl2::numlist 0 1 k) bools) nil)
                       (take k (bools->bits bools)))
     :hints(("Goal" :in-theory (enable acl2::bits-equiv)
             :do-not-induct t)))
   
   (defthm bools->bits-of-bits->bools-under-bits-equiv
     (acl2::bits-equiv (bools->bits (bits->bools x)) x)
     :hints(("Goal" :in-theory (enable acl2::bits-equiv))))

   (defthm eval-lit-of-lit-negate-cond
     (implies (bitp val)
              (equal (equal (satlink::eval-lit (satlink::lit-negate-cond lit neg) env) val)
                     (equal (satlink::eval-lit lit env) (b-xor neg val))))
     :hints(("Goal" :in-theory (enable satlink::eval-lit))))

   ;; (defthm bits-equiv-of-cnf->aignet-invals-of-aignet->cnf-vals
   ;;   (acl2::bits-equiv (aignet::cnf->aignet-invals
   ;;                      nil
   ;;                      (aignet::aignet->cnf-vals
   ;;                       invals nil nil sat-lits aignet)
   ;;                      sat-lits aignet)
   ;;                     (take (aignet::stype-count :pi aignet) invals))
   ;;   :hints(("Goal" :in-theory (enable acl2::bits-equiv))))
   ))



(define logicman-bfr->ipasir ((bfr lbfr-p)
                              (logicman))
  :guard (and (bfr-mode-is :aignet (logicman->mode logicman))
              (logicman-invar logicman))
  :returns (new-logicman)
  :guard-hints (("goal" :in-theory (enable logicman-invar)))
  (b* ((logicman (logicman-update-refcounts logicman))
       (lit (bfr->aignet-lit bfr (logicman->bfrstate))))
    (stobj-let ((aignet (logicman->aignet logicman))
                (ipasir (logicman->ipasir logicman))
                (u32arr (logicman->aignet-refcounts logicman))
                (sat-lits (logicman->sat-lits logicman)))
               (sat-lits ipasir)
               (b* (((acl2::hintcontext-bind
                      ((sat-lits-orig sat-lits)
                       (ipasir-orig ipasir))))
                    ((mv sat-lits ipasir)
                     (aignet::aignet-lit->ipasir lit t u32arr sat-lits aignet ipasir))
                    (sat-lit (aignet::aignet-lit->sat-lit lit sat-lits))
                    (ipasir (ipasir::ipasir-assume ipasir sat-lit))
                    ((acl2::hintcontext :assume)))
                 (mv sat-lits ipasir))
               logicman))
  ///
  (local
   #!aignet
   (defthm sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id-rw
     (implies (and (bind-free '((aignet . #!fgl (logicman->aignet logicman))) (aignet))
                   (sat-lits-wfp sat-lits aignet)
                   (aignet-id-has-sat-var n sat-lits))
              (sat-varp (satlink::lit->var (aignet-id->sat-lit n sat-lits))
                        sat-lits))))

  (defret logicman-invar-of-<fn>
    (implies (and (logicman-invar logicman)
                  (lbfr-p bfr)
                  (lbfr-mode-is :aignet))
             (logicman-invar new-logicman))
    :hints(("Goal" :in-theory (enable logicman-invar
                                      ipasir::ipasir-assume$a
                                      bfr-p))))

  (defret logicman-get-of-<fn>
    (implies (and (not (equal (logicman-field-fix key) :sat-lits))
                  (not (equal (logicman-field-fix key) :aignet-refcounts))
                  (not (equal (logicman-field-fix key) :refcounts-index))
                  (not (equal (logicman-field-fix key) :ipasir)))
             (equal (logicman-get key new-logicman)
                    (logicman-get key logicman))))

  

  (set-ignore-ok t)

  #!aignet
  (local (defthm lit-eval-norm-when-no-regs
           (implies (and (syntaxp (not (equal regvals ''nil)))
                         (equal (stype-count :reg aignet) 0))
                    (equal (lit-eval lit invals regvals aignet)
                           (lit-eval lit invals nil aignet)))
           :hints (("goal" :use ((:instance lit-eval-of-take-num-regs
                                  (n 0)))
                    :in-theory (disable lit-eval-of-take-num-regs)))))

  (defret logicman-ipasir-assumption-of-<fn>
    (implies (and (logicman-invar logicman)
                  (lbfr-mode-is :aignet)
                  (lbfr-p bfr)
                  (equal (satlink::eval-formula
                          (ipasir::ipasir$a->formula (logicman->ipasir new-logicman))
                          env)
                         1))
             (equal (satlink::eval-cube
                     (ipasir::ipasir$a->assumption (logicman->ipasir new-logicman))
                     env)
                    (b* ((vals (aignet::cnf->aignet-invals
                                nil env (logicman->sat-lits new-logicman)
                                (logicman->aignet logicman))))
                      (b-and (satlink::eval-cube
                              (ipasir::ipasir$a->assumption (logicman->ipasir logicman))
                              env)
                             (bool->bit
                              (bfr-eval bfr (pairlis$ (acl2::numlist 0 1 (aignet::num-ins (logicman->aignet logicman)))
                                                      (bits->bools vals))
                                        logicman))))))
    :hints(("Goal" :in-theory (e/d (bfr-eval logicman-invar)
                                   (aignet::cnf-for-aignet-implies-lit-sat-when-cnf-sat
                                    ;; aignet::cnf-for-aignet-preserved-by-aignet-lit->cnf
                                    ))
            :expand ((:free (a b) (satlink::eval-cube (cons a b) env))))
           (acl2::function-termhint
            logicman-bfr->ipasir
            (:assume
             `(:use ((:instance aignet::cnf-for-aignet-implies-lit-sat-when-cnf-sat
                      (invals nil) (cnf-vals env)
                      (sat-lits ,(acl2::hq sat-lits))
                      (aignet ,(acl2::hq aignet))
                      (regvals nil)
                      (cnf ,(acl2::hq (ipasir::ipasir$a->formula ipasir)))
                      (lit ,(acl2::hq lit)))))))))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

  (defret aignet-id-has-sat-var-of-<fn>
    (implies (and (logicman-invar logicman)
                  (lbfr-p bfr)
                  (lbfr-mode-is :aignet)
                  (equal bfrstate (logicman->bfrstate)))
             (aignet::aignet-id-has-sat-var
              (satlink::lit->var
               (bfr->aignet-lit bfr bfrstate))
              (logicman->sat-lits new-logicman))))
  
  ;; (defret ipasir-formula-norm-of-<fn>
  ;;   (implies (and (equal ipasir (logicman->ipasir logicman))
  ;;                 (syntaxp (and (quotep ipasir)
  ;;                               (equal (unquote ipasir) *logicman-empty-ipasir*))))
  ;;            (equal
  ;;             (ipasir::ipasir$a->formula (logicman->ipasir new-logicman))
  ;;             (append (ipasir::ipasir$a->formula (logicman->ipasir
  ;;                                                 (logicman-bfr->ipasir
  ;;                                                  bfr (logicman-delete-ipasir logicman))))
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
  ;;                                                    (logicman-bfr->ipasir
  ;;                                                     bfr (logicman-delete-ipasir logicman))))
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
  ;;              (logicman-bfr->ipasir
  ;;               bfr (logicman-delete-ipasir logicman)))))
  ;;   :hints(("Goal" :in-theory (enable logicman-delete-ipasir
  ;;                                     logicman-update-refcounts))))

  (defret sat-lit-extension-p-of-<fn>
    (implies (equal sat-lits (logicman->sat-lits logicman))
             (aignet::sat-lit-extension-p (logicman->sat-lits new-logicman) sat-lits))))


(defthm eval-formula-of-append
  (equal (satlink::eval-formula (append a b) env)
         (b-and (satlink::eval-formula a env)
                (satlink::eval-formula b env)))
  :hints(("Goal" :in-theory (enable satlink::eval-formula))))

  
(define logicman-ipasir-solve (logicman)
  :returns (mv status new-logicman)
  :guard (logicman-invar logicman)
  :guard-hints (("goal" :in-theory (enable logicman-invar)))
  (stobj-let ((ipasir (logicman->ipasir logicman)))
             (status ipasir)
             (ipasir::ipasir-solve ipasir)
             (mv status logicman))
  ///
  (defret logicman-equiv-of-<fn>
    (logicman-equiv new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-equiv))))

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

  (defret logicman-invar-of-<fn>
    (implies (logicman-invar logicman)
             (logicman-invar new-logicman))
    :hints(("Goal" :in-theory (enable logicman-invar))))

  (defret ipasir-assumption-of-<fn>
    (equal (ipasir::ipasir$a->assumption (logicman->ipasir new-logicman)) nil))

  (defretd <fn>-unsat-implies
    (b* ((ipasir (logicman->ipasir logicman)))
      (implies (and (equal status :unsat)
                    (equal (satlink::eval-formula (ipasir::ipasir$a->formula ipasir) env) 1))
               (equal (satlink::eval-cube (ipasir::ipasir$a->assumption ipasir) env) 0)))))



    


(defthm logicman-pathcond-eval-of-pairlis$-numlist
  (implies (and (lbfr-mode-is :aignet)
                (equal num-ins (aignet::stype-count :pi (logicman->aignet logicman)))
                (nth *pathcond-enabledp* pathcond))
           (equal (logicman-pathcond-eval (pairlis$
                                           (acl2::numlist 0 1 num-ins)
                                           bits)
                                          pathcond logicman)
                  (aignet::aignet-pathcond-eval (logicman->aignet logicman)
                                                (nth *pathcond-aignet* pathcond)
                                                (bools->bits bits)
                                                nil)))
  :hints(("Goal" :in-theory (enable logicman-pathcond-eval))))
    


(define interp-st-ipasir-sat-check-core ((config fgl-ipasir-config-p)
                                  (bfr interp-st-bfr-p)
                                  (interp-st interp-st-bfrs-ok)
                                  state)
  :guard (bfr-mode-is :aignet (interp-st-bfr-mode))
  :returns (mv (ans)
               new-interp-st)
  :ignore-ok t
  :irrelevant-formals-ok t
  ;; :guard-debug t
  :guard-hints (("goal" :in-theory (enable interp-st-bfrs-ok)))
  (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
        (mv bfr interp-st))
       ((fgl-ipasir-config config)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (pathcond (interp-st->pathcond interp-st))
                (constraint-pathcond (interp-st->constraint interp-st)))
               (ans logicman)
               (b* ((logicman (logicman-maybe-recycle-ipasir config logicman))
                    (logicman (if (or** config.ignore-pathcond
                                        (not (pathcond-enabledp pathcond)))
                                  logicman
                                (logicman-pathcond-to-ipasir pathcond logicman)))
                    (logicman (if (or** config.ignore-constraint
                                        (not (pathcond-enabledp constraint-pathcond)))
                                  logicman
                                (logicman-pathcond-to-ipasir constraint-pathcond logicman)))
                    (logicman (logicman-bfr->ipasir bfr logicman))
                    ;; ((acl2::hintcontext-bind ((logicman-solve logicman))))
                    )
                 (acl2::hintcontext :solve
                                    (logicman-ipasir-solve logicman)))
               (if (eq ans :unsat)
                   (mv nil interp-st)
                 (mv bfr interp-st))))
  ///
  
  (defret interp-st-bfrs-ok-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (interp-st-bfr-p bfr))
             (interp-st-bfrs-ok new-interp-st))
    :hints(("Goal" :in-theory (enable interp-st-bfrs-ok))))

  (defret interp-st-bfr-p-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (interp-st-bfr-p bfr)
                  (equal logicman (interp-st->logicman interp-st)))
             (lbfr-p ans logicman)))

  (defret logicman-equiv-of-<fn>
    (logicman-equiv (interp-st->logicman new-interp-st)
                    (interp-st->logicman interp-st))
    :hints(("Goal" :in-theory (enable logicman-equiv))))

  (local (defthm logicman-invar-implies-cnf-for-aignet-rw
           (implies (and (logicman-invar logicman)
                         (equal aignet (logicman->aignet logicman)))
                    (b* ((ipasir (logicman->ipasir logicman))
                         (sat-lits (logicman->sat-lits logicman)))
                      (aignet::cnf-for-aignet
                       aignet (ipasir::ipasir$a->formula ipasir) sat-lits)))))

  (local (defthm logicman-invar-implies-sat-lits-wfp-rw
           (implies (and (logicman-invar logicman)
                         (equal aignet (logicman->aignet logicman)))
                    (b* ((sat-lits (logicman->sat-lits logicman)))
                      (aignet::sat-lits-wfp
                       sat-lits aignet)))))

  (local
   #!aignet
   (defthm aignet-eval-conjunction-of-nil
     (equal (aignet-eval-conjunction nil invals regvals aignet) 1)
     :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))
  
  #!aignet
  (local (defthm lit-eval-norm-when-no-regs
           (implies (and (syntaxp (not (equal regvals ''nil)))
                         (equal (stype-count :reg aignet) 0))
                    (equal (lit-eval lit invals regvals aignet)
                           (lit-eval lit invals nil aignet)))
           :hints (("goal" :use ((:instance lit-eval-of-take-num-regs
                                  (n 0)))
                    :in-theory (disable lit-eval-of-take-num-regs)))))

  (local
   #!aignet
   (defthm cnf-for-aignet-implies-lit-sat-when-cnf-sat-rw
     (b* ((invals (cnf->aignet-invals invals cnf-vals satlits aignet))
          (regvals nil))
       (implies (and (sat-lits-wfp satlits aignet)
                     (bind-free
                      (case-match satlits
                        (('fgl::logicman->sat-lits x)
                         `((cnf . (ipasir::ipasir$a->formula$inline (fgl::logicman->ipasir ,x)))))
                        (& nil))
                      (cnf))
                     (cnf-for-aignet aignet cnf satlits)
                     (aignet-litp lit aignet)
                     (aignet-id-has-sat-var (lit-id lit) satlits)
                     (equal 1 (satlink::eval-formula cnf cnf-vals))
                     (equal (stype-count :reg aignet) 0))
                (equal (lit-eval lit invals regvals aignet)
                       (satlink::eval-lit
                        (aignet-lit->sat-lit lit satlits)
                        cnf-vals))))
     :hints (("goal" :use ((:instance cnf-for-aignet-implies-lit-sat-when-cnf-sat
                            (sat-lits satlits)))
              :in-theory (disable cnf-for-aignet-implies-lit-sat-when-cnf-sat)))))

  (local (in-theory (disable aignet::aignet-lit->sat-lit)))

  (local
   #!aignet
   (acl2::def-updater-independence-thm eval-conjunction-in-aignet->cnf-vals-of-sat-lit-extension-logicman
     (implies (and (sat-lit-extension-p (fgl::logicman->sat-lits new)
                                        (fgl::logicman->sat-lits old))
                   (sat-lit-listp conjunction (fgl::logicman->sat-lits old)))
              (equal (eval-cube
                      conjunction (aignet->cnf-vals
                                   invals regvals cnf-vals
                                   (fgl::logicman->sat-lits new) aignet))
                     (eval-cube
                      conjunction (aignet->cnf-vals
                                   invals regvals cnf-vals
                                   (fgl::logicman->sat-lits old) aignet))))))

  (local
   #!aignet
   (acl2::def-updater-independence-thm nbalist-has-sat-lits-of-sat-lit-extension-logicman
     (implies (and (sat-lit-extension-p (fgl::logicman->sat-lits new)
                                        (fgl::logicman->sat-lits old))
                   (nbalist-has-sat-lits nbalist (fgl::logicman->sat-lits old)))
              (nbalist-has-sat-lits nbalist (fgl::logicman->sat-lits new)))))

  (local
   #!aignet
   (defthm cnf-for-aignet-implies-cnf-sat-when-lit-sat-rw
     (b* ((cnf-vals (aignet->cnf-vals
                     invals regvals cnf-vals sat-lits aignet)))
       (implies (and (sat-lits-wfp sat-lits aignet)
                     (bind-free
                      (case-match sat-lits
                        (('fgl::logicman->sat-lits x)
                         `((cnf . (ipasir::ipasir$a->formula$inline (fgl::logicman->ipasir ,x)))))
                        (& nil))
                      (cnf))
                     (cnf-for-aignet aignet cnf sat-lits)
                     (aignet-litp lit aignet)
                     (aignet-id-has-sat-var (lit-id lit) sat-lits))
                (equal (satlink::eval-lit
                        (aignet-lit->sat-lit lit sat-lits)
                        cnf-vals)
                       (lit-eval lit invals regvals aignet)
                       ;; (lit-eval lit invals regvals aignet)
                       )))))

  (local
   #!aignet
   (defthm cnf-for-aignet-implies-eval-formula
     (implies (cnf-for-aignet aignet cnf sat-lits)
              (equal (satlink::eval-formula
                      cnf (aignet->cnf-vals invals regvals cnf-vals sat-lits aignet))
                     1))))


  (local (in-theory (disable aignet::eval-cube-of-aignet->cnf-vals)))

  (local (defthm eval-cube-of-nil
           (equal (satlink::eval-cube nil env) 1)
           :hints(("Goal" :in-theory (enable satlink::eval-cube)))))


  #!aignet
  (local (defthm aignet-pathcond-eval-norm-when-no-regs
           (implies (and (syntaxp (not (equal regvals ''nil)))
                         (equal (stype-count :reg aignet) 0))
                    (iff (aignet-pathcond-eval aignet pathcond invals regvals)
                         (aignet-pathcond-eval aignet pathcond invals nil)))
           :hints ((and stable-under-simplificationp
                        (let* ((lit (assoc 'aignet-pathcond-eval clause))
                               (other (if (eq (car (last lit)) 'regvals)
                                          nil
                                        'regvals)))
                          `(:expand (,lit)
                            :use ((:instance aignet-pathcond-eval-necc
                                   (id (aignet-pathcond-eval-witness . ,(cdr lit)))
                                   (nbalist pathcond)
                                   (regvals ,other)))
                            :do-not-induct t))))))

  (local
   #!aignet
   (defthm cnf-for-aignet-implies-aignet-pathcond-eval-when-cnf-sat-no-regs
     (b* ((invals (cnf->aignet-invals invals cnf-vals sat-lits aignet))
          (regvals nil))
       (implies (and (sat-lits-wfp sat-lits aignet)
                     (bind-free
                      (case-match sat-lits
                        (('fgl::logicman->sat-lits x)
                         `((cnf . (ipasir::ipasir$a->formula$inline (fgl::logicman->ipasir ,x)))))
                        (& nil))
                      (cnf))
                     (cnf-for-aignet aignet cnf sat-lits)
                     (aignet-pathcond-p nbalist aignet)
                     (nbalist-has-sat-lits nbalist sat-lits)
                     (equal 1 (satlink::eval-formula cnf cnf-vals))
                     (equal (stype-count :reg aignet) 0))
                (equal (aignet-pathcond-eval aignet nbalist invals regvals)
                       (bit->bool (satlink::eval-cube
                                   (aignet-lits->sat-lits (nbalist-to-cube nbalist) sat-lits)
                                   cnf-vals)))))
     :hints(("Goal" :use cnf-for-aignet-implies-aignet-pathcond-eval-when-cnf-sat
             :in-theory (disable cnf-for-aignet-implies-aignet-pathcond-eval-when-cnf-sat)))
     ))

  (local (defthm aignet-pathcond-p-when-logicman-pathcond-p
           (implies (and (logicman-pathcond-p pathcond logicman)
                         (lbfr-mode-is :aignet))
                    (aignet::aignet-pathcond-p (nth *pathcond-aignet* pathcond) 
                                               (logicman->aignet logicman)))
           :hints(("Goal" :in-theory (enable logicman-pathcond-p)))))

  (local
   #!aignet
   (defthm bitp-cdar-of-nbalist-fix
     (implies (consp (nbalist-fix x))
              (Bitp (cdar (nbalist-fix x))))
     :hints(("Goal" :in-theory (enable nbalist-fix)))
     :rule-classes :type-prescription))

  (local
   #!aignet
   (defthm cnf-for-aignet-implies-eval-nbalist-to-cube-of-aignet->cnf-vals
     (b* ((cnf-vals (aignet->cnf-vals
                     invals regvals cnf-vals sat-lits aignet)))
       (implies (and (sat-lits-wfp sat-lits aignet)
                     (bind-free
                      (case-match sat-lits
                        (('fgl::logicman->sat-lits x)
                         `((cnf . (ipasir::ipasir$a->formula$inline (fgl::logicman->ipasir ,x)))))
                        (& nil))
                      (cnf))
                     (cnf-for-aignet aignet cnf sat-lits)
                     (aignet-pathcond-p nbalist aignet)
                     (nbalist-has-sat-lits nbalist sat-lits))
                (equal (satlink::eval-cube
                        (aignet-lits->sat-lits (nbalist-to-cube nbalist) sat-lits)
                        cnf-vals)
                       (bool->bit (aignet-pathcond-eval aignet nbalist invals regvals))
                       ;; (lit-eval lit invals regvals aignet)
                       )))
     :hints(("Goal" :in-theory (enable nbalist-has-sat-lits
                                       aignet-pathcond-p-redef
                                       aignet-pathcond-eval-redef
                                       nbalist-to-cube
                                       eval-cube
                                       lit-eval)))))

  (set-ignore-ok t)

  (defret eval-of-<fn>
    (implies (and (interp-st-bfrs-ok interp-st)
                  (interp-st-bfr-p bfr)
                  (not (interp-st->errmsg new-interp-st))
                  (equal logicman (interp-st->logicman interp-st))
                  (logicman-pathcond-eval (gl-env->bfr-vals env)
                                          (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (logicman-pathcond-eval (gl-env->bfr-vals env)
                                          (interp-st->constraint interp-st)
                                          (interp-st->logicman interp-st)))
             (equal (gobj-bfr-eval ans env logicman)
                    (gobj-bfr-eval bfr env (interp-st->logicman interp-st))))
    :hints ((acl2::function-termhint
             interp-st-ipasir-sat-check-core
             (:solve
              (b* ((aignet (logicman->aignet logicman))
                   (sat-lits (logicman->sat-lits logicman))
                   (ipasir (logicman->ipasir logicman))
                   (aignet-invals (alist-to-bitarr (aignet::num-ins aignet)
                                                   (gl-env->bfr-vals env) nil))
                   (cnf-vals (aignet::aignet->cnf-vals aignet-invals nil nil sat-lits aignet)))
                `(:use ((:instance logicman-ipasir-solve-unsat-implies
                         (logicman ,(acl2::hq logicman))
                         (env ,(acl2::hq cnf-vals)))
                        ;; (:instance aignet::cnf-for-aignet-implies-eval-formula
                        ;;  (cnf ,(acl2::hq (ipasir::ipasir$a->formula ipasir)))
                        ;;  (invals ,(acl2::hq aignet-invals))
                        ;;  (regvals nil)
                        ;;  (cnf-vals nil)
                        ;;  (sat-lits ,(acl2::hq sat-lits))
                        ;;  (aignet ,(acl2::hq aignet)))
                        )
                  :in-theory (e/d (bfr-eval logicman-pathcond-eval)
                                  ;; (aignet::cnf-for-aignet-necc
                                  ;;  aignet::cnf-for-aignet-implies-eval-formula)
                                  )))))))
  


  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :logicman))
                  (not (equal (interp-st-field-fix key) :errmsg))
                  (not (equal (interp-st-field-fix key) :debug-info))
                  (not (equal (interp-st-field-fix key) :debug-stack)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  ;; (defret major-stack-ev-of-<fn>
  ;;   (implies (equal stack (interp-st->stack interp-st))
  ;;            (equal (major-stack-ev stack env (interp-st->logicman new-interp-st))
  ;;                   (major-stack-ev stack env (interp-st->logicman interp-st)))))

  (defret logicman->mode-of-<fn>
    (equal (logicman->mode (interp-st->logicman new-interp-st))
           (logicman->mode (interp-st->logicman interp-st))))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars (interp-st->logicman new-interp-st))
           (bfr-nvars (interp-st->logicman interp-st))))

  ;; (defret pathcond-eval-checkpoints-of-<fn>
  ;;   (implies (equal pathcond (interp-st->pathcond interp-st))
  ;;            (equal (logicman-pathcond-eval-checkpoints!
  ;;                    env
  ;;                    pathcond
  ;;                    (interp-st->logicman new-interp-st))
  ;;                   (logicman-pathcond-eval-checkpoints!
  ;;                    env
  ;;                    pathcond
  ;;                    (interp-st->logicman interp-st)))))

  ;;   (defret constraint-eval-of-<fn>
  ;;     (implies (equal constraint (interp-st->constraint interp-st))
  ;;              (equal (logicman-pathcond-eval
  ;;                      env
  ;;                      constraint
  ;;                      (interp-st->logicman new-interp-st))
  ;;                     (logicman-pathcond-eval
  ;;                      env
  ;;                      constraint
  ;;                      (interp-st->logicman interp-st)))))
  
  (defret <fn>-return-values-correct
    (equal (list . <values>)
           <call>))

  (defret <fn>-preserves-errmsg
    (let ((errmsg (interp-st->errmsg interp-st)))
      (implies errmsg
               (equal (interp-st->errmsg new-interp-st) errmsg))))

  
  
  ;; (defret get-bvar->term-eval-of-<fn>
  ;;   (implies (equal bvar-db (interp-st->bvar-db interp-st))
  ;;            (iff (fgl-object-eval (get-bvar->term$a n bvar-db)
  ;;                                  env
  ;;                                  (interp-st->logicman new-interp-st))
  ;;                 (fgl-object-eval (get-bvar->term$a n bvar-db)
  ;;                                  env
  ;;                                  (interp-st->logicman interp-st)))))

  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
             (not (equal (interp-st->errmsg new-interp-st) :unreachable)))))

(local (in-theory (disable w)))

(make-event
 `(define interp-st-ipasir-sat-check-impl (params
                                           (bfr interp-st-bfr-p)
                                           (interp-st interp-st-bfrs-ok)
                                           state)
    :returns (mv (ans)
                 new-interp-st
                 new-state)
    (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
          ;; Skip the SAT check when not in aignet mode, for now.
          (mv bfr interp-st state))
         ((when (interp-st->errmsg interp-st))
          (mv nil interp-st state))
         ((unless (fgl-ipasir-config-p params))
          (gl-interp-error
           :msg (gl-msg "Malformed fgl-sat-check call: params was not resolved to a fgl-ipasir-config object")))
         ((when (eq bfr nil))
          (mv nil interp-st state))
         ((mv ans interp-st)
          (interp-st-ipasir-sat-check-core params bfr interp-st state)))
      (mv ans interp-st state))
    ///
    . ,*interp-st-sat-check-thms*))





;; NOTE: This preserves any values in bitarr that are not set in the ipasir's
;; solution.  So if we wanted to add some randomization and the ipasir solver
;; that we used ever produced a partial satisfying assignment, we could seed
;; the bitarr with random values first.
(define ipasir-assignment->cnf-vals ((n natp) ipasir bitarr)
  :guard (and (<= n (bits-length bitarr))
              (equal (ipasir-get-status ipasir) :sat))
  :guard-debug t
  :measure (nfix (- (bits-length bitarr) (nfix n)))
  :returns (new-bitarr)
  (b* (((when (mbe :logic (zp (- (bits-length bitarr) (nfix n)))
                   :exec (eql n (bits-length bitarr))))
        bitarr)
       (val (ipasir-val ipasir (satlink::make-lit n 0)))
       (bitarr (if val
                   (set-bit n val bitarr)
                 bitarr)))
    (ipasir-assignment->cnf-vals (1+ (lnfix n)) ipasir bitarr))
  ///
  (defret len-of-<fn>
    (equal (len new-bitarr) (len bitarr))))
    
  

(define logicman-ipasir->env$ (logicman env$)
  :guard (logicman-invar logicman)
  :returns (mv err new-env$)
  (b* ((bfrstate (logicman->bfrstate)))
    (stobj-let ((ipasir (logicman->ipasir logicman))
                (aignet (logicman->aignet logicman))
                (sat-lits (logicman->sat-lits logicman)))
               (err env$)
               (stobj-let ((bitarr (env$->bitarr env$)))
                          (err bitarr)
                          (bfrstate-case
                            :aignet
                            (b* (((unless (equal (ipasir::ipasir-get-status ipasir) :sat))
                                  (b* ((bitarr (resize-bits (+ 1 (bfrstate->bound bfrstate)) bitarr)))
                                    (mv "Error: expected ipasir status to be :sat" bitarr)))
                                 ((acl2::local-stobjs aignet::cnf-vals)
                                  (mv err bitarr aignet::cnf-vals))
                                 (aignet::cnf-vals (resize-bits (aignet::sat-next-var sat-lits) aignet::cnf-vals))
                                 (aignet::cnf-vals (ipasir-assignment->cnf-vals 0 ipasir aignet::cnf-vals))
                                 (bitarr (resize-bits (aignet::num-fanins aignet) bitarr))
                                 (bitarr (aignet::cnf->aignet-vals bitarr aignet::cnf-vals sat-lits aignet))
                                 (bitarr (aignet::aignet-eval bitarr aignet)))
                              (mv nil bitarr aignet::cnf-vals))
                            :bdd
                            (b* ((bitarr (resize-bits (bfrstate->bound bfrstate) bitarr)))
                              (mv "Error: expected bfr mode to be :aignet"
                                  bitarr))
                            :aig 
                            (mv "Error: expected bfr mode to be :aignet"
                                bitarr))
                          (mv err env$))
               (mv err env$)))
  ///
  (defret bfr-env$-p-of-<fn>
    (bfr-env$-p new-env$ (logicman->bfrstate))
    :hints(("Goal" :in-theory (enable bfr-env$-p)))))



(define interp-st-ipasir-counterexample (params
                                         (interp-st interp-st-bfrs-ok)
                                         state)
  :returns (mv err new-interp-st)
  (declare (ignore params state))
  (stobj-let ((logicman (interp-st->logicman interp-st))
              (env$ (interp-st->ctrex-env interp-st)))
             (err env$)
             (logicman-ipasir->env$ logicman env$)
             (mv err interp-st))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :ctrex-env))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret bfr-env$-p-of-<fn>
    (implies (not err)
             (bfr-env$-p (interp-st->ctrex-env new-interp-st)
                         (logicman->bfrstate (interp-st->logicman interp-st))))))

(defmacro fgl-use-ipasir ()
  '(progn (defattach interp-st-sat-check interp-st-ipasir-sat-check-impl)
          (defattach interp-st-sat-counterexample interp-st-ipasir-counterexample)))

(fgl-use-ipasir)
