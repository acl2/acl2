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
(include-book "centaur/satlink/top" :dir :system)
(local (std::add-default-post-define-hook :fix))
(local (include-book "std/lists/resize-list" :dir :system))


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

(define logicman-bfr->cnf ((bfr lbfr-p)
                           (logicman)
                           (sat-lits)
                           (cnf satlink::lit-list-listp)
                           (cube satlink::lit-listp))
  :guard (and (bfr-mode-is :aignet (logicman->mode logicman))
              (b* ((index (logicman->refcounts-index logicman)))
                (stobj-let ((aignet (logicman->aignet logicman))
                            (u32arr (logicman->aignet-refcounts logicman)))
                           (ok)
                           (and (<= index (aignet::u32-length u32arr))
                                (equal index (aignet::num-fanins aignet))
                                (aignet::sat-lits-wfp sat-lits aignet))
                           ok)))
  :returns (mv new-sat-lits
               (new-cnf satlink::lit-list-listp)
               (new-cube satlink::lit-listp))
  :guard-hints (("goal" :in-theory (enable logicman-invar)))
  (b* ((lit (bfr->aignet-lit bfr (logicman->bfrstate))))
    (stobj-let ((aignet (logicman->aignet logicman))
                (u32arr (logicman->aignet-refcounts logicman)))
               (sat-lits cnf cube)
               (b* (((acl2::hintcontext-bind
                      ((sat-lits-orig sat-lits)
                       (cnf-orig cnf)
                       (cube-orig cube))))
                    ((mv sat-lits cnf)
                     (aignet::aignet-lit->cnf lit t u32arr sat-lits aignet
                                              (satlink::lit-list-list-fix cnf)))
                    (sat-lit (aignet::aignet-lit->sat-lit lit sat-lits))
                    (cube (cons sat-lit (satlink::lit-list-fix cube)))
                    ((acl2::hintcontext :assume)))
                 (mv sat-lits cnf cube))
               (mv sat-lits cnf cube)))
  ///
  (local
   #!aignet
   (defthm sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id-rw
     (implies (and (bind-free '((aignet . #!fgl (logicman->aignet logicman))) (aignet))
                   (sat-lits-wfp sat-lits aignet)
                   (aignet-id-has-sat-var n sat-lits))
              (sat-varp (satlink::lit->var (aignet-id->sat-lit n sat-lits))
                        sat-lits))))

  (defret sat-lits-wfp-of-<fn>
    (implies (and (aignet::sat-lits-wfp sat-lits (logicman->aignet logicman))
                  (lbfr-p bfr)
                  (lbfr-mode-is :aignet))
             (and (implies (equal aignet (logicman->aignet logicman))
                           (aignet::sat-lits-wfp new-sat-lits aignet))
                  (implies (aignet::sat-lit-list-listp cnf sat-lits)
                           (aignet::sat-lit-list-listp new-cnf new-sat-lits))
                  (implies (aignet::sat-lit-listp cube sat-lits)
                           (aignet::sat-lit-listp new-cube new-sat-lits))))
    :hints(("Goal" :in-theory (enable bfr-p))))

  

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

  (defret cube-assumption-of-<fn>
    (implies (and (aignet::sat-lits-wfp sat-lits (logicman->aignet logicman))
                  (aignet::sat-lit-list-listp cnf sat-lits)
                  (aignet::sat-lit-listp cube sat-lits)
                  (aignet::cnf-for-aignet (logicman->aignet logicman)
                                          cnf sat-lits)
                  (lbfr-mode-is :aignet)
                  (equal (aignet::stype-count :reg (logicman->aignet logicman)) 0)
                  (lbfr-p bfr)
                  (equal (satlink::eval-formula new-cnf env) 1))
             (equal (satlink::eval-cube new-cube env)
                    (b* ((vals (aignet::cnf->aignet-invals
                                nil env new-sat-lits
                                (logicman->aignet logicman))))
                      (b-and (satlink::eval-cube cube env)
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
            logicman-bfr->cnf
            (:assume
             `(:use ((:instance aignet::cnf-for-aignet-implies-lit-sat-when-cnf-sat
                      (invals nil) (cnf-vals env)
                      (sat-lits ,(acl2::hq sat-lits))
                      (aignet ,(acl2::hq aignet))
                      (regvals nil)
                      (cnf ,(acl2::hq cnf))
                      (lit ,(acl2::hq lit)))))))))

  (defret cnf-for-aignet-of-<fn>
    (implies (and (aignet::sat-lits-wfp sat-lits (logicman->aignet logicman))
                  (aignet::sat-lit-list-listp cnf sat-lits)
                  (aignet::sat-lit-listp cube sat-lits)
                  (aignet::cnf-for-aignet (logicman->aignet logicman)
                                          cnf sat-lits)
                  (lbfr-mode-is :aignet)
                  (equal (aignet::stype-count :reg (logicman->aignet logicman)) 0)
                  (lbfr-p bfr)
                  (equal aignet (logicman->aignet logicman)))
             (aignet::cnf-for-aignet aignet
                                     new-cnf new-sat-lits))
    :hints(("Goal" :in-theory (e/d (bfr-eval logicman-invar)
                                   (
                                    ;; aignet::cnf-for-aignet-preserved-by-aignet-lit->cnf
                                    )))))

  (defret aignet-id-has-sat-var-of-<fn>
    (implies (and (aignet::sat-lits-wfp sat-lits (logicman->aignet logicman))
                  (aignet::sat-lit-list-listp cnf sat-lits)
                  (aignet::sat-lit-listp cube sat-lits)
                  (lbfr-p bfr)
                  (lbfr-mode-is :aignet)
                  (equal bfrstate (logicman->bfrstate)))
             (aignet::aignet-id-has-sat-var
              (satlink::lit->var
               (bfr->aignet-lit bfr bfrstate))
              new-sat-lits)))
  
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
    (aignet::sat-lit-extension-p new-sat-lits sat-lits)))

(encapsulate
  (((fgl-satlink-config) => *))
  (local (defun fgl-satlink-config ()
           satlink::*default-config*))
  (defthm fgl-satlink-config-constraint
    (satlink::config-p (fgl-satlink-config))))

(defun fgl-default-satlink-config ()
  (declare (xargs :guard t))
  (satlink::change-config satlink::*default-config*
                          :verbose nil))

(defattach fgl-satlink-config fgl-default-satlink-config)

(define cnf-assume-cube ((cube satlink::lit-listp)
                         (cnf satlink::lit-list-listp))
  :returns (new-cnf satlink::lit-list-listp)
  (if (atom cube)
      (satlink::lit-list-list-fix cnf)
    (cnf-assume-cube
     (cdr cube)
     (cons (list (satlink::lit-fix (car cube)))
           (satlink::lit-list-list-fix cnf))))
  ///
  (defthm eval-of-cnf-assume-cube
    (equal (satlink::eval-formula (cnf-assume-cube cube cnf) env)
           (b-and (satlink::eval-cube cube env)
                  (satlink::eval-formula cnf env)))
    :hints(("Goal" :in-theory (enable satlink::eval-formula satlink::eval-cube satlink::eval-clause)))))


(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

(local (defcong logicman-equiv equal (logicman-extension-p new old) 1
         :hints(("Goal" :in-theory (enable logicman-equiv logicman-extension-p)))))

(local (defthm logicman-extension-p-when-logicman-equiv
         (implies (logicman-equiv (double-rewrite new) old)
                  (logicman-extension-p new old))))

(local (defthm logicman-update-refcounts-preserves-logicman-invar
         (implies (logicman-invar logicman)
                  (logicman-invar (logicman-update-refcounts logicman)))
         :hints(("Goal" :in-theory (enable logicman-invar)))))

(local (defthm logicman-pathcond-to-cnf-preserves-logicman-invar
         (implies (logicman-invar logicman)
                  (logicman-invar (mv-nth 0 (logicman-pathcond-to-cnf pathcond logicman sat-lits cnf cube))))
         :hints(("Goal" :in-theory (enable logicman-invar logicman-pathcond-to-cnf)))))

(local (in-theory (disable resize-list
                           lrat::nth-n59-listp
                           lrat::nth-i60-listp)))

(define interp-st-satlink-sat-check-core ((config fgl-sat-config-p)
                                          (bfr interp-st-bfr-p)
                                          (interp-st interp-st-bfrs-ok)
                                          state)
  :guard (bfr-mode-is :aignet (interp-st-bfr-mode))
  :returns (mv (ans)
               new-interp-st)
  :ignore-ok t
  :irrelevant-formals-ok t
  ;; :guard-debug t
  :guard-hints (("goal" :in-theory (e/d (interp-st-bfrs-ok) (not))))
  (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
        (mv bfr interp-st))
       ((fgl-sat-config config)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (pathcond (interp-st->pathcond interp-st))
                (constraint-pathcond (interp-st->constraint interp-st))
                (env$ (interp-st->ctrex-env interp-st)))
               (ans logicman env$)
               (b* (((acl2::local-stobjs sat-lits satlink::env$)
                     (mv ans logicman env$ sat-lits satlink::env$))
                    (cnf nil)
                    (cube nil)
                    (num-fanins (stobj-let ((aignet (logicman->aignet logicman)))
                                           (num-fanins)
                                           (aignet::num-fanins aignet)
                                           num-fanins))
                    (sat-lits (resize-aignet->sat num-fanins sat-lits))
                    ((mv logicman sat-lits cnf cube)
                     (if (or** config.ignore-pathcond
                               (not (pathcond-enabledp pathcond)))
                         (mv logicman sat-lits cnf cube)
                       (logicman-pathcond-to-cnf pathcond logicman sat-lits cnf cube)))
                    ((mv logicman sat-lits cnf cube)
                     (if (or** config.ignore-constraint
                               (not (pathcond-enabledp constraint-pathcond)))
                         (mv logicman sat-lits cnf cube)
                       (logicman-pathcond-to-cnf constraint-pathcond logicman sat-lits cnf cube)))
                    (logicman (logicman-update-refcounts logicman))
                    ((mv sat-lits cnf cube)
                     (logicman-bfr->cnf bfr logicman sat-lits cnf cube))
                    (cnf (cnf-assume-cube cube cnf))
                    (config  (fgl-satlink-config))
                    ;; ((acl2::hintcontext-bind ((logicman-solve logicman))))
                    ((acl2::hintcontext :solve))
                    ((mv ans satlink::env$) (satlink::sat cnf satlink::env$ :config config))
                    (env$
                     (stobj-let ((bitarr (env$->bitarr env$)))
                                (bitarr)
                                (stobj-let ((aignet (logicman->aignet logicman)))
                                           (bitarr)
                                           (b* ((bitarr (resize-bits (aignet::num-fanins aignet) bitarr)))
                                             (aignet::cnf->aignet-vals bitarr satlink::env$ sat-lits aignet))
                                           bitarr)
                                env$)))
                 (mv ans logicman env$ sat-lits satlink::env$))
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
                        (('mv-nth ''0 ('fgl::logicman-bfr->cnf . args))
                         `((cnf . (mv-nth '1 (fgl::logicman-bfr->cnf . ,args)))))
                        (& (cw "satlits: ~x0~%" satlits)))
                      
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
                        (('mv-nth ''0 ('fgl::logicman-bfr->cnf . args))
                         `((cnf . (mv-nth '1 (fgl::logicman-bfr->cnf . ,args)))))
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
                        (('mv-nth ''0 ('fgl::logicman-bfr->cnf . args))
                         `((cnf . (mv-nth '1 (fgl::logicman-bfr->cnf . ,args)))))
                        (('mv-nth ''1 ('fgl::logicman-pathcond-to-cnf . args))
                         `((cnf . (mv-nth '2 (fgl::logicman-pathcond-to-cnf . ,args)))))
                        (& nil))
                      (cnf))
                     (cnf-for-aignet aignet cnf sat-lits)
                     (aignet-pathcond-p nbalist aignet)
                     (nbalist-has-sat-lits nbalist sat-lits)
                     (equal 1 (satlink::eval-formula cnf cnf-vals))
                     (equal (stype-count :reg aignet) 0))
                (equal (aignet-pathcond-eval aignet nbalist invals regvals)
                       (bit->bool (satlink::eval-cube
                                   (nbalist-to-cube nbalist sat-lits)
                                   cnf-vals)))))
     :hints(("Goal" :use cnf-for-aignet-implies-aignet-pathcond-eval-when-cnf-sat
             :in-theory (disable cnf-for-aignet-implies-aignet-pathcond-eval-when-cnf-sat)))))

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
   (defthm cnf-for-aignet-implies-eval-nbalist-to-cube-of-aignet->cnf-vals-lemma
     (b* ((cnf-vals (aignet->cnf-vals
                     invals regvals cnf-vals sat-lits aignet)))
       (implies (and (sat-lits-wfp sat-lits aignet)
                     (bind-free
                      (case-match sat-lits
                        (('mv-nth ''0 ('fgl::logicman-bfr->cnf . args))
                         `((cnf . (mv-nth '1 (fgl::logicman-bfr->cnf . ,args)))))
                        (('mv-nth ''1 ('fgl::logicman-pathcond-to-cnf . args))
                         `((cnf . (mv-nth '2 (fgl::logicman-pathcond-to-cnf . ,args)))))
                        (& nil))
                      (cnf))
                     (cnf-for-aignet aignet cnf sat-lits)
                     (aignet-pathcond-p nbalist aignet)
                     (nbalist-has-sat-lits nbalist sat-lits))
                (equal (satlink::eval-cube
                        (nbalist-to-cube nbalist sat-lits)
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

  (local
   #!aignet
   (defthm cnf-for-aignet-implies-eval-nbalist-to-cube-of-aignet->cnf-vals
     (b* ((cnf-vals (aignet->cnf-vals
                     invals regvals cnf-vals sat-lits aignet)))
       (implies (and (sat-lits-wfp sat-lits aignet)
                     (bind-free
                      (case-match sat-lits
                        (('mv-nth ''0 ('fgl::logicman-bfr->cnf . args))
                         `((cnf . (mv-nth '1 (fgl::logicman-bfr->cnf . ,args)))))
                        (('mv-nth ''1 ('fgl::logicman-pathcond-to-cnf . args))
                         `((cnf . (mv-nth '2 (fgl::logicman-pathcond-to-cnf . ,args)))))
                        (& nil))
                      (cnf))
                     (cnf-for-aignet aignet cnf sat-lits)
                     (aignet-pathcond-p nbalist aignet)
                     (nbalist-has-sat-lits nbalist sat-lits1)
                     (aignet::sat-lit-extension-p sat-lits sat-lits1))
                (equal (satlink::eval-cube
                        (nbalist-to-cube nbalist sat-lits1)
                        cnf-vals)
                       (bool->bit (aignet-pathcond-eval aignet nbalist invals regvals))
                       ;; (lit-eval lit invals regvals aignet)
                       )))
     :hints(("Goal" :use ((:instance cnf-for-aignet-implies-eval-nbalist-to-cube-of-aignet->cnf-vals-lemma))
             :in-theory (disable cnf-for-aignet-implies-eval-nbalist-to-cube-of-aignet->cnf-vals-lemma)))))

  (set-ignore-ok t)

  (local (in-theory (disable b-and)))

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
             interp-st-satlink-sat-check-core
             (:solve
              (b* ((aignet (logicman->aignet logicman))
                   (aignet-invals (alist-to-bitarr (aignet::num-ins aignet)
                                                   (gl-env->bfr-vals env) nil))
                   (cnf-vals (aignet::aignet->cnf-vals aignet-invals nil nil sat-lits aignet)))
                `(:use ((:instance satlink::sat-when-unsat
                         (formula ,(acl2::hq cnf))
                         (env ,(acl2::hq cnf-vals))
                         (config ,(acl2::hq config))
                        ;; (:instance aignet::cnf-for-aignet-implies-eval-formula
                        ;;  (cnf ,(acl2::hq (ipasir::ipasir$a->formula ipasir)))
                        ;;  (invals ,(acl2::hq aignet-invals))
                        ;;  (regvals nil)
                        ;;  (cnf-vals nil)
                        ;;  (sat-lits ,(acl2::hq sat-lits))
                        ;;  (aignet ,(acl2::hq aignet)))
                        ))
                  :in-theory (e/d (bfr-eval logicman-pathcond-eval)
                                  ;; (aignet::cnf-for-aignet-necc
                                  ;;  aignet::cnf-for-aignet-implies-eval-formula)
                                  )))))))
  


  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :logicman))
                  (not (equal (interp-st-field-fix key) :errmsg))
                  (not (equal (interp-st-field-fix key) :debug-info))
                  (not (equal (interp-st-field-fix key) :ctrex-env)))
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


(make-event
 `(define interp-st-satlink-sat-check-impl (params
                                            (bfr interp-st-bfr-p)
                                            (interp-st interp-st-bfrs-ok)
                                            state)
    :returns (mv (ans)
                 new-interp-st)
    (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
          ;; Skip the SAT check when not in aignet mode, for now.
          (mv bfr interp-st))
         ((when (interp-st->errmsg interp-st))
          (mv nil interp-st))
         ((unless (fgl-sat-config-p params))
          (gl-interp-error
           :msg (gl-msg "Malformed fgl-sat-check call: params was not resolved to a fgl-sat-config object"))))
      (interp-st-satlink-sat-check-core params bfr interp-st state))
    ///
    . ,*interp-st-sat-check-thms*))



(define logicman-satlink-counterexample (logicman
                                         env$)  ;; ctrex-env field
  :returns (mv err new-env$)
  (b* ((bfrstate (logicman->bfrstate)))
    (stobj-let ((aignet (logicman->aignet logicman)))
               (err env$)
               (stobj-let ((bitarr (env$->bitarr env$)))
                          (err bitarr)
                          (bfrstate-case
                            :aignet
                            (b* ((bitarr (resize-bits (aignet::num-fanins aignet) bitarr))
                                 (bitarr (aignet::aignet-eval bitarr aignet)))
                              (mv nil bitarr))
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


(define interp-st-satlink-counterexample ((interp-st interp-st-bfrs-ok)
                                         state)
  :returns (mv err new-interp-st)
  (declare (ignore state))
  (stobj-let ((logicman (interp-st->logicman interp-st))
              (env$ (interp-st->ctrex-env interp-st)))
             (err env$)
             (logicman-satlink-counterexample logicman env$)
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

(defmacro fgl-use-satlink-for-monolithic-sat ()
  '(progn (defattach interp-st-monolithic-sat-check interp-st-satlink-sat-check-impl)
          (defattach interp-st-monolithic-sat-counterexample interp-st-satlink-counterexample)))

(fgl-use-satlink-for-monolithic-sat)
