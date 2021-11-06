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

(include-book "design-fsm")
;; (include-book "cycle-compile")
(include-book "../svex/compose-theory-base")
(include-book "cycle-base")
;; (include-book "pipeline")
(include-book "assign")
(include-book "probe")
(include-book "../svex/alist-equiv")
(include-book "std/stobjs/nicestobj" :dir :system)

(local (include-book "std/util/termhints" :dir :system))
(local (defstub hq (x) nil))
(local (acl2::termhint-add-quotesym hq))

(local (include-book "std/lists/resize-list" :dir :System))
(local (in-theory (disable nth update-nth resize-list
                           acl2::resize-list-when-atom
                           hons-dups-p)))


(local (in-theory (enable stobjs::redundant-update-nth)))
;; (local (defthm redundant-update-nth-free
;;          (implies (and (equal v (nth n x))
;;                        (< (nfix n) (len x)))
;;                   (equal (update-nth n v x)
;;                          x))))

(local (defthm member-equal-is-booleanp
         (iff (member-equal k '(t nil))
              (booleanp k))))



(local (in-theory (disable member-equal)))
(local (std::add-default-post-define-hook :fix))




(defprod pipeline-setup
  ((probes svtv-probealist)
   (inputs svex-alistlist)
   (overrides svex-alistlist)
   (initst svex-alist)))

(defconst *svtv-data-nonstobj-fields*
  `((design :type (satisfies design-p)
            :pred design-p :fix design-fix :initially ,(make-design :top ""))

    (user-names :type (satisfies svtv-namemap-p)
                :pred svtv-namemap-p :fix svtv-namemap-fix)
    (namemap :type (satisfies svtv-name-lhs-map-p)
                :pred svtv-name-lhs-map-p :fix svtv-name-lhs-map-fix)
    (namemap-validp :type (member t nil) :pred booleanp :fix bool-fix)
;;     (moddb-validp :type (member t nil) :pred booleanp :fix bool-fix)

    
    (flatten :type (satisfies flatten-res-p) :pred flatten-res-p :fix flatten-res-fix
             :initially ,(make-flatten-res))
    (flatten-validp :type (member t nil) :pred booleanp :fix bool-fix)

    (flatnorm-setup :type (satisfies flatnorm-setup-p) :pred flatnorm-setup-p :fix flatnorm-setup-fix
                    :initially ,(make-flatnorm-setup))
    (flatnorm :type (satisfies flatnorm-res-p) :pred flatnorm-res-p :fix flatnorm-res-fix
              :initially ,(make-flatnorm-res))
    (flatnorm-validp :type (member t nil) :pred booleanp :fix bool-fix)


    (phase-fsm-setup :type (satisfies phase-fsm-config-p) :pred phase-fsm-config-p :fix phase-fsm-config-fix
                     :initially ,(make-phase-fsm-config
                                  :override-config (make-svtv-assigns-override-config-omit)))
    (phase-fsm :type (satisfies base-fsm-p) :pred base-fsm-p :fix base-fsm-fix
               :initially ,(make-base-fsm))
    (phase-fsm-validp :type (member t nil) :pred booleanp :fix bool-fix)

    (cycle-phases :type (satisfies svtv-cyclephaselist-p) :pred svtv-cyclephaselist-p :fix svtv-cyclephaselist-fix)
    (cycle-fsm :type (satisfies base-fsm-p) :pred base-fsm-p :fix base-fsm-fix
               :initially ,(make-base-fsm))
    (cycle-fsm-validp :type (member t nil) :pred booleanp :fix bool-fix)

    (pipeline-setup :type (satisfies pipeline-setup-p) :pred pipeline-setup-p :fix pipeline-setup-fix
                    :initially ,(make-pipeline-setup))
    (pipeline :type (satisfies svex-alist-p) :pred svex-alist-p :fix svex-alist-fix)
    (pipeline-validp :type (member t nil) :pred booleanp :fix bool-fix)
    ))

(make-event
 `(stobjs::defnicestobj svtv-data$c
    ,@*svtv-data-nonstobj-fields*

    (moddb :type moddb)
    (aliases :type aliases)))


(defsection svtv-data-field-defs
  (local (defun make-svtv-data-field-defs (fields)
           (declare (xargs :mode :program))
           (if (atom fields)
               nil
             (cons
              (b* ((name (caar fields)))
                (acl2::template-subst
                '(define svtv-data$a-><fieldname> (x)
                   :enabled t
                   (non-exec (svtv-data$c-><fieldname> x)))
                :str-alist `(("<FIELDNAME>" . ,(symbol-name name)))
                :pkg-sym 'sv-package))
              (make-svtv-data-field-defs (cdr fields))))))
  (make-event
   (cons 'progn (make-svtv-data-field-defs *svtv-data-nonstobj-fields*))))



  



(define svtv-data$c-flatten-okp (svtv-data$c
                                 (flatten flatten-res-p))
  :guard (modalist-addr-p (design->modalist (svtv-data$c->design svtv-data$c)))
  (non-exec
   (b* (((mv err res moddb aliases)
         (svtv-design-flatten (svtv-data$c->design svtv-data$c)
                              :moddb nil :aliases nil)))
     (and (not err)
          (equal (svtv-data$c->moddb svtv-data$c) moddb)
          (equal (svtv-data$c->aliases svtv-data$c) aliases)
          (equal (flatten-res-fix flatten) res))))
  ///
  (local (in-theory (enable svtv-design-flatten)))

  (defthm moddb-ok-when-flatten-okp
    (implies (svtv-data$c-flatten-okp svtv-data$c flatten)
             (let ((moddb (svtv-data$c->moddb svtv-data$c)))
               (and (moddb-mods-ok moddb)
                    (moddb-basics-ok moddb)))))

  (defthm moddb-index-when-flatten-okp
    (implies (svtv-data$c-flatten-okp svtv-data$c flatten)
             (b* ((moddb (svtv-data$c->moddb svtv-data$c))
                  (modidx (moddb-modname-get-index (design->top (svtv-data$c->design svtv-data$c)) moddb)))
               (and modidx
                    (natp modidx)))))


  (defthm moddb-totalwires-when-flatten-okp
    (implies (svtv-data$c-flatten-okp svtv-data$c flatten)
             (b* ((moddb (svtv-data$c->moddb svtv-data$c))
                  (aliases (svtv-data$c->aliases svtv-data$c))
                  (modidx (moddb-modname-get-index (design->top (svtv-data$c->design svtv-data$c)) moddb)))
               (<= (moddb-mod-totalwires modidx moddb)
                   (len aliases))))
    :rule-classes (:rewrite :linear))

  (defthm svarlist-bounded-p-when-flatten-okp
    (implies (svtv-data$c-flatten-okp svtv-data$c flatten)
             (b* ((moddb (svtv-data$c->moddb svtv-data$c))
                  (modidx (moddb-modname-get-index (design->top (svtv-data$c->design svtv-data$c)) moddb)))
               (svarlist-boundedp (flatten-res-vars flatten)
                                  (moddb-mod-totalwires modidx moddb))))
    :hints (("goal" :use ((:instance assigns-boundedp-of-svex-design-flatten
                           (x (svtv-data$c->design svtv-data$c)) (moddb nil) (aliases nil)))
             :in-theory (e/d (flatten-res-vars)
                             (assigns-boundedp-of-svex-design-flatten)))))

  (defthm svarlist-bounded-by-aliases-length-when-flatten-okp
    (implies (svtv-data$c-flatten-okp svtv-data$c flatten)
             (svarlist-boundedp (flatten-res-vars flatten)
                                (len (svtv-data$c->aliases svtv-data$c))))
    :hints (("goal" :use ((:instance assigns-boundedp-of-svex-design-flatten
                           (x (svtv-data$c->design svtv-data$c)) (moddb nil) (aliases nil)))
             :in-theory (e/d (flatten-res-vars)
                             (assigns-boundedp-of-svex-design-flatten)))))

  (acl2::def-updater-independence-thm svtv-data$c-flatten-okp-updater-independence
    (let ((new acl2::new) (old acl2::old))
      (implies (and (equal (svtv-data$c->design new)
                           (svtv-data$c->design old))
                    (equal (svtv-data$c->moddb new)
                           (svtv-data$c->moddb old))
                    (equal (svtv-data$c->aliases new)
                           (svtv-data$c->aliases old)))
               (equal (svtv-data$c-flatten-okp new flatten)
                      (svtv-data$c-flatten-okp old flatten))))))

(define svtv-data$a-flatten-okp (x (flatten flatten-res-p))
  :guard (modalist-addr-p (design->modalist (svtv-data$a->design x)))
  :enabled t
  :hooks nil
  (non-exec (svtv-data$c-flatten-okp x flatten)))



(define svtv-data$c-flatnorm-okp (svtv-data$c
                                  (flatnorm flatnorm-res-p))
  :guard (and (modalist-addr-p (design->modalist (svtv-data$c->design svtv-data$c)))
              (svtv-data$c-flatten-okp svtv-data$c (svtv-data$c->flatten svtv-data$c)))
  :enabled t
  (flatnorm-res-equiv flatnorm
                      (b* ((flatten (svtv-data$c->flatten svtv-data$c))
                           (setup (svtv-data$c->flatnorm-setup svtv-data$c)))
                        (stobj-let ((aliases (svtv-data$c->aliases svtv-data$c)))
                                   (assigns)
                                   (svtv-normalize-assigns flatten aliases setup)
                                   assigns)))
  ///
  
  (acl2::def-updater-independence-thm svtv-data$c-flatnorm-okp-updater-independence
    (let ((new acl2::new) (old acl2::old))
      (implies (and (equal (svtv-data$c->flatten new)
                           (svtv-data$c->flatten old))
                    (equal (svtv-data$c->aliases new)
                           (svtv-data$c->aliases old))
                    (equal (svtv-data$c->flatnorm-setup new)
                           (svtv-data$c->flatnorm-setup old)))
               (equal (svtv-data$c-flatnorm-okp new flatnorm)
                      (svtv-data$c-flatnorm-okp old flatnorm))))))

(define svtv-data$a-flatnorm-okp (x
                                  (flatnorm flatnorm-res-p))
  :guard (and (modalist-addr-p (design->modalist (svtv-data$a->design x)))
              (svtv-data$a-flatten-okp x (svtv-data$a->flatten x)))
  :enabled t
  :hooks nil
  (non-exec (svtv-data$c-flatnorm-okp x flatnorm)))




(define svtv-data$c-phase-fsm-okp (svtv-data$c (phase-fsm base-fsm-p))
  ;; :guard (and (modalist-addr-p (design->modalist (svtv-data$c->design svtv-data$c)))
  ;;             ;; (svtv-data$c-flatten-okp svtv-data$c (svtv-data$c->flatten svtv-data$c))
  ;;             )
  :enabled t
  (b* ((flatnorm ;; (b* ((flatten (svtv-data$c->flatten svtv-data$c))
                 ;;      (setup (svtv-data$c->flatnorm-setup svtv-data$c)))
                 ;;   (stobj-let ((aliases (svtv-data$c->aliases svtv-data$c)))
                 ;;              (assigns)
                 ;;              (svtv-normalize-assigns flatten aliases setup)
                 ;;              assigns))
        (svtv-data$c->flatnorm svtv-data$c))
       (config (svtv-data$c->phase-fsm-setup svtv-data$c)))
    (ec-call (phase-fsm-composition-p phase-fsm flatnorm config)))
  ///
  (defcong base-fsm-eval-equiv equal (svtv-data$c-phase-fsm-okp svtv-data$c phase-fsm) 2)

  (acl2::def-updater-independence-thm svtv-data$c-phase-fsm-okp-updater-independence
    (let ((new acl2::new) (old acl2::old))
      (implies (and (equal (svtv-data$c->flatnorm new)
                           (svtv-data$c->flatnorm old))
                    (equal (svtv-data$c->phase-fsm-setup new)
                           (svtv-data$c->phase-fsm-setup old)))
               (equal (svtv-data$c-phase-fsm-okp new phase-fsm)
                      (svtv-data$c-phase-fsm-okp old phase-fsm))))))


(define svtv-data$a-phase-fsm-okp (x (phase-fsm base-fsm-p))
  ;; :guard (and (modalist-addr-p (design->modalist (svtv-data$a->design x)))
  ;;             (svtv-data$a-flatten-okp x (svtv-data$a->flatten x)))
  :enabled t
  :hooks nil
  (non-exec (svtv-data$c-phase-fsm-okp x phase-fsm)))





;; (define svtv-data$c-phase-fsm-okp (svtv-data$c
;;                                   (values svex-alist-p)
;;                                   (nextstate svex-alist-p))
;;   :enabled t
;;   (b* (((mv err fsm moddb aliases)
;;         (non-exec (svtv-design-to-fsm (svtv-data$c->design svtv-data$c)
;;                                       :moddb nil :aliases nil)))
;;        ((when err) nil)
;;        ((svtv-fsm fsm)))
;;     (and (ec-call (svex-alist-eval-equiv values fsm.values))
;;          (ec-call (svex-alist-eval-equiv! nextstate fsm.nextstate))
;;          ;; (not (hons-dups-p (svex-alist-keys nextstate)))
;;          (equal (non-exec (svtv-data$c->moddb svtv-data$c)) moddb)
;;          (equal (non-exec (svtv-data$c->aliases svtv-data$c)) aliases))))

;; (define svtv-data$a-phase-fsm-okp (x
;;                                   (values svex-alist-p)
;;                                   (nextstate svex-alist-p))
;;   :enabled t
;;   (non-exec (svtv-data$c-phase-fsm-okp x values nextstate)))


(define svtv-data$c-namemap-okp (svtv-data$c (namemap svtv-name-lhs-map-p))
  :guard (and (modalist-addr-p (design->modalist (svtv-data$c->design svtv-data$c)))
              (svtv-data$c-flatten-okp svtv-data$c (svtv-data$c->flatten svtv-data$c)))
  (b* ((top (design->top (svtv-data$c->design svtv-data$c)))
       (names (svtv-data$c->user-names svtv-data$c)))
    (stobj-let ((moddb (svtv-data$c->moddb svtv-data$c))
                (aliases (svtv-data$c->aliases svtv-data$c)))
               (errs lhsmap)
               (svtv-namemap->lhsmap
                names
                (moddb-modname-get-index top moddb)
                moddb aliases)
               (and (not errs)
                    (svtv-name-lhs-map-equiv namemap
                                             lhsmap))))
  ///
  (acl2::def-updater-independence-thm svtv-data$c-namemap-okp-updater-independence
    (let ((new acl2::new) (old acl2::old))
      (implies (and (equal (svtv-data$c->user-names new)
                           (svtv-data$c->user-names old))
                    (equal (svtv-data$c->design new)
                           (svtv-data$c->design old))
                    (equal (svtv-data$c->moddb new)
                           (svtv-data$c->moddb old))
                    (equal (svtv-data$c->aliases new)
                           (svtv-data$c->aliases old)))
               (equal (svtv-data$c-namemap-okp new namemap)
                      (svtv-data$c-namemap-okp old namemap))))))

(define svtv-data$a-namemap-okp (x (namemap svtv-name-lhs-map-p))
  :enabled t
  :guard (and (modalist-addr-p (design->modalist (svtv-data$a->design x)))
              (svtv-data$a-flatten-okp x (svtv-data$a->flatten x)))
  :hooks nil
  (non-exec (svtv-data$c-namemap-okp x namemap)))




(defsection svtv-data$c-cycle-fsm-okp
  (defun-sk svtv-data$c-cycle-fsm-okp (svtv-data$c cycle-fsm)
    (declare (xargs :guard (base-fsm-p cycle-fsm)
                    :stobjs svtv-data$c))
    (forall env
            (non-exec
             (b* ((phase-fsm (svtv-data$c->phase-fsm svtv-data$c))
                  (phases (svtv-data$c->cycle-phases svtv-data$c))
                  (statevars (svex-alist-keys (base-fsm->nextstate phase-fsm)))
                  (prev-st (svex-env-extract statevars env))
                  ((base-fsm cycle-fsm)))
               (and (ec-call
                     (svex-envs-equivalent (svex-alist-eval cycle-fsm.values env)
                                           (svtv-cycle-eval-outs
                                            env prev-st phases phase-fsm)))
                    (ec-call
                     (svex-envs-equivalent (svex-alist-eval cycle-fsm.nextstate env)
                                           (svtv-cycle-eval-nextst
                                            env prev-st phases phase-fsm)))
                    (equal (svex-alist-keys cycle-fsm.nextstate) statevars)))))
    :rewrite :direct)

  (in-theory (disable svtv-data$c-cycle-fsm-okp))

  (defcong base-fsm-eval-equiv equal (svtv-data$c-cycle-fsm-okp svtv-data$c cycle-fsm) 2
    :hints (("goal" :cases ((svtv-data$c-cycle-fsm-okp svtv-data$c cycle-fsm)))
            (b* ((conc (assoc 'svtv-data$c-cycle-fsm-okp clause))
                 (other (if (eq (caddr conc) 'cycle-fsm)
                            'cycle-fsm-equiv
                          'cycle-fsm)))
              (and conc
                   `(:expand (,conc)
                     :use ((:instance svtv-data$c-cycle-fsm-okp-necc
                            (cycle-fsm ,other)
                            (env (svtv-data$c-cycle-fsm-okp-witness . ,(cdr conc)))))
                     :in-theory (disable svtv-data$c-cycle-fsm-okp-necc))))))


  (defthm cycle-fsm-okp-when-equivalent-fsm
    (implies (svtv-data$c-cycle-fsm-okp svtv-data cycle-fsm1)
             (iff (svtv-data$c-cycle-fsm-okp svtv-data cycle-fsm)
                  (base-fsm-eval-equiv cycle-fsm1 cycle-fsm)))
    :hints((acl2::use-termhint
            (and (svtv-data$c-cycle-fsm-okp svtv-data cycle-fsm)
                 (b* (((base-fsm cycle-fsm))
                      ((base-fsm cycle-fsm1)))
                   (if (svex-alist-eval-equiv cycle-fsm1.values cycle-fsm.values)
                       (b* ((witness (svex-alist-eval-equiv-envs-equivalent-witness cycle-fsm1.nextstate cycle-fsm.nextstate)))
                         `(:use ((:instance svex-envs-equivalent-implies-alist-eval-equiv
                                  (x ,(hq cycle-fsm1.nextstate)) (y ,(hq cycle-fsm.nextstate)))
                                 (:instance svtv-data$c-cycle-fsm-okp-necc
                                  (svtv-data$c svtv-data) (cycle-fsm cycle-fsm1)
                                  (env ,(hq witness)))
                                 (:instance svtv-data$c-cycle-fsm-okp-necc
                                  (svtv-data$c svtv-data) (cycle-fsm cycle-fsm)
                                  (env ,(hq witness))))
                           :in-theory (e/d (svex-alist-eval-equiv!-when-svex-alist-eval-equiv
                                            base-fsm-eval-equiv)
                                           (svtv-data$c-cycle-fsm-okp-necc))))
                     (b* ((witness (svex-alist-eval-equiv-envs-equivalent-witness cycle-fsm1.values cycle-fsm.values)))
                       `(:use ((:instance svex-envs-equivalent-implies-alist-eval-equiv
                                (x ,(hq cycle-fsm1.values)) (y ,(hq cycle-fsm.values)))
                               (:instance svtv-data$c-cycle-fsm-okp-necc
                                (svtv-data$c svtv-data) (cycle-fsm cycle-fsm1)
                                (env ,(hq witness)))
                               (:instance svtv-data$c-cycle-fsm-okp-necc
                                (svtv-data$c svtv-data) (cycle-fsm cycle-fsm)
                                (env ,(hq witness))))
                         :in-theory (e/d (base-fsm-eval-equiv)
                                         (svtv-data$c-cycle-fsm-okp-necc))))))))))

  (acl2::def-updater-independence-thm cycle-fsm-okp-updater-independence
    (let ((new acl2::new) (old acl2::old))
      (implies (and (base-fsm-eval-equiv (svtv-data$c->phase-fsm new)
                                         (svtv-data$c->phase-fsm old))
                    (equal (svtv-data$c->cycle-phases new)
                           (svtv-data$c->cycle-phases old)))
               (equal (svtv-data$c-cycle-fsm-okp new cycle-fsm)
                      (svtv-data$c-cycle-fsm-okp old cycle-fsm))))
    :hints (("goal" :cases ((svtv-data$c-cycle-fsm-okp acl2::new cycle-fsm)))
            (acl2::use-termhint
             (b* ((new acl2::new) (old acl2::old)
                  ((mv ok-data notok-data)
                   (if (svtv-data$c-cycle-fsm-okp new cycle-fsm)
                       (mv new old)
                     (mv old new)))
                  (witness (svtv-data$c-cycle-fsm-okp-witness notok-data cycle-fsm)))
               `(:expand ((svtv-data$c-cycle-fsm-okp ,(hq notok-data) cycle-fsm))
                 :use ((:instance svtv-data$c-cycle-fsm-okp-necc
                        (svtv-data$c ,(hq ok-data))
                        (env ,(hq witness))))
                 :in-theory (disable svtv-data$c-cycle-fsm-okp-necc)))))))
                  
(define svtv-data$a-cycle-fsm-okp (x (cycle-fsm base-fsm-p))
  :enabled t
  :hooks nil
  (non-exec (svtv-data$c-cycle-fsm-okp x cycle-fsm)))

(defsection svtv-data$c-pipeline-okp
  (defun-sk svtv-data$c-pipeline-okp (svtv-data$c results)
    (declare (xargs :guard (svex-alist-p results)
                    :stobjs svtv-data$c))
    (forall env
            (non-exec
             (b* ((fsm (svtv-data$c->cycle-fsm svtv-data$c))
                  (rename-fsm (make-svtv-fsm :base-fsm fsm
                                             ;; :design (svtv-data$c->design svtv-data$c)
                                             ;; :user-names (svtv-data$c->user-names svtv-data$c)
                                             :namemap (svtv-data$c->namemap svtv-data$c)))
                  ((pipeline-setup pipe) (svtv-data$c->pipeline-setup svtv-data$c))
                  (run (svtv-fsm-run
                        (svex-alistlist-eval pipe.inputs env)
                        (svex-alistlist-eval pipe.overrides env)
                        (svex-alist-eval pipe.initst env)
                        rename-fsm (svtv-probealist-outvars pipe.probes))))
               (and (equal (svex-alist-keys pipe.initst)
                           (svex-alist-keys (base-fsm->nextstate fsm)))
                    (ec-call
                     (svex-envs-equivalent
                      (svex-alist-eval results env)
                      (svtv-probealist-extract pipe.probes run)))))))
    :rewrite :direct)

  (in-theory (disable svtv-data$c-pipeline-okp))

  (defcong svex-alist-eval-equiv equal (svtv-data$c-pipeline-okp svtv-data$c results) 2
    :hints (("goal" :cases ((svtv-data$c-pipeline-okp svtv-data$c results)))
            (b* ((conc (assoc 'svtv-data$c-pipeline-okp clause))
                 (other (if (eq (caddr conc) 'results)
                            'results-equiv
                          'results)))
              (and conc
                   `(:expand (,conc)
                     :use ((:instance svtv-data$c-pipeline-okp-necc
                            (results ,other)
                            (env (svtv-data$c-pipeline-okp-witness . ,(cdr conc)))))
                     :in-theory (disable svtv-data$c-pipeline-okp-necc))))))

  (acl2::def-updater-independence-thm pipeline-okp-updater-independence
    (let ((new acl2::new) (old acl2::old))
      (implies (and (base-fsm-eval-equiv (svtv-data$c->cycle-fsm new)
                                         (svtv-data$c->cycle-fsm old))
                    (equal (svtv-data$c->pipeline-setup new)
                           (svtv-data$c->pipeline-setup old))
                    (equal (svtv-data$c->namemap new)
                           (svtv-data$c->namemap old)))
               (equal (svtv-data$c-pipeline-okp new results)
                      (svtv-data$c-pipeline-okp old results))))
    :hints (("goal" :cases ((svtv-data$c-pipeline-okp acl2::new results)))
            (acl2::use-termhint
             (b* ((new acl2::new) (old acl2::old)
                  ((mv ok-data notok-data)
                   (if (svtv-data$c-pipeline-okp new results)
                       (mv new old)
                     (mv old new)))
                  (witness (svtv-data$c-pipeline-okp-witness notok-data results)))
               `(:expand ((svtv-data$c-pipeline-okp ,(hq notok-data) results))
                 :use ((:instance svtv-data$c-pipeline-okp-necc
                        (svtv-data$c ,(hq ok-data))
                        (env ,(hq witness))))
                 :in-theory (disable svtv-data$c-pipeline-okp-necc)))))))
  

;; (define svtv-data$c-pipeline-okp (svtv-data$c (results svex-alist-p))
;;   :enabled t
;;   (non-exec
;;    (b* ((fsm (svtv-data$c->cycle-fsm svtv-data$c))
;;         (probes (svtv-data$c->pipeline-probes svtv-data$c))
;;         (result
;;          (svtv-probealist-extract-alist
;;           probes
;;           (svtv-fsm-run-compile
;;            (svtv-data$c->pipeline-inputs svtv-data$c)
;;            (svtv-data$c->pipeline-overrides svtv-data$c)
;;            (svtv-data$c->pipeline-initst svtv-data$c)
;;            fsm
;;            (svtv-probealist-outvars probes) nil))))
;;      (ec-call (svex-alist-eval-equiv results result)))))


(define svtv-data$a-pipeline-okp (x (results svex-alist-p))
  :enabled t :hooks nil
  (non-exec (svtv-data$c-pipeline-okp x results)))


(define svtv-data$ap (x)
  (non-exec
   (and ;; (svtv-data$cp x)
    (modalist-addr-p (design->modalist (svtv-data$c->design x)))
    (implies (svtv-data$c->flatten-validp x)
             (svtv-data$c-flatten-okp x (svtv-data$c->flatten x)))
    (implies (svtv-data$c->flatnorm-validp x)
             (svtv-data$c-flatnorm-okp x (svtv-data$c->flatnorm x)))

    (implies (svtv-data$c->namemap-validp x)
             (svtv-data$c-namemap-okp x (svtv-data$c->namemap x)))

    (implies (svtv-data$c->phase-fsm-validp x)
             (svtv-data$c-phase-fsm-okp x (svtv-data$c->phase-fsm x)))

    (implies (svtv-data$c->cycle-fsm-validp x)
             (ec-call
              (svtv-data$c-cycle-fsm-okp x (svtv-data$c->cycle-fsm x))))

    (implies (svtv-data$c->pipeline-validp x)
             (ec-call
              (svtv-data$c-pipeline-okp x (svtv-data$c->pipeline x))))))
  ///
  (defthm svtv-data$ap-implies-modalist-addr-p
    (implies (svtv-data$ap x)
             (svarlist-addr-p (modalist-vars (design->modalist (svtv-data$c->design x))))))

  (defthm svtv-data$ap-implies-flatten-okp
    (implies (and (svtv-data$ap x)
                  (svtv-data$c->flatten-validp x))
             (svtv-data$c-flatten-okp x (svtv-data$c->flatten x))))

  (defthm svtv-data$ap-implies-flatnorm-okp
    (implies (and (svtv-data$ap x)
                  ;; (svtv-data$c->flatten-validp x)
                  (svtv-data$c->flatnorm-validp x))
             (svtv-data$c-flatnorm-okp x (svtv-data$c->flatnorm x))))

  (defthm svtv-data$ap-implies-namemap-okp
    (implies (and (svtv-data$ap x)
                  ;; (svtv-data$c->flatten-validp x)
                  (svtv-data$c->namemap-validp x))
             (svtv-data$c-namemap-okp x (svtv-data$c->namemap x))))

  (defthm svtv-data$ap-implies-phase-fsm-okp
    (implies (and (svtv-data$ap x)
                  ;; (svtv-data$c->flatten-validp x)
                  (svtv-data$c->phase-fsm-validp x))
             (svtv-data$c-phase-fsm-okp x (svtv-data$c->phase-fsm x))))

  (defthm svtv-data$ap-implies-cycle-fsm-okp
    (implies (and (svtv-data$ap x)
                  ;; (svtv-data$c->flatten-validp x)
                  (svtv-data$c->cycle-fsm-validp x))
             (svtv-data$c-cycle-fsm-okp x (svtv-data$c->cycle-fsm x))))

  (defthm svtv-data$ap-implies-pipeline-okp
    (implies (and (svtv-data$ap x)
                  ;; (svtv-data$c->flatten-validp x)
                  (svtv-data$c->pipeline-validp x))
             (svtv-data$c-pipeline-okp x (svtv-data$c->pipeline x))))

  (defthm no-duplicatesp-nextstate-keys-of-svtv-data->phase-fsm
    (implies (and (svtv-data$ap x)
                  (svtv-data$a->phase-fsm-validp x)
                  (svtv-data$a->flatnorm-validp x)
                  )
             (no-duplicatesp-equal
              (svex-alist-keys (base-fsm->nextstate (svtv-data$c->phase-fsm x)))))
    :hints(("Goal" :in-theory (e/d (svtv-data$ap)
                                   (no-duplicate-nextstates-of-svtv-compose-assigns/delays))
            :use ((:instance no-duplicate-nextstates-of-svtv-compose-assigns/delays
                   (flatnorm (svtv-normalize-assigns (svtv-data$c->flatten x)
                                                     (svtv-data$c->aliases x)
                                                     (svtv-data$c->flatnorm-setup x))))))))

  (defthm moddb-ok-when-svtv-data$ap
    (implies (and (svtv-data$ap x)
                  (svtv-data$c->flatten-validp x))
             (and (moddb-basics-ok (svtv-data$c->moddb x))
                  (moddb-mods-ok (svtv-data$c->moddb x))))
    :hints(("Goal" :in-theory (e/d (svtv-data$c-flatten-okp)
                                   (svtv-data$ap-implies-flatten-okp
                                    svtv-data$ap))
            :use svtv-data$ap-implies-flatten-okp)))

  (defthm moddb-index-when-svtv-data$ap
    (implies (and (svtv-data$ap x)
                  (svtv-data$c->flatten-validp x))
             (b* ((moddb (svtv-data$c->moddb x))
                  (modidx (moddb-modname-get-index (design->top (svtv-data$c->design x)) moddb)))
               (and modidx
                    (natp modidx))))
    :hints(("Goal" :in-theory (e/d (svtv-data$c-flatten-okp)
                                   (svtv-data$ap-implies-flatten-okp
                                    svtv-data$ap))
            :use svtv-data$ap-implies-flatten-okp))
    :rule-classes (:rewrite :type-prescription))


  (defthm moddb-totalwires-when-svtv-data$ap
    (implies (and (svtv-data$ap x)
                  (svtv-data$c->flatten-validp x))
             (b* ((moddb (svtv-data$c->moddb x))
                  (aliases (svtv-data$c->aliases x))
                  (modidx (moddb-modname-get-index (design->top (svtv-data$c->design x)) moddb)))
               (<= (moddb-mod-totalwires modidx moddb)
                   (len aliases))))
    :hints(("Goal" :in-theory (e/d (svtv-data$c-flatten-okp)
                                   (svtv-data$ap-implies-flatten-okp
                                    svtv-data$ap))
            :use svtv-data$ap-implies-flatten-okp))
    :rule-classes (:rewrite :linear)))





                    
                 
;; (define svtv-data$c-compute-phase-fsm (svtv-data$c)
;;   :guard (and (not (svtv-data$c->namemap-validp svtv-data$c))
;;               (not (svtv-data$c->cycle-fsm-validp svtv-data$c))
;;               (not (svtv-data$c->pipeline-validp svtv-data$c))
;;               (modalist-addr-p (design->modalist (svtv-data$c->design svtv-data$c))))
;;   :returns (mv errmsg new-svtv-data$c)
;;   (b* ((design (svtv-data$c->design svtv-data$c)))
;;     (stobj-let ((moddb (svtv-data$c->moddb svtv-data$c))
;;                 (aliases (svtv-data$c->aliases svtv-data$c)))
;;                (err fsm moddb aliases)
;;                (svtv-design-to-fsm design)
;;                (b* (((when err) (mv err svtv-data$c))
;;                     ((svtv-fsm fsm))
;;                     (svtv-data$c (update-svtv-data$c->base-values fsm.values svtv-data$c))
;;                     (svtv-data$c (update-svtv-data$c->base-nextstate fsm.nextstate svtv-data$c))
;;                     (svtv-data$c (update-svtv-data$c->phase-fsm-validp t svtv-data$c)))
;;                  (mv nil svtv-data$c))))
;;   ///
;;   (defret svtv-data$c-get-of-<fn>
;;     (implies (and (equal key (svtv-data$c-field-fix k))
;;                   (not (equal key :moddb))
;;                   (not (equal key :aliases))
;;                   (not (equal key :base-values))
;;                   (not (equal key :base-nextstate))
;;                   (not (equal key :phase-fsm-validp)))
;;              (equal (svtv-data$c-get k new-svtv-data$c)
;;                     (svtv-data$c-get key svtv-data$c))))

;;   (defret phase-fsm-validp-of-<fn>
;;     (implies (not errmsg)
;;              (svtv-data$c->phase-fsm-validp new-svtv-data$c))))



;; (define svtv-data$a-compute-phase-fsm ((x svtv-data$ap))
;;   :guard (and (not (svtv-data$a->namemap-validp x))
;;               (not (svtv-data$a->cycle-fsm-validp x))
;;               (not (svtv-data$a->pipeline-validp x)))
;;   :enabled t
;;   (b* (((mv a b) (non-exec (svtv-data$c-compute-phase-fsm x))))
;;     (mv a b)))




(defthm svtv-data$ap-of-update-design
  (implies (and (svtv-data$ap x)
                (not (svtv-data$c->flatten-validp x))
                (not (svtv-data$c->namemap-validp x))
                (modalist-addr-p (design->modalist design)))
           (svtv-data$ap (update-svtv-data$c->design design x)))
  :hints(("Goal" :expand ((svtv-data$ap (update-svtv-data$c->design design x))))))

(define update-svtv-data$a->design ((design design-p) x)
  :guard (and (not (svtv-data$a->flatten-validp x))
              (not (svtv-data$a->namemap-validp x))
              (modalist-addr-p (design->modalist design)))
  :enabled t
  :hooks nil
  (non-exec (update-svtv-data$c->design design x)))



(defthm update-flatten-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (and (or (not (svtv-data$a->flatten-validp x))
                         (svtv-data$a-flatten-okp x flatten))
                     (not (svtv-data$a->namemap-validp x))
                     (not (svtv-data$a->flatnorm-validp x))
                     ;; (not (svtv-data$a->phase-fsm-validp x))
                     ;; (not (svtv-data$a->cycle-fsm-validp x))
                     ;; (not (svtv-data$a->pipeline-validp x))
                     ))
           (svtv-data$ap (update-svtv-data$c->flatten flatten x)))
  :hints(("Goal" :expand ((svtv-data$ap (update-svtv-data$c->flatten flatten x))))))

(define update-svtv-data$a->flatten ((flatten flatten-res-p) (x svtv-data$ap))
  :guard 
  (and (or (not (svtv-data$a->flatten-validp x))
           (svtv-data$a-flatten-okp x flatten))
       (not (svtv-data$a->namemap-validp x))
       (not (svtv-data$a->flatnorm-validp x)))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->flatten flatten x)))

(defthm update-flatten-validp-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (or (not validp)
                    (svtv-data$a->flatten-validp x)
                    (and (svtv-data$a-flatten-okp x (svtv-data$a->flatten x))
                         (not (svtv-data$a->namemap-validp x))
                         (not (svtv-data$a->flatnorm-validp x))
                         ;; (not (svtv-data$a->phase-fsm-validp x))
                         ;; (not (svtv-data$a->cycle-fsm-validp x))
                         ;; (not (svtv-data$a->pipeline-validp x))
                         )))
           (svtv-data$ap (update-svtv-data$c->flatten-validp validp x)))
  :hints (("goal" :expand ((:free (validp) (svtv-data$ap (update-svtv-data$c->flatten-validp validp x))))))
  :otf-flg t)

(define update-svtv-data$a->flatten-validp ((validp booleanp) (x svtv-data$ap))
  :guard (or (not validp)
             (svtv-data$a->flatten-validp x)
             (and (svtv-data$a-flatten-okp x (svtv-data$a->flatten x))
                  (not (svtv-data$a->namemap-validp x))
                  (not (svtv-data$a->flatnorm-validp x))
                  ;; (not (svtv-data$a->phase-fsm-validp x))
                  ;; (not (svtv-data$a->cycle-fsm-validp x))
                  ;; (not (svtv-data$a->pipeline-validp x))
                  ))
  
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->flatten-validp validp x)))


(defthm update-flatnorm-setup-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (not (svtv-data$a->flatnorm-validp x))
                ;; (not (svtv-data$a->phase-fsm-validp x))
                )
           (svtv-data$ap (update-svtv-data$c->flatnorm-setup flatnorm-setup x)))
  :hints(("Goal" :expand ((svtv-data$ap (update-svtv-data$c->flatnorm-setup flatnorm-setup x))))))


(define update-svtv-data$a->flatnorm-setup ((flatnorm-setup flatnorm-setup-p) x)
  :guard (and (not (svtv-data$a->flatnorm-validp x)))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->flatnorm-setup flatnorm-setup x)))

(defthm update-flatnorm-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (or (not (svtv-data$a->flatnorm-validp x))
                    (svtv-data$a-flatnorm-okp x flatnorm))
                (not (svtv-data$a->phase-fsm-validp x)))
           (svtv-data$ap (update-svtv-data$c->flatnorm flatnorm x)))
  :hints(("Goal" :expand ((svtv-data$ap (update-svtv-data$c->flatnorm flatnorm x))))))

(define update-svtv-data$a->flatnorm ((flatnorm flatnorm-res-p) (x svtv-data$ap))
  :guard (and (or (not (svtv-data$a->flatnorm-validp x))
                  (ec-call (svtv-data$a-flatnorm-okp x flatnorm)))
              (not (svtv-data$a->phase-fsm-validp x)))
  ;; :guard-hints ((and stable-under-simplificationp '(:in-theory (enable svtv-data$ap))))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->flatnorm flatnorm x)))

(defthm update-flatnorm-validp-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (or (not validp)
                    (svtv-data$a-flatnorm-okp x (svtv-data$a->flatnorm x))))
           (svtv-data$ap (update-svtv-data$c->flatnorm-validp validp x)))
  :hints(("Goal" :expand ((:free (validp) (svtv-data$ap (update-svtv-data$c->flatnorm-validp validp x)))))))

(define update-svtv-data$a->flatnorm-validp ((validp booleanp) (x svtv-data$ap))
  :guard (or (not validp)
             (ec-call (svtv-data$a-flatnorm-okp x (svtv-data$a->flatnorm x))))
  ;; :guard-hints ((and stable-under-simplificationp '(:in-theory (enable svtv-data$ap))))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->flatnorm-validp validp x)))


(defthm update-phase-fsm-setup-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (not (svtv-data$a->phase-fsm-validp x))
                ;; (not (svtv-data$a->phase-fsm-validp x))
                )
           (svtv-data$ap (update-svtv-data$c->phase-fsm-setup phase-fsm-setup x)))
  :hints(("Goal" :expand ((svtv-data$ap (update-svtv-data$c->phase-fsm-setup phase-fsm-setup x))))))


(define update-svtv-data$a->phase-fsm-setup ((phase-fsm-setup phase-fsm-config-p) x)
  :guard (and (not (svtv-data$a->phase-fsm-validp x)))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->phase-fsm-setup phase-fsm-setup x)))




(defthm update-phase-fsm-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (or (not (svtv-data$a->cycle-fsm-validp x))
                    (base-fsm-eval-equiv phase-fsm (svtv-data$c->phase-fsm x)))
                (or (not (svtv-data$c->phase-fsm-validp x))
                    (svtv-data$c-phase-fsm-okp x phase-fsm)))
           (svtv-data$ap (update-svtv-data$c->phase-fsm phase-fsm x)))
  :hints(("Goal" :expand ((svtv-data$ap (update-svtv-data$c->phase-fsm phase-fsm x)))
          :use ((:instance svtv-data$ap-implies-phase-fsm-okp))
          :in-theory (disable svtv-data$ap-implies-phase-fsm-okp))))

(define update-svtv-data$a->phase-fsm ((phase-fsm base-fsm-p) (x svtv-data$ap))
  :guard (and (or (not (svtv-data$a->cycle-fsm-validp x))
                  (base-fsm-eval-equiv phase-fsm (svtv-data$a->phase-fsm x)))
              (or (not (svtv-data$a->phase-fsm-validp x))
                  (ec-call (svtv-data$a-phase-fsm-okp x phase-fsm))))
  ;; :guard-hints ((and stable-under-simplificationp '(:in-theory (enable svtv-data$ap))))  
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->phase-fsm phase-fsm x)))

(defthm update-phase-fsm-validp-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (or (not validp)
                    (svtv-data$a->phase-fsm-validp x)
                    (and (svtv-data$a-phase-fsm-okp x (svtv-data$a->phase-fsm x))
                         (not (svtv-data$a->cycle-fsm-validp x)))))
           (svtv-data$ap (update-svtv-data$c->phase-fsm-validp validp x)))
  :hints(("Goal" :expand ((:free (validp) (svtv-data$ap (update-svtv-data$c->phase-fsm-validp validp x)))))))

(define update-svtv-data$a->phase-fsm-validp ((validp booleanp) (x svtv-data$ap))
  :guard (or (not validp)
             (svtv-data$a->phase-fsm-validp x)
             (and (ec-call (svtv-data$a-phase-fsm-okp x (svtv-data$a->phase-fsm x)))
                  (not (svtv-data$a->cycle-fsm-validp x))))
  ;; :guard-hints ((and stable-under-simplificationp '(:in-theory (enable svtv-data$ap))))                
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->phase-fsm-validp validp x)))
  
(defthm update-user-names-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (not (svtv-data$a->namemap-validp x)))
           (svtv-data$ap (update-svtv-data$c->user-names user-names x)))
  :hints(("Goal" :expand ((svtv-data$ap (update-svtv-data$c->user-names user-names x))))))

(define update-svtv-data$a->user-names ((names svtv-namemap-p) x)
  :guard (not (svtv-data$a->namemap-validp x))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->user-names names x)))

(defthm update-namemap-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (if (svtv-data$a->namemap-validp x)
                    (svtv-data$a-namemap-okp x namemap)
                  (not (svtv-data$a->pipeline-validp x))))
           (svtv-data$ap (update-svtv-data$c->namemap namemap x)))
  :hints(("Goal" :expand ((svtv-data$ap (update-svtv-data$c->namemap namemap x)))
          :in-theory (e/d (svtv-data$c-namemap-okp)
                          (svtv-data$ap-implies-namemap-okp))
          :use ((:instance svtv-data$ap-implies-namemap-okp)))))

(define update-svtv-data$a->namemap ((namemap svtv-name-lhs-map-p) x)
  :guard (if (svtv-data$a->namemap-validp x)
             (ec-call (svtv-data$a-namemap-okp x namemap))
           (not (svtv-data$a->pipeline-validp x)))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->namemap namemap x)))

(defthm update-namemap-validp-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (or (not validp)
                    (svtv-data$a-namemap-okp x (svtv-data$a->namemap x))))
           (svtv-data$ap (update-svtv-data$c->namemap-validp validp x)))
  :hints(("Goal" :expand ((:free (validp) (svtv-data$ap (update-svtv-data$c->namemap-validp validp x))))
          :in-theory (e/d (svtv-data$c-namemap-okp)
                          (svtv-data$ap-implies-namemap-okp))
          :use ((:instance svtv-data$ap-implies-namemap-okp)))))

(define update-svtv-data$a->namemap-validp ((validp booleanp) (x svtv-data$ap))
  :guard (or (not validp)
             (ec-call (svtv-data$a-namemap-okp x (svtv-data$a->namemap x))))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->namemap-validp validp x)))


(defthm update-cycle-phases-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (not (svtv-data$a->cycle-fsm-validp x)))
           (svtv-data$ap (update-svtv-data$c->cycle-phases phases x)))
  :hints(("Goal" 
          :expand ((svtv-data$ap (update-svtv-data$c->cycle-phases phases x))))))

(define update-svtv-data$a->cycle-phases ((phases svtv-cyclephaselist-p) x)
  :guard (not (svtv-data$a->cycle-fsm-validp x))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->cycle-phases phases x)))

(defthm update-cycle-fsm-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (if (svtv-data$c->cycle-fsm-validp x)
                    (svtv-data$c-cycle-fsm-okp x cycle-fsm)
                  (not (svtv-data$c->pipeline-validp x))))
           (svtv-data$ap (update-svtv-data$c->cycle-fsm cycle-fsm x)))
  :hints(("Goal" :expand ((svtv-data$ap (update-svtv-data$c->cycle-fsm cycle-fsm x))))
         (and stable-under-simplificationp
              '(:in-theory (e/d (SVTV-DATA$C-CYCLE-FSM-OKP)
                                (svtv-data$ap-implies-cycle-fsm-okp))
                :use svtv-data$ap-implies-cycle-fsm-okp))))

(define update-svtv-data$a->cycle-fsm ((cycle-fsm base-fsm-p) (x svtv-data$ap))
  :guard (if (svtv-data$a->cycle-fsm-validp x)
             (svtv-data$a-cycle-fsm-okp x cycle-fsm)
           (not (svtv-data$a->pipeline-validp x)))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->cycle-fsm cycle-fsm x)))


(defthm update-cycle-fsm-validp-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (or (not validp)
                    (and (svtv-data$a-cycle-fsm-okp x (svtv-data$a->cycle-fsm x))
                         (not (svtv-data$a->pipeline-validp x)))))
           (svtv-data$ap (update-svtv-data$c->cycle-fsm-validp validp x)))
  :hints(("Goal" :expand ((:free (validp) (svtv-data$ap (update-svtv-data$c->cycle-fsm-validp validp x)))))))

(define update-svtv-data$a->cycle-fsm-validp ((validp booleanp) (x svtv-data$ap))
  :guard (or (not validp)
             (and (svtv-data$a-cycle-fsm-okp x (svtv-data$a->cycle-fsm x))
                  (not (svtv-data$a->pipeline-validp x))))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->cycle-fsm-validp validp x)))


(defthm update-pipeline-setup-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (not (svtv-data$a->pipeline-validp x)))
           (svtv-data$ap (update-svtv-data$c->pipeline-setup pipeline-setup x)))
  :hints(("Goal" :expand ((svtv-data$ap (update-svtv-data$c->pipeline-setup pipeline-setup x))))))


(define update-svtv-data$a->pipeline-setup ((pipeline-setup pipeline-setup-p) x)
  :guard (not (svtv-data$a->pipeline-validp x))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->pipeline-setup pipeline-setup x)))


(defthm update-pipeline-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (or (not (svtv-data$a->pipeline-validp x))
                    (svtv-data$a-pipeline-okp x pipeline)))
           (svtv-data$ap (update-svtv-data$c->pipeline pipeline x)))
  :hints(("Goal" :expand ((svtv-data$ap (update-svtv-data$c->pipeline pipeline x))))))

(define update-svtv-data$a->pipeline ((pipeline svex-alist-p) (x svtv-data$ap))
  :guard (or (not (svtv-data$a->pipeline-validp x))
             (svtv-data$a-pipeline-okp x pipeline))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->pipeline pipeline x)))


(defthm update-pipeline-validp-preserves-svtv-data$ap
  (implies (and (svtv-data$ap x)
                (or (not validp)
                    (svtv-data$a-pipeline-okp x (svtv-data$a->pipeline x))))
           (svtv-data$ap (update-svtv-data$c->pipeline-validp validp x)))
  :hints(("Goal" :expand ((:free (validp) (svtv-data$ap (update-svtv-data$c->pipeline-validp validp x)))))))

(define update-svtv-data$a->pipeline-validp ((validp booleanp) (x svtv-data$ap))
  :guard (or (not validp)
             (svtv-data$a-pipeline-okp x (svtv-data$a->pipeline x)))
  :enabled t :hooks nil
  (non-exec (update-svtv-data$c->pipeline-validp validp x)))






;; (local (in-theory (disable hons-dups-p)))

;; (define svtv-data$c-compute-cycle (svtv-data$c)
;;   :guard (and (not (svtv-data$c->cycle-fsm-validp svtv-data$c))
;;               (no-duplicatesp-equal (svex-alist-keys (svtv-fsm->nextstate (svtv-data$c->phase-fsm svtv-data$c)))))
;;   (b* ((fsm (svtv-data$c->phase-fsm svtv-data$c))
;;        (phases (svtv-data$c->cycle-phases svtv-data$c))
;;        ((svtv-fsm cycle-fsm) (svtv-fsm-to-cycle phases fsm))
;;        (svtv-data$c (update-svtv-data$c->cycle-values cycle-fsm.values svtv-data$c))
;;        (svtv-data$c (update-svtv-data$c->cycle-nextstate cycle-fsm.nextstate svtv-data$c)))
;;     (update-svtv-data$c->cycle-fsm-validp t svtv-data$c)))


;; (define svtv-data$a-compute-cycle ((x svtv-data$ap))
;;   :guard (and (not (svtv-data$a->cycle-fsm-validp x))
;;               (svtv-data$a->phase-fsm-validp x))
;;   :enabled t :hooks nil
;;   (non-exec (svtv-data$c-compute-cycle x)))





                    
(defsection svtv-data$ap-of-create-svtv-data
  (local (defun svtv-data-field-names (fields)
           (declare (xargs :mode :program))
           (if (atom fields)
               nil
             (append
              (b* ((name (caar fields)))
                (acl2::template-subst
                 '(svtv-data$c-><fieldname>
                   svtv-data$c-><fieldname>^)
                 :str-alist `(("<FIELDNAME>" . ,(symbol-name name)))
                 :pkg-sym 'sv-package))
              (svtv-data-field-names (cdr fields))))))
  (make-event
   `(defthm svtv-data$ap-of-create-svtv-data
      (svtv-data$ap (create-svtv-data$c))
      :hints(("Goal" :in-theory (e/d (create-svtv-data$c
                                      svtv-data$ap
                                      . ,(svtv-data-field-names *svtv-data-nonstobj-fields*))
                                     ((create-svtv-data$c)
                                      create-moddb)))))))

(define create-svtv-data$a ()
  :enabled t
  (non-exec (create-svtv-data$c)))



(define svtv-data$a->moddb ((x svtv-data$ap))
  :enabled t
  (non-exec (svtv-data$c->moddb x)))

(define svtv-data$a->aliases ((x svtv-data$ap))
  :enabled t
  (non-exec (svtv-data$c->aliases x)))

(encapsulate nil
  (defthm moddb-when-flatten-okp
    (implies (svtv-data$c-flatten-okp x flatten)
             (equal (svtv-data$c->moddb x)
                    (mv-nth 2 (svtv-design-flatten
                               (svtv-data$c->design x)
                               :moddb nil :aliases nil))))
    :hints(("Goal" :in-theory (enable svtv-data$c-flatten-okp))))

  (defthm update-moddb-preserves-svtv-data$ap
    (implies (and (svtv-data$ap x)
                  (and (or (not (svtv-data$a->flatten-validp x))
                           (equal moddb
                                  (mv-nth 2 (svtv-design-flatten (svtv-data$c->design x)
                                                                 :moddb nil :aliases nil))))
                       (not (svtv-data$a->namemap-validp x))))
             (svtv-data$ap (update-svtv-data$c->moddb moddb x)))
    :hints(("Goal" :in-theory (enable svtv-data$ap)))))

(define update-svtv-data$a->moddb (moddb (x svtv-data$ap))
  :guard (and (or (not (svtv-data$a->flatten-validp x))
                  (non-exec (equal moddb
                                   (mv-nth 2 (svtv-design-flatten
                                              (svtv-data$a->design x)
                                              :moddb nil :aliases nil)))))
              (not (svtv-data$a->namemap-validp x)))
  :hooks nil
  :enabled t
  (non-exec (update-svtv-data$c->moddb moddb x)))

(encapsulate nil
  (defthm aliases-when-flatten-okp
    (implies (svtv-data$c-flatten-okp x flatten)
             (equal (svtv-data$c->aliases x)
                    (mv-nth 3 (svtv-design-flatten
                               (svtv-data$c->design x)
                               :moddb nil :aliases nil))))
    :hints(("Goal" :in-theory (enable svtv-data$c-flatten-okp))))

  (defthm update-aliases-preserves-svtv-data$ap
    (implies (and (svtv-data$ap x)
                  (and (or (not (svtv-data$a->flatten-validp x))
                           (equal aliases
                                  (mv-nth 3 (svtv-design-flatten (svtv-data$c->design x)
                                                                 :moddb nil :aliases nil))))
                       (not (svtv-data$a->namemap-validp x))
                       ;; (not (svtv-data$a->phase-fsm-validp x))
                       (not (svtv-data$a->flatnorm-validp x))
                       ))
             (svtv-data$ap (update-svtv-data$c->aliases aliases x)))
    :hints(("Goal" :in-theory (enable svtv-data$ap)))))

(define update-svtv-data$a->aliases (aliases (x svtv-data$ap))
  :guard (and (or (not (svtv-data$a->flatten-validp x))
                  (non-exec (equal aliases
                                   (mv-nth 3 (svtv-design-flatten (svtv-data$c->design x)
                                                                  :moddb nil :aliases nil)))))
              (not (svtv-data$a->namemap-validp x))
              ;; (not (svtv-data$a->phase-fsm-validp x))
              (not (svtv-data$a->flatnorm-validp x)))
  :hooks nil
  :enabled t
  (non-exec (update-svtv-data$c->aliases aliases x)))



(defsection svtv-data
  (local (in-theory (disable (create-svtv-data$a)
                             (create-svtv-data$c)
                             create-moddb
                             create-svtv-data$c
                             )))
  ;; (local (in-theory (set-difference-theories
  ;;                    (current-theory :here)
  ;;                    (executable-counterpart-theory :here))));; (create-svtv-data$a)


  ;; (svtv-data$ap)
  ;; (svtv-data$c->design))))

  ;; (local (in-theory (enable svtv-data$ap
  ;;                           svtv-data$c-compute-phase-fsm
  ;;                           ;; svtv-data$c-compute-cycle
  ;;                           svtv-data$c-compute-namemap
  ;;                           svtv-data$c->phase-fsm
  ;;                           (design-p)
  ;;                           (design-fix)
  ;;                           (svtv-fsm-p)
  ;;                           (svarlist-addr-p)
  ;;                           (design->modalist)
  ;;                           (modalist-vars)
  ;;                           (svarlist-addr-p)
  ;;                           (svtv-data$c-Field-fix))))


  ;; (local (set-default-hints
  ;;         '((and stable-under-simplificationp
  ;;                '(:in-theory (enable svtv-data$c-compute-phase-fsm ;; svtv-data$c-compute-cycle
  ;;                                     )))
  ;;           (and stable-under-simplificationp
  ;;                '(:in-theory (enable svtv-data$cp
  ;;                                     svtv-data$c->design
  ;;                                     svtv-data$c->design^
  ;;                                     svtv-data$c->phase-fsm-validp
  ;;                                     svtv-data$c->phase-fsm-validp^
  ;;                                     svtv-data$c->cycle-fsm-validp
  ;;                                     svtv-data$c->cycle-fsm-validp^
  ;;                                     svtv-data$c->namemap-validp
  ;;                                     svtv-data$c->namemap-validp^
  ;;                                     )))
  ;;           (and stable-under-simplificationp
  ;;                (let ((lit (hons-assoc-equal 'svtv-data$c-cycle-fsm-okp clause)))
  ;;                  (and lit
  ;;                       `(:Expand ,lit
  ;;                         :use ((:instance svtv-data$c-cycle-fsm-okp-necc
  ;;                                (svtv-data$c svtv-data)
  ;;                                (values (svtv-data$c->cycle-values svtv-data))
  ;;                                (nextstate (svtv-data$c->cycle-nextstate svtv-data))
  ;;                                (env (svtv-data$c-cycle-fsm-okp-witness . ,(cdr lit)))))))))
  ;;           (and stable-under-simplificationp
  ;;                (let ((lit (hons-assoc-equal 'svtv-data$c-pipeline-okp clause)))
  ;;                  (and lit
  ;;                       `(:Expand ,lit
  ;;                         :use ((:instance svtv-data$c-pipeline-okp-necc
  ;;                                (svtv-data$c svtv-data)
  ;;                                (results (svtv-data$c->pipeline-results svtv-data))
  ;;                                (env (svtv-data$c-pipeline-okp-witness . ,(cdr lit))))))))))))
  (local (defun make-svtv-data-accessor-defs (fields)
           (declare (xargs :mode :program))
           (if (atom fields)
               nil
             (cons
              (b* ((name (caar fields)))
                (acl2::template-subst
                 '(svtv-data-><fieldname> :logic svtv-data$a-><fieldname> :exec svtv-data$c-><fieldname>$inline)
                 :str-alist `(("<FIELDNAME>" . ,(symbol-name name)))
                 :pkg-sym 'sv-package))
              (make-svtv-data-accessor-defs (cdr fields))))))

  (local (defun make-svtv-data-updater-defs (fields)
           (declare (xargs :mode :program))
           (if (atom fields)
               nil
             (cons
              (b* ((name (caar fields)))
                (acl2::template-subst
                 '(update-svtv-data-><fieldname> :logic update-svtv-data$a-><fieldname> :exec update-svtv-data$c-><fieldname>$inline)
                 :str-alist `(("<FIELDNAME>" . ,(symbol-name name)))
                 :pkg-sym 'sv-package))
              (make-svtv-data-updater-defs (cdr fields))))))

  ;; (local (defthm values-of-svtv-fsm-to-cycle-of-svtv-fsm-normalize
  ;;          (implies (syntaxp (not (and (equal user-names ''nil)
  ;;                                      (equal namemap ''nil))))
  ;;                   (equal (svtv-fsm->values
  ;;                           (svtv-fsm-to-cycle phases
  ;;                                              (svtv-fsm values nextstate design user-names namemap)))
  ;;                          (svtv-fsm->values
  ;;                           (svtv-fsm-to-cycle phases
  ;;                                              (svtv-fsm values nextstate design nil nil)))))
  ;;          :hints(("Goal" :in-theory (enable svtv-fsm-to-cycle svtv-cycle-compile)))))
  

  (make-event
   `(acl2::defabsstobj-events svtv-data
      :foundation svtv-data$c
      :corr-fn equal
      :recognizer (svtv-datap :logic svtv-data$ap :exec svtv-data$cp)
      :creator (create-svtv-data :logic create-svtv-data$a :exec create-svtv-data$c)
      :exports (,@(make-svtv-data-accessor-defs *svtv-data-nonstobj-fields*)
                  ;; (update-svtv-data->design :logic update-svtv-data$a->design :exec update-svtv-data$c->design$inline)

                  (svtv-data-flatten-okp :logic svtv-data$a-flatten-okp :exec svtv-data$c-flatten-okp)
                  (svtv-data-flatnorm-okp :logic svtv-data$a-flatnorm-okp :exec svtv-data$c-flatnorm-okp)
                  (svtv-data-phase-fsm-okp :logic svtv-data$a-phase-fsm-okp :exec svtv-data$c-phase-fsm-okp)
                  (svtv-data-namemap-okp :logic svtv-data$a-namemap-okp :exec svtv-data$c-namemap-okp)
                  (svtv-data-cycle-fsm-okp :logic svtv-data$a-cycle-fsm-okp :exec svtv-data$c-cycle-fsm-okp)
                  (svtv-data-pipeline-okp :logic svtv-data$a-pipeline-okp :exec svtv-data$c-pipeline-okp)

                  ;; (svtv-data-compute-flatten :logic svtv-data$a-compute-flatten
                  ;;                            :exec svtv-data$c-compute-flatten :protect t)
                  ;; (svtv-data-compute-flatnorm :logic svtv-data$a-compute-flatnorm
                  ;;                            :exec svtv-data$c-compute-flatnorm :protect t)
                  ;; (svtv-data-compute-namemap :logic svtv-data$a-compute-namemap
                  ;;                            :exec svtv-data$c-compute-namemap :protect t)
                  
                  (svtv-data->moddb :logic svtv-data$a->moddb :exec svtv-data$c->moddb
                                    :updater update-svtv-data->moddb)
                  (svtv-data->aliases :logic svtv-data$a->aliases :exec svtv-data$c->aliases
                                    :updater update-svtv-data->aliases)
                  (update-svtv-data->moddb :logic update-svtv-data$a->moddb
                                           :exec update-svtv-data$c->moddb)
                  (update-svtv-data->aliases :logic update-svtv-data$a->aliases
                                             :exec update-svtv-data$c->aliases)
                  

                  ,@(make-svtv-data-updater-defs *svtv-data-nonstobj-fields*)
                  ))))








(define svtv-data-compute-flatten (svtv-data)
  :guard (and (not (svtv-data->flatnorm-validp svtv-data))
              (not (svtv-data->namemap-validp svtv-data)))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap
                                          normalize-stobjs-of-svtv-design-flatten
                                          svtv-data$c-flatten-okp))))
  :guard-debug t
  :returns (mv err new-svtv-data)
  (b* ((design (svtv-data->design svtv-data)))
    (stobj-let ((moddb (svtv-data->moddb svtv-data))
                (aliases (svtv-data->aliases svtv-data)))
               (err flatten moddb aliases)
               (svtv-design-flatten design)
               (b* ((svtv-data (update-svtv-data->flatten flatten svtv-data))
                    ((when err)
                     (mv err svtv-data))
                    (svtv-data (update-svtv-data->flatten-validp t svtv-data)))
                 (mv nil svtv-data))))
  ///
  (defret <fn>-preserves-svtv-data$ap
    (implies (and (svtv-data$ap svtv-data)
                  (not (svtv-data$c->flatnorm-validp svtv-data))
                  (not (svtv-data$c->namemap-validp svtv-data)))
             (svtv-data$ap new-svtv-data))
    :hints(("Goal" :in-theory (enable svtv-data$ap svtv-data$c-flatten-okp
                                      normalize-stobjs-of-svtv-design-flatten))))

  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :flatten))
                  (not (equal key :flatten-validp))
                  (not (equal key :moddb))
                  (not (equal key :aliases)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret flatten-validp-of-<fn>
    (implies (not err)
             (svtv-data$c->flatten-validp new-svtv-data))))


(define svtv-data-compute-flatnorm (svtv-data)
  :guard (and (svtv-data->flatten-validp svtv-data)
              (not (svtv-data->phase-fsm-validp svtv-data)))
  :returns new-svtv-data
  (b* ((flatten (svtv-data->flatten svtv-data))
       (flatnorm-setup (svtv-data->flatnorm-setup svtv-data)))
    (stobj-let ((aliases (svtv-data->aliases svtv-data)))
               (assigns)
               (svtv-normalize-assigns flatten aliases flatnorm-setup)
               (b* ((svtv-data (update-svtv-data->flatnorm assigns svtv-data)))
                 (update-svtv-data->flatnorm-validp t svtv-data))))
  ///
  (defret <fn>-preserves-svtv-data$ap
    (implies (and (svtv-data$ap svtv-data)
                  (not (svtv-data$c->phase-fsm-validp svtv-data)))
             (svtv-data$ap new-svtv-data))
    :hints(("Goal" :in-theory (enable svtv-data$ap svtv-data$c-flatnorm-okp))))

  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :flatnorm))
                  (not (equal key :flatnorm-validp)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret flatnorm-validp-of-<fn>
    (svtv-data$c->flatnorm-validp new-svtv-data)))



(define svtv-data-compute-namemap (svtv-data)
  :returns (mv err new-svtv-data)
  :guard (and (svtv-data->flatten-validp svtv-data)
              (not (svtv-data->pipeline-validp svtv-data)))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable normalize-stobjs-of-svtv-design-flatten
                                          svtv-data$c-namemap-okp
                                          svtv-data$c-flatten-okp))))
  (b* ((user-names (svtv-data->user-names svtv-data))
       (design (svtv-data->design svtv-data)))
    (stobj-let ((moddb (svtv-data->moddb svtv-data))
                (aliases (svtv-data->aliases svtv-data)))
               (errs lhsmap)
               (svtv-namemap->lhsmap user-names
                                     (moddb-modname-get-index (design->top design) moddb)
                                     moddb aliases)
               (b* (((when errs)
                     (mv (msg-list errs) svtv-data))
                    (svtv-data (update-svtv-data->namemap lhsmap svtv-data))
                    (svtv-data (update-svtv-data->namemap-validp t svtv-data)))
                 (mv nil svtv-data))))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :namemap))
                  (not (equal key :namemap-validp)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret namemap-validp-of-<fn>
    (implies (not err)
             (svtv-data$c->namemap-validp new-svtv-data)))

  (defret <fn>-preserves-svtv-data$ap
    (implies (and (svtv-data$ap svtv-data)
                  (svtv-data$c->flatten-validp svtv-data)
                  (not (svtv-data$c->pipeline-validp svtv-data)))
             (svtv-data$ap new-svtv-data))
    :hints(("Goal" :in-theory (enable svtv-data$ap
                                      svtv-data$c-namemap-okp)))))







;; ;; (defun svtv-data-corr (c a)
;; ;;   (equal c a))

;; (defthm svtv-data$c->cycle-fsm-of-update-base-values
;;   (implies (svex-alist-eval-equiv base-values (svtv-data$c->base-values svtv-data))
;;            (svtv-fsm-equiv (svtv-data$c->cycle-fsm (update-svtv-data$c->base-values values svtv-data))
;;                            (svtv-data$c->cycle-fsm svtv-data)))
;;   :hints(("Goal" :in-theory (enable svtv-data$c->cycle-fsm))))

;; (defthm svtv-data$c->cycle-fsm-of-update-base-nextstate
;;   (implies (svex-alist-eval-equiv base-nextstate (svtv-data$c->base-nextstate svtv-data))
;;            (svtv-fsm-equiv (svtv-data$c->cycle-fsm (update-svtv-data$c->base-nextstate nextstate svtv-data))
;;                            (svtv-data$c->cycle-fsm svtv-data)))
;;   :hints(("Goal" :in-theory (enable svtv-data$c->cycle-fsm))))

;; (defthm svtv-data$c->cycle-fsm-of-update-cycle-nextstate
;;   (implies (svex-alist-eval-equiv nextstate (svtv-data$c->cycle-nextstate svtv-data))
;;            (svtv-fsm-eval/namemap-equiv
;;             (svtv-data$c->cycle-fsm (update-svtv-data$c->cycle-nextstate nextstate svtv-data))
;;             (svtv-data$c->cycle-fsm svtv-data)))
;;   :hints(("Goal" :in-theory (enable svtv-data$c->cycle-fsm svtv-fsm-eval/namemap-equiv))))

;; (defthm svtv-data$c->cycle-fsm-of-update-cycle-values
;;   (implies (svex-alist-eval-equiv values (svtv-data$c->cycle-values svtv-data))
;;            (svtv-fsm-eval/namemap-equiv
;;             (svtv-data$c->cycle-fsm (update-svtv-data$c->cycle-values values svtv-data))
;;             (svtv-data$c->cycle-fsm svtv-data)))
;;   :hints(("Goal" :in-theory (enable svtv-data$c->cycle-fsm svtv-fsm-eval/namemap-equiv))))


;; (defthm svtv-fsm-under-svtv-fsm-eval-equiv
;;   (implies (syntaxp (not (and (or (equal design (list 'quote (design-fix nil)))
;;                                   (equal design ''nil))
;;                               (equal user-names ''nil)
;;                               (equal namemap ''nil))))
;;            (svtv-fsm-eval-equiv (svtv-fsm values nextstate design user-names namemap)
;;                                 (svtv-fsm values nextstate (design-fix nil) nil nil)))
;;   :hints(("Goal" :in-theory (enable svtv-fsm-eval-equiv))))

;; (defsection svtv-data

;;   (local (in-theory (set-difference-theories
;;                      (current-theory :here)
;;                      (executable-counterpart-theory :here))));; (create-svtv-data$a)
;;   ;; (svtv-data$ap)
;;   ;; (svtv-data$c->design))))

;;   (local (in-theory (enable svtv-data$ap
;;                             svtv-data$c-compute-phase-fsm
;;                             ;; svtv-data$c-compute-cycle
;;                             svtv-data$c-compute-namemap
;;                             svtv-data$c->phase-fsm
;;                             (design-p)
;;                             (design-fix)
;;                             (svtv-fsm-p)
;;                             (svarlist-addr-p)
;;                             (design->modalist)
;;                             (modalist-vars)
;;                             (svarlist-addr-p)
;;                             (svtv-data$c-Field-fix))))


;;   (local (set-default-hints
;;           '((and stable-under-simplificationp
;;                  '(:in-theory (enable svtv-data$c-compute-phase-fsm ;; svtv-data$c-compute-cycle
;;                                       )))
;;             (and stable-under-simplificationp
;;                  '(:in-theory (enable svtv-data$cp
;;                                       svtv-data$c->design
;;                                       svtv-data$c->design^
;;                                       svtv-data$c->phase-fsm-validp
;;                                       svtv-data$c->phase-fsm-validp^
;;                                       svtv-data$c->cycle-fsm-validp
;;                                       svtv-data$c->cycle-fsm-validp^
;;                                       svtv-data$c->namemap-validp
;;                                       svtv-data$c->namemap-validp^
;;                                       )))
;;             (and stable-under-simplificationp
;;                  (let ((lit (hons-assoc-equal 'svtv-data$c-cycle-fsm-okp clause)))
;;                    (and lit
;;                         `(:Expand ,lit
;;                           :use ((:instance svtv-data$c-cycle-fsm-okp-necc
;;                                  (svtv-data$c svtv-data)
;;                                  (values (svtv-data$c->cycle-values svtv-data))
;;                                  (nextstate (svtv-data$c->cycle-nextstate svtv-data))
;;                                  (env (svtv-data$c-cycle-fsm-okp-witness . ,(cdr lit)))))))))
;;             (and stable-under-simplificationp
;;                  (let ((lit (hons-assoc-equal 'svtv-data$c-pipeline-okp clause)))
;;                    (and lit
;;                         `(:Expand ,lit
;;                           :use ((:instance svtv-data$c-pipeline-okp-necc
;;                                  (svtv-data$c svtv-data)
;;                                  (results (svtv-data$c->pipeline-results svtv-data))
;;                                  (env (svtv-data$c-pipeline-okp-witness . ,(cdr lit))))))))))))
;;   (local (defun make-svtv-data-accessor-defs (fields)
;;            (declare (xargs :mode :program))
;;            (if (atom fields)
;;                nil
;;              (cons
;;               (b* ((name (caar fields)))
;;                 (acl2::template-subst
;;                  '(svtv-data-><fieldname> :logic svtv-data$a-><fieldname> :exec svtv-data$c-><fieldname>$inline)
;;                  :str-alist `(("<FIELDNAME>" . ,(symbol-name name)))
;;                  :pkg-sym 'sv-package))
;;               (make-svtv-data-accessor-defs (cdr fields))))))

;;   (local (defun make-svtv-data-updater-defs (fields)
;;            (declare (xargs :mode :program))
;;            (if (atom fields)
;;                nil
;;              (cons
;;               (b* ((name (caar fields)))
;;                 (acl2::template-subst
;;                  '(update-svtv-data-><fieldname> :logic update-svtv-data$a-><fieldname> :exec update-svtv-data$c-><fieldname>$inline)
;;                  :str-alist `(("<FIELDNAME>" . ,(symbol-name name)))
;;                  :pkg-sym 'sv-package))
;;               (make-svtv-data-updater-defs (cdr fields))))))

;;   ;; (local (defthm values-of-svtv-fsm-to-cycle-of-svtv-fsm-normalize
;;   ;;          (implies (syntaxp (not (and (equal user-names ''nil)
;;   ;;                                      (equal namemap ''nil))))
;;   ;;                   (equal (svtv-fsm->values
;;   ;;                           (svtv-fsm-to-cycle phases
;;   ;;                                              (svtv-fsm values nextstate design user-names namemap)))
;;   ;;                          (svtv-fsm->values
;;   ;;                           (svtv-fsm-to-cycle phases
;;   ;;                                              (svtv-fsm values nextstate design nil nil)))))
;;   ;;          :hints(("Goal" :in-theory (enable svtv-fsm-to-cycle svtv-cycle-compile)))))
  

;;   (make-event
;;    `(acl2::defabsstobj-events svtv-data
;;       :foundation svtv-data$c
;;       :corr-fn equal
;;       :recognizer (svtv-datap :logic svtv-data$ap :exec svtv-data$cp)
;;       :creator (create-svtv-data :logic create-svtv-data$a :exec create-svtv-data$c)
;;       :exports (,@(make-svtv-data-accessor-defs *svtv-data-nonstobj-fields*)
;;                   ;; (update-svtv-data->design :logic update-svtv-data$a->design :exec update-svtv-data$c->design$inline)
;;                   (svtv-data-compute-phase-fsm :logic svtv-data$a-compute-phase-fsm :exec svtv-data$c-compute-phase-fsm :protect t)

;;                   (svtv-data->phase-fsm :logic svtv-data$a->phase-fsm :exec svtv-data$c->phase-fsm)
;;                   (svtv-data->cycle-fsm :logic svtv-data$a->cycle-fsm :exec svtv-data$c->cycle-fsm)

;;                   (svtv-data-phase-fsm-okp :logic svtv-data$a-phase-fsm-okp :exec svtv-data$c-phase-fsm-okp)
;;                   (svtv-data-namemap-okp :logic svtv-data$a-namemap-okp :exec svtv-data$c-namemap-okp)
;;                   (svtv-data-cycle-fsm-okp :logic svtv-data$a-cycle-fsm-okp :exec svtv-data$c-cycle-fsm-okp)
;;                   (svtv-data-pipeline-okp :logic svtv-data$a-pipeline-okp :exec svtv-data$c-pipeline-okp)

;;                   ,@(make-svtv-data-updater-defs *svtv-data-nonstobj-fields*)

;;                   (svtv-data-compute-namemap :logic svtv-data$a-compute-namemap :exec svtv-data$c-compute-namemap :protect t)
;;                   ))))




(define svtv-data-invalidate (svtv-data)
  :enabled t
  (b* ((svtv-data (update-svtv-data->flatten-validp nil svtv-data))
       (svtv-data (update-svtv-data->namemap-validp nil svtv-data))
       (svtv-data (update-svtv-data->flatnorm-validp nil svtv-data))
       (svtv-data (update-svtv-data->phase-fsm-validp nil svtv-data))
       (svtv-data (update-svtv-data->cycle-fsm-validp nil svtv-data))
       (svtv-data (update-svtv-data->pipeline-validp nil svtv-data)))
    svtv-data))
