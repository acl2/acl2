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
(include-book "cycle-compile")
(include-book "pipeline")
(include-book "../svex/alist-equiv")
(include-book "std/stobjs/nicestobj" :dir :system)

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


(defxdoc svtv-data
  :parents (svtv)
  :short "A stobj encapsulating an SVTV and the steps used in creating it, from
the initial SV design to (potentially) a pipelined symbolic run."
  :long "

<p>An svtv-data stobj holds an SV design and several other pieces of data, such
as finite-state machine and symbolic pipeline objects, tied to that design.
These data objects are constrained by the abstract stobj invariant to have
certain relationships among each other and to the design.  For example, one
invariant states that if the @('base-fsm-validp') field is true, then the
@('base-values'), @('base-nextstate'), @('moddb'), and @('aliases') fields all
equal certain functions of the original design, namely, they are outputs of
@('svtv-design-to-fsm').  These relationships can be used to show that facts
proved about the pipelines imply facts about the FSM, which imply facts about
the original design.</p>

<p>The stobj contains data members that trace the following steps:</p>

<ul>

<li>The initial SV design is processed into an FSM (the \"base FSM\"),
producing as well a @('moddb') and @('aliases') table.</li>

<li>The user may attach names to certain signals, which are processed into a
@('namemap').</li>

<li>The user may define a <em>cycle</em> as a composition of one or
more (usually two) phases of the base FSM into a new FSM.</li>

<li>The user may define a <em>pipeline</em> as a run of several cycles of the
cycle FSM in which certain inputs are given symbolic or concrete values at
particular times and certain outputs are read at particular times.</li>

</ul>




")



(defconst *svtv-data-nonstobj-fields*
  `((design :type (satisfies design-p)
            :pred design-p :fix design-fix :initially ,(make-design :top ""))

    (user-names :type (satisfies svtv-namemap-p)
                :pred svtv-namemap-p :fix svtv-namemap-fix)
    (namemap :type (satisfies svtv-name-lhs-map-p)
                :pred svtv-name-lhs-map-p :fix svtv-name-lhs-map-fix)
    (namemap-validp :type (member t nil) :pred booleanp :fix bool-fix)
;;     (moddb-validp :type (member t nil) :pred booleanp :fix bool-fix)

    (base-values :type (satisfies svex-alist-p) :pred svex-alist-p :fix svex-alist-fix)
    (base-nextstate :type (satisfies svex-alist-p) :pred svex-alist-p :fix svex-alist-fix)
    (base-fsm-validp :type (member t nil) :pred booleanp :fix bool-fix)

    (cycle-phases :type (satisfies svtv-cyclephaselist-p) :pred svtv-cyclephaselist-p :fix svtv-cyclephaselist-fix)
    (cycle-values :type (satisfies svex-alist-p) :pred svex-alist-p :fix svex-alist-fix)
    (cycle-nextstate :type (satisfies svex-alist-p) :pred svex-alist-p :fix svex-alist-fix)
    (cycle-fsm-validp :type (member t nil) :pred booleanp :fix bool-fix)

    (pipeline-probes :type (satisfies svtv-probealist-p) :pred svtv-probealist-p :fix svtv-probealist-fix)
    (pipeline-inputs :type (satisfies svex-alistlist-p) :pred svex-alistlist-p :fix svex-alistlist-fix)
    (pipeline-overrides :type (satisfies svex-alistlist-p) :pred svex-alistlist-p :fix svex-alistlist-fix)
    (pipeline-initst :type (satisfies svex-alist-p) :pred svex-alist-p :fix svex-alist-fix)
    (pipeline-results :type (satisfies svex-alist-p) :pred svex-alist-p :fix svex-alist-fix)
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


;; (define svtv-data$c-invalidate-base-fsm (svtv-data$c)
;;   :enabled t
;;   (update-svtv-data$c->base-fsm-validp nil svtv-data$c))

;; (define svtv-data$a-invalidate-base-fsm (x)
;;   :enabled t
;;   (non-exec (update-svtv-data$c->base-fsm-validp nil x)))

;; (define svtv-data$c-invalidate-cycle-fsm (svtv-data$c)
;;   :enabled t
;;   (update-svtv-data$c->cycle-fsm-validp nil svtv-data$c))

;; (define svtv-data$a-invalidate-cycle-fsm (x)
;;   :enabled t
;;   (non-exec (update-svtv-data$c->cycle-fsm-validp nil x)))

;; (define svtv-data$c-invalidate-namemap (svtv-data$c)
;;   :enabled t
;;   (update-svtv-data$c->namemap-validp nil svtv-data$c))

;; (define svtv-data$a-invalidate-namemap (x)
;;   :enabled t
;;   (non-exec (update-svtv-data$c->namemap-validp nil x)))

;; (define svtv-data$c-invalidate-pipeline (svtv-data$c)
;;   :enabled t
;;   (update-svtv-data$c->pipeline-validp nil svtv-data$c))

;; (define svtv-data$a-invalidate-pipeline (x)
;;   :enabled t
;;   (non-exec (update-svtv-data$c->pipeline-validp nil x)))


(define update-svtv-data$a->design ((design design-p) x)
  :guard (and (not (svtv-data$a->base-fsm-validp x))
              (modalist-addr-p (design->modalist design)))
  :enabled t
  (non-exec (update-svtv-data$c->design design x)))

(define svtv-data$c-compute-base-fsm (svtv-data$c)
  :guard (and (not (svtv-data$c->namemap-validp svtv-data$c))
              (not (svtv-data$c->cycle-fsm-validp svtv-data$c))
              (not (svtv-data$c->pipeline-validp svtv-data$c))
              (modalist-addr-p (design->modalist (svtv-data$c->design svtv-data$c))))
  :returns (mv errmsg new-svtv-data$c)
  (b* ((design (svtv-data$c->design svtv-data$c)))
    (stobj-let ((moddb (svtv-data$c->moddb svtv-data$c))
                (aliases (svtv-data$c->aliases svtv-data$c)))
               (err fsm moddb aliases)
               (svtv-design-to-fsm design)
               (b* (((when err) (mv err svtv-data$c))
                    ((svtv-fsm fsm))
                    (svtv-data$c (update-svtv-data$c->base-values fsm.values svtv-data$c))
                    (svtv-data$c (update-svtv-data$c->base-nextstate fsm.nextstate svtv-data$c))
                    (svtv-data$c (update-svtv-data$c->base-fsm-validp t svtv-data$c)))
                 (mv nil svtv-data$c)))))

(define svtv-data$c->base-fsm (svtv-data$c)
  :returns (fsm svtv-fsm-p)
  (make-svtv-fsm
   :values (svtv-data$c->base-values svtv-data$c)
   :nextstate (svtv-data$c->base-nextstate svtv-data$c)
   :design (svtv-data$c->design svtv-data$c)
   :user-names (svtv-data$c->user-names svtv-data$c)
   :namemap (svtv-data$c->namemap svtv-data$c))
  ///
  (stobjs::def-updater-independence-thm svtv-data$c->base-fsm-of-update
    (let ((new acl2::new) (old acl2::old))
      (implies (and (equal (svtv-data$c-get :base-values new)
                           (svtv-data$c-get :base-values old))
                    (equal (svtv-data$c-get :base-nextstate new)
                           (svtv-data$c-get :base-nextstate old))
                    (equal (svtv-data$c-get :design new)
                           (svtv-data$c-get :design old))
                    (equal (svtv-data$c-get :user-names new)
                           (svtv-data$c-get :user-names old))
                    (equal (svtv-data$c-get :namemap new)
                           (svtv-data$c-get :namemap old)))
               (equal (svtv-data$c->base-fsm new)
                      (svtv-data$c->base-fsm old)))))

  (defret nextstate-of-<fn>
    (equal (svtv-fsm->nextstate fsm)
           (svtv-data$c->base-nextstate svtv-data$c))))

(define svtv-data$a->base-fsm (x)
  :enabled t
  (non-exec (svtv-data$c->base-fsm x)))


(define svtv-data$c->cycle-fsm (svtv-data$c)
  :returns (fsm svtv-fsm-p)
  (make-svtv-fsm
   :values (svtv-data$c->cycle-values svtv-data$c)
   :nextstate (svtv-data$c->cycle-nextstate svtv-data$c)
   :design (svtv-data$c->design svtv-data$c)
   :user-names (svtv-data$c->user-names svtv-data$c)
   :namemap (svtv-data$c->namemap svtv-data$c))
  ///
  (stobjs::def-updater-independence-thm svtv-data$c->cycle-fsm-of-update
    (let ((new acl2::new) (old acl2::old))
      (implies (and (equal (svtv-data$c-get :cycle-values new)
                           (svtv-data$c-get :cycle-values old))
                    (equal (svtv-data$c-get :cycle-nextstate new)
                           (svtv-data$c-get :cycle-nextstate old))
                    (equal (svtv-data$c-get :design new)
                           (svtv-data$c-get :design old))
                    (equal (svtv-data$c-get :user-names new)
                           (svtv-data$c-get :user-names old))
                    (equal (svtv-data$c-get :namemap new)
                           (svtv-data$c-get :namemap old)))
               (equal (svtv-data$c->cycle-fsm new)
                      (svtv-data$c->cycle-fsm old)))))

  (defret nextstate-of-<fn>
    (equal (svtv-fsm->nextstate fsm)
           (svtv-data$c->cycle-nextstate svtv-data$c))))

(define svtv-data$a->cycle-fsm (x)
  :enabled t
  (non-exec (svtv-data$c->cycle-fsm x)))

(define svtv-data$c-base-fsm-okp (svtv-data$c
                                  (values svex-alist-p)
                                  (nextstate svex-alist-p))
  :enabled t
  (b* (((mv err fsm moddb aliases)
        (non-exec (svtv-design-to-fsm (svtv-data$c->design svtv-data$c)
                                      :moddb nil :aliases nil)))
       ((when err) nil)
       ((svtv-fsm fsm)))
    (and (ec-call (svex-alist-eval-equiv values fsm.values))
         (ec-call (svex-alist-eval-equiv nextstate fsm.nextstate))
         (not (hons-dups-p (svex-alist-keys nextstate)))
         (equal (non-exec (svtv-data$c->moddb svtv-data$c)) moddb)
         (equal (non-exec (svtv-data$c->aliases svtv-data$c)) aliases))))

(define svtv-data$a-base-fsm-okp (x
                                  (values svex-alist-p)
                                  (nextstate svex-alist-p))
  :enabled t
  (non-exec (svtv-data$c-base-fsm-okp x values nextstate)))


(define svtv-data$c-namemap-okp (svtv-data$c (namemap svtv-name-lhs-map-p))
  :enabled t
  (b* (((mv errs lhsmap)
        (non-exec
         (svtv-namemap->lhsmap
          (svtv-data$c->user-names svtv-data$c)
          (non-exec
           (moddb-modname-get-index
            (design->top (svtv-data$c->design svtv-data$c))
            (non-exec (svtv-data$c->moddb svtv-data$c))))
          (non-exec (svtv-data$c->moddb svtv-data$c))
          (non-exec (svtv-data$c->aliases svtv-data$c))))))
    (and (not errs)
         (equal namemap
                lhsmap))))

(define svtv-data$a-namemap-okp (x (namemap svtv-name-lhs-map-p))
  :enabled t
  (non-exec (svtv-data$c-namemap-okp x namemap)))

(define svtv-data$c-cycle-fsm-okp (svtv-data$c (values svex-alist-p) (nextstate svex-alist-p))
  :enabled t
  (b* (((svtv-fsm cycle-fsm)
        (ec-call (svtv-fsm-to-cycle (svtv-data$c->cycle-phases svtv-data$c)
                                    (svtv-data$c->base-fsm svtv-data$c)))))
    (and (ec-call (svex-alist-eval-equiv values cycle-fsm.values))
         (ec-call (svex-alist-eval-equiv nextstate cycle-fsm.nextstate))
         (not (hons-dups-p (svex-alist-keys nextstate))))))

(define svtv-data$a-cycle-fsm-okp (x (values svex-alist-p) (nextstate svex-alist-p))
  :enabled t
  (non-exec (svtv-data$c-cycle-fsm-okp x values nextstate)))

(define svtv-data$c-pipeline-okp (svtv-data$c (results svex-alist-p))
  :enabled t
  (non-exec
   (b* ((fsm (svtv-data$c->cycle-fsm svtv-data$c))
        (probes (svtv-data$c->pipeline-probes svtv-data$c))
        (result
         (svtv-probealist-extract-alist
          probes
          (svtv-fsm-run-renamed-compile
           (svtv-data$c->pipeline-inputs svtv-data$c)
           (svtv-data$c->pipeline-overrides svtv-data$c)
           (svtv-data$c->pipeline-initst svtv-data$c)
           fsm
           (svtv-probealist-outvars probes) nil))))
     (ec-call (svex-alist-eval-equiv results result)))))


(define svtv-data$a-pipeline-okp (x (results svex-alist-p))
  :enabled t
  (non-exec (svtv-data$c-pipeline-okp x results)))
  

(define svtv-data$ap (x)
  (non-exec
   (and ;; (svtv-data$cp x)
        (modalist-addr-p (design->modalist (svtv-data$c->design x)))
        (implies (svtv-data$c->base-fsm-validp x)
                 (and (svtv-data$c-base-fsm-okp x
                                                (svtv-data$c->base-values x)
                                                (svtv-data$c->base-nextstate x))
                      
                      (implies (svtv-data$c->namemap-validp x)
                               (svtv-data$c-namemap-okp x (svtv-data$c->namemap x)))
                      
                      (implies (svtv-data$c->cycle-fsm-validp x)
                               (svtv-data$c-cycle-fsm-okp x
                                                          (svtv-data$c->cycle-values x)
                                                          (svtv-data$c->cycle-nextstate x)))

                      (implies (and (svtv-data$c->pipeline-validp x)
                                    (svtv-data$c->cycle-fsm-validp x)
                                    (svtv-data$c->namemap-validp x))
                               (svtv-data$c-pipeline-okp x (svtv-data$c->pipeline-results x))))))))

(define svtv-data$a-compute-base-fsm ((x svtv-data$ap))
  :guard (and (not (svtv-data$a->namemap-validp x))
              (not (svtv-data$a->cycle-fsm-validp x))
              (not (svtv-data$a->pipeline-validp x)))
  :enabled t
  (b* (((mv a b) (non-exec (svtv-data$c-compute-base-fsm x))))
    (mv a b)))


(define update-svtv-data$a->base-values ((values svex-alist-p) (x svtv-data$ap))
  :guard (or (not (svtv-data$a->base-fsm-validp x))
             (svtv-data$a-base-fsm-okp x values (svtv-data$a->base-nextstate x)))
  :enabled t
  (non-exec (update-svtv-data$c->base-values values x)))

(define update-svtv-data$a->base-nextstate ((nextstate svex-alist-p) (x svtv-data$ap))
  :guard (or (not (svtv-data$a->base-fsm-validp x))
             (svtv-data$a-base-fsm-okp x (svtv-data$a->base-values x) nextstate))
  :enabled t
  (non-exec (update-svtv-data$c->base-nextstate nextstate x)))

(define update-svtv-data$a->base-fsm-validp ((validp booleanp) (x svtv-data$ap))
  :guard (or (not validp)
             (and (svtv-data$a-base-fsm-okp x (svtv-data$a->base-values x)
                                            (svtv-data$a->base-nextstate x))
                  (not (svtv-data$a->cycle-fsm-validp x))
                  (not (svtv-data$a->namemap-validp x))))
              
  :enabled t
  (non-exec (update-svtv-data$c->base-fsm-validp validp x)))
  
(define update-svtv-data$a->namemap ((namemap svtv-name-lhs-map-p) (x svtv-data$ap))
  :guard (and (or (not (svtv-data$a->namemap-validp x))
                  (svtv-data$a-namemap-okp x namemap))
              (not (svtv-data$a->pipeline-validp x)))
  :enabled t
  (non-exec (update-svtv-data$c->namemap namemap x)))

(define update-svtv-data$a->namemap-validp ((validp booleanp) (x svtv-data$ap))
  :guard (and (or (not validp)
                  (svtv-data$a-namemap-okp x (svtv-data$a->namemap x)))
              (not (svtv-data$a->pipeline-validp x)))
  :enabled t
  (non-exec (update-svtv-data$c->namemap-validp validp x)))


(define update-svtv-data$a->cycle-values ((values svex-alist-p) (x svtv-data$ap))
  :guard (or (not (svtv-data$a->cycle-fsm-validp x))
             (not (svtv-data$a->base-fsm-validp x))
             (svtv-data$a-cycle-fsm-okp x values (svtv-data$a->cycle-nextstate x)))
  :enabled t
  (non-exec (update-svtv-data$c->cycle-values values x)))

(define update-svtv-data$a->cycle-nextstate ((nextstate svex-alist-p) (x svtv-data$ap))
  :guard (or (not (svtv-data$a->cycle-fsm-validp x))
             (not (svtv-data$a->base-fsm-validp x))
             (svtv-data$a-cycle-fsm-okp x (svtv-data$a->cycle-values x) nextstate))
  :enabled t
  (non-exec (update-svtv-data$c->cycle-nextstate nextstate x)))

(define update-svtv-data$a->cycle-fsm-validp ((validp booleanp) (x svtv-data$ap))
  :guard (or (not validp)
             (and (svtv-data$a-cycle-fsm-okp x (svtv-data$a->cycle-values x)
                                             (svtv-data$a->cycle-nextstate x))
                  (not (svtv-data$a->pipeline-validp x))))
  :enabled t
  (non-exec (update-svtv-data$c->cycle-fsm-validp validp x)))

(define update-svtv-data$a->pipeline-results ((results svex-alist-p) (x svtv-data$ap))
  :guard (or (not (svtv-data$a->base-fsm-validp x))
             (not (svtv-data$a->cycle-fsm-validp x))
             (not (svtv-data$a->namemap-validp x))
             (not (svtv-data$a->pipeline-validp x))
             (svtv-data$a-pipeline-okp x results))
  :enabled t
  (non-exec (update-svtv-data$c->pipeline-results results x)))


(define update-svtv-data$a->pipeline-validp ((validp booleanp) (x svtv-data$ap))
  :guard (or (not validp)
             (svtv-data$a-pipeline-okp x (svtv-data$a->pipeline-results x)))
  :enabled t
  (non-exec (update-svtv-data$c->pipeline-validp validp x)))





(define update-svtv-data$a->cycle-phases ((phases svtv-cyclephaselist-p) x)
  :guard (not (svtv-data$a->cycle-fsm-validp x))
  :enabled t
  (non-exec (update-svtv-data$c->cycle-phases phases x)))

;; (local (in-theory (disable hons-dups-p)))

;; (define svtv-data$c-compute-cycle (svtv-data$c)
;;   :guard (and (not (svtv-data$c->cycle-fsm-validp svtv-data$c))
;;               (no-duplicatesp-equal (svex-alist-keys (svtv-fsm->nextstate (svtv-data$c->base-fsm svtv-data$c)))))
;;   (b* ((fsm (svtv-data$c->base-fsm svtv-data$c))
;;        (phases (svtv-data$c->cycle-phases svtv-data$c))
;;        ((svtv-fsm cycle-fsm) (svtv-fsm-to-cycle phases fsm))
;;        (svtv-data$c (update-svtv-data$c->cycle-values cycle-fsm.values svtv-data$c))
;;        (svtv-data$c (update-svtv-data$c->cycle-nextstate cycle-fsm.nextstate svtv-data$c)))
;;     (update-svtv-data$c->cycle-fsm-validp t svtv-data$c)))


;; (define svtv-data$a-compute-cycle ((x svtv-data$ap))
;;   :guard (and (not (svtv-data$a->cycle-fsm-validp x))
;;               (svtv-data$a->base-fsm-validp x))
;;   :enabled t
;;   (non-exec (svtv-data$c-compute-cycle x)))

(define update-svtv-data$a->user-names ((names svtv-namemap-p) x)
  :guard (and (not (svtv-data$a->namemap-validp x))
              (not (svtv-data$a->pipeline-validp x)))
  :enabled t
  (non-exec (update-svtv-data$c->user-names names x)))


(define update-svtv-data$a->pipeline-probes ((names svtv-probealist-p) x)
  :guard (not (svtv-data$a->pipeline-validp x))
  :enabled t
  (non-exec (update-svtv-data$c->pipeline-probes names x)))

(define update-svtv-data$a->pipeline-inputs ((names svex-alistlist-p) x)
  :guard (not (svtv-data$a->pipeline-validp x))
  :enabled t
  (non-exec (update-svtv-data$c->pipeline-inputs names x)))

(define update-svtv-data$a->pipeline-overrides ((names svex-alistlist-p) x)
  :guard (not (svtv-data$a->pipeline-validp x))
  :enabled t
  (non-exec (update-svtv-data$c->pipeline-overrides names x)))

(define update-svtv-data$a->pipeline-initst ((names svex-alist-p) x)
  :guard (not (svtv-data$a->pipeline-validp x))
  :enabled t
  (non-exec (update-svtv-data$c->pipeline-initst names x)))





(define svtv-data$c-compute-namemap (svtv-data$c)
  :returns (mv err new-svtv-data$c)
  :guard (b* ((design (svtv-data$c->design svtv-data$c)))
           (stobj-let ((moddb (svtv-data$c->moddb svtv-data$c))
                       (aliases (svtv-data$c->aliases svtv-data$c)))
                      (ok)
                      (and (moddb-ok moddb)
                           (b* ((index (moddb-modname-get-index
                             (design->top design) moddb)))
                             (and index
                                  (svtv-mod-alias-guard
                                   index
                                   moddb aliases))))
                      ok))
  (b* ((user-names (svtv-data$c->user-names svtv-data$c))
       (design (svtv-data$c->design svtv-data$c)))
    (stobj-let ((moddb (svtv-data$c->moddb svtv-data$c))
                (aliases (svtv-data$c->aliases svtv-data$c)))
               (errs lhsmap)
               (svtv-namemap->lhsmap user-names
                                     (moddb-modname-get-index (design->top design) moddb)
                                     moddb aliases)
               (b* (((when errs)
                     (mv (msg-list errs) svtv-data$c))
                    (svtv-data$c (update-svtv-data$c->namemap lhsmap svtv-data$c))
                    (svtv-data$c (update-svtv-data$c->namemap-validp t svtv-data$c)))
                 (mv nil svtv-data$c)))))

(define svtv-data$a-compute-namemap ((x svtv-data$ap))
  :guard (svtv-data$a->base-fsm-validp x)
  :enabled t
  (b* (((mv a b) (non-exec (svtv-data$c-compute-namemap x))))
    (mv a b)))
                    


 ;; BOZO allow names

(define create-svtv-data$a ()
  :enabled t
  (non-exec (create-svtv-data$c)))



(local
 (defsection svtv-fsm-to-cycle-cong
   (defret eval-outs-lookup-of-<fn>
     (equal (svex-eval (svex-lookup var outs) env)
            (svex-env-lookup var (svtv-cycle-eval-outs env
                                                       (svex-alist-eval prev-st env)
                                                       phases x)))
     :hints (("goal" :use eval-outs-of-<fn>
              :in-theory (disable eval-outs-of-<fn>)))
     :fn svtv-cycle-compile)

   (local
    (defret outs-lookup-exists-of-<fn>
      (iff (svex-lookup var outs)
           (svex-env-boundp var (svtv-cycle-eval-outs env
                                                      (svex-alist-eval prev-st env)
                                                      phases x)))
      :hints (("goal" :use eval-outs-of-<fn>
               :in-theory (disable eval-outs-of-<fn>)))
      :fn svtv-cycle-compile))

   (defret eval-nextst-lookup-of-<fn>
     (equal (svex-eval (svex-lookup var nextst) env)
            (svex-env-lookup var (svtv-cycle-eval-nextst env
                                                       (svex-alist-eval prev-st env)
                                                       phases x)))
     :hints (("goal" :use eval-nextsts-of-<fn>
              :in-theory (disable eval-nextsts-of-<fn>)))
     :fn svtv-cycle-compile)

   (local
    (defret nextst-lookup-exists-of-<fn>
      (iff (svex-lookup var nextst)
           (svex-env-boundp var (svtv-cycle-eval-nextst env
                                                      (svex-alist-eval prev-st env)
                                                      phases x)))
      :hints (("goal" :use eval-nextsts-of-<fn>
               :in-theory (disable eval-nextsts-of-<fn>)))
      :fn svtv-cycle-compile))

   (defthm svtv-fsm-eval-equiv-congruence-of-svtv-cycle-compile-outs
     (implies (svtv-fsm-eval-equiv fsm fsm-equiv)
              (svex-alist-eval-equiv (mv-nth 0 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 0 (svtv-cycle-compile prev-st phases fsm-equiv))))
     :hints((witness) (witness))
     :rule-classes :congruence)

   (defthm svtv-fsm-eval-equiv-congruence-of-svtv-cycle-compile-nextst
     (implies (svtv-fsm-eval-equiv fsm fsm-equiv)
              (svex-alist-eval-equiv (mv-nth 1 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 1 (svtv-cycle-compile prev-st phases fsm-equiv))))
     :hints((witness) (witness))
     :rule-classes :congruence)
   
   (defthm prev-st-congruence-of-svtv-cycle-compile-outs
     (implies (svex-alist-eval-equiv prev-st prev-st-equiv)
              (svex-alist-eval-equiv (mv-nth 0 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 0 (svtv-cycle-compile prev-st-equiv phases fsm))))
     :hints((witness :ruleset svex-alist-eval-equiv-witnessing) ;; (witness)
            (witness :ruleset svex-eval-equiv-witnessing)
            )
     :rule-classes :congruence)

   (defthm prev-st-congruence-of-svtv-cycle-compile-nextst
     (implies (svex-alist-eval-equiv prev-st prev-st-equiv)
              (svex-alist-eval-equiv (mv-nth 1 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 1 (svtv-cycle-compile prev-st-equiv phases fsm))))
     :hints((witness :ruleset svex-alist-eval-equiv-witnessing) ;; (witness)
            (witness :ruleset svex-eval-equiv-witnessing)
            )
     :rule-classes :congruence)

   (defthm svtv-fsm-eval-equiv-congruence-of-svtv-cycle-compile-nextst
     (implies (svtv-fsm-eval-equiv fsm fsm-equiv)
              (svex-alist-eval-equiv (mv-nth 1 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 1 (svtv-cycle-compile prev-st phases fsm-equiv))))
     :hints((witness) (witness))
     :rule-classes :congruence)

   (defthm svtv-fsm-eval-equiv-congruence-of-svtv-cycle-compile-outs
     (implies (svtv-fsm-eval-equiv fsm fsm-equiv)
              (svex-alist-eval-equiv (mv-nth 0 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 0 (svtv-cycle-compile prev-st phases fsm-equiv))))
     :hints((witness) (witness))
     :rule-classes :congruence)

   (defthm svtv-fsm-eval-equiv-congruence-of-svtv-cycle-compile-nextst
     (implies (svtv-fsm-eval-equiv fsm fsm-equiv)
              (svex-alist-eval-equiv (mv-nth 1 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 1 (svtv-cycle-compile prev-st phases fsm-equiv))))
     :hints((witness) (witness))
     :rule-classes :congruence)

   (defthm svtv-fsm-under-svtv-fsm-eval-equiv
     (implies (syntaxp (not (and (equal design (list 'quote (design-fix nil)))
                                 (equal user-names ''nil)
                                 (equal namemap ''nil))))
              (svtv-fsm-eval-equiv (svtv-fsm values nextstate design user-names namemap)
                                   (svtv-fsm values nextstate (design-fix nil) nil nil)))
     :hints(("Goal" :in-theory (enable svtv-fsm-eval-equiv))))

   

   (defcong svtv-fsm-eval-equiv svtv-fsm-eval-equiv (svtv-fsm-to-cycle phases fsm) 2
     :hints(("Goal" :in-theory (enable svtv-fsm-to-cycle))))))

;; (defun svtv-data-corr (c a)
;;   (equal c a))

(defthm svtv-data$c->cycle-fsm-of-update-base-values
  (implies (svex-alist-eval-equiv base-values (svtv-data$c->base-values svtv-data))
           (svtv-fsm-equiv (svtv-data$c->cycle-fsm (update-svtv-data$c->base-values values svtv-data))
                           (svtv-data$c->cycle-fsm svtv-data)))
  :hints(("Goal" :in-theory (enable svtv-data$c->cycle-fsm))))

(defthm svtv-data$c->cycle-fsm-of-update-base-nextstate
  (implies (svex-alist-eval-equiv base-nextstate (svtv-data$c->base-nextstate svtv-data))
           (svtv-fsm-equiv (svtv-data$c->cycle-fsm (update-svtv-data$c->base-nextstate nextstate svtv-data))
                           (svtv-data$c->cycle-fsm svtv-data)))
  :hints(("Goal" :in-theory (enable svtv-data$c->cycle-fsm))))

(defthm svtv-data$c->cycle-fsm-of-update-cycle-nextstate
  (implies (svex-alist-eval-equiv nextstate (svtv-data$c->cycle-nextstate svtv-data))
           (svtv-fsm-eval/namemap-equiv
            (svtv-data$c->cycle-fsm (update-svtv-data$c->cycle-nextstate nextstate svtv-data))
            (svtv-data$c->cycle-fsm svtv-data)))
  :hints(("Goal" :in-theory (enable svtv-data$c->cycle-fsm svtv-fsm-eval/namemap-equiv))))

(defthm svtv-data$c->cycle-fsm-of-update-cycle-values
  (implies (svex-alist-eval-equiv values (svtv-data$c->cycle-values svtv-data))
           (svtv-fsm-eval/namemap-equiv
            (svtv-data$c->cycle-fsm (update-svtv-data$c->cycle-values values svtv-data))
            (svtv-data$c->cycle-fsm svtv-data)))
  :hints(("Goal" :in-theory (enable svtv-data$c->cycle-fsm svtv-fsm-eval/namemap-equiv))))




(defsection svtv-data

  (local (in-theory (set-difference-theories
                     (current-theory :here)
                     (executable-counterpart-theory :here))));; (create-svtv-data$a)
  ;; (svtv-data$ap)
  ;; (svtv-data$c->design))))

  (local (in-theory (enable svtv-data$ap
                            svtv-data$c-compute-base-fsm
                            ;; svtv-data$c-compute-cycle
                            ;; svtv-data$c-compute-namemap
                            svtv-data$c->base-fsm
                            (design-p)
                            (svtv-fsm-p)
                            (svarlist-addr-p)
                            (design->modalist)
                            (modalist-vars)
                            (svarlist-addr-p)
                            (svtv-data$c-Field-fix))))


  (local (set-default-hints
          '((and stable-under-simplificationp
                 '(:in-theory (enable svtv-data$c-compute-base-fsm ;; svtv-data$c-compute-cycle
                                      )))
            (and stable-under-simplificationp
                 '(:in-theory (enable svtv-data$cp
                                      svtv-data$c->design
                                      svtv-data$c->design^
                                      svtv-data$c->base-fsm-validp
                                      svtv-data$c->base-fsm-validp^
                                      svtv-data$c->cycle-fsm-validp
                                      svtv-data$c->cycle-fsm-validp^
                                      svtv-data$c->namemap-validp
                                      svtv-data$c->namemap-validp^
                                      ))))))
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

  (local (defthm values-of-svtv-fsm-to-cycle-of-svtv-fsm-normalize
           (implies (syntaxp (not (and (equal user-names ''nil)
                                       (equal namemap ''nil))))
                    (equal (svtv-fsm->values
                            (svtv-fsm-to-cycle phases
                                               (svtv-fsm values nextstate design user-names namemap)))
                           (svtv-fsm->values
                            (svtv-fsm-to-cycle phases
                                               (svtv-fsm values nextstate design nil nil)))))
           :hints(("Goal" :in-theory (enable svtv-fsm-to-cycle svtv-cycle-compile)))))
  

  (make-event
   `(acl2::defabsstobj-events svtv-data
      :concrete svtv-data$c
      :corr-fn equal
      :recognizer (svtv-datap :logic svtv-data$ap :exec svtv-data$cp)
      :creator (create-svtv-data :logic create-svtv-data$a :exec create-svtv-data$c)
      :exports (,@(make-svtv-data-accessor-defs *svtv-data-nonstobj-fields*)
                  ;; (update-svtv-data->design :logic update-svtv-data$a->design :exec update-svtv-data$c->design$inline)
                  (svtv-data-compute-base-fsm :logic svtv-data$a-compute-base-fsm :exec svtv-data$c-compute-base-fsm :protect t)

                  (svtv-data->base-fsm :logic svtv-data$a->base-fsm :exec svtv-data$c->base-fsm)
                  (svtv-data->cycle-fsm :logic svtv-data$a->cycle-fsm :exec svtv-data$c->cycle-fsm)

                  (svtv-data-base-fsm-okp :logic svtv-data$a-base-fsm-okp :exec svtv-data$c-base-fsm-okp)
                  (svtv-data-namemap-okp :logic svtv-data$a-namemap-okp :exec svtv-data$c-namemap-okp)
                  (svtv-data-cycle-fsm-okp :logic svtv-data$a-cycle-fsm-okp :exec svtv-data$c-cycle-fsm-okp)
                  (svtv-data-pipeline-okp :logic svtv-data$a-pipeline-okp :exec svtv-data$c-pipeline-okp)

                  ,@(make-svtv-data-updater-defs *svtv-data-nonstobj-fields*)
                  
                  
                  ;; ;; (svtv-data-invalidate-base-fsm :logic svtv-data$a-invalidate-base-fsm :exec svtv-data$c-invalidate-base-fsm)
                  ;; ;; (svtv-data-invalidate-cycle-fsm :logic svtv-data$a-invalidate-cycle-fsm :exec svtv-data$c-invalidate-cycle-fsm)
                  ;; ;; (svtv-data-invalidate-namemap :logic svtv-data$a-invalidate-namemap :exec svtv-data$c-invalidate-namemap)
                  ;; (update-svtv-data->cycle-phases :logic update-svtv-data$a->cycle-phases :exec update-svtv-data$c->cycle-phases$inline)
                  ;; (svtv-data-compute-cycle :logic svtv-data$a-compute-cycle :exec svtv-data$c-compute-cycle :protect t)
                  ;; (update-svtv-data->user-names :logic update-svtv-data$a->user-names :exec update-svtv-data$c->user-names$inline)
                  ;; (svtv-data-compute-namemap :logic svtv-data$a-compute-namemap :exec svtv-data$c-compute-namemap :protect t)
                  ;; (svtv-data->base-fsm :logic svtv-data$a->base-fsm :exec svtv-data$c->base-fsm)
                  ;; (svtv-data->cycle-fsm :logic svtv-data$a->cycle-fsm :exec svtv-data$c->cycle-fsm)
                  ))))

  
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/take" :dir :system))

(local (fty::deflist svexlist :elt-type svex :true-listp t))

(local (defthm svex-lookup-of-pairlis
         (equal (svex-lookup var (pairlis$ x y))
                (b* ((index (index-of (svar-fix var) x)))
                  (and index
                       (svex-fix (nth index y)))))
         :hints(("Goal" :in-theory (enable svex-lookup svarlist-fix index-of)))))



(local
 (encapsulate nil
   ;; (local (defthm svex-eval-of-nth-split
   ;;          (equal (svex-eval (nth n x) env)
   ;;                 (if (< (nfix n) (len x))
   ;;                     (nth n (svexlist-eval x env))
   ;;                   (4vec-x)))
   ;;          :hints(("Goal" :in-theory (enable nth svexlist-eval)))))
   (local (defcong svexlist-eval-equiv equal (consp x) 1
            :hints (("goal" :use ((:instance consp-of-svexlist-eval (x x))
                                  (:instance consp-of-svexlist-eval (x x-equiv)))
                     :in-theory (disable consp-of-svexlist-eval)))))

   (local (defun ind (n x x-equiv)
            (if (zp n)
                (list x x-equiv)
              (ind (1- n) (cdr x) (cdr x-equiv)))))

   (defcong svexlist-eval-equiv svex-eval-equiv (nth n x) 2
     :hints (("goal" :induct (ind n x x-equiv) :in-theory (enable nth))))))

(local (defcong svexlist-eval-equiv svex-alist-eval-equiv (pairlis$ x y) 2
         :hints ((witness))))

(local (defcong svexlist-eval-equiv svexlist-eval-equiv (nthcdr n x) 2))

(local (defcong svexlist-eval-equiv svexlist-eval-equiv (take n x) 2))

(local (defthm svexlist-rewrite-fixpoint-under-svexlist-eval-equiv
         (svexlist-eval-equiv (svexlist-rewrite-fixpoint x :count count :verbosep verbosep)
                              x)
         :hints ((witness))))

(local (defthm pairlis-svex-alist-keys-svex-alist-vals
         (equal (pairlis$ (svex-alist-keys x) (svex-alist-vals x))
                (svex-alist-fix x))
         :hints(("Goal" :in-theory (enable pairlis$ svex-alist-keys svex-alist-vals svex-alist-fix)))))

(define svtv-data-rewrite-base-fsm (svtv-data &key ((count natp) '4) (verbosep 'nil))
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap))))
  (b* ((values (svtv-data->base-values svtv-data))
       (nextstate (svtv-data->base-nextstate svtv-data))
       (svexes (append (svex-alist-vals values) (svex-alist-vals nextstate)))
       (svexes-rw (svexlist-rewrite-fixpoint svexes :count count :verbosep verbosep))
       (values-keys (svex-alist-keys values))
       (values-len (len values-keys))
       (values-rw (pairlis$ values-keys (take values-len svexes-rw)))
       (nextstate-keys (svex-alist-keys nextstate))
       (nextstate-rw (pairlis$ nextstate-keys (nthcdr values-len svexes-rw)))
       (svtv-data (update-svtv-data->base-values values-rw svtv-data)))
    (update-svtv-data->base-nextstate nextstate-rw svtv-data)))


(define svtv-data-rewrite-cycle-fsm (svtv-data &key ((count natp) '4) (verbosep 'nil))
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap)))
                )
  (b* ((values (svtv-data->cycle-values svtv-data))
       (nextstate (svtv-data->cycle-nextstate svtv-data))
       (svexes (append (svex-alist-vals values) (svex-alist-vals nextstate)))
       (svexes-rw (svexlist-rewrite-fixpoint svexes :count count :verbosep verbosep))
       (values-keys (svex-alist-keys values))
       (values-len (len values-keys))
       (values-rw (pairlis$ values-keys (take values-len svexes-rw)))
       (nextstate-keys (svex-alist-keys nextstate))
       (nextstate-rw (pairlis$ nextstate-keys (nthcdr values-len svexes-rw)))
       (svtv-data (update-svtv-data->cycle-values values-rw svtv-data)))
    (update-svtv-data->cycle-nextstate nextstate-rw svtv-data)))


(local (defthm eval-lookup-of-svex-alist-rewrite-fixpoint
         (equal (svex-eval (svex-lookup v (svex-alist-rewrite-fixpoint x :count count :verbosep verbosep)) env)
                (svex-eval (svex-lookup v x) env))
         :hints (("goal" :use ((:instance svex-env-lookup-of-svex-alist-eval
                                (k v) (x (svex-alist-rewrite-fixpoint x :count count :verbosep verbosep)))
                               (:instance svex-env-lookup-of-svex-alist-eval
                                (k v) (x x)))
                  :in-theory (disable svex-env-lookup-of-svex-alist-eval)))))

(local (defthm svex-alist-rewrite-fixpoint-under-svex-alist-eval-equiv
         (svex-alist-eval-equiv (svex-alist-rewrite-fixpoint x :count count :verbosep verbosep)
                              x)
         :hints ((witness) (witness))))

(define svtv-data-rewrite-pipeline (svtv-data &key ((count natp) '4) (verbosep 'nil))
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap)))
                )
  (b* ((results (svtv-data->pipeline-results svtv-data))
       (results-rw (svex-alist-rewrite-fixpoint results :count count :verbosep verbosep)))
    (update-svtv-data->pipeline-results results-rw svtv-data)))
       
(local (in-theory (disable hons-dups-p)))


(define svtv-data-compute-cycle-fsm (svtv-data)
  :guard (and (svtv-data->base-fsm-validp svtv-data)
              (not (svtv-data->pipeline-validp svtv-data)))
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap)))
                )
  (b* (((svtv-fsm cycle-fsm)
        (svtv-fsm-to-cycle (svtv-data->cycle-phases svtv-data)
                           (svtv-data->base-fsm svtv-data)))
       (svtv-data (update-svtv-data->cycle-values cycle-fsm.values svtv-data))
       (svtv-data (update-svtv-data->cycle-nextstate cycle-fsm.nextstate svtv-data)))
    (update-svtv-data->cycle-fsm-validp t svtv-data)))


(define svtv-data-compute-pipeline (svtv-data &key ((rewrite booleanp) 't))
  :guard (and (svtv-data->base-fsm-validp svtv-data)
              (svtv-data->namemap-validp svtv-data)
              (svtv-data->cycle-fsm-validp svtv-data)
              (equal (svex-alist-keys (svtv-data->pipeline-initst svtv-data))
                     (svex-alist-keys (svtv-data->cycle-nextstate svtv-data))))
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable svtv-data$ap))))
  (b* ((fsm (svtv-data->cycle-fsm svtv-data))
       (probes (svtv-data->pipeline-probes svtv-data))
       (inputs (svtv-data->pipeline-inputs svtv-data))
       (overrides (svtv-data->pipeline-overrides svtv-data))
       (initst (svtv-data->pipeline-initst svtv-data))
       (outvars (svtv-probealist-outvars probes))
       (outs (svtv-fsm-run-renamed-compile inputs overrides initst fsm outvars rewrite))
       (result (svtv-probealist-extract-alist probes outs))
       (svtv-data (update-svtv-data->pipeline-results result svtv-data)))
    (update-svtv-data->pipeline-validp t svtv-data)))
       
