; FGL - A Symbolic Simulation Framework for ACL2
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
(include-book "bvar-db-equivs")
(include-book "constraint-db")
(include-book "config")
(include-book "contexts")
(include-book "stack")
(include-book "centaur/fty/bitstruct" :dir :system)
(include-book "prof")
(include-book "array-alist")
(include-book "cgraph")
(local (include-book "std/lists/resize-list" :dir :System))
(local (in-theory (disable nth update-nth resize-list
                           acl2::resize-list-when-atom)))
(local (in-theory (disable unsigned-byte-p)))

(local (std::add-default-post-define-hook :fix))

(fty::defbitstruct interp-flags
  ((intro-bvars booleanp :default t)
   (intro-synvars booleanp :default t)
   (simplify-logic booleanp :default t)
   (trace-rewrites booleanp :default nil)
   (make-ites booleanp :default nil)
   (branch-on-ifs booleanp :default t)))

(local (defthm unsigned-byte-p-of-flags
         (implies (interp-flags-p flags)
                  (unsigned-byte-p 60 flags))
         :hints(("Goal" :in-theory (enable interp-flags-p unsigned-byte-p)))))

(acl2::defstobj-clone constraint-pathcond pathcond :prefix "CONSTRAINT-")


(acl2::defstobj-clone bitarr acl2::bitarr :pkg fgl-pkg)

(stobjs::defnicestobj env$
  (alist :initially nil)
  (bitarr :type bitarr)
  (obj-alist :type (satisfies obj-alist-p) :fix obj-alist-fix))


(local (defthmd equal-of-len
         (implies (syntaxp (quotep n))
                  (equal (equal (len x) n)
                         (cond ((not (natp n)) nil)
                               ((equal n 0) (not (consp x)))
                               (t (and (Consp x)
                                       (equal (len (cdr x)) (1- n)))))))))

(define env$-init (env$)
  :enabled t
  :guard-hints (("goal" :in-theory (enable* env$-defs
                                            equal-of-len
                                            update-nth)))
  (mbe :logic (non-exec (create-env$))
       :exec (b* ((env$ (update-env$->alist nil env$))
                  (env$ (update-env$->obj-alist nil env$)))
               (stobj-let ((bitarr (env$->bitarr env$)))
                          (bitarr)
                          (resize-bits 0 bitarr)
                          env$))))
  


(make-event
 `(stobjs::defnicestobj interp-st
    (stack :type stack)
    (logicman :type logicman)
    (bvar-db :type bvar-db)
    (pathcond :type pathcond)
    (constraint :type pathcond)
    (constraint-db :type (satisfies constraint-db-p) :fix constraint-db-fix :pred constraint-db-p)
    (prof :type interp-profiler)
    (backchain-limit :type integer :initially -1 :fix ifix)
    ;; (bvar-mode :type t)
    (equiv-contexts :type (satisfies equiv-contextsp) :fix equiv-contexts-fix :pred equiv-contextsp)
    (reclimit :type (integer 0 *) :initially 0 :fix lnfix :pred natp)
    (config :type (satisfies fgl-config-p) :initially ,(make-fgl-config) :fix fgl-config-fix :pred fgl-config-p)
    (flags :type (and (unsigned-byte 60)
                      (satisfies interp-flags-p))
           :initially ,(make-interp-flags)
           :fix interp-flags-fix :pred interp-flags-p)

    ;; backing arrays for fgarray primitives -- see fgarrays.lisp
    (fgarrays :type (array fgarray (0)) :resizable t :pred fgarray-alistp)
    (next-fgarray :type (integer 0 *) :initially 0 :fix lnfix :pred natp)

    ;; no logical significance
    (cgraph :type (satisfies cgraph-p) :initially nil :fix cgraph-fix)
    (cgraph-memo :type (satisfies cgraph-alist-p) :initially nil :fix cgraph-alist-fix)
    (cgraph-index :type (integer 0 *) :initially 0 :fix lnfix :pred natp)
    (ctrex-env :type env$)
    (sat-ctrex :type bitarr)

    (user-scratch :type (satisfies obj-alist-p) :initially nil :fix obj-alist-fix)
    (trace-scratch :type t :initially nil)

    (errmsg :type t :initially nil)
    (debug-info :type t)
    (debug-stack :type (satisfies major-stack-p) :initially ,(list (make-major-frame)) :fix major-stack-fix)))


(define interp-st-init (interp-st)
  :guard-hints (("goal" :in-theory (e/d* (interp-st-defs
                                           update-nth
                                           equal-of-len)
                                         (default-car default-cdr cons-equal
                                           (:t update-nth) (:t true-listp)
                                           (:t true-listp-update-nth)
                                           len set::sets-are-true-lists-cheap
                                           (:t pathcondp)
                                           pathcondp-implies-update-aig-equal
                                           pathcondp-implies-update-bdd-equal
                                           pathcondp-implies-update-aignet-equal
                                           acl2::consp-of-nth-when-atom-listp))))
  (mbe :logic
       (non-exec (b* ((logicman (interp-st->logicman interp-st))
                      (interp-st (create-interp-st)))
                   (update-interp-st->logicman (logicman-init) interp-st)))
       :exec (stobj-let ((stack (interp-st->stack interp-st))
                         (logicman (interp-st->logicman interp-st))
                         (bvar-db (interp-st->bvar-db interp-st))
                         (pathcond (interp-st->pathcond interp-st))
                         (constraint-pathcond (interp-st->constraint interp-st))
                         (interp-profiler (interp-st->prof interp-st))
                         (env$ (interp-st->ctrex-env interp-st))
                         (bitarr (interp-st->sat-ctrex interp-st)))
                        (stack logicman bvar-db pathcond constraint-pathcond interp-profiler env$ bitarr)
                        (b* ((stack (stack-empty stack))
                             (logicman (logicman-init))
                             (bvar-db (init-bvar-db 0 bvar-db))
                             (pathcond (pathcond-init pathcond))
                             (constraint-pathcond (pathcond-init constraint-pathcond))
                             (interp-profiler (interp-profiler-init interp-profiler))
                             (env$ (env$-init env$))
                             (bitarr (resize-bits 0 bitarr)))
                          (mv stack logicman bvar-db pathcond constraint-pathcond interp-profiler env$ bitarr))
                        (b* ((interp-st (update-interp-st->constraint-db nil interp-st))
                             (interp-st (update-interp-st->backchain-limit -1 interp-st))
                             (interp-st (update-interp-st->equiv-contexts nil interp-st))
                             (interp-st (update-interp-st->reclimit 0 interp-st))
                             (interp-st (update-interp-st->config (make-fgl-config) interp-st))
                             (interp-st (update-interp-st->flags (make-interp-flags) interp-st))
                             (interp-st (resize-interp-st->fgarrays 0 interp-st))
                             (interp-st (update-interp-st->next-fgarray 0 interp-st))
                             (- (fast-alist-free (interp-st->cgraph interp-st))
                                (fast-alist-free (interp-st->cgraph-memo interp-st)))
                             (interp-st (update-interp-st->cgraph nil interp-st))
                             (interp-st (update-interp-st->cgraph-memo nil interp-st))
                             (interp-st (update-interp-st->cgraph-index 0 interp-st))
                             (interp-st (update-interp-st->user-scratch nil interp-st))
                             (interp-st (update-interp-st->trace-scratch nil interp-st))
                             (interp-st (update-interp-st->errmsg nil interp-st))
                             (interp-st (update-interp-st->debug-info nil interp-st)))
                          (update-interp-st->debug-stack (list (make-major-frame)) interp-st)))))



(define interp-st-put-user-scratch (key val interp-st)
  :returns (new-interp-st)
  (update-interp-st->user-scratch
   (hons-acons key val (interp-st->user-scratch interp-st))
   interp-st)
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix k) :user-scratch))
             (equal (interp-st-get k new-interp-st)
                    (interp-st-get k interp-st)))))



(defthm interp-st-implies-natp-flags
  (natp (interp-st->flags interp-st))
  :hints(("Goal" :in-theory (enable interp-st->flags)))
  :rule-classes :type-prescription)

(in-theory (disable interp-stp))






(define interp-st-prof-push (name interp-st)       
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-push name interp-profiler)
   interp-st))

(define interp-st-prof-pop-increment (successp interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-pop-increment successp interp-profiler)
   interp-st))

;; (define interp-st-prof-simple-increment-def (name interp-st)
;;   :returns (new-interp-st)
;;   :enabled t :hooks nil
;;   (stobj-let
;;    ((interp-profiler (interp-st->prof interp-st)))
;;    (interp-profiler)
;;    (prof-simple-increment-def name interp-profiler)
;;    interp-st))

(define interp-st-prof-simple-increment-exec (name interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-simple-increment-exec name interp-profiler)
   interp-st))

(define interp-st-prof-simple-increment-g (name interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-simple-increment-g name interp-profiler)
   interp-st))

(define interp-st-prof-unwind-stack (interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-unwind-stack interp-profiler)
   interp-st))

(define interp-st-prof-print-report (interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (res)
   (prof-print-report interp-profiler)
   res))

(define interp-st-prof-report (interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-report interp-profiler)
   interp-st))

(define interp-st-prof-reset (interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (prof-reset interp-profiler)
   interp-st))

(define interp-st-prof-enable (interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (update-prof-enabledp t interp-profiler)
   interp-st))

(define interp-st-prof-disable (interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (update-prof-enabledp nil interp-profiler)
   interp-st))

(define interp-st-prof-enabledp (interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (enabledp)
   (prof-enabledp interp-profiler)
   enabledp))

(define update-interp-st-prof-enabledp ((val booleanp) interp-st)
  :returns (new-interp-st)
  :enabled t :hooks nil
  (stobj-let
   ((interp-profiler (interp-st->prof interp-st)))
   (interp-profiler)
   (update-prof-enabledp val interp-profiler)
   interp-st))




(define interp-st-bindings (interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (bindings)
             (stack-bindings stack)
             bindings))

(define interp-st-minor-bindings (interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (bindings)
             (stack-minor-bindings stack)
             bindings))

(define interp-st-stack-frames (interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (frames)
             (stack-frames stack)
             frames))

(define interp-st-stack-minor-frames (interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (frames)
             (stack-minor-frames stack)
             frames))

(define interp-st-scratch-len (interp-st)
  :enabled t :hooks nil
  (stobj-let ((stack (interp-st->stack interp-st)))
             (len)
             (stack-scratch-len stack)
             len))

(define interp-st-full-scratch-len (interp-st)
  :enabled t :hooks nil
  (stobj-let ((stack (interp-st->stack interp-st)))
             (len)
             (stack-full-scratch-len stack)
             len))

(define interp-st-pop-frame (interp-st)
  :enabled t :hooks nil
  :inline t
  :guard (and (< 1 (interp-st-stack-frames interp-st))
              (eql 1 (interp-st-stack-minor-frames interp-st))
              (eql 0 (interp-st-scratch-len interp-st)))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-pop-frame stack)
             interp-st))

(define interp-st-pop-minor-frame (interp-st)
  :enabled t :hooks nil
  :inline t
  :guard (and (< 1 (interp-st-stack-minor-frames interp-st))
              (eql 0 (interp-st-scratch-len interp-st)))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-pop-minor-frame stack)
             interp-st))



(define interp-st-pop-scratch (interp-st)
  :enabled t :hooks nil
  :inline t
  :guard (< 0 (interp-st-scratch-len interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-pop-scratch stack)
             interp-st))

(define interp-st-top-scratch (interp-st)
  :enabled t :hooks nil
  :inline t
  :guard (< 0 (interp-st-scratch-len interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (obj)
             (stack-top-scratch stack)
             obj))

(define interp-st-nth-scratch ((n natp) interp-st)
  :enabled t :hooks nil
  :inline t
  :guard (< n (interp-st-full-scratch-len interp-st))
  (stobj-let ((stack (interp-st->stack interp-st)))
             (obj)
             (stack-nth-scratch n stack)
             obj))


(defsection interp-st-push/pop-scratch-kinds
  (local (include-book "scratchobj"))
  ;; (local (include-book "tools/templates" :dir :system))
  (make-event
   `(progn
      .
      ,(acl2::template-append
        '((define interp-st-push-scratch-<kind> ((x <pred>)
                                                 interp-st)
            :enabled t :hooks nil
            :inline t
            (stobj-let ((stack (interp-st->stack interp-st)))
                       (stack)
                       (stack-push-scratch-<kind> x stack)
                       interp-st))
          (define interp-st-top-scratch-<kind> (interp-st)
            :enabled t :hooks nil
            :inline t
            :guard (and (< 0 (interp-st-scratch-len interp-st))
                        (scratchobj-case (interp-st-top-scratch interp-st) :<kind>))
            (stobj-let ((stack (interp-st->stack interp-st)))
                       (obj)
                       (stack-top-scratch-<kind> stack)
                       obj))

          (define interp-st-nth-scratch-<kind> ((n natp) interp-st)
            :enabled t :hooks nil
            :inline t
            :guard (and (< n (interp-st-full-scratch-len interp-st))
                        (scratchobj-case (interp-st-nth-scratch n interp-st) :<kind>))
            (stobj-let ((stack (interp-st->stack interp-st)))
                       (obj)
                       (stack-nth-scratch-<kind> n stack)
                       obj))

          (define interp-st-update-scratch-<kind> ((n natp) (obj <pred>) interp-st)
            :enabled t :hooks nil
            :inline t
            :guard (< n (interp-st-scratch-len interp-st))
            (stobj-let ((stack (interp-st->stack interp-st)))
                       (stack)
                       (stack-update-scratch-<kind> n obj stack)
                       interp-st))

          (define interp-st-pop-scratch-<kind> (interp-st)
            :enabled t :hooks nil
            :inline t
            :guard (and (< 0 (interp-st-scratch-len interp-st))
                        (scratchobj-case (interp-st-top-scratch interp-st) :<kind>))
            (stobj-let ((stack (interp-st->stack interp-st)))
                       (obj stack)
                       (stack-pop-scratch-<kind> stack)
                       (mv obj interp-st))))
        *scratchobj-tmplsubsts*))))

(define interp-st-add-binding ((var pseudo-var-p)
                               (val fgl-object-p)
                               interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-add-binding var val stack)
             interp-st))

(define interp-st-set-bindings ((bindings fgl-object-bindings-p)
                                interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-bindings bindings stack)
             interp-st))

(define interp-st-add-minor-bindings ((bindings fgl-object-bindings-p)
                                      interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-add-minor-bindings bindings stack)
             interp-st))

(define interp-st-set-minor-bindings ((bindings fgl-object-bindings-p)
                                      interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-minor-bindings bindings stack)
             interp-st))

(define interp-st-push-frame ((bindings fgl-object-bindings-p)
                              interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (b* ((stack (stack-push-frame stack)))
               (stack-set-bindings bindings stack))
             interp-st))

(define interp-st-push-minor-frame (interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (b* ((bindings (stack-minor-bindings stack))
                  (stack (stack-push-minor-frame stack)))
               (stack-set-minor-bindings bindings stack))
             interp-st))

(define interp-st-set-rule ((rule maybe-fgl-generic-rule-p) interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-rule rule stack)
             interp-st))

(define interp-st-set-phase ((phase acl2::maybe-natp) interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-phase phase stack)
             interp-st))


(define interp-st-set-term ((term pseudo-termp) interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-term term stack)
             interp-st))

(define interp-st-set-term-index ((term-index acl2::maybe-natp) interp-st)
  :enabled t :hooks nil
  :inline t
  (stobj-let ((stack (interp-st->stack interp-st)))
             (stack)
             (stack-set-term-index term-index stack)
             interp-st))




(define interp-st-decrement-reclimit (interp-st)
  :guard (posp (interp-st->reclimit interp-st))
  (update-interp-st->reclimit (1- (interp-st->reclimit interp-st)) interp-st))

(define interp-st-increment-reclimit (interp-st)
  (update-interp-st->reclimit (1+ (lnfix (interp-st->reclimit interp-st))) interp-st))




;; Interp-st-bind:
;;
;; This works differently from a regular LET* or something.  Instead of
;; containing an expression whose value is returned, this splices some bindings
;; in between bindings that set some interp-st slots to new values and restore
;; them to their old values.  E.g.:
;;   (b* (...
;;        ((interp-st-bind
;;          (flags new-flag-expr flag-backup-var)
;;          (equiv-contexts new-equiv-contexts-expr))
;;         ((fgl-interp-recursive-call err successp-interp-st state)
;;          (fgl-rewrite-relieve-hyps rule.hyps interp-st state)))
;;        ...)
;;     ...)
;; Note: The bindings are of the form
;;        (slot-name new-value-expr &optional backup-varname)
;; If backup-varname is specified, it should be already bound to the current value of that slot.
;; Slot is accessed with interp-st->[slotname] and updated with update-interp-st->[slotname].



(define interp-st-bind-default-backup-name (slotname)
  :mode :program
  (intern-in-package-of-symbol
   (concatenate 'string "CURRENT-INTERP-ST-" (symbol-name slotname))
   'fgl::fgl-package-symbol))

(define interp-st-accessor (slotname)
  :mode :program
  (acl2::tmpl-sym-sublis `(("<FIELD>" . ,(symbol-name slotname)))
                         'interp-st-><field>
                         'fgl::fgl-package))

(define interp-st-updater (slotname)
  :mode :program
  (acl2::tmpl-sym-sublis `(("<FIELD>" . ,(symbol-name slotname)))
                         'update-interp-st-><field>
                         'fgl::fgl-package))

(define interp-st-bind-backup-vals (args interp-st-name)
  :mode :program
  (b* (((when (atom args)) nil)
       (arg (car args))
       ((when (eql (len arg) 3))
        (interp-st-bind-backup-vals (cdr args) interp-st-name))
       ((list slotname ?expr) arg)
       (backup-name (interp-st-bind-default-backup-name slotname)))
    (cons `(,backup-name (,(interp-st-accessor slotname) ,interp-st-name))
          (interp-st-bind-backup-vals (cdr args) interp-st-name))))

(define interp-st-bind-new-vals (args interp-st-name)
  :mode :program
  (b* (((when (atom args)) nil)
       (arg (car args))
       ((list slotname expr) arg))
    (cons `(,interp-st-name (,(interp-st-updater slotname) ,expr ,interp-st-name))
          (interp-st-bind-new-vals (cdr args) interp-st-name))))

(define interp-st-unbind-vals (args interp-st-name)
  :mode :program
  (b* (((when (atom args)) nil)
       (arg (car args))
       ((list slotname ?expr backup-name) arg)
       (backup-name (or backup-name (interp-st-bind-default-backup-name slotname))))
    (cons `(,interp-st-name (,(interp-st-updater slotname) ,backup-name ,interp-st-name))
          (interp-st-unbind-vals (cdr args) interp-st-name))))

(def-b*-binder interp-st-bind
  :body
  `(b* (,@(interp-st-bind-backup-vals args 'interp-st)
        ,@(interp-st-bind-new-vals args 'interp-st)
        ,@forms
        ,@(interp-st-unbind-vals args 'interp-st))
     ,rest-expr))



(define interp-st-bfr-p (x &optional (interp-st 'interp-st))
  :enabled t :hooks nil
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (ok)
             (lbfr-p x)
             ok))

(define interp-st-bfr-fix (x &optional (interp-st 'interp-st))
  :enabled t :hooks nil
  :guard (interp-st-bfr-p x)
  (mbe :logic (stobj-let ((logicman (interp-st->logicman interp-st)))
                         (new-x)
                         (lbfr-fix x)
                         new-x)
       :exec x))

(define interp-st-bfr-listp (x &optional (interp-st 'interp-st))
  :enabled t :hooks nil
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (ok)
             (lbfr-listp x)
             ok))

(define interp-st-fgl-bfr-object-fix ((x fgl-object-p) &optional (interp-st 'interp-st))
  :guard (interp-st-bfr-listp (fgl-object-bfrlist x))
  :enabled t
  (mbe :logic (stobj-let ((logicman (interp-st->logicman interp-st)))
                         (new-x)
                         (lgl-bfr-object-fix x)
                         new-x)
       :exec x))

(define interp-st-fgl-bfr-objectlist-fix ((x fgl-objectlist-p) &optional (interp-st 'interp-st))
  :guard (interp-st-bfr-listp (fgl-objectlist-bfrlist x))
  :enabled t
  (mbe :logic (stobj-let ((logicman (interp-st->logicman interp-st)))
                         (new-x)
                         (lgl-bfr-objectlist-fix x)
                         new-x)
       :exec x))


(define interp-st-bfr-mode (&optional (interp-st 'interp-st))
  :enabled t :hooks nil
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (mode)
             (logicman->mode logicman)
             mode))

(define interp-st-bfr-state (&optional (interp-st 'interp-st))
  :enabled t :hooks nil
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (bfrstate)
             (logicman->bfrstate logicman)
             bfrstate))

(define interp-st-bfr-not (x &optional (interp-st 'interp-st))
  :enabled t :hooks nil
  :inline t
  :guard (interp-st-bfr-p x)
  (stobj-let ((logicman (interp-st->logicman interp-st)))
             (not)
             (bfr-not x)
             not))


(define interp-st-nvars-ok (interp-st)
  (stobj-let ((bvar-db (interp-st->bvar-db interp-st))
              (logicman (interp-st->logicman interp-st)))
             (ok)
             (equal (next-bvar bvar-db) (bfr-nvars))
             ok))


(local
 (defthm subsetp-of-bvar-db-bfrlist-when-get-term->bvar$a
   (implies (get-term->bvar$a x bvar-db)
            (subsetp (fgl-object-bfrlist x) (bvar-db-bfrlist bvar-db)))
   :hints (("goal" :use ((:instance subsetp-bfrlist-of-bvar-db-bfrlist
                          (m (get-term->bvar$a x bvar-db))))
            :in-theory (disable subsetp-bfrlist-of-bvar-db-bfrlist)))))

(define interp-st-add-term-bvar ((x fgl-object-p) interp-st state)
  :returns (mv bfr new-interp-st)
  :guard (interp-st-nvars-ok interp-st)
  :prepwork ((local (in-theory (enable interp-st-nvars-ok))))
  (stobj-let ((bvar-db (interp-st->bvar-db interp-st))
              (logicman (interp-st->logicman interp-st)))
             (bfr bvar-db logicman)
             (b* ((nextvar (next-bvar bvar-db))
                  (bvar-db (add-term-bvar (fgl-object-fix x) bvar-db))
                  (bvar-db (maybe-add-equiv-term (fgl-object-fix x) nextvar bvar-db state))
                  (logicman (logicman-add-var logicman))
                  (bfr (bfr-var nextvar logicman)))
               (mv bfr bvar-db logicman))
             (mv bfr interp-st))
  ///
  (defret interp-st-nvars-ok-of-interp-st-add-term-bvar
    (implies (interp-st-nvars-ok interp-st)
             (interp-st-nvars-ok new-interp-st)))

  (defret bfr-p-of-interp-st-add-term-bvar
    (implies (interp-st-nvars-ok interp-st)
             (lbfr-p bfr (interp-st->logicman new-interp-st)))
    :hints(("Goal" :in-theory (enable interp-st-bfr-p))))

  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :logicman))
                  (not (equal (interp-st-field-fix key) :bvar-db)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret logicman-extension-p-of-<fn>
    (implies (equal old-logicman (interp-st->logicman interp-st))
             (logicman-extension-p (interp-st->logicman new-interp-st) old-logicman)))

  (defret nvars-ok-of-<fn>
    (implies (equal (next-bvar$a (interp-st->bvar-db interp-st))
                    (bfr-nvars (interp-st->logicman interp-st)))
             (equal (next-bvar$a (interp-st->bvar-db new-interp-st))
                    (bfr-nvars (interp-st->logicman new-interp-st)))))

  (defret bvar-db-bfrlist-of-<fn>
    (acl2::set-equiv (bvar-db-bfrlist (interp-st->bvar-db new-interp-st))
                     (append (fgl-object-bfrlist x)
                             (bvar-db-bfrlist (interp-st->bvar-db interp-st)))))

  (defret logicman-get-of-<fn>
    (implies (not (equal (logicman-field-fix key) :aignet))
             (equal (logicman-get key (interp-st->logicman new-interp-st))
                    (logicman-get key (interp-st->logicman interp-st))))))

(define interp-st-add-term-bvar-unique ((x fgl-object-p) interp-st state)
  :returns (mv bfr new-interp-st)
  :guard (interp-st-nvars-ok interp-st)
  :prepwork ((local (in-theory (enable interp-st-nvars-ok
                                       bfr-varname-p))))
  (stobj-let ((bvar-db (interp-st->bvar-db interp-st))
              (logicman (interp-st->logicman interp-st)))
             (bfr bvar-db logicman)
             (b* ((var (get-term->bvar x bvar-db))
                  ((when var)
                   (mv (bfr-var var logicman) bvar-db logicman))
                  (nextvar (next-bvar bvar-db))
                  (bvar-db (add-term-bvar (fgl-object-fix x) bvar-db))
                  (bvar-db (maybe-add-equiv-term (fgl-object-fix x) nextvar bvar-db state))
                  (logicman (logicman-add-var logicman))
                  (bfr (bfr-var nextvar logicman)))
               (mv bfr bvar-db logicman))
             (mv bfr interp-st))
  ///
  (defret interp-st-nvars-ok-of-interp-st-add-term-bvar-unique
    (implies (interp-st-nvars-ok interp-st)
             (interp-st-nvars-ok new-interp-st)))

  (defret bfr-p-of-interp-st-add-term-bvar-unique
    (implies (interp-st-nvars-ok interp-st)
             (lbfr-p bfr (interp-st->logicman new-interp-st)))
    :hints(("Goal" :in-theory (enable interp-st-bfr-p))))

  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :logicman))
                  (not (equal (interp-st-field-fix key) :bvar-db)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret logicman-extension-p-of-<fn>
    (implies (equal old-logicman (interp-st->logicman interp-st))
             (logicman-extension-p (interp-st->logicman new-interp-st) old-logicman)))

  (defret nvars-ok-of-<fn>
    (implies (equal (next-bvar$a (interp-st->bvar-db interp-st))
                    (bfr-nvars (interp-st->logicman interp-st)))
             (equal (next-bvar$a (interp-st->bvar-db new-interp-st))
                    (bfr-nvars (interp-st->logicman new-interp-st)))))

  (defret bvar-db-bfrlist-of-<fn>
    (acl2::set-equiv (bvar-db-bfrlist (interp-st->bvar-db new-interp-st))
                     (append (fgl-object-bfrlist x)
                             (bvar-db-bfrlist (interp-st->bvar-db interp-st)))))

  (defret logicman-get-of-<fn>
    (implies (not (equal (logicman-field-fix key) :aignet))
             (equal (logicman-get key (interp-st->logicman new-interp-st))
                    (logicman-get key (interp-st->logicman interp-st))))))


(def-updater-independence-thm logicman->aignet-of-interp-st->logicman
  (implies (equal (logicman-get :aignet (interp-st->logicman new))
                  (logicman-get :aignet (interp-st->logicman old)))
           (equal (logicman->aignet (interp-st->logicman new))
                  (logicman->aignet (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get)
                                 (logicman->aignet-of-update)))))

(def-updater-independence-thm logicman->strash-of-interp-st->logicman
  (implies (equal (logicman-get :strash (interp-st->logicman new))
                  (logicman-get :strash (interp-st->logicman old)))
           (equal (logicman->strash (interp-st->logicman new))
                  (logicman->strash (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get)
                                 (logicman->strash-of-update)))))

(def-updater-independence-thm logicman->ipasir-of-interp-st->logicman
  (implies (equal (logicman-get :ipasir (interp-st->logicman new))
                  (logicman-get :ipasir (interp-st->logicman old)))
           (equal (logicman->ipasiri n (interp-st->logicman new))
                  (logicman->ipasiri n (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get logicman->ipasiri)
                                 (logicman->ipasiri-of-update)))))

(def-updater-independence-thm logicman->sat-lits-of-interp-st->logicman
  (implies (equal (logicman-get :sat-lits (interp-st->logicman new))
                  (logicman-get :sat-lits (interp-st->logicman old)))
           (equal (logicman->sat-litsi n (interp-st->logicman new))
                  (logicman->sat-litsi n (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get logicman->sat-litsi)
                                 (logicman->sat-litsi-of-update)))))

(def-updater-independence-thm logicman->mode-of-interp-st->logicman
  (implies (equal (logicman-get :mode (interp-st->logicman new))
                  (logicman-get :mode (interp-st->logicman old)))
           (equal (logicman->mode (interp-st->logicman new))
                  (logicman->mode (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get)
                                 (logicman->mode-of-update)))))

(def-updater-independence-thm logicman->aignet-refcounts-of-interp-st->logicman
  (implies (equal (logicman-get :aignet-refcounts (interp-st->logicman new))
                  (logicman-get :aignet-refcounts (interp-st->logicman old)))
           (equal (logicman->aignet-refcounts (interp-st->logicman new))
                  (logicman->aignet-refcounts (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get)
                                 (logicman->aignet-refcounts-of-update)))))

(def-updater-independence-thm logicman->refcounts-index-of-interp-st->logicman
  (implies (equal (logicman-get :refcounts-index (interp-st->logicman new))
                  (logicman-get :refcounts-index (interp-st->logicman old)))
           (equal (logicman->refcounts-index (interp-st->logicman new))
                  (logicman->refcounts-index (interp-st->logicman old))))
  :hints(("Goal" :in-theory (e/d (logicman-get)
                                 (logicman->refcounts-index-of-update)))))


(def-updater-independence-thm logicman-invar-of-interp-st-logicman-extension
  (implies (and (equal new-logicman (interp-st->logicman new))
                (equal old-logicman (interp-st->logicman old))
                (logicman-extension-p new-logicman old-logicman)
                (logicman-invar old-logicman)
                (equal (logicman-get :ipasir new-logicman)
                       (logicman-get :ipasir old-logicman))
                (equal (logicman-get :sat-lits new-logicman)
                       (logicman-get :sat-lits old-logicman))
                (equal (logicman->refcounts-index new-logicman)
                       (logicman->refcounts-index old-logicman))
                (equal (logicman->aignet-refcounts new-logicman)
                       (logicman->aignet-refcounts old-logicman)))
           (logicman-invar (interp-st->logicman new))))






;; Trace this!
(define fgl-interp-error-message ((str stringp)
                                   (arglist))
  :returns (error-message (or (consp error-message)
                              (stringp error-message))
                          :rule-classes :type-prescription)
  (if arglist
      (cons (str-fix str) arglist)
    (str-fix str)))

(defmacro fgl-msg (str &rest args)
  `(fgl-interp-error-message ,str ,(make-fmt-bindings acl2::*base-10-chars* args)))


(define fgl-interp-store-debug-info (msg obj interp-st)
  :returns new-interp-st
  :guard (not (eq msg :unreachable))
  (b* (((when (interp-st->errmsg interp-st))
        interp-st)
       ((unless (mbt (not (eq msg :unreachable))))
        interp-st)
       (interp-st (update-interp-st->errmsg msg interp-st))
       (stack-obj (stobj-let ((stack (interp-st->stack interp-st)))
                             (obj)
                             (stack-extract stack)
                             obj))
       (interp-st (update-interp-st->debug-info obj interp-st))
       (interp-st (update-interp-st->debug-stack stack-obj interp-st)))
    interp-st)
  ///

  (defret interp-st-get-of-<fn>
    (implies (and (not (equal (interp-st-field-fix key) :errmsg))
                  (not (equal (interp-st-field-fix key) :debug-info))
                  (not (equal (interp-st-field-fix key) :debug-stack)))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret <fn>-preserves-error
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret interp-st->errmsg-of-<fn>
    (implies (and msg
                  (not (equal msg :unreachable)))
             (interp-st->errmsg new-interp-st)))

  (defret interp-st->errmsg-equal-unreachable-of-<fn>
    (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
             (not (equal (interp-st->errmsg new-interp-st) :unreachable)))))

(defmacro fgl-interp-error (&key msg debug-obj (nvals '1))
  `(b* ((msg ,msg)
        (debug-obj ,debug-obj)
        (interp-st (fgl-interp-store-debug-info msg debug-obj interp-st)))
     ,(if (eql nvals 0)
          '(mv interp-st state)
        `(mv ,@(acl2::repeat nvals nil) interp-st state))))


(define interp-st-set-error (msg interp-st)
  :returns new-interp-st
  (if (interp-st->errmsg interp-st)
      interp-st
    (update-interp-st->errmsg msg interp-st))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (equal (interp-st-field-fix key) :errmsg))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st))))

  (defret <fn>-preserves-error
    (implies (interp-st->errmsg interp-st)
             (equal (interp-st->errmsg new-interp-st)
                    (interp-st->errmsg interp-st))))

  (defret interp-st->errmsg-of-<fn>
    (implies msg
             (interp-st->errmsg new-interp-st)))

  (defret errmsg-differs-of-<fn>
    (implies (and msg2 (not (equal msg2 msg)))
             (equal (equal (interp-st->errmsg new-interp-st) msg2)
                    (equal (interp-st->errmsg interp-st) msg2)))))

(define interp-st-bvar-db-debug (interp-st)
  (stobj-let ((bvar-db (interp-st->bvar-db interp-st)))
             (alist)
             (bvar-db-debug bvar-db)
             alist))
