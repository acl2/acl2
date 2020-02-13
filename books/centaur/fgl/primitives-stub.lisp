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

(include-book "interp-st")
(include-book "stack-ev")
(include-book "scratch-isomorphic")
(include-book "interp-st-bfrs-ok")
(include-book "centaur/meta/world-equiv" :dir :system)
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable w)))

;; BOZO maybe doesn't belong here
(defmacro eval-alist-extension-p (x y)
    `(acl2::sub-alistp ,y ,x))

(defun-sk fgl-ev-context-equiv-forall-extensions (contexts
                                                  obj
                                                  term
                                                  eval-alist)
  (forall (ext)
          (implies (eval-alist-extension-p ext eval-alist)
                   (equal (fgl-ev-context-fix contexts
                                              (fgl-ev term ext))
                          (fgl-ev-context-fix contexts obj))))
  :rewrite :direct)


(defsection fgl-major-stack-concretize-of-interp-st-logicman-extension

  (def-updater-independence-thm fgl-object-concretize-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (fgl-object-bfrlist x) (interp-st->logicman old)))
             (equal (fgl-object-concretize x env (interp-st->logicman new))
                    (fgl-object-concretize x env (interp-st->logicman old)))))



  (def-updater-independence-thm fgl-objectlist-concretize-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (fgl-objectlist-bfrlist x) (interp-st->logicman old)))
             (equal (fgl-objectlist-concretize x env (interp-st->logicman new))
                    (fgl-objectlist-concretize x env (interp-st->logicman old)))))



  (def-updater-independence-thm fgl-object-bindings-concretize-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (fgl-object-bindings-bfrlist x) (interp-st->logicman old)))
             (equal (fgl-object-bindings-concretize x env (interp-st->logicman new))
                    (fgl-object-bindings-concretize x env (interp-st->logicman old)))))



  (def-updater-independence-thm constraint-instance-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (constraint-instance-bfrlist x) (interp-st->logicman old)))
             (equal (fgl-constraint-instance-concretize x env (interp-st->logicman new))
                    (fgl-constraint-instance-concretize x env (interp-st->logicman old)))))



  (def-updater-independence-thm fgl-constraint-instancelist-concretize-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (constraint-instancelist-bfrlist x) (interp-st->logicman old)))
             (equal (fgl-constraint-instancelist-concretize x env (interp-st->logicman new))
                    (fgl-constraint-instancelist-concretize x env (interp-st->logicman old)))))



  (def-updater-independence-thm fgl-scratchobj-concretize-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (scratchobj->bfrlist x) (interp-st->logicman old)))
             (equal (fgl-scratchobj-concretize x env (interp-st->logicman new))
                    (fgl-scratchobj-concretize x env (interp-st->logicman old)))))



  (def-updater-independence-thm fgl-scratchlist-concretize-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (scratchlist-bfrlist x) (interp-st->logicman old)))
             (equal (fgl-scratchlist-concretize x env (interp-st->logicman new))
                    (fgl-scratchlist-concretize x env (interp-st->logicman old)))))



  (def-updater-independence-thm fgl-minor-frame-concretize-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (minor-frame-bfrlist x) (interp-st->logicman old)))
             (equal (fgl-minor-frame-concretize x env (interp-st->logicman new))
                    (fgl-minor-frame-concretize x env (interp-st->logicman old)))))



  (def-updater-independence-thm fgl-minor-stack-concretize-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (minor-stack-bfrlist x) (interp-st->logicman old)))
             (equal (fgl-minor-stack-concretize x env (interp-st->logicman new))
                    (fgl-minor-stack-concretize x env (interp-st->logicman old)))))



  (def-updater-independence-thm fgl-major-frame-concretize-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (major-frame-bfrlist x) (interp-st->logicman old)))
             (equal (fgl-major-frame-concretize x env (interp-st->logicman new))
                    (fgl-major-frame-concretize x env (interp-st->logicman old)))))



  (def-updater-independence-thm fgl-major-stack-concretize-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (major-stack-bfrlist x) (interp-st->logicman old)))
             (equal (fgl-major-stack-concretize x env (interp-st->logicman new))
                    (fgl-major-stack-concretize x env (interp-st->logicman old))))))

;; BOZO maybe doesn't belong here
(define interp-st-scratch-isomorphic (x y)
  :non-executable t
  :verify-guards nil
  (major-stack-scratch-isomorphic (interp-st->stack x) (interp-st->stack y))
  ///
  (defequiv interp-st-scratch-isomorphic)

  (defcong interp-st-scratch-isomorphic major-stack-scratch-isomorphic (interp-st->stack x) 1)

  (defcong major-stack-scratch-isomorphic interp-st-scratch-isomorphic (update-interp-st->stack stack x) 1)

  (defthm update-interp-st->stack-norm-under-interp-st-scratch-isomorphic
    (implies (syntaxp (not (equal x ''nil)))
             (interp-st-scratch-isomorphic
              (update-interp-st->stack stack x)
              (update-interp-st->stack stack nil))))

  (defthm interp-st-scratch-isomorphic-of-update-interp-st->stack-identity
    (interp-st-scratch-isomorphic
     (update-interp-st->stack (major-stack-fix (interp-st->stack interp-st)) x)
     interp-st))

  (defthm interp-st-scratch-isomorphic-of-update-interp-st->stack-identity2
    (interp-st-scratch-isomorphic
     (update-interp-st->stack (interp-st->stack interp-st) x)
     interp-st))

  (def-updater-independence-thm interp-st-scratch-isomorphic-identity
    (implies (major-stack-equiv (interp-st->stack new) (interp-st->stack old))
             (equal (interp-st-scratch-isomorphic new x)
                    (interp-st-scratch-isomorphic old x)))))

(defconst *fgl-meta-primitive-and-binder-rule-thms*
  '((defret interp-st->reclimit-of-<fn>
      (equal (interp-st->reclimit new-interp-st)
             (interp-st->reclimit interp-st)))

    ;; (defret interp-st->errmsg-of-<fn>
    ;;   (equal (interp-st->errmsg new-interp-st)
    ;;          (interp-st->errmsg interp-st)))

    (defret interp-st->errmsg-of-<fn>
      (implies (interp-st->errmsg interp-st)
               (equal (interp-st->errmsg new-interp-st)
                      (interp-st->errmsg interp-st))))

    ;; (defret interp-st->errmsg-equal-unreachable-of-<fn>
    ;;   (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
    ;;            (not (equal (interp-st->errmsg new-interp-st)
    ;;                        :unreachable))))

    (defret interp-st->equiv-contexts-of-<fn>
      (equal (interp-st->equiv-contexts new-interp-st)
             (interp-st->equiv-contexts interp-st)))

    (defret scratch-isomorphic-of-<fn>
      (interp-st-scratch-isomorphic new-interp-st (double-rewrite interp-st)))

    (defret logicman->mode-of-<fn>
      (equal (logicman->mode (interp-st->logicman new-interp-st))
             (logicman->mode (interp-st->logicman interp-st))))

    (defret bfr-nvars-of-<fn>
      (equal (bfr-nvars (interp-st->logicman new-interp-st))
             (bfr-nvars (interp-st->logicman interp-st))))

    (defret pathcond-enabledp-of-<fn>
      (iff (nth *pathcond-enabledp* (interp-st->pathcond new-interp-st))
           (nth *pathcond-enabledp* (interp-st->pathcond interp-st))))

    (defret pathcond-rewind-stack-len-of-<fn>
      (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
               (equal (pathcond-rewind-stack-len mode (interp-st->pathcond new-interp-st))
                      (pathcond-rewind-stack-len mode (interp-st->pathcond interp-st)))))

    (defret pathcond-rewind-ok-of-<fn>
      (implies (equal mode (logicman->mode (interp-st->logicman interp-st)))
               (iff (pathcond-rewind-ok mode (interp-st->pathcond new-interp-st))
                    (pathcond-rewind-ok mode (interp-st->pathcond interp-st)))))

    (defret pathcond-eval-checkpoints-of-<fn>
      (implies (interp-st-bfrs-ok interp-st)
               (equal (logicman-pathcond-eval-checkpoints!
                       env
                       (interp-st->pathcond new-interp-st)
                       (interp-st->logicman new-interp-st))
                      (logicman-pathcond-eval-checkpoints!
                       env
                       (interp-st->pathcond interp-st)
                       (interp-st->logicman interp-st)))))

    (defret interp-st->errmsg-equal-unreachable-of-<fn>
      (implies (and (not (equal (interp-st->errmsg interp-st) :unreachable))
                    (bind-free '((env . env)) (env))
                    (logicman-pathcond-eval env (interp-st->pathcond interp-st)
                                            (interp-st->logicman interp-st))
                    (logicman-pathcond-eval env (interp-st->constraint interp-st)
                                            (interp-st->logicman interp-st))
                    (interp-st-bfrs-ok interp-st))
               (not (equal (interp-st->errmsg new-interp-st)
                           :unreachable))))

    (defret constraint-eval-of-<fn>
      (implies (interp-st-bfrs-ok interp-st)
               (equal (logicman-pathcond-eval
                       env
                       (interp-st->constraint new-interp-st)
                       (interp-st->logicman new-interp-st))
                      (logicman-pathcond-eval
                       env
                       (interp-st->constraint interp-st)
                       (interp-st->logicman interp-st)))))

    (defret next-bvar-of-<fn>
      (equal (next-bvar$a (interp-st->bvar-db new-interp-st))
             (next-bvar$a (interp-st->bvar-db interp-st))))

    (defret base-bvar-of-<fn>
      (equal (base-bvar$a (interp-st->bvar-db new-interp-st))
             (base-bvar$a (interp-st->bvar-db interp-st))))

    (defret w-state-of-<fn>
      (equal (w new-state) (w state)))


    (defret get-bvar->term-eval-of-<fn>
      (b* ((bvar-db (interp-st->bvar-db interp-st)))
        (implies (and (interp-st-bfrs-ok interp-st)
                      (<= (base-bvar$a bvar-db) (nfix n))
                      (< (nfix n) (next-bvar$a bvar-db)))
                 (iff (fgl-object-eval (get-bvar->term$a n (interp-st->bvar-db new-interp-st))
                                       env
                                       (interp-st->logicman new-interp-st))
                      (fgl-object-eval (get-bvar->term$a n bvar-db)
                                       env
                                       (interp-st->logicman interp-st))))))

    (defret major-stack-concretize-of-<fn>
      (implies (interp-st-bfrs-ok interp-st)
               (equal (fgl-major-stack-concretize (interp-st->stack new-interp-st) env (interp-st->logicman new-interp-st))
                      (fgl-major-stack-concretize (interp-st->stack interp-st) env (interp-st->logicman interp-st)))))))

(defconst *fgl-meta-and-primitive-rule-thms*
  (append '((defret interp-st-bfrs-ok-of-<fn>
              (implies (and (interp-st-bfrs-ok interp-st)
                            (lbfr-listp (fgl-objectlist-bfrlist args)
                                        (interp-st->logicman interp-st)))
                       (interp-st-bfrs-ok new-interp-st))))
          *fgl-meta-primitive-and-binder-rule-thms*))

(defconst *fgl-primitive-rule-thms*
  (append '((defret fgl-object-p-ans-of-<fn>
              (fgl-object-p ans))

            (defret bfr-listp-of-<fn>
              (implies (and
                        (interp-st-bfrs-ok interp-st)
                        (lbfr-listp (fgl-objectlist-bfrlist args)
                                    (interp-st->logicman interp-st)))
                       (lbfr-listp (fgl-object-bfrlist ans)
                                   (interp-st->logicman new-interp-st)))))
          *fgl-meta-and-primitive-rule-thms*))

(set-state-ok t)

(define implies* (x y)
  :no-function t
  (implies x y)
  ///
  (defthm implies*-of-nil
    (implies* nil x))

  (defthm implies*-of-t
    (iff (implies* t x) x))

  (defthm implies*-x-nil
    (iff (implies* x nil)
         (not x)))

  (defthm implies*-x-t
    (implies* x t))

  (defcong iff equal (implies* x y) 1)
  (defcong iff equal (implies* x y) 2))

(define not* (x)
  :no-function t
  (not x)
  ///
  (defcong iff equal (not* x) 1))

(local (in-theory (enable implies* not*)))

(defmacro <=* (x y) `(not* (< ,y ,x)))
(defmacro >=* (x y) `(not* (< ,x ,y)))

(make-event
 (let ((body `;; (b* (((mv successp ans new-interp-st new-state) result))
                (and* ,@(sublis '((implies . implies*)
                                  (and . and*)
                                  (not . not*)
                                  (iff . iff*)
                                  (or . or*)
                                  (<= . <=*)
                                  (>= . >=*))
                                (strip-cars (strip-cdrs (strip-cdrs *fgl-primitive-rule-thms*))))
                      (implies* (and* successp
                                     (equal contexts (interp-st->equiv-contexts interp-st))
                                     (fgl-ev-meta-extract-global-facts :state st)
                                     formula-check
                                     (equal (w st) (w state))
                                     (interp-st-bfrs-ok interp-st)
                                     (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
                                     (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                             (interp-st->constraint interp-st)
                                                             (interp-st->logicman interp-st))
                                     (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                             (interp-st->pathcond interp-st)
                                                             (interp-st->logicman interp-st)))
                                (equal (fgl-ev-context-fix contexts
                                                           (fgl-object-eval ans env (interp-st->logicman new-interp-st)))
                                       (fgl-ev-context-fix contexts
                                                           (fgl-object-eval (g-apply origfn args) env (interp-st->logicman interp-st))))))))
   `(progn (defconst *fgl-primitive-constraint-base-body* ',body)
           (defun-nx fgl-primitive-constraint-base (successp ans new-interp-st new-state
                                                    origfn args interp-st state
                                                    formula-check
                                                    mode env n contexts st)
             ,body))))

(defun-sk fgl-primitive-constraint (successp ans new-interp-st new-state
                                    origfn args interp-st sta
                                    formula-check)
  (forall (mode env n contexts st)
          (fgl-primitive-constraint-base
           successp ans new-interp-st new-state
           origfn args interp-st sta
           formula-check
           mode env n contexts st))
  :rewrite :direct)

(defthm fgl-primitive-constraint-of-fail
  (fgl-primitive-constraint nil nil interp-st state
                            origfn args interp-st state formula-check))


(defconst *fgl-meta-rule-thms*
  (append '((defret fgl-object-bindings-p-bindings-of-<fn>
              (fgl-object-bindings-p bindings))

            (defret pseudo-termp-rhs-of-<fn>
              (pseudo-termp rhs))

            (defret bfr-listp-of-<fn>
              (implies (and
                        (interp-st-bfrs-ok interp-st)
                        (lbfr-listp (fgl-objectlist-bfrlist args)
                                    (interp-st->logicman interp-st)))
                       (lbfr-listp (fgl-object-bindings-bfrlist bindings)
                                   (interp-st->logicman new-interp-st)))))

          *fgl-meta-and-primitive-rule-thms*))




(make-event
 (let ((body `;; (b* (((mv successp rhs bindings new-interp-st new-state) result))
                (and* ,@(sublis '((implies . implies*)
                                  (and . and*)
                                  (not . not*)
                                  (iff . iff*)
                                  (or . or*)
                                  (<= . <=*)
                                  (>= . >=*))
                                (strip-cars (strip-cdrs (strip-cdrs *fgl-meta-rule-thms*))))
                      (implies* (and* successp
                                     (equal contexts (interp-st->equiv-contexts interp-st))
                                     (fgl-ev-meta-extract-global-facts :state st)
                                     formula-check
                                     (equal (w st) (w state))
                                     (interp-st-bfrs-ok interp-st)
                                     (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
                                     (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                             (interp-st->constraint interp-st)
                                                             (interp-st->logicman interp-st))
                                     (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                             (interp-st->pathcond interp-st)
                                                             (interp-st->logicman interp-st))
                                     (pseudo-fnsym-p origfn))
                                (fgl-ev-context-equiv-forall-extensions
                                 contexts
                                 (fgl-ev (cons origfn (kwote-lst
                                                       (fgl-objectlist-eval
                                                        args env
                                                        (interp-st->logicman interp-st))))
                                         nil)
                                 rhs
                                 (fgl-object-bindings-eval bindings env (interp-st->logicman new-interp-st)))))))
   `(progn
      (defconst *fgl-meta-constraint-base-body* ',body)
      (defun-nx fgl-meta-constraint-base (successp rhs bindings new-interp-st new-state
                                          origfn args interp-st state
                                          formula-check
                                          mode env n contexts st)
        ,body))))

(defun-sk fgl-meta-constraint (successp rhs bindings new-interp-st new-state
                               origfn args interp-st sta
                               formula-check)
  (forall (mode env n contexts st)
          (fgl-meta-constraint-base
           successp rhs bindings new-interp-st new-state
           origfn args interp-st sta
           formula-check
           mode env n contexts st))
  :rewrite :direct)

(defthm fgl-meta-constraint-of-fail
  (fgl-meta-constraint nil nil nil interp-st state
                       origfn args interp-st state formula-check))

(defconst *fgl-binder-rule-thms*
  (append '((defret fgl-object-bindings-p-of-<fn>
              (fgl-object-bindings-p bindings))

            (defret pseudo-termp-rhs-of-<fn>
              (pseudo-termp rhs))

            (defret equiv-contextsp-rhs-contexts-of-<fn>
              (equiv-contextsp rhs-contexts))

            (defret bfr-listp-of-<fn>
              (implies (and
                        (interp-st-bfrs-ok interp-st)
                        (lbfr-listp (fgl-objectlist-bfrlist args)
                                    (interp-st->logicman interp-st)))
                       (lbfr-listp (fgl-object-bindings-bfrlist bindings)
                                   (interp-st->logicman new-interp-st))))

            (defret interp-st-bfrs-ok-of-<fn>
              (implies (and (interp-st-bfrs-ok interp-st)
                            (lbfr-listp (fgl-objectlist-bfrlist args)
                                        (interp-st->logicman interp-st)))
                       (interp-st-bfrs-ok new-interp-st))))

          *fgl-meta-primitive-and-binder-rule-thms*))

(make-event
 (let ((body `;; (b* (((mv successp rhs bindings rhs-contexts new-interp-st new-state) result))
                (and* ,@(sublis '((implies . implies*)
                                  (and . and*)
                                  (not . not*)
                                  (iff . iff*)
                                  (or . or*)
                                  (<= . <=*)
                                  (>= . >=*))
                                (strip-cars (strip-cdrs (strip-cdrs *fgl-binder-rule-thms*))))
                     (implies* (and* successp
                                   (equal contexts (interp-st->equiv-contexts interp-st))
                                   (fgl-ev-meta-extract-global-facts :state st)
                                   formula-check
                                   (equal (w st) (w state))
                                   (interp-st-bfrs-ok interp-st)
                                   (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
                                   (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                           (interp-st->constraint interp-st)
                                                           (interp-st->logicman interp-st))
                                   (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                                           (interp-st->pathcond interp-st)
                                                           (interp-st->logicman interp-st))
                                   (fgl-ev-context-equiv-forall-extensions
                                    rhs-contexts
                                    rhs-val
                                    rhs eval-alist)
                                   (eval-alist-extension-p eval-alist (fgl-object-bindings-eval bindings env (interp-st->logicman new-interp-st)))
                                   (pseudo-fnsym-p origfn))
                              (equal (fgl-ev-context-fix contexts (fgl-ev (cons origfn
                                                                                (cons (pseudo-term-quote rhs-val)
                                                                                      (kwote-lst
                                                                                       (fgl-objectlist-eval
                                                                                        args env
                                                                                        (interp-st->logicman interp-st)))))
                                                                          nil))
                                     (fgl-ev-context-fix contexts rhs-val))))))
   `(progn (defconst *fgl-binder-constraint-base-body* ',body)
           (defun-nx fgl-binder-constraint-base (successp rhs bindings rhs-contexts new-interp-st new-state
                                                 origfn args interp-st state
                                                 formula-check
                                                 mode env n contexts st rhs-val eval-alist)
             ,body))))

(defun-sk fgl-binder-constraint (successp rhs bindings rhs-contexts new-interp-st new-state
                                 origfn args interp-st sta
                                 formula-check)
  (forall (mode env n contexts st rhs-val eval-alist)
          (fgl-binder-constraint-base
           successp rhs bindings rhs-contexts new-interp-st new-state
           origfn args interp-st sta
           formula-check
           mode env n contexts st rhs-val eval-alist))
  :rewrite :direct)

(defthm fgl-binder-constraint-of-fail
  (fgl-binder-constraint nil nil nil nil interp-st state
                         origfn args interp-st state formula-check))






(encapsulate
  (((fgl-primitive-fncall-stub * * * interp-st state) => (mv * * interp-st state)
    :formals (primfn origfn args interp-st state)
    :guard (and (pseudo-fnsym-p primfn)
                (pseudo-fnsym-p origfn)
                (fgl-objectlist-p args)
                (interp-st-bfrs-ok interp-st)
                (interp-st-bfr-listp (fgl-objectlist-bfrlist args))))
   ((fgl-meta-fncall-stub * * * interp-st state) => (mv * * * interp-st state)
    :formals (primfn origfn args interp-st state)
    :guard (and (pseudo-fnsym-p primfn)
                (pseudo-fnsym-p origfn)
                (fgl-objectlist-p args)
                (interp-st-bfrs-ok interp-st)
                (interp-st-bfr-listp (fgl-objectlist-bfrlist args))))

   ((fgl-binder-fncall-stub * * * interp-st state) => (mv * * * * interp-st state)
    :formals (primfn origfn args interp-st state)
    :guard (and (pseudo-fnsym-p primfn)
                (pseudo-fnsym-p origfn)
                (fgl-objectlist-p args)
                (interp-st-bfrs-ok interp-st)
                (interp-st-bfr-listp (fgl-objectlist-bfrlist args))))
   ((fgl-formula-checks-stub state) => *
    :formals (state))
   )
  

  (local (define fgl-formula-checks-stub (state)
           :ignore-ok t
           :irrelevant-formals-ok t
           :returns (okp)
           t))

  (defcong world-equiv equal (fgl-formula-checks-stub state) 1)

  (define fgl-primitive-fncall-stub ((primfn pseudo-fnsym-p)
                                     (origfn pseudo-fnsym-p)
                                     (args fgl-objectlist-p)
                                     (interp-st interp-st-bfrs-ok)
                                     state)
    :guard (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
    :ignore-ok t
    :irrelevant-formals-ok t
    :returns (mv successp ans new-interp-st new-state)
    :local-def t
    :progn t
    :hooks nil
    (mv nil nil interp-st state))

  (local (in-theory (enable fgl-primitive-fncall-stub)))

  ;; ,@*fgl-primitive-rule-thms*

  ;; (defret eval-of-<fn>
  ;;   (implies (and successp
  ;;                 (equal contexts (interp-st->equiv-contexts interp-st))
  ;;                 (fgl-ev-meta-extract-global-facts :state st)
  ;;                 (fgl-formula-checks-stub st)
  ;;                 (equal (w st) (w state))
  ;;                 (interp-st-bfrs-ok interp-st)
  ;;                 (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
  ;;                 (logicman-pathcond-eval (fgl-env->bfr-vals env)
  ;;                                         (interp-st->constraint interp-st)
  ;;                                         (interp-st->logicman interp-st))
  ;;                 (logicman-pathcond-eval (fgl-env->bfr-vals env)
  ;;                                         (interp-st->pathcond interp-st)
  ;;                                         (interp-st->logicman interp-st)))
  ;;            (equal (fgl-ev-context-fix contexts
  ;;                                       (fgl-object-eval ans env (interp-st->logicman new-interp-st)))
  ;;                   (fgl-ev-context-fix contexts
  ;;                                       (fgl-object-eval (g-apply origfn args) env (interp-st->logicman interp-st))))))

  (defret fgl-primitive-constraint-of-<fn>
    (fgl-primitive-constraint successp ans new-interp-st new-state
                              origfn args interp-st state
                              (fgl-formula-checks-stub state))
    :fn fgl-primitive-fncall-stub)

  (deffixequiv fgl-primitive-fncall-stub :skip-const-thm t :skip-cong-thm t)



  (define fgl-meta-fncall-stub ((primfn pseudo-fnsym-p)
                                (origfn pseudo-fnsym-p)
                                (args fgl-objectlist-p)
                                (interp-st interp-st-bfrs-ok)
                                state)
    :guard (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
    :ignore-ok t
    :irrelevant-formals-ok t
    :returns (mv successp rhs bindings new-interp-st new-state)
    :local-def t
    :progn t
    :hooks nil
    (mv nil nil nil interp-st state))

  (local (in-theory (enable fgl-meta-fncall-stub)))

  ;; ,@*fgl-meta-rule-thms*

  
  ;; (defret eval-of-<fn>
  ;;   (implies (and successp
  ;;                 (equal contexts (interp-st->equiv-contexts interp-st))
  ;;                 (fgl-ev-meta-extract-global-facts :state st)
  ;;                 (fgl-formula-checks-stub st)
  ;;                 (equal (w st) (w state))
  ;;                 (interp-st-bfrs-ok interp-st)
  ;;                 (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
  ;;                 (logicman-pathcond-eval (fgl-env->bfr-vals env)
  ;;                                         (interp-st->constraint interp-st)
  ;;                                         (interp-st->logicman interp-st))
  ;;                 (logicman-pathcond-eval (fgl-env->bfr-vals env)
  ;;                                         (interp-st->pathcond interp-st)
  ;;                                         (interp-st->logicman interp-st))
  ;;                 (pseudo-fnsym-p origfn))
  ;;            (fgl-ev-context-equiv-forall-extensions
  ;;             contexts
  ;;             (fgl-ev (cons origfn (kwote-lst
  ;;                                   (fgl-objectlist-eval
  ;;                                    args env
  ;;                                    (interp-st->logicman interp-st))))
  ;;                     nil)
  ;;             rhs
  ;;             (fgl-object-bindings-eval bindings env (interp-st->logicman new-interp-st)))))

  (defret fgl-meta-constraint-of-<fn>
    (fgl-meta-constraint successp rhs bindings new-interp-st new-state
                         origfn args interp-st state
                         (fgl-formula-checks-stub state))
    :fn fgl-meta-fncall-stub)

  (deffixequiv fgl-meta-fncall-stub :skip-const-thm t :skip-cong-thm t)


  (define fgl-binder-fncall-stub ((primfn pseudo-fnsym-p)
                                  (origfn pseudo-fnsym-p)
                                  (args fgl-objectlist-p)
                                  (interp-st interp-st-bfrs-ok)
                                  state)
    :guard (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
    :ignore-ok t
    :irrelevant-formals-ok t
    :returns (mv successp rhs bindings rhs-contexts new-interp-st new-state)
    :local-def t
    :progn t
    :hooks nil
    (mv nil nil nil nil interp-st state))

  (local (in-theory (enable fgl-binder-fncall-stub)))
  
  ;; ,@*fgl-binder-rule-thms*

  ;; (defret eval-of-<fn>
  ;;   (implies (and successp
  ;;                 (equal contexts (interp-st->equiv-contexts interp-st))
  ;;                 (fgl-ev-meta-extract-global-facts :state st)
  ;;                 (fgl-formula-checks-stub st)
  ;;                 (equal (w st) (w state))
  ;;                 (interp-st-bfrs-ok interp-st)
  ;;                 (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
  ;;                 (logicman-pathcond-eval (fgl-env->bfr-vals env)
  ;;                                         (interp-st->constraint interp-st)
  ;;                                         (interp-st->logicman interp-st))
  ;;                 (logicman-pathcond-eval (fgl-env->bfr-vals env)
  ;;                                         (interp-st->pathcond interp-st)
  ;;                                         (interp-st->logicman interp-st))
  ;;                 (fgl-ev-context-equiv-forall-extensions
  ;;                  rhs-contexts
  ;;                  rhs-val
  ;;                  rhs eval-alist)
  ;;                 (eval-alist-extension-p eval-alist (fgl-object-bindings-eval bindings env (interp-st->logicman new-interp-st)))
  ;;                 (pseudo-fnsym-p origfn))
  ;;            (equal (fgl-ev-context-fix contexts (fgl-ev (cons origfn
  ;;                                                              (cons (pseudo-term-quote rhs-val)
  ;;                                                                    (kwote-lst
  ;;                                                                     (fgl-objectlist-eval
  ;;                                                                      args env
  ;;                                                                      (interp-st->logicman interp-st)))))
  ;;                                                        nil))
  ;;                   (fgl-ev-context-fix contexts rhs-val))))

  (defret fgl-binder-constraint-of-<fn>
    (fgl-binder-constraint successp rhs bindings rhs-contexts new-interp-st new-state
                           origfn args interp-st state
                           (fgl-formula-checks-stub state))
    :fn fgl-binder-fncall-stub)

  (deffixequiv fgl-binder-fncall-stub :skip-const-thm t :skip-cong-thm t))

(deffixequiv fgl-primitive-fncall-stub)
(deffixequiv fgl-meta-fncall-stub)
(deffixequiv fgl-binder-fncall-stub)

(local (defun remove-bind-free (x)
         (if (atom x)
             x
           (if (and (consp (car x))
                    (eq (caar x) 'bind-free))
               (remove-bind-free (cdr x))
             (cons (remove-bind-free (car x))
                   (remove-bind-free (cdr x)))))))
             

(local (defthm w-state-equal-forward
         (implies (equal (w st) (w state))
                  (world-equiv st state))
         :hints(("Goal" :in-theory (enable world-equiv)))
         :rule-classes :forward-chaining))

(local (defthm fgl-formula-checks-stub-when-world-equal
         (implies (and (fgl-formula-checks-stub st)
                       (equal (w st) (w state)))
                  (fgl-formula-checks-stub state))))

(defsection and*-split-clause-proc
  (defevaluator and*-ev and*-ev-list ((acl2::binary-and* x y) (if a b c) (not x) (equal x y) (implies x y)) :namedp t)
  (local (acl2::def-join-thms and*-ev))

  (local (acl2::def-ev-pseudo-term-fty-support and*-ev and*-ev-list))

  (define lambda-calls-from-bodies ((formals symbol-listp)
                                   (bodies pseudo-term-listp)
                                   (args pseudo-term-listp))
    :guard (eql (len formals) (len args))
    :hooks nil
    :returns (lambdas pseudo-term-listp)
    (if (atom bodies)
        nil
      (cons (pseudo-term-lambda formals (car bodies) args)
            (lambda-calls-from-bodies formals (cdr bodies) args)))
    ///
    (defret and*-ev-of-conjoin-<fn>
      (iff (and*-ev (conjoin lambdas) env)
           (and*-ev (conjoin bodies) (pairlis$ formals (and*-ev-list args env)))))

    (defret and*-ev-of-disjoin-<fn>
      (iff (and*-ev (disjoin lambdas) env)
           (and*-ev (disjoin bodies) (pairlis$ formals (and*-ev-list args env))))))

  (define split-and* ((x pseudo-termp))
    :returns (conj pseudo-term-listp)
    :measure (pseudo-term-count x)
    :verify-guards nil
    (pseudo-term-case x
      :fncall (cond ((eq x.fn 'acl2::binary-and*)
                     (append (split-and* (first x.args))
                             (split-and* (second x.args))))
                    ((and (eq x.fn 'acl2::if)
                          (equal (third x.args) ''nil))
                     (append (split-and* (first x.args))
                             (split-and* (second x.args))))
                    (t (list (pseudo-term-fix x))))
      :lambda (lambda-calls-from-bodies x.formals (split-and* x.body) x.args)
      :otherwise (list (pseudo-term-fix x)))
    ///
    (verify-guards split-and*)
    
    (local (defun-sk and*-ev-of-split-and-cond (x)
             (forall env
                     (iff (and*-ev (conjoin (split-and* x)) env)
                          (and*-ev x env)))
             :rewrite :direct))
    (local (in-theory (disable and*-ev-of-split-and-cond)))
    (local (defthm and*-ev-of-split-and-lemma
             (and*-ev-of-split-and-cond x)
             :hints (("goal" :induct (split-and* x))
                     (and stable-under-simplificationp
                          `(:expand (,(car (last clause))))))))
    (defthm and*-ev-of-split-and
      (iff (and*-ev (conjoin (split-and* x)) env)
           (and*-ev x env))))

  (local (defthm and*-ev-disjoin-pseudo-term-list-fix
           (iff (and*-ev (disjoin (pseudo-term-list-fix x)) a)
                (and*-ev (disjoin x) a))
           :hints(("Goal" :in-theory (enable pseudo-term-list-fix)
                   :induct (len x)))))

  (define add-last-clauses ((prev pseudo-term-listp) (lasts pseudo-term-listp))
    :returns (clauses pseudo-term-list-listp)
    (if (atom lasts)
        nil
      (cons (append (pseudo-term-list-fix prev)
                    (list (pseudo-term-fix (car lasts))))
            (add-last-clauses prev (cdr lasts))))
    ///
    (defthm conjoin-clauses-of-add-last-clauses
      (iff (and*-ev (conjoin-clauses (add-last-clauses prev lasts)) env)
           (or (and*-ev (disjoin prev) env)
               (and*-ev (conjoin lasts) env)))))
  
  (local (defthm and*-ev-of-disjoin-take
           (implies (not (and*-ev (disjoin x) a))
                    (not (and*-ev (disjoin (take n x)) a)))))

  (local (defthm and*-ev-of-car-last
           (implies (not (and*-ev (disjoin x) a))
                    (not (and*-ev (car (last x)) a)))))

  (define and*-split-clause-proc ((clause pseudo-term-listp))
    :hooks nil
    (b* ((last (car (last clause)))
         (prev (butlast clause 1)))
      (add-last-clauses prev (split-and* last)))
    ///
    (defthm and*-split-clause-proc-correct
      (implies (and (pseudo-term-listp clause)
                    (alistp a)
                    (and*-ev (conjoin-clauses (and*-split-clause-proc clause)) a))
               (and*-ev (disjoin clause) a))
      :rule-classes :clause-processor))

  (local (defthm and*ev-dumb-negate-lit-correct
           (implies (pseudo-termp x)
                    (iff (and*-ev (acl2::dumb-negate-lit x) a)
                         (not (and*-ev x a))))
           :hints(("Goal" :in-theory (enable acl2::dumb-negate-lit)))))


  (verify-termination acl2::dumb-negate-lit-lst)


  (local (defthm and*-ev-disjoin-dumb-negate-lit-list
           (implies (pseudo-term-listp x)
                    (iff (and*-ev (disjoin (acl2::dumb-negate-lit-lst x)) a)
                         (not (and*-ev (conjoin x) a))))
           :hints(("Goal" :in-theory (enable acl2::dumb-negate-lit-lst)))))

  (local (defthm pseudo-term-listp-of-dumb-negate-lit-lst
           (implies (pseudo-term-listp x)
                    (pseudo-term-listp (acl2::dumb-negate-lit-lst x)))
           :hints(("Goal" :in-theory (enable acl2::dumb-negate-lit-lst)))))

  (define flatten-and*-hyp ((lit pseudo-termp))
    :returns (lits pseudo-term-listp)
    :measure (pseudo-term-count lit)
    :verify-guards nil
    (pseudo-term-case lit
      :fncall (cond ((eq lit.fn 'not)
                     (ec-call (acl2::dumb-negate-lit-lst (split-and* (first lit.args)))))
                    ((eq lit.fn 'implies)
                     (append (ec-call (acl2::dumb-negate-lit-lst (split-and* (first lit.args))))
                             (list (second lit.args))))
                    (t (list (pseudo-term-fix lit))))
      :lambda (lambda-calls-from-bodies lit.formals
                                        (flatten-and*-hyp lit.body)
                                        lit.args)
      :otherwise (list (pseudo-term-fix lit)))
    ///
    (verify-guards flatten-and*-hyp)
    (local (defun-sk and*-ev-of-flatten-and*-hyp-cond (lit)
             (forall a
                     (iff (and*-ev (disjoin (flatten-and*-hyp lit)) a)
                          (and*-ev lit a)))
             :rewrite :direct))
    (local (in-theory (disable and*-ev-of-flatten-and*-hyp-cond)))
    (local (defthmd and*-ev-of-flatten-and*-hyp-lemma
             (and*-ev-of-flatten-and*-hyp-cond lit)
             :hints (("goal" :induct (flatten-and*-hyp lit))
                     (and stable-under-simplificationp
                          `(:expand (,(car (last clause))))))))
    (defthm and*-ev-of-flatten-and*-hyp
      (iff (and*-ev (disjoin (flatten-and*-hyp lit)) a)
           (and*-ev lit a))
      :hints (("goal" :use and*-ev-of-flatten-and*-hyp-lemma))))

  (define flatten-and*-hyps ((clause pseudo-term-listp))
    :returns (new-clause pseudo-term-listp)
    (if (atom clause)
        nil
      (append (flatten-and*-hyp (car clause))
              (flatten-and*-hyps (cdr clause))))
    ///
    (defthm and*-ev-of-flatten-and*-hyps
      (iff (and*-ev (disjoin (flatten-and*-hyps clause)) a)
           (and*-ev (disjoin clause) a))))

  (define flatten-and*-clause-proc ((clause pseudo-term-listp))
    (list (flatten-and*-hyps clause))
    ///
    (defthm flatten-and*-clause-proc-correct
      (implies (and (pseudo-term-listp clause)
                    (alistp a)
                    (and*-ev (conjoin-clauses (flatten-and*-clause-proc clause)) a))
               (and*-ev (disjoin clause) a))
      :rule-classes :clause-processor)))


(make-event
 `(defthm fgl-primitive-constraint-rule
    (b* (((mv successp ans new-interp-st new-state)
          (fgl-primitive-fncall-stub
           primfn origfn args interp-st state))
         (formula-check (fgl-formula-checks-stub state)))
      ,(sublis '((and* . and)
                 (implies* . implies)
                 (iff* . iff)
                 (not* . not)
                 (or* . or)
                 (<=* . <=)
                 (>=* . >=))
               ;; (remove-bind-free

               *fgl-primitive-constraint-base-body*))
    :hints (("goal" :use (fgl-primitive-constraint-of-fgl-primitive-fncall-stub
                          (:instance fgl-primitive-constraint-necc
                           (successp (mv-nth 0 (fgl-primitive-fncall-stub
                                                primfn origfn args interp-st state)))
                           (ans      (mv-nth 1 (fgl-primitive-fncall-stub
                                                primfn origfn args interp-st state)))
                           (new-interp-st (mv-nth 2 (fgl-primitive-fncall-stub
                                                     primfn origfn args interp-st state)))
                           (new-state (mv-nth 3 (fgl-primitive-fncall-stub
                                                 primfn origfn args interp-st state)))
                           (sta state)
                           (formula-check (fgl-formula-checks-stub state))))
             :in-theory nil)
            '(:clause-processor (flatten-and*-clause-proc clause)
              :in-theory '(fgl-primitive-constraint-base))
            '(:clause-processor (and*-split-clause-proc clause))
            '(:in-theory '(fgl-primitive-constraint-base
                           implies*-of-nil implies*-of-t implies*-x-nil implies*-x-t
                           acl2::and*-rem-first acl2::and*-rem-second
                           acl2::and*-nil-first acl2::and*-nil-second
                           iff-implies-equal-implies*-1
                           iff-implies-equal-implies*-2
                           iff-implies-equal-not*-1
                           acl2::iff-implies-equal-and*-1
                           acl2::iff-implies-iff-and*-2
                           iff*
                           (not*))
              :do-not '(preprocess)
              ;; :case-split-limitations (10 10)
              )
            (and stable-under-simplificationp
                 '(:clause-processor (flatten-and*-clause-proc clause))))))

(defsection fgl-primitive-fncall-stub
  (local (std::set-define-current-function fgl-primitive-fncall-stub))
  ;; (local (defthm iff-is-iff*
  ;;          (equal (iff x y) (iff* x y))))
  ;; (local
  ;;  #!acl2
  ;;  (progn (defun quick-and-dirty-srs-off (cl1 ac)
  ;;           (declare (ignore cl1 ac)
  ;;                    (xargs :mode :logic :guard t))
  ;;           nil)

  ;;         (defattach-system quick-and-dirty-srs quick-and-dirty-srs-off)))
  (local
   (make-event
    `(defthm fgl-primitive-constraint-rule
       (b* (((mv successp ans new-interp-st new-state)
             (fgl-primitive-fncall-stub
              primfn origfn args interp-st state))
            (formula-check (fgl-formula-checks-stub state)))
         ,(sublis '((and* . and)
                    (implies* . implies)
                    (iff* . iff)
                    (not* . not)
                    (or* . or)
                    (<=* . <=)
                    (>=* . >=))
                  *fgl-primitive-constraint-base-body*))
       :hints (("goal" :use (fgl-primitive-constraint-of-fgl-primitive-fncall-stub
                             (:instance fgl-primitive-constraint-necc
                              (successp (mv-nth 0 (fgl-primitive-fncall-stub
                                                   primfn origfn args interp-st state)))
                              (ans      (mv-nth 1 (fgl-primitive-fncall-stub
                                                   primfn origfn args interp-st state)))
                              (new-interp-st (mv-nth 2 (fgl-primitive-fncall-stub
                                                        primfn origfn args interp-st state)))
                              (new-state (mv-nth 3 (fgl-primitive-fncall-stub
                                                    primfn origfn args interp-st state)))
                              (sta state)
                              (formula-check (fgl-formula-checks-stub state))))
                :in-theory nil)
               '(:in-theory '(fgl-primitive-constraint-base
                              implies*-of-nil implies*-of-t implies*-x-nil implies*-x-t
                              acl2::and*-rem-first acl2::and*-rem-second
                              acl2::and*-nil-first acl2::and*-nil-second
                              iff-implies-equal-implies*-1
                              iff-implies-equal-implies*-2
                              iff-implies-equal-not*-1
                              acl2::iff-implies-equal-and*-1
                              acl2::iff-implies-iff-and*-2
                              iff*
                              (not*)))))))
  (make-event
   `(progn . ,*fgl-primitive-rule-thms*))

  (set-default-hints nil)


  (defret eval-of-<fn>
    (implies (and successp
                  (equal contexts (interp-st->equiv-contexts interp-st))
                  (fgl-ev-meta-extract-global-facts :state st)
                  (fgl-formula-checks-stub st)
                  (equal (w st) (w state))
                  (interp-st-bfrs-ok interp-st)
                  (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
                  (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                          (interp-st->constraint interp-st)
                                          (interp-st->logicman interp-st))
                  (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                          (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st)))
             (equal (fgl-ev-context-fix contexts
                                        (fgl-object-eval ans env (interp-st->logicman new-interp-st)))
                    (fgl-ev-context-fix contexts
                                        (fgl-object-eval (g-apply origfn args) env (interp-st->logicman interp-st)))))))




(defsection fgl-meta-fncall-stub
  (local (std::set-define-current-function fgl-meta-fncall-stub))
  ;; (local (defthm iff-is-iff*
  ;;          (equal (iff x y) (iff* x y))))
  (local
   (make-event
    `(defthm fgl-meta-constraint-rule
       (b* (((mv successp rhs bindings new-interp-st new-state)
             (fgl-meta-fncall-stub
              primfn origfn args interp-st state))
            (formula-check (fgl-formula-checks-stub state)))
         ,(sublis '((and* . and)
                    (implies* . implies)
                    (iff* . iff)
                    (not* . not)
                    (or* . or)
                    (<=* . <=)
                    (>=* . >=))
                  ;; (remove-bind-free

                  *fgl-meta-constraint-base-body*))
       :hints (("goal" :use (fgl-meta-constraint-of-fgl-meta-fncall-stub
                             (:instance fgl-meta-constraint-necc
                              (successp (mv-nth 0 (fgl-meta-fncall-stub
                                                   primfn origfn args interp-st state)))
                              (rhs      (mv-nth 1 (fgl-meta-fncall-stub
                                                   primfn origfn args interp-st state)))
                              (bindings (mv-nth 2 (fgl-meta-fncall-stub
                                                   primfn origfn args interp-st state)))
                              (new-interp-st (mv-nth 3 (fgl-meta-fncall-stub
                                                        primfn origfn args interp-st state)))
                              (new-state (mv-nth 4 (fgl-meta-fncall-stub
                                                    primfn origfn args interp-st state)))
                              (sta state)
                              (formula-check (fgl-formula-checks-stub state))))
                :in-theory nil)
               '(:in-theory '(fgl-meta-constraint-base
                              implies*-of-nil implies*-of-t implies*-x-nil implies*-x-t
                              acl2::and*-rem-first acl2::and*-rem-second
                              acl2::and*-nil-first acl2::and*-nil-second
                              iff-implies-equal-implies*-1
                              iff-implies-equal-implies*-2
                              iff-implies-equal-not*-1
                              acl2::iff-implies-equal-and*-1
                              acl2::iff-implies-iff-and*-2
                              iff*
                              (not*)))))))
  
  (make-event
   `(progn . ,*fgl-meta-rule-thms*))

  (defret eval-of-<fn>
    (implies (and successp
                  (equal contexts (interp-st->equiv-contexts interp-st))
                  (fgl-ev-meta-extract-global-facts :state st)
                  (fgl-formula-checks-stub st)
                  (equal (w st) (w state))
                  (interp-st-bfrs-ok interp-st)
                  (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
                  (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                          (interp-st->constraint interp-st)
                                          (interp-st->logicman interp-st))
                  (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                          (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (pseudo-fnsym-p origfn))
             (fgl-ev-context-equiv-forall-extensions
              contexts
              (fgl-ev (cons origfn (kwote-lst
                                    (fgl-objectlist-eval
                                     args env
                                     (interp-st->logicman interp-st))))
                      nil)
              rhs
              (fgl-object-bindings-eval bindings env (interp-st->logicman new-interp-st))))))





(defsection fgl-binder-fncall-stub
  (local (std::set-define-current-function fgl-binder-fncall-stub))

  (local
   (make-event
    `(defthm fgl-binder-constraint-rule
       (b* (((mv successp rhs bindings rhs-contexts new-interp-st new-state)
             (fgl-binder-fncall-stub
              primfn origfn args interp-st state))
            (formula-check (fgl-formula-checks-stub state)))
         ,(sublis '((and* . and)
                    (implies* . implies)
                    (iff* . iff)
                    (not* . not)
                    (or* . or)
                    (<=* . <=)
                    (>=* . >=))
                  *fgl-binder-constraint-base-body*))
       :hints (("goal" :use (fgl-binder-constraint-of-fgl-binder-fncall-stub
                             (:instance fgl-binder-constraint-necc
                              (successp (mv-nth 0 (fgl-binder-fncall-stub
                                                   primfn origfn args interp-st state)))
                              (rhs      (mv-nth 1 (fgl-binder-fncall-stub
                                                   primfn origfn args interp-st state)))
                              (bindings (mv-nth 2 (fgl-binder-fncall-stub
                                                   primfn origfn args interp-st state)))
                              (rhs-contexts (mv-nth 3 (fgl-binder-fncall-stub
                                                       primfn origfn args interp-st state)))
                              (new-interp-st (mv-nth 4 (fgl-binder-fncall-stub
                                                        primfn origfn args interp-st state)))
                              (new-state (mv-nth 5 (fgl-binder-fncall-stub
                                                    primfn origfn args interp-st state)))
                              (sta state)
                              (formula-check (fgl-formula-checks-stub state))))
                :in-theory nil)
               '(:in-theory '(fgl-binder-constraint-base
                              implies*-of-nil implies*-of-t implies*-x-nil implies*-x-t
                              acl2::and*-rem-first acl2::and*-rem-second
                              acl2::and*-nil-first acl2::and*-nil-second
                              iff-implies-equal-implies*-1
                              iff-implies-equal-implies*-2
                              iff-implies-equal-not*-1
                              acl2::iff-implies-equal-and*-1
                              acl2::iff-implies-iff-and*-2
                              iff*
                              (not*)))))))
  
  (make-event
   `(progn . ,*fgl-binder-rule-thms*))

  (defret eval-of-<fn>
    (implies (and successp
                  (equal contexts (interp-st->equiv-contexts interp-st))
                  (fgl-ev-meta-extract-global-facts :state st)
                  (fgl-formula-checks-stub st)
                  (equal (w st) (w state))
                  (interp-st-bfrs-ok interp-st)
                  (interp-st-bfr-listp (fgl-objectlist-bfrlist args))
                  (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                          (interp-st->constraint interp-st)
                                          (interp-st->logicman interp-st))
                  (logicman-pathcond-eval (fgl-env->bfr-vals env)
                                          (interp-st->pathcond interp-st)
                                          (interp-st->logicman interp-st))
                  (fgl-ev-context-equiv-forall-extensions
                   rhs-contexts
                   rhs-val
                   rhs eval-alist)
                  (eval-alist-extension-p eval-alist (fgl-object-bindings-eval bindings env (interp-st->logicman new-interp-st)))
                  (pseudo-fnsym-p origfn))
             (equal (fgl-ev-context-fix contexts (fgl-ev (cons origfn
                                                               (cons (pseudo-term-quote rhs-val)
                                                                     (kwote-lst
                                                                      (fgl-objectlist-eval
                                                                       args env
                                                                       (interp-st->logicman interp-st)))))
                                                         nil))
                    (fgl-ev-context-fix contexts rhs-val)))
    :hints(("Goal" :in-theory (disable fgl-ev-context-equiv-forall-extensions)))))




