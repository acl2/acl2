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

(include-book "interp-st")
(include-book "stack-ev")
(include-book "scratch-isomorphic")
(include-book "interp-st-bfrs-ok")
(local (std::add-default-post-define-hook :fix))


(acl2::def-meta-extract fgl-ev fgl-ev-list)

;; BOZO maybe doesn't belong here
(defsection major-stack-ev-of-interp-st-logicman-extension

  (def-updater-independence-thm gl-object-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (gl-object-bfrlist x) (interp-st->logicman old)))
             (equal (gl-object-ev x env (interp-st->logicman new))
                    (gl-object-ev x env (interp-st->logicman old)))))



  (def-updater-independence-thm gl-objectlist-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (gl-objectlist-bfrlist x) (interp-st->logicman old)))
             (equal (gl-objectlist-ev x env (interp-st->logicman new))
                    (gl-objectlist-ev x env (interp-st->logicman old)))))



  (def-updater-independence-thm gl-object-bindings-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (gl-object-bindings-bfrlist x) (interp-st->logicman old)))
             (equal (gl-object-bindings-ev x env (interp-st->logicman new))
                    (gl-object-bindings-ev x env (interp-st->logicman old)))))



  (def-updater-independence-thm constraint-instance-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (constraint-instance-bfrlist x) (interp-st->logicman old)))
             (equal (constraint-instance-ev x env (interp-st->logicman new))
                    (constraint-instance-ev x env (interp-st->logicman old)))))



  (def-updater-independence-thm constraint-instancelist-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (constraint-instancelist-bfrlist x) (interp-st->logicman old)))
             (equal (constraint-instancelist-ev x env (interp-st->logicman new))
                    (constraint-instancelist-ev x env (interp-st->logicman old)))))



  (def-updater-independence-thm scratchobj-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (scratchobj->bfrlist x) (interp-st->logicman old)))
             (equal (scratchobj-ev x env (interp-st->logicman new))
                    (scratchobj-ev x env (interp-st->logicman old)))))



  (def-updater-independence-thm scratchlist-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (scratchlist-bfrlist x) (interp-st->logicman old)))
             (equal (scratchlist-ev x env (interp-st->logicman new))
                    (scratchlist-ev x env (interp-st->logicman old)))))



  (def-updater-independence-thm minor-frame-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (minor-frame-bfrlist x) (interp-st->logicman old)))
             (equal (minor-frame-ev x env (interp-st->logicman new))
                    (minor-frame-ev x env (interp-st->logicman old)))))



  (def-updater-independence-thm minor-stack-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (minor-stack-bfrlist x) (interp-st->logicman old)))
             (equal (minor-stack-ev x env (interp-st->logicman new))
                    (minor-stack-ev x env (interp-st->logicman old)))))



  (def-updater-independence-thm major-frame-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (major-frame-bfrlist x) (interp-st->logicman old)))
             (equal (major-frame-ev x env (interp-st->logicman new))
                    (major-frame-ev x env (interp-st->logicman old)))))



  (def-updater-independence-thm major-stack-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (major-stack-bfrlist x) (interp-st->logicman old)))
             (equal (major-stack-ev x env (interp-st->logicman new))
                    (major-stack-ev x env (interp-st->logicman old))))))

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

(defconst *gl-primitive-thms*
  '(
    (defret gl-object-p-ans-of-<fn>
      (gl-object-p ans))
    
    (defret interp-st-bfrs-ok-of-<fn>
      (implies (and (interp-st-bfrs-ok interp-st)
                    (lbfr-listp (gl-objectlist-bfrlist args)
                                (interp-st->logicman interp-st)))
               (interp-st-bfrs-ok new-interp-st)))

    (defret bfr-listp-of-<fn>
      (implies (and
                (interp-st-bfrs-ok interp-st)
                (lbfr-listp (gl-objectlist-bfrlist args)
                            (interp-st->logicman interp-st)))
               (lbfr-listp (gl-object-bfrlist ans)
                           (interp-st->logicman new-interp-st))))

    (defret interp-st-get-of-<fn>
      (implies (and (not (equal (interp-st-field-fix key) :logicman))
                    (not (equal (interp-st-field-fix key) :stack))
                    (not (equal (interp-st-field-fix key) :pathcond))
                    (not (equal (interp-st-field-fix key) :constraint))
                    (not (equal (interp-st-field-fix key) :bvar-db)))
               (equal (interp-st-get key new-interp-st)
                      (interp-st-get key interp-st))))

    (defret major-stack-ev-of-<fn>
      (implies (interp-st-bfrs-ok interp-st)
               (equal (major-stack-ev (interp-st->stack new-interp-st) env (interp-st->logicman new-interp-st))
                      (major-stack-ev (interp-st->stack interp-st) env (interp-st->logicman interp-st)))))

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

    (defret next-bvar-of-<fn>
      (equal (next-bvar$a (interp-st->bvar-db new-interp-st))
             (next-bvar$a (interp-st->bvar-db interp-st))))

    (defret base-bvar-of-<fn>
      (equal (base-bvar$a (interp-st->bvar-db new-interp-st))
             (base-bvar$a (interp-st->bvar-db interp-st))))))



(make-event 
 `(encapsulate
    (((gl-primitive-fncall-stub * * interp-st state) => (mv * * interp-st)
      :formals (fn args interp-st state)
      :guard (and (pseudo-fnsym-p fn)
                  (gl-objectlist-p args)
                  (interp-st-bfrs-ok interp-st)
                  (interp-st-bfr-listp (gl-objectlist-bfrlist args))))
     ;; ((gl-primitive-formula-checks-stub state) => *
     ;;  :formals (state))
     )
                                              

    ;; (local (define gl-primitive-formula-checks-stub (state)
    ;;          :ignore-ok t
    ;;          :irrelevant-formals-ok t
    ;;          :returns (okp)
    ;;          t))


    (local (define gl-primitive-fncall-stub ((fn pseudo-fnsym-p)
                                             (args gl-objectlist-p)
                                             (interp-st interp-st-bfrs-ok)
                                             state)
             :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
             :ignore-ok t
             :irrelevant-formals-ok t
             :returns (mv successp ans new-interp-st)
             (mv nil nil interp-st)))

    (local (in-theory (enable gl-primitive-fncall-stub)))

    ,@*gl-primitive-thms*

    (defret eval-of-<fn>
      (implies (and successp
                    (fgl-ev-meta-extract-global-facts :state st)
                    ;; (gl-primitive-formula-checks-stub st)
                    (equal (w st) (w state))
                    (interp-st-bfrs-ok interp-st)
                    (interp-st-bfr-listp (gl-objectlist-bfrlist args)))
               (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                      (fgl-ev (cons (pseudo-fnsym-fix fn)
                                    (kwote-lst (fgl-objectlist-eval args env (interp-st->logicman interp-st))))
                              nil))))

    (deffixequiv gl-primitive-fncall-stub)))



(make-event
 `(define gl-primitive-fncall ((fn pseudo-fnsym-p)
                               (args gl-objectlist-p)
                               (dont)
                               (interp-st interp-st-bfrs-ok) 
                               state)
    :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
    :returns (mv successp
                 (ans gl-object-p)
                 new-interp-st)
    (if dont
        (mv nil nil interp-st)
      (gl-primitive-fncall-stub fn args interp-st state))
    ///
    ,@*gl-primitive-thms*
    (defret eval-of-<fn>
      (implies (and successp
                    (fgl-ev-meta-extract-global-facts :state st)
                    ;; (gl-primitive-formula-checks-stub st)
                    (equal (w st) (w state))
                    (interp-st-bfrs-ok interp-st)
                    (interp-st-bfr-listp (gl-objectlist-bfrlist args)))
               (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                      (fgl-ev (cons (pseudo-fnsym-fix fn)
                                    (kwote-lst (fgl-objectlist-eval args env (interp-st->logicman interp-st))))
                              nil))))))
