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

(include-book "logicman")
(include-book "stack")
(local (std::add-default-post-define-hook :fix))

(define fgl-object-concretize ((x fgl-object-p)
                      (env fgl-env-p)
                      &optional (logicman 'logicman))
  :guard (lbfr-listp (fgl-object-bfrlist x))
  :returns (new-x fgl-object-p)
  (g-concrete (fgl-object-eval x env))
  ///

  (defthm fgl-object-concretize-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (fgl-object-bfrlist x) old))
             (equal (fgl-object-concretize x env new)
                    (fgl-object-concretize x env old)))
    :hints(("Goal" :in-theory (enable fgl-object-bfrlist))))

  (defcong logicman-equiv equal (fgl-object-concretize x env logicman) 3))

(define fgl-objectlist-concretize ((x fgl-objectlist-p)
                      (env fgl-env-p)
                      &optional (logicman 'logicman))
  :guard (lbfr-listp (fgl-objectlist-bfrlist x))
  :returns (new-x fgl-objectlist-p)
  (if (atom x)
      nil
    (cons (fgl-object-concretize (car x) env)
          (fgl-objectlist-concretize (cdr x) env)))
  ///

  (defthm fgl-objectlist-concretize-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (fgl-objectlist-bfrlist x) old))
             (equal (fgl-objectlist-concretize x env new)
                    (fgl-objectlist-concretize x env old)))
    :hints(("Goal" :in-theory (enable fgl-objectlist-bfrlist))))

  (defcong logicman-equiv equal (fgl-objectlist-concretize x env logicman) 3))

(define fgl-object-alist-concretize ((x fgl-object-alist-p)
                      (env fgl-env-p)
                      &optional (logicman 'logicman))
  :guard (lbfr-listp (fgl-object-alist-bfrlist x))
  :prepwork ((local (in-theory (enable fgl-object-alist-bfrlist
                                       fgl-object-alist-fix))))
  :returns (new-x fgl-object-alist-p)
  (if (atom x)
      x
    (if (mbt (consp (car x)))
        (cons (cons (caar x)
                    (fgl-object-concretize (cdar x) env))
              (fgl-object-alist-concretize (cdr x) env))
      (fgl-object-alist-concretize (cdr x) env)))
  ///

  (defthm fgl-object-alist-concretize-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (fgl-object-alist-bfrlist x) old))
             (equal (fgl-object-alist-concretize x env new)
                    (fgl-object-alist-concretize x env old)))
    :hints(("Goal" :in-theory (enable fgl-object-alist-bfrlist)
            :induct t
            :expand ((fgl-object-alist-bfrlist x)))))

  (defcong logicman-equiv equal (fgl-object-alist-concretize x env logicman) 3))




(define fgl-object-bindings-concretize ((x fgl-object-bindings-p)
                                   (env fgl-env-p)
                                   &optional (logicman 'logicman))
  :guard (lbfr-listp (fgl-object-bindings-bfrlist x))
  :guard-hints (("goal" :in-theory (enable fgl-object-bindings-bfrlist)))
  :returns (ans fgl-object-bindings-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (pseudo-var-p (caar x))))
        (cons (cons (caar x)
                    (fgl-object-concretize (cdar x) env))
              (fgl-object-bindings-concretize (cdr x) env))
      (fgl-object-bindings-concretize (cdr x) env)))
  ///
  (local (in-theory (enable fgl-object-bindings-fix)))

  (defthm fgl-object-bindings-concretize-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (fgl-object-bindings-bfrlist x) old))
             (equal (fgl-object-bindings-concretize x env new)
                    (fgl-object-bindings-concretize x env old)))
    :hints(("Goal" :in-theory (enable fgl-object-bindings-bfrlist))))

  (defret lookup-under-iff-of-fgl-object-bindings-ev
    (implies (pseudo-var-p k)
             (iff (hons-assoc-equal k ans)
                  (hons-assoc-equal k x))))

  (defret lookup-of-fgl-object-bindings-ev
    (implies (and (pseudo-var-p k)
                  (hons-assoc-equal k x))
             (equal (hons-assoc-equal k ans)
                    (cons k (fgl-object-concretize (cdr (hons-assoc-equal k x)) env)))))

  (defcong logicman-equiv equal (fgl-object-bindings-concretize x env logicman) 3))

(define fgl-constraint-instance-concretize ((x constraint-instance-p)
                                       (env fgl-env-p)
                                       &optional (logicman 'logicman))
  :guard (lbfr-listp (constraint-instance-bfrlist x))
  :prepwork ((local (in-theory (enable constraint-instance-bfrlist))))
  :returns (ev constraint-instance-p)
  (b* (((constraint-instance x)))
    (make-constraint-instance
     :thmname x.thmname
     :subst (fgl-object-bindings-concretize x.subst env)))
  ///
  (defthm constraint-instance-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (constraint-instance-bfrlist x) old))
             (equal (fgl-constraint-instance-concretize x env new)
                    (fgl-constraint-instance-concretize x env old))))

  (defcong logicman-equiv equal (fgl-constraint-instance-concretize x env logicman) 3))

(define fgl-constraint-instancelist-concretize ((x constraint-instancelist-p)
                                           (env fgl-env-p)
                                           &optional (logicman 'logicman))
  :guard (lbfr-listp (constraint-instancelist-bfrlist x))
  :prepwork ((local (in-theory (enable constraint-instancelist-bfrlist))))
  :returns (ev constraint-instancelist-p)
  (if (atom x)
      nil
    (cons (fgl-constraint-instance-concretize (car x) env)
          (fgl-constraint-instancelist-concretize (cdr x) env)))
  ///
  (defthm fgl-constraint-instancelist-concretize-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (constraint-instancelist-bfrlist x) old))
             (equal (fgl-constraint-instancelist-concretize x env new)
                    (fgl-constraint-instancelist-concretize x env old))))

  (defcong logicman-equiv equal (fgl-constraint-instancelist-concretize x env logicman) 3))

(define fgl-scratchobj-concretize ((x scratchobj-p)
                              (env fgl-env-p)
                              &optional (logicman 'logicman))
  :guard (lbfr-listp (scratchobj->bfrlist x))
  :returns (ev scratchobj-p)
  :guard-hints ((and stable-under-simplificationp
                     '(:expand ((scratchobj->bfrlist x)))))
  ;; :prepwork ((local (in-theory (enable scratchobj->bfrlist))))
  (scratchobj-case x
    :fgl-obj (scratchobj-fgl-obj (fgl-object-concretize x.val env))
    :fgl-objlist (scratchobj-fgl-objlist (fgl-objectlist-concretize x.val env))
    :bfr (scratchobj-bfr (gobj-bfr-eval x.val env))
    :bfrlist (scratchobj-bfrlist (gobj-bfr-list-eval x.val env))
    :cinst (scratchobj-cinst (fgl-constraint-instance-concretize x.val env))
    :cinstlist (scratchobj-cinstlist (fgl-constraint-instancelist-concretize x.val env)))
  ///
  (defthm fgl-scratchobj-concretize-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (scratchobj->bfrlist x) old))
             (equal (fgl-scratchobj-concretize x env new)
                    (fgl-scratchobj-concretize x env old)))
    :hints ((and stable-under-simplificationp
                     '(:expand ((scratchobj->bfrlist x))))))

  (defthm fgl-scratchobj-concretize-of-scratchobj-fgl-obj
    (equal (fgl-scratchobj-concretize (Scratchobj-fgl-obj val) env)
           (scratchobj-fgl-obj (fgl-object-concretize val env))))

  (defthm fgl-scratchobj-concretize-of-scratchobj-fgl-objlist
    (equal (fgl-scratchobj-concretize (Scratchobj-fgl-objlist val) env)
           (scratchobj-fgl-objlist (fgl-objectlist-concretize val env))))

  (defthm fgl-scratchobj-concretize-of-scratchobj-bfr
    (equal (fgl-scratchobj-concretize (Scratchobj-bfr val) env)
           (scratchobj-bfr (gobj-bfr-eval val env))))

  (defcong logicman-equiv equal (fgl-scratchobj-concretize x env logicman) 3
    :hints(("Goal" :in-theory (disable fgl-scratchobj-concretize-of-scratchobj-fgl-obj
                                       fgl-scratchobj-concretize-of-scratchobj-fgl-objlist
                                       fgl-scratchobj-concretize-of-scratchobj-bfr
                                       ;; fgl-object-ev-of-scratchobj-fgl-obj->val
                                       ;; FGL-OBJECTLIST-EV-OF-SCRATCHOBJ-FGL-OBJLIST->VAL
                                       ;; GOBJ-BFR-EVAL-OF-SCRATCHOBJ-BFR->VAL
                                       )))))

(define fgl-scratchlist-concretize ((x scratchlist-p)
                        (env fgl-env-p)
                        &optional (logicman 'logicman))
  :guard (lbfr-listp (scratchlist-bfrlist x))
  :returns (ev scratchlist-p)
  (if (atom x)
      nil
    (cons (fgl-scratchobj-concretize (car x) env)
          (fgl-scratchlist-concretize (cdr x) env)))
  ///
  (defthm fgl-scratchlist-concretize-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (scratchlist-bfrlist x) old))
             (equal (fgl-scratchlist-concretize x env new)
                    (fgl-scratchlist-concretize x env old))))

  (defcong logicman-equiv equal (fgl-scratchlist-concretize x env logicman) 3))

(define fgl-minor-frame-concretize ((x minor-frame-p)
                               (env fgl-env-p)
                               &optional (logicman 'logicman))
  :guard (lbfr-listp (minor-frame-bfrlist x))
  :prepwork ((local (in-theory (enable minor-frame-bfrlist))))
  :returns (ev minor-frame-p)
  (b* (((minor-frame x)))
    (change-minor-frame
     x
     :bindings (fgl-object-bindings-concretize x.bindings env)
     :scratch (fgl-scratchlist-concretize x.scratch env)))
  ///
  (defthm fgl-minor-frame-concretize-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (minor-frame-bfrlist x) old))
             (equal (fgl-minor-frame-concretize x env new)
                    (fgl-minor-frame-concretize x env old))))

  (defcong logicman-equiv equal (fgl-minor-frame-concretize x env logicman) 3))

(define fgl-minor-stack-concretize ((x minor-stack-p)
                               (env fgl-env-p)
                               &optional (logicman 'logicman))
  :guard (lbfr-listp (minor-stack-bfrlist x))
  :returns (ev minor-stack-p)
  :measure (len x)
  :ruler-extenders (cons)
  (cons (fgl-minor-frame-concretize (car x) env)
        (and (consp (cdr x))
             (fgl-minor-stack-concretize (cdr x) env)))
  ///
  (defthm fgl-minor-stack-concretize-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (minor-stack-bfrlist x) old))
             (equal (fgl-minor-stack-concretize x env new)
                    (fgl-minor-stack-concretize x env old))))

  (defcong logicman-equiv equal (fgl-minor-stack-concretize x env logicman) 3))



(define fgl-major-frame-concretize ((x major-frame-p)
                               (env fgl-env-p)
                               &optional (logicman 'logicman))
  :guard (lbfr-listp (major-frame-bfrlist x))
  :prepwork ((local (in-theory (enable major-frame-bfrlist))))
  :returns (ev major-frame-p)
  (b* (((major-frame x)))
    (change-major-frame
     x
     :bindings (fgl-object-bindings-concretize x.bindings env)
     :minor-stack (fgl-minor-stack-concretize x.minor-stack env)))
  ///
  (defthm fgl-major-frame-concretize-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (major-frame-bfrlist x) old))
             (equal (fgl-major-frame-concretize x env new)
                    (fgl-major-frame-concretize x env old))))

  (defcong logicman-equiv equal (fgl-major-frame-concretize x env logicman) 3))

(define fgl-major-stack-concretize ((x major-stack-p)
                               (env fgl-env-p)
                               &optional (logicman 'logicman))
  :guard (lbfr-listp (major-stack-bfrlist x))
  :returns (ev major-stack-p)
  :measure (len x)
  :ruler-extenders (cons)
  (cons (fgl-major-frame-concretize (car x) env)
        (and (consp (cdr x))
             (fgl-major-stack-concretize (cdr x) env)))
  ///
  (defthm fgl-major-stack-concretize-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (major-stack-bfrlist x) old))
             (equal (fgl-major-stack-concretize x env new)
                    (fgl-major-stack-concretize x env old))))

  (defcong logicman-equiv equal (fgl-major-stack-concretize x env logicman) 3))



(defsection stack-semantics-preserved-lemmas
  (local (in-theory (enable fgl-major-stack-concretize
                            fgl-minor-stack-concretize
                            fgl-major-frame-concretize
                            fgl-minor-frame-concretize)))

  (defthm fgl-scratchlist-concretize-of-cdr
    (equal (fgl-scratchlist-concretize (cdr x) env)
           (cdr (fgl-scratchlist-concretize x env)))
    :hints(("Goal" :in-theory (enable fgl-scratchlist-concretize))))

  (defthm fgl-scratchlist-concretize-of-cons
    (equal (fgl-scratchlist-concretize (cons x y) env)
           (cons (fgl-scratchobj-concretize x env)
                 (fgl-scratchlist-concretize y env)))
    :hints(("Goal" :in-theory (enable fgl-scratchlist-concretize))))

  (defthm fgl-scratchlist-concretize-of-nil
    (equal (fgl-scratchlist-concretize nil env) nil)
    :hints(("Goal" :in-theory (enable fgl-scratchlist-concretize))))

  (defthm fgl-object-bindings-concretize-of-nil
    (equal (fgl-object-bindings-concretize nil env) nil)
    :hints(("Goal" :in-theory (enable fgl-object-bindings-concretize))))

  (defthm fgl-major-stack-concretize-of-stack$a-pop-scratch
    (equal (fgl-major-stack-concretize (stack$a-pop-scratch stack) env)
           (stack$a-pop-scratch (fgl-major-stack-concretize stack env)))
    :hints(("Goal" :in-theory (enable stack$a-pop-scratch))))

  (defthm fgl-major-stack-concretize-of-stack$a-push-scratch
    (equal (fgl-major-stack-concretize (stack$a-push-scratch obj stack) env)
           (stack$a-push-scratch
            (fgl-scratchobj-concretize obj env)
            (fgl-major-stack-concretize stack env)))
    :hints(("Goal" :in-theory (enable stack$a-push-scratch))))

  (defthm fgl-major-stack-concretize-of-stack$a-pop-frame
    (equal (fgl-major-stack-concretize (stack$a-pop-frame stack) env)
           (stack$a-pop-frame (fgl-major-stack-concretize stack env)))
    :hints(("Goal" :in-theory (enable stack$a-pop-frame default-car))))

  (defthm fgl-major-stack-concretize-of-stack$a-set-bindings
    (equal (fgl-major-stack-concretize (stack$a-set-bindings bindings stack) env)
           (stack$a-set-bindings (fgl-object-bindings-concretize bindings env)
                                 (fgl-major-stack-concretize stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-bindings))))

  (defthm fgl-major-stack-concretize-of-stack$a-push-frame
    (equal (fgl-major-stack-concretize (stack$a-push-frame stack) env)
           (stack$a-push-frame (fgl-major-stack-concretize stack env)))
    :hints(("Goal" :in-theory (enable stack$a-push-frame))))

  (defthm fgl-major-stack-concretize-of-stack$a-set-rule
    (equal (fgl-major-stack-concretize (stack$a-set-rule obj stack) env)
           (stack$a-set-rule obj (fgl-major-stack-concretize stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-rule))))

  (defthm fgl-major-stack-concretize-of-stack$a-set-phase
    (equal (fgl-major-stack-concretize (stack$a-set-phase obj stack) env)
           (stack$a-set-phase obj (fgl-major-stack-concretize stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-phase))))

  (defthm fgl-major-stack-concretize-of-stack$a-set-term
    (equal (fgl-major-stack-concretize (stack$a-set-term obj stack) env)
           (stack$a-set-term obj (fgl-major-stack-concretize stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-term))))

  (defthm fgl-major-stack-concretize-of-stack$a-set-term-index
    (equal (fgl-major-stack-concretize (stack$a-set-term-index obj stack) env)
           (stack$a-set-term-index obj (fgl-major-stack-concretize stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-term-index))))

  (defthm fgl-object-bindings-concretize-of-append
    (equal (fgl-object-bindings-concretize (append a b) env)
           (append (fgl-object-bindings-concretize a env)
                   (fgl-object-bindings-concretize b env)))
    :hints(("Goal" :in-theory (enable fgl-object-bindings-concretize))))

  (defthm fgl-major-stack-concretize-of-stack$a-add-minor-bindings
    (equal (fgl-major-stack-concretize (stack$a-add-minor-bindings bindings stack) env)
           (stack$a-add-minor-bindings
            (fgl-object-bindings-concretize bindings env)
            (fgl-major-stack-concretize stack env)))
    :hints(("Goal" :in-theory (enable stack$a-add-minor-bindings))))

  (defthm fgl-major-stack-concretize-of-stack$a-pop-minor-frame
    (equal (fgl-major-stack-concretize (stack$a-pop-minor-frame stack) env)
           (stack$a-pop-minor-frame (fgl-major-stack-concretize stack env)))
    :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame))))

  (defthm fgl-major-stack-concretize-of-stack$a-set-minor-bindings
    (equal (fgl-major-stack-concretize (stack$a-set-minor-bindings bindings stack) env)
           (stack$a-set-minor-bindings
            (fgl-object-bindings-concretize bindings env)
            (fgl-major-stack-concretize stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-minor-bindings))))

  (defthm fgl-major-stack-concretize-of-stack$a-push-minor-frame
    (equal (fgl-major-stack-concretize (stack$a-push-minor-frame stack) env)
           (stack$a-push-minor-frame (fgl-major-stack-concretize stack env)))
    :hints(("Goal" :in-theory (enable stack$a-push-minor-frame)))))




(defsection ev-identities
  (defthm fgl-object-concretize-identity
    (equal (fgl-object-concretize (fgl-object-concretize x env) env2 logicman2)
           (fgl-object-concretize x env))
    :hints(("Goal" :in-theory (enable fgl-object-concretize))))

  (defthm fgl-objectlist-concretize-identity
    (equal (fgl-objectlist-concretize (fgl-objectlist-concretize x env) env2 logicman2)
           (fgl-objectlist-concretize x env))
    :hints(("Goal" :in-theory (enable fgl-objectlist-concretize))))

  (defthm bfr-eval-of-boolean
    (implies (booleanp x)
             (equal (bfr-eval x env) x))
    :hints(("Goal" :in-theory (enable bfr-eval booleanp bfr->aignet-lit))))

  (defthm gobj-bfr-eval-identity
    (equal (gobj-bfr-eval (gobj-bfr-eval x env) env2 logicman2)
           (gobj-bfr-eval x env))
    :hints(("Goal" :in-theory (e/d (gobj-bfr-eval)))))

  (defthm gobj-bfr-list-eval-identity
    (equal (gobj-bfr-list-eval (gobj-bfr-list-eval x env) env2 logicman2)
           (gobj-bfr-list-eval x env))
    :hints(("Goal" :in-theory (e/d (gobj-bfr-list-eval)))))

  (defthm fgl-object-bindings-concretize-identity
    (equal (fgl-object-bindings-concretize (fgl-object-bindings-concretize x env) env2 logicman2)
           (fgl-object-bindings-concretize x env))
    :hints(("Goal" :in-theory (enable fgl-object-bindings-concretize))))

  (defthm fgl-constraint-instance-concretize-identity
    (equal (fgl-constraint-instance-concretize (fgl-constraint-instance-concretize x env) env2 logicman2)
           (fgl-constraint-instance-concretize x env))
    :hints(("Goal" :in-theory (enable fgl-constraint-instance-concretize))))

  (defthm fgl-constraint-instancelist-concretize-identity
    (equal (fgl-constraint-instancelist-concretize (fgl-constraint-instancelist-concretize x env) env2 logicman2)
           (fgl-constraint-instancelist-concretize x env))
    :hints(("Goal" :in-theory (enable fgl-constraint-instancelist-concretize))))

  (defthm fgl-scratchobj-concretize-identity
    (equal (fgl-scratchobj-concretize (fgl-scratchobj-concretize x env) env2 logicman2)
           (fgl-scratchobj-concretize x env))
    :hints(("Goal" :in-theory (e/d (fgl-scratchobj-concretize)))))

  (defthm fgl-scratchlist-concretize-identity
    (equal (fgl-scratchlist-concretize (fgl-scratchlist-concretize x env) env2 logicman2)
           (fgl-scratchlist-concretize x env))
    :hints(("Goal" :in-theory (enable fgl-scratchlist-concretize))))

  (defthm fgl-minor-frame-concretize-identity
    (equal (fgl-minor-frame-concretize (fgl-minor-frame-concretize x env) env2 logicman2)
           (fgl-minor-frame-concretize x env))
    :hints(("Goal" :in-theory (enable fgl-minor-frame-concretize))))

  (defthm fgl-minor-stack-concretize-identity
    (equal (fgl-minor-stack-concretize (fgl-minor-stack-concretize x env) env2 logicman2)
           (fgl-minor-stack-concretize x env))
    :hints(("Goal" :in-theory (enable fgl-minor-stack-concretize))))

  (defthm fgl-major-frame-concretize-identity
    (equal (fgl-major-frame-concretize (fgl-major-frame-concretize x env) env2 logicman2)
           (fgl-major-frame-concretize x env))
    :hints(("Goal" :in-theory (enable fgl-major-frame-concretize))))

  (defthm fgl-major-stack-concretize-identity
    (equal (fgl-major-stack-concretize (fgl-major-stack-concretize x env) env2 logicman2)
           (fgl-major-stack-concretize x env))
    :hints(("Goal" :in-theory (enable fgl-major-stack-concretize)))))




