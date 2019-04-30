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

(include-book "logicman")
(include-book "stack")
(local (std::add-default-post-define-hook :fix))

(define gl-object-ev ((x gl-object-p)
                      (env gl-env-p)
                      &optional (logicman 'logicman))
  :guard (lbfr-listp (gl-object-bfrlist x))
  :returns (new-x gl-object-p)
  (g-concrete (fgl-object-eval x env))
  ///

  (defthm gl-object-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (gl-object-bfrlist x) old))
             (equal (gl-object-ev x env new)
                    (gl-object-ev x env old)))
    :hints(("Goal" :in-theory (enable gl-object-bfrlist))))

  (defcong logicman-equiv equal (gl-object-ev x env logicman) 3))

(define gl-objectlist-ev ((x gl-objectlist-p)
                      (env gl-env-p)
                      &optional (logicman 'logicman))
  :guard (lbfr-listp (gl-objectlist-bfrlist x))
  :returns (new-x gl-objectlist-p)
  (if (atom x)
      nil
    (cons (gl-object-ev (car x) env)
          (gl-objectlist-ev (cdr x) env)))
  ///

  (defthm gl-objectlist-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (gl-objectlist-bfrlist x) old))
             (equal (gl-objectlist-ev x env new)
                    (gl-objectlist-ev x env old)))
    :hints(("Goal" :in-theory (enable gl-objectlist-bfrlist))))

  (defcong logicman-equiv equal (gl-objectlist-ev x env logicman) 3))




(define gl-object-alist-ev ((x gl-object-alist-p)
                                   (env gl-env-p)
                                   &optional (logicman 'logicman))
  :guard (lbfr-listp (gl-object-alist-bfrlist x))
  :guard-hints (("goal" :in-theory (enable gl-object-alist-bfrlist)))
  :returns (ans gl-object-alist-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (pseudo-var-p (caar x))))
        (cons (cons (caar x)
                    (gl-object-ev (cdar x) env))
              (gl-object-alist-ev (cdr x) env))
      (gl-object-alist-ev (cdr x) env)))
  ///
  (local (in-theory (enable gl-object-alist-fix)))

  (defthm gl-object-alist-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (gl-object-alist-bfrlist x) old))
             (equal (gl-object-alist-ev x env new)
                    (gl-object-alist-ev x env old)))
    :hints(("Goal" :in-theory (enable gl-object-alist-bfrlist))))

  (defret lookup-under-iff-of-gl-object-alist-ev
    (implies (pseudo-var-p k)
             (iff (hons-assoc-equal k ans)
                  (hons-assoc-equal k x))))

  (defret lookup-of-gl-object-alist-ev
    (implies (and (pseudo-var-p k)
                  (hons-assoc-equal k x))
             (equal (hons-assoc-equal k ans)
                    (cons k (gl-object-ev (cdr (hons-assoc-equal k x)) env)))))

  (defcong logicman-equiv equal (gl-object-alist-ev x env logicman) 3))

(define constraint-instance-ev ((x constraint-instance-p)
                                       (env gl-env-p)
                                       &optional (logicman 'logicman))
  :guard (lbfr-listp (constraint-instance-bfrlist x))
  :prepwork ((local (in-theory (enable constraint-instance-bfrlist))))
  :returns (ev constraint-instance-p)
  (b* (((constraint-instance x)))
    (make-constraint-instance
     :thmname x.thmname
     :subst (gl-object-alist-ev x.subst env)))
  ///
  (defthm constraint-instance-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (constraint-instance-bfrlist x) old))
             (equal (constraint-instance-ev x env new)
                    (constraint-instance-ev x env old))))

  (defcong logicman-equiv equal (constraint-instance-ev x env logicman) 3))

(define constraint-instancelist-ev ((x constraint-instancelist-p)
                                           (env gl-env-p)
                                           &optional (logicman 'logicman))
  :guard (lbfr-listp (constraint-instancelist-bfrlist x))
  :prepwork ((local (in-theory (enable constraint-instancelist-bfrlist))))
  :returns (ev constraint-instancelist-p)
  (if (atom x)
      nil
    (cons (constraint-instance-ev (car x) env)
          (constraint-instancelist-ev (cdr x) env)))
  ///
  (defthm constraint-instancelist-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (constraint-instancelist-bfrlist x) old))
             (equal (constraint-instancelist-ev x env new)
                    (constraint-instancelist-ev x env old))))

  (defcong logicman-equiv equal (constraint-instancelist-ev x env logicman) 3))

(define scratchobj-ev ((x scratchobj-p)
                              (env gl-env-p)
                              &optional (logicman 'logicman))
  :guard (lbfr-listp (scratchobj->bfrlist x))
  :returns (ev scratchobj-p)
  :guard-hints ((and stable-under-simplificationp
                     '(:expand ((scratchobj->bfrlist x)))))
  ;; :prepwork ((local (in-theory (enable scratchobj->bfrlist))))
  (scratchobj-case x
    :gl-obj (scratchobj-gl-obj (gl-object-ev x.val env))
    :gl-objlist (scratchobj-gl-objlist (gl-objectlist-ev x.val env))
    :bfr (scratchobj-bfr (gobj-bfr-eval x.val env))
    :bfrlist (scratchobj-bfrlist (gobj-bfr-list-eval x.val env))
    :cinst (scratchobj-cinst (constraint-instance-ev x.val env))
    :cinstlist (scratchobj-cinstlist (constraint-instancelist-ev x.val env)))
  ///
  (defthm scratchobj-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (scratchobj->bfrlist x) old))
             (equal (scratchobj-ev x env new)
                    (scratchobj-ev x env old)))
    :hints ((and stable-under-simplificationp
                     '(:expand ((scratchobj->bfrlist x))))))

  (defthm scratchobj-ev-of-scratchobj-gl-obj
    (equal (scratchobj-ev (Scratchobj-gl-obj val) env)
           (scratchobj-gl-obj (gl-object-ev val env))))

  (defthm scratchobj-ev-of-scratchobj-gl-objlist
    (equal (scratchobj-ev (Scratchobj-gl-objlist val) env)
           (scratchobj-gl-objlist (gl-objectlist-ev val env))))

  (defthm scratchobj-ev-of-scratchobj-bfr
    (equal (scratchobj-ev (Scratchobj-bfr val) env)
           (scratchobj-bfr (gobj-bfr-eval val env))))

  (defcong logicman-equiv equal (scratchobj-ev x env logicman) 3
    :hints(("Goal" :in-theory (disable scratchobj-ev-of-scratchobj-gl-obj
                                       scratchobj-ev-of-scratchobj-gl-objlist
                                       scratchobj-ev-of-scratchobj-bfr
                                       ;; fgl-object-ev-of-scratchobj-gl-obj->val
                                       ;; FGL-OBJECTLIST-EV-OF-SCRATCHOBJ-GL-OBJLIST->VAL
                                       ;; GOBJ-BFR-EVAL-OF-SCRATCHOBJ-BFR->VAL
                                       )))))

(define scratchlist-ev ((x scratchlist-p)
                        (env gl-env-p)
                        &optional (logicman 'logicman))
  :guard (lbfr-listp (scratchlist-bfrlist x))
  :returns (ev scratchlist-p)
  (if (atom x)
      nil
    (cons (scratchobj-ev (car x) env)
          (scratchlist-ev (cdr x) env)))
  ///
  (defthm scratchlist-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (scratchlist-bfrlist x) old))
             (equal (scratchlist-ev x env new)
                    (scratchlist-ev x env old))))

  (defcong logicman-equiv equal (scratchlist-ev x env logicman) 3))

(define minor-frame-ev ((x minor-frame-p)
                               (env gl-env-p)
                               &optional (logicman 'logicman))
  :guard (lbfr-listp (minor-frame-bfrlist x))
  :prepwork ((local (in-theory (enable minor-frame-bfrlist))))
  :returns (ev minor-frame-p)
  (b* (((minor-frame x)))
    (make-minor-frame
     :bindings (gl-object-alist-ev x.bindings env)
     :debug x.debug
     :scratch (scratchlist-ev x.scratch env)))
  ///
  (defthm minor-frame-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (minor-frame-bfrlist x) old))
             (equal (minor-frame-ev x env new)
                    (minor-frame-ev x env old))))

  (defcong logicman-equiv equal (minor-frame-ev x env logicman) 3))

(define minor-stack-ev ((x minor-stack-p)
                               (env gl-env-p)
                               &optional (logicman 'logicman))
  :guard (lbfr-listp (minor-stack-bfrlist x))
  :returns (ev minor-stack-p)
  :measure (len x)
  :ruler-extenders (cons)
  (cons (minor-frame-ev (car x) env)
        (and (consp (cdr x))
             (minor-stack-ev (cdr x) env)))
  ///
  (defthm minor-stack-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (minor-stack-bfrlist x) old))
             (equal (minor-stack-ev x env new)
                    (minor-stack-ev x env old))))

  (defcong logicman-equiv equal (minor-stack-ev x env logicman) 3))



(define major-frame-ev ((x major-frame-p)
                               (env gl-env-p)
                               &optional (logicman 'logicman))
  :guard (lbfr-listp (major-frame-bfrlist x))
  :prepwork ((local (in-theory (enable major-frame-bfrlist))))
  :returns (ev major-frame-p)
  (b* (((major-frame x)))
    (make-major-frame
     :bindings (gl-object-alist-ev x.bindings env)
     :debug x.debug
     :minor-stack (minor-stack-ev x.minor-stack env)))
  ///
  (defthm major-frame-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (major-frame-bfrlist x) old))
             (equal (major-frame-ev x env new)
                    (major-frame-ev x env old))))

  (defcong logicman-equiv equal (major-frame-ev x env logicman) 3))

(define major-stack-ev ((x major-stack-p)
                               (env gl-env-p)
                               &optional (logicman 'logicman))
  :guard (lbfr-listp (major-stack-bfrlist x))
  :returns (ev major-stack-p)
  :measure (len x)
  :ruler-extenders (cons)
  (cons (major-frame-ev (car x) env)
        (and (consp (cdr x))
             (major-stack-ev (cdr x) env)))
  ///
  (defthm major-stack-ev-of-logicman-extension
    (implies (and (bind-logicman-extension new old)
                  (lbfr-listp (major-stack-bfrlist x) old))
             (equal (major-stack-ev x env new)
                    (major-stack-ev x env old))))

  (defcong logicman-equiv equal (major-stack-ev x env logicman) 3))



(defsection stack-semantics-preserved-lemmas
  (local (in-theory (enable major-stack-ev
                            minor-stack-ev
                            major-frame-ev
                            minor-frame-ev)))

  (defthm scratchlist-ev-of-cdr
    (equal (scratchlist-ev (cdr x) env)
           (cdr (scratchlist-ev x env)))
    :hints(("Goal" :in-theory (enable scratchlist-ev))))

  (defthm scratchlist-ev-of-cons
    (equal (scratchlist-ev (cons x y) env)
           (cons (scratchobj-ev x env)
                 (scratchlist-ev y env)))
    :hints(("Goal" :in-theory (enable scratchlist-ev))))

  (defthm scratchlist-ev-of-nil
    (equal (scratchlist-ev nil env) nil)
    :hints(("Goal" :in-theory (enable scratchlist-ev))))

  (defthm gl-object-alist-ev-of-nil
    (equal (gl-object-alist-ev nil env) nil)
    :hints(("Goal" :in-theory (enable gl-object-alist-ev))))

  (defthm major-stack-ev-of-stack$a-pop-scratch
    (equal (major-stack-ev (stack$a-pop-scratch stack) env)
           (stack$a-pop-scratch (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-pop-scratch))))

  (defthm major-stack-ev-of-stack$a-push-scratch
    (equal (major-stack-ev (stack$a-push-scratch obj stack) env)
           (stack$a-push-scratch
            (scratchobj-ev obj env)
            (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-push-scratch))))

  (defthm major-stack-ev-of-stack$a-pop-frame
    (equal (major-stack-ev (stack$a-pop-frame stack) env)
           (stack$a-pop-frame (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-pop-frame default-car))))

  (defthm major-stack-ev-of-stack$a-set-bindings
    (equal (major-stack-ev (stack$a-set-bindings bindings stack) env)
           (stack$a-set-bindings (gl-object-alist-ev bindings env)
                                 (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-bindings))))

  (defthm major-stack-ev-of-stack$a-push-frame
    (equal (major-stack-ev (stack$a-push-frame stack) env)
           (stack$a-push-frame (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-push-frame))))

  (defthm major-stack-ev-of-stack$a-set-debug
    (equal (major-stack-ev (stack$a-set-debug obj stack) env)
           (stack$a-set-debug obj (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-debug))))

  (defthm gl-object-alist-ev-of-append
    (equal (gl-object-alist-ev (append a b) env)
           (append (gl-object-alist-ev a env)
                   (gl-object-alist-ev b env)))
    :hints(("Goal" :in-theory (enable gl-object-alist-ev))))

  (defthm major-stack-ev-of-stack$a-add-minor-bindings
    (equal (major-stack-ev (stack$a-add-minor-bindings bindings stack) env)
           (stack$a-add-minor-bindings
            (gl-object-alist-ev bindings env)
            (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-add-minor-bindings))))

  (defthm major-stack-ev-of-stack$a-pop-minor-frame
    (equal (major-stack-ev (stack$a-pop-minor-frame stack) env)
           (stack$a-pop-minor-frame (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-pop-minor-frame))))

  (defthm major-stack-ev-of-stack$a-set-minor-debug
    (equal (major-stack-ev (stack$a-set-minor-debug obj stack) env)
           (stack$a-set-minor-debug obj (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-minor-debug))))

  (defthm major-stack-ev-of-stack$a-set-minor-bindings
    (equal (major-stack-ev (stack$a-set-minor-bindings bindings stack) env)
           (stack$a-set-minor-bindings
            (gl-object-alist-ev bindings env)
            (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-set-minor-bindings))))

  (defthm major-stack-ev-of-stack$a-push-minor-frame
    (equal (major-stack-ev (stack$a-push-minor-frame stack) env)
           (stack$a-push-minor-frame (major-stack-ev stack env)))
    :hints(("Goal" :in-theory (enable stack$a-push-minor-frame)))))




(defsection ev-identities
  (defthm gl-object-ev-identity
    (equal (gl-object-ev (gl-object-ev x env) env2 logicman2)
           (gl-object-ev x env))
    :hints(("Goal" :in-theory (enable gl-object-ev))))

  (defthm gl-objectlist-ev-identity
    (equal (gl-objectlist-ev (gl-objectlist-ev x env) env2 logicman2)
           (gl-objectlist-ev x env))
    :hints(("Goal" :in-theory (enable gl-objectlist-ev))))

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

  (defthm gl-object-alist-ev-identity
    (equal (gl-object-alist-ev (gl-object-alist-ev x env) env2 logicman2)
           (gl-object-alist-ev x env))
    :hints(("Goal" :in-theory (enable gl-object-alist-ev))))

  (defthm constraint-instance-ev-identity
    (equal (constraint-instance-ev (constraint-instance-ev x env) env2 logicman2)
           (constraint-instance-ev x env))
    :hints(("Goal" :in-theory (enable constraint-instance-ev))))

  (defthm constraint-instancelist-ev-identity
    (equal (constraint-instancelist-ev (constraint-instancelist-ev x env) env2 logicman2)
           (constraint-instancelist-ev x env))
    :hints(("Goal" :in-theory (enable constraint-instancelist-ev))))

  (defthm scratchobj-ev-identity
    (equal (scratchobj-ev (scratchobj-ev x env) env2 logicman2)
           (scratchobj-ev x env))
    :hints(("Goal" :in-theory (e/d (scratchobj-ev)))))

  (defthm scratchlist-ev-identity
    (equal (scratchlist-ev (scratchlist-ev x env) env2 logicman2)
           (scratchlist-ev x env))
    :hints(("Goal" :in-theory (enable scratchlist-ev))))

  (defthm minor-frame-ev-identity
    (equal (minor-frame-ev (minor-frame-ev x env) env2 logicman2)
           (minor-frame-ev x env))
    :hints(("Goal" :in-theory (enable minor-frame-ev))))

  (defthm minor-stack-ev-identity
    (equal (minor-stack-ev (minor-stack-ev x env) env2 logicman2)
           (minor-stack-ev x env))
    :hints(("Goal" :in-theory (enable minor-stack-ev))))

  (defthm major-frame-ev-identity
    (equal (major-frame-ev (major-frame-ev x env) env2 logicman2)
           (major-frame-ev x env))
    :hints(("Goal" :in-theory (enable major-frame-ev))))

  (defthm major-stack-ev-identity
    (equal (major-stack-ev (major-stack-ev x env) env2 logicman2)
           (major-stack-ev x env))
    :hints(("Goal" :in-theory (enable major-stack-ev)))))




