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
(include-book "bfr-arithmetic")
(include-book "stack-ev")
(include-book "scratch-isomorphic")
(include-book "interp-st-bfrs-ok")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))


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



  (def-updater-independence-thm gl-object-alist-ev-of-interp-st-logicman-extension
    (implies (and (logicman-extension-p (interp-st->logicman new) (interp-st->logicman old))
                  (lbfr-listp (gl-object-alist-bfrlist x) (interp-st->logicman old)))
             (equal (gl-object-alist-ev x env (interp-st->logicman new))
                    (gl-object-alist-ev x env (interp-st->logicman old)))))



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
      (equal (major-stack-ev (interp-st->stack new-interp-st) env (interp-st->logicman new-interp-st))
             (major-stack-ev (interp-st->stack interp-st) env (interp-st->logicman interp-st))))

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
      (equal (logicman-pathcond-eval-checkpoints!
              env
              (interp-st->pathcond new-interp-st)
              (interp-st->logicman new-interp-st))
             (logicman-pathcond-eval-checkpoints!
              env
              (interp-st->pathcond interp-st)
              (interp-st->logicman interp-st))))

    (defret constraint-eval-of-<fn>
      (equal (logicman-pathcond-eval
              env
              (interp-st->constraint new-interp-st)
              (interp-st->logicman new-interp-st))
             (logicman-pathcond-eval
              env
              (interp-st->constraint interp-st)
              (interp-st->logicman interp-st))))
    
    (defret get-bvar->term-eval-of-<fn>
      (iff (fgl-object-eval (get-bvar->term$a n (interp-st->bvar-db new-interp-st))
                            env
                            (interp-st->logicman new-interp-st))
           (fgl-object-eval (get-bvar->term$a n (interp-st->bvar-db interp-st))
                            env
                            (interp-st->logicman interp-st))))))

(defun def-gl-primitive-fn (fn formals body)
  (declare (Xargs :mode :program))
  (b* ((primfn (intern-in-package-of-symbol
                (concatenate 'string "GL-" (symbol-name fn) "-PRIMITIVE")
                'gl-package)))
    `(define ,primfn ((args gl-objectlist-p)
                      interp-st
                      state)
       :returns (mv successp
                    (ans gl-object-p)
                    new-interp-st)
       (if (eql (len args) ,(len formals))
           (b* (((list . ,formals) (gl-objectlist-fix args)))
             ,body)
         (mv nil nil interp-st))
       ///
       ,@*gl-primitive-thms*

       (defret eval-of-<fn>
         (implies successp
                  (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                         (fgl-ev (cons ',fn
                                       (kwote-lst (fgl-objectlist-eval args env (interp-st->logicman interp-st))))
                                 nil))))
       (table gl-primitives ',fn ',primfn))))


(defmacro def-gl-primitive (fn formals body)
  (def-gl-primitive-fn fn formals body))


(set-ignore-ok t)

(local (defthm fgl-objectlist-eval-when-consp
         (implies (consp x)
                  (equal (fgl-objectlist-eval x env)
                         (cons (fgl-object-eval (car x) env)
                               (fgl-objectlist-eval (cdr x) env))))
         :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))))

(local (in-theory (enable gl-objectlist-bfrlist-when-consp)))

(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (not (consp x)))))

(local (defthm len-of-cons
         (equal (len (cons a b))
                (+ 1 (len b)))))

(local (defun len-is (x n)
         (if (zp n)
             (and (eql n 0) (atom x))
           (and (consp x)
                (len-is (cdr x) (1- n))))))

(local (defthm open-len-is
         (implies (syntaxp (quotep n))
                  (equal (len-is x n)
                         (if (zp n)
                             (and (eql n 0) (atom x))
                           (and (consp x)
                                (len-is (cdr x) (1- n))))))))
                         

(local (defthm equal-len-hyp
         (implies (syntaxp (and (or (acl2::rewriting-negative-literal-fn `(equal (len ,x) ,n) mfc state)
                                    (acl2::rewriting-negative-literal-fn `(equal ,n (len ,x)) mfc state))
                                (quotep n)))
                  (equal (equal (len x) n)
                         (len-is x n)))))

(local (in-theory (enable* gl-object-bfrlist-when-thms)))

(local (defthm gobj-bfr-list-eval-of-nil
         (equal (gobj-bfr-list-eval nil x) nil)
         :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))

(local (defthm bools->int-of-single
         (equal (bools->int (list x))
                (- (bool->bit x)))
         :hints(("Goal" :in-theory (enable bools->int)))))

(local (in-theory (disable len)))

(local (defthm bools->int-of-cons
         (equal (bools->int (cons x y))
                (if (consp y)
                    (logcons (bool->bit x) (bools->int y))
                  (- (bool->bit x))))
         :hints(("Goal" :in-theory (enable bools->int)))))

(local (defthm logcar-of-bools->int
         (equal (logcar (bools->int x))
                (bool->bit (car x)))))

(local (defthm car-of-gobj-bfr-list-eval
         (equal (car (gobj-bfr-list-eval x env))
                (gobj-bfr-eval (car x) env))))

(local (defthm scdr-of-gobj-bfr-list-eval
         (equal (scdr (gobj-bfr-list-eval x env))
                (gobj-bfr-list-eval (scdr x) env))
         :hints(("Goal" :in-theory (enable scdr gobj-bfr-list-eval)))))

(def-gl-primitive int (x)
  (gl-object-case x
    :g-integer (mv t (gl-object-fix x) interp-st)
    :otherwise (mv nil nil interp-st)))


(def-gl-primitive endint (x)
  (gl-object-case x
    :g-boolean (mv t (g-integer (list x.bool)) interp-st)
    :otherwise (mv nil nil interp-st)))

(def-gl-primitive intcons (car cdr)
  (gl-object-case car
    :g-boolean (gl-object-case cdr
                 :g-integer (mv t (g-integer (cons car.bool
                                                   (if (atom cdr.bits)
                                                       '(nil)
                                                     cdr.bits)))
                                interp-st)
                 :otherwise (mv nil nil interp-st))
    :otherwise (mv nil nil interp-st)))

(table gl-primitives 'intcons* 'gl-intcons-primitive)

(def-gl-primitive intcar (x)
  (gl-object-case x
    :g-integer (mv t (g-boolean (car x.bits)) interp-st)
    :otherwise (mv nil nil interp-st)))

(def-gl-primitive intcdr (x)
  (gl-object-case x
    :g-integer (mv t (g-integer (scdr x.bits)) interp-st)
    :otherwise (mv nil nil interp-st)))

(def-gl-primitive bool (x)
  (gl-object-case x
    :g-boolean (mv t (gl-object-fix x) interp-st)
    :otherwise (mv nil nil interp-st)))

(def-gl-primitive cons (car cdr)
  (mv t
      (if (and (gl-object-case car :g-concrete)
               (gl-object-case cdr :g-concrete))
          (g-concrete (cons (g-concrete->val car)
                            (g-concrete->val cdr)))
        (g-cons car cdr))
      interp-st))

(def-gl-primitive car (x)
  (gl-object-case x
    :g-concrete (mv t (g-concrete (mbe :logic (car x.val)
                                       :exec (and (consp x.val) (car x.val))))
                    interp-st)
    :g-boolean (mv t nil interp-st)
    :g-integer (mv t nil interp-st)
    :g-cons (mv t x.car interp-st)
    :otherwise (mv nil nil interp-st)))

(def-gl-primitive cdr (x)
  (gl-object-case x
    :g-concrete (mv t (g-concrete (mbe :logic (cdr x.val)
                                       :exec (and (consp x.val) (cdr x.val))))
                    interp-st)
    :g-boolean (mv t nil interp-st)
    :g-integer (mv t nil interp-st)
    :g-cons (mv t x.cdr interp-st)
    :otherwise (mv nil nil interp-st)))
    
    


(local
 (defun gl-primitive-fncall-entries (table)
   (if (atom table)
       `((otherwise (mv nil nil interp-st)))
     (b* (((cons fn prim) (car table)))
       (cons `(,fn (,prim args interp-st state))
             (gl-primitive-fncall-entries (cdr table)))))))

(make-event
 `(define gl-primitive-fncall ((fn pseudo-fnsym-p)
                               (args gl-objectlist-p)
                               (dont)
                               interp-st
                               state)
    :returns (mv successp
                 (ans gl-object-p)
                 new-interp-st)
    (if dont
        (mv nil nil interp-st)
      (case (pseudo-fnsym-fix fn)
        . ,(gl-primitive-fncall-entries (table-alist 'gl-primitives (w state)))))
    ///
    ,@*gl-primitive-thms*
    (defret eval-of-<fn>
      (implies successp
               (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                      (fgl-ev (cons (pseudo-fnsym-fix fn)
                                    (kwote-lst (fgl-objectlist-eval args env (interp-st->logicman interp-st))))
                              nil))))))
