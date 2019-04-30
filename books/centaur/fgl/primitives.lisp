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

(include-book "primitives-stub")
(include-book "bfr-arithmetic")
(include-book "centaur/misc/hons-remove-dups" :dir :system)
(local (include-book "primitive-lemmas"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))



     
(defun gl-primitive-formula-checks (formulas state)
  (declare (xargs :stobjs state :mode :program))
  (if (atom formulas)
      nil
    (cons `(equal (meta-extract-formula ',(car formulas) state)
                  ',(meta-extract-formula (car formulas) state))
          (gl-primitive-formula-checks (cdr formulas) state))))

(defun def-gl-formula-checks-fn (name formulas state)
  (declare (xargs :stobjs state :mode :program))
  `(define ,name (state)
     :returns (ok)
     (and . ,(gl-primitive-formula-checks formulas state))
     ///
     (table gl-formula-checks ',name ',formulas)))

(defmacro def-gl-formula-checks (name formulas)
  `(make-event
    (def-gl-formula-checks-fn ',name ',formulas state)))


(defun def-gl-primitive-fn (fn formals body name-override formula-check-fn prepwork)
  (declare (Xargs :mode :program))
  (b* ((primfn (or name-override
                   (intern-in-package-of-symbol
                    (concatenate 'string "GL-" (symbol-name fn) "-PRIMITIVE")
                    'gl-package))))
    `(define ,primfn ((args gl-objectlist-p)
                      (interp-st interp-st-bfrs-ok)
                      state)
       :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
       :returns (mv successp
                    ans
                    new-interp-st)
       :prepwork ,prepwork
       (if (eql (len args) ,(len formals))
           (b* (((list . ,formals) (gl-objectlist-fix args)))
             ,body)
         (mv nil nil interp-st))
       ///
       ,@*gl-primitive-thms*

       (defret eval-of-<fn>
         (implies (and successp
                       (fgl-ev-meta-extract-global-facts :state st)
                       ,@(and formula-check-fn
                              `((,formula-check-fn st)))
                       (equal (w st) (w state))
                       (interp-st-bfrs-ok interp-st)
                       (interp-st-bfr-listp (gl-objectlist-bfrlist args)))
                  (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                         (fgl-ev (cons ',fn
                                       (kwote-lst (fgl-objectlist-eval args env (interp-st->logicman interp-st))))
                                 nil))))
       (table gl-primitives ',fn ',primfn))))


(defmacro def-gl-primitive (fn formals body &key (fnname) (formula-check) (prepwork))
  (def-gl-primitive-fn fn formals body fnname formula-check prepwork))


(defun gl-primitive-fncall-entries (table)
  (if (atom table)
      `((otherwise (mv nil nil interp-st)))
    (b* (((cons fn prim) (car table)))
      (cons `(,fn (,prim args interp-st state))
            (gl-primitive-fncall-entries (cdr table))))))

(defun append-alist-vals (x)
  (if (atom x)
      nil
    (append (cdar x)
            (append-alist-vals (cdr x)))))

(defun formula-check-thms (name table)
  (if (atom table)
      nil
    (b* ((check-name (caar table))
         (thmname (intern-in-package-of-symbol
                   (concatenate 'string (symbol-name check-name) "-WHEN-" (symbol-name name))
                   name)))
      (cons `(defthm ,thmname
               (implies (,name st)
                        (,check-name st))
               :hints (("Goal" :in-theory '(,name ,check-name))))
            (formula-check-thms name (cdr table))))))

(set-state-ok t)

(defun install-gl-primitives-fn (name state)
  (declare (xargs :mode :program))
  (b* ((wrld (w state))
       (name-formula-checks (intern-in-package-of-symbol
                             (concatenate 'string (symbol-name name) "-FORMULA-CHECKS")
                             name))
       (formula-checks-table (table-alist 'gl-formula-checks wrld))
       (all-formulas (gl-primitive-formula-checks
                      (acl2::hons-remove-dups (append-alist-vals formula-checks-table))
                      state))
       (formula-check-thms (formula-check-thms name-formula-checks formula-checks-table)))
    
    `(progn
       (define ,name-formula-checks (state)
         :ignore-ok t
         :irrelevant-formals-ok t
         (and . ,all-formulas)
         ///
         . ,formula-check-thms)
       (define ,name ((fn pseudo-fnsym-p)
                      (args gl-objectlist-p)
                      (interp-st interp-st-bfrs-ok)
                      state)
         :guard (interp-st-bfr-listp (gl-objectlist-bfrlist args))
         :returns (mv successp ans new-interp-st)
         (case (pseudo-fnsym-fix fn)
           . ,(gl-primitive-fncall-entries (table-alist 'gl-primitives wrld)))
         ///
         ,@*gl-primitive-thms*
         (defret eval-of-<fn>
           (implies (and successp
                         (fgl-ev-meta-extract-global-facts :state st)
                         ;; (,name-formula-checks st)
                         (equal (w st) (w state))
                         (interp-st-bfrs-ok interp-st)
                         (interp-st-bfr-listp (gl-objectlist-bfrlist args)))
                    (equal (fgl-object-eval ans env (interp-st->logicman new-interp-st))
                           (fgl-ev (cons (pseudo-fnsym-fix fn)
                                         (kwote-lst (fgl-objectlist-eval args env (interp-st->logicman interp-st))))
                                   nil)))))

       ;; bozo, dumb theorem needed to prove fixequiv hook
       (local (defthm pseudo-fnsym-fix-equal-forward
                (implies (equal (pseudo-fnsym-fix x) (pseudo-fnsym-fix y))
                         (pseudo-fnsym-equiv x y))
                :rule-classes :forward-chaining))

       (defattach
         (gl-primitive-fncall-stub ,name)
         ;; (gl-primitive-formula-checks-stub ,name-formula-checks)
         ))))

(defmacro install-gl-primitives (name)
  `(make-event
    (install-gl-primitives-fn ',name state)))


(set-ignore-ok t)

(def-gl-primitive int (x)
  (b* (((mv ok fix) (gobj-syntactic-integer-fix x))
       ((unless ok) (mv nil nil interp-st)))
    (mv t fix interp-st)))


(def-gl-primitive endint (x)
  (gl-object-case x
    :g-concrete (mv t (if x.val -1 0) interp-st)
    :g-boolean (mv t (mk-g-integer (list x.bool)) interp-st)
    :g-cons (mv t -1 interp-st)
    :g-integer (mv t -1 interp-st)
    :otherwise (mv nil nil interp-st)))




(def-gl-primitive intcons (car cdr)
  (b* (((mv ok car-fix) (gobj-syntactic-boolean-fix car))
       ((unless ok) (mv nil nil interp-st))
       ((mv ok cdr-fix) (gobj-syntactic-integer-fix cdr))
       ((unless ok) (mv nil nil interp-st)))
    (mv t (mk-g-integer (scons (gobj-syntactic-boolean->bool car-fix)
                               (gobj-syntactic-integer->bits cdr-fix)))
        interp-st)))

(table gl-primitives 'intcons* 'gl-intcons-primitive)

(local (defthm logcar-when-not-integerp
         (implies (not (integerp x))
                  (equal (logcar x) 0))
         :hints(("Goal" :in-theory (enable logcar)))))

(def-gl-primitive intcar (x)
  (gl-object-case x
    :g-concrete (mv t (and (integerp x.val)
                           (intcar x.val))
                    interp-st)
    :g-integer (mv t (mk-g-boolean (car x.bits)) interp-st)
    :g-boolean (mv t nil interp-st)
    :g-cons (mv t nil interp-st)
    :otherwise (mv nil nil interp-st)))

(local (defthm logcdr-when-not-integerp
         (implies (not (integerp x))
                  (equal (logcdr x) 0))
         :hints(("Goal" :in-theory (enable logcdr)))))

(local (in-theory (enable gl-object-kind-when-integerp
                          g-concrete->val-when-integerp)))

(local (in-theory (disable logcdr-of-bools->int)))

(def-gl-primitive intcdr (x)
  (gl-object-case x
    :g-concrete (mv t (if (integerp x.val)
                          (intcdr x.val)
                        0)
                    interp-st)
    :g-integer (mv t (g-integer (scdr x.bits)) interp-st)
    :g-boolean (mv t 0 interp-st)
    :g-cons (mv t 0 interp-st)
    :otherwise (mv nil nil interp-st)))

(local (in-theory (enable bool-fix)))

(def-gl-primitive bool (x)
  (gl-object-case x
    :g-concrete (mv t (bool-fix x.val) interp-st)
    :g-boolean (mv t (gl-object-fix x) interp-st)
    :g-integer (mv t t interp-st)
    :g-cons (mv t t interp-st)
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
    

(defthm integerp-in-terms-of-int
  (equal (integerp x)
         (equal (int x) x))
  :rule-classes nil)





  (local (defthmd gl-object-bfrlist-of-get-bvar->term$a-aux
           (implies (and (not (member v (bvar-db-bfrlist-aux m bvar-db)))
                         (< (nfix n) (nfix m))
                         (<= (base-bvar$a bvar-db) (nfix n)))
                    (not (member v (gl-object-bfrlist (get-bvar->term$a n bvar-db)))))
           :hints(("Goal" :in-theory (enable bvar-db-bfrlist-aux)))))

  (local (defthm gl-object-bfrlist-of-get-bvar->term$a
           (implies (and (not (member v (bvar-db-bfrlist bvar-db)))
                         (<= (base-bvar$a bvar-db) (nfix n))
                         (< (nfix n) (next-bvar$a bvar-db)))
                    (not (member v (gl-object-bfrlist (get-bvar->term$a n bvar-db)))))
           :hints (("goal" :in-theory (enable bvar-db-bfrlist)
                    :use ((:instance gl-object-bfrlist-of-get-bvar->term$a-aux
                           (m (next-bvar$a bvar-db))))))))

;;(local (in-theory (enable gobj-bfr-list-eval-is-bfr-list-eval)))

(define int+ (x y)
  (+ (ifix x) (ifix y)))



(def-gl-formula-checks int+-formula-checks (int+ ifix))

(define w-equiv (x y)
  :non-executable t
  :no-function t
  :verify-guards nil
  (equal (w x) (w y))
  ///
  (defequiv w-equiv)
  (defcong w-equiv equal (w x) 1)
  (defcong w-equiv equal (meta-extract-formula name state) 2
    :hints(("Goal" :in-theory (enable meta-extract-formula))))

  (defthm ws-equal-forward
    (implies (equal (w st) (w state))
             (w-equiv st state))
    :rule-classes :forward-chaining))

(local (in-theory (disable w)))

(defthm fgl-ev-of-ifix-call
  (implies (and (fgl-ev-meta-extract-global-facts :state st)
                (int+-formula-checks st)
                (equal (w st) (w state)))
           (equal (fgl-ev (list 'ifix x) a)
                  (ifix (fgl-ev x a))))
  :hints(("Goal" :in-theory (e/d (int+
                                  int+-formula-checks
                                  fgl-ev-of-fncall-args)
                                 (fgl-ev-meta-extract-formula))
          :use ((:instance fgl-ev-meta-extract-formula
                 (st state) (state st)
                 (name 'ifix)
                 (a (list (cons 'x (fgl-ev x a)))))))))

(defthm fgl-ev-of-int+-call
  (implies (and (fgl-ev-meta-extract-global-facts :state st)
                (int+-formula-checks st)
                (equal (w st) (w state)))
           (equal (fgl-ev (list 'int+ x y) a)
                  (int+ (fgl-ev x a)
                        (fgl-ev y a))))
  :hints(("Goal" :in-theory (e/d (int+
                                  int+-formula-checks
                                  fgl-ev-of-fncall-args)
                                 (fgl-ev-meta-extract-formula))
          :use ((:instance fgl-ev-meta-extract-formula
                 (st state) (state st)
                 (name 'int+)
                 (a (list (cons 'x (fgl-ev x a))
                          (cons 'y (fgl-ev y a)))))))))

(local (defthm fgl-objectlist-eval-of-atom
         (implies (not (consp x))
                  (equal (fgl-objectlist-eval x env) nil))
         :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))
         :rule-classes ((:rewrite :backchain-limit-lst 0))))

(local (defthm bools->int-of-eval-syntactic-integer-bits
         (b* (((mv ok xfix) (gobj-syntactic-integer-fix x)))
           (implies ok
                    (equal (bools->int (gobj-bfr-list-eval (gobj-syntactic-integer->bits xfix)
                                                           env))
                           (ifix (fgl-object-eval x env)))))
         :hints(("Goal" :in-theory (enable gobj-syntactic-integer->bits
                                           gobj-syntactic-integer-fix)))))


;; (def-gl-primitive int+ (x y)
;;   (b* (((mv ok xfix) (gobj-syntactic-integer-fix x))
;;        ((unless ok) (mv nil nil interp-st))
;;        ((mv ok yfix) (gobj-syntactic-integer-fix y))
;;        ((unless ok) (mv nil nil interp-st))
;;        (xbits (gobj-syntactic-integer->bits xfix))
;;        (ybits (gobj-syntactic-integer->bits yfix)))
;;     (stobj-let ((logicman (interp-st->logicman interp-st)))
;;                (bits logicman)
;;                (bfr-+-ss nil xbits ybits logicman)
;;                (mv t (mk-g-integer bits) interp-st)))
;;   :formula-check int+-formula-checks
;;   :prepwork ((local (in-theory (enable int+)))))



(install-gl-primitives gl-primitive-fncall-base)

