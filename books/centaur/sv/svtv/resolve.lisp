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

(include-book "../mods/lhs")


(local (std::add-default-post-define-hook :fix))



;; -- Define a set of input and output names as an lhsmap. (Separate namespaces or no?)
;; -- Provide phase/cycle inputs and extract outputs in terms of these names.
;; -- Check that input assignments do not overlap.

;; -- Overrides:
;;    Most common desirable behavior: if signal is assigned, then override it,
;;    otherwise don't.  But user can specify value of override mask if desired.
;;    Default: mask is -1 if a value is provided, X (same effect as 0) if not.




;; Implementation: 
;; For each assigned value, get the associated LHS giving the canonical signal
;; names of its segments.  Get the associated mask from the override-masks, or
;; -1 if not bound.

;; For each segment in the masks, skip over if Z, otherwise check whether the
;; variable has an update function.  If so, set the mask/val, otherwise just
;; set the segment of the variable.

;; There could be more than one assignment to the same variable.  We probably
;; don't want to allow real overlaps, but we should resolve together
;; assignments to disjoint pieces.  We do this for symbolic values with
;; assigns->netassigns->resolves, so we need a version for concrete values as well.



(defprod 4vec-driver
  ;; Similar to driver, but with a 4vec payload rather than an svex
  ((value 4vec)
   (strength natp :default 6))
  :layout :tree)

(define driver-eval ((x driver-p) (env svex-env-p))
  :returns (val 4vec-driver-p)
  (b* (((driver x)))
    (make-4vec-driver :value (svex-eval x.value env)
                      :strength x.strength))
  ///
  (defret value-of-<fn>
    (equal (4vec-driver->value val)
           (svex-eval (driver->value x) env)))

  (defret strength-of-<fn>
    (equal (4vec-driver->strength val)
           (driver->strength x))))

(defalist 4vec-assigns :key-type lhs :val-type 4vec-driver)

(define assigns-eval ((x assigns-p) (env svex-env-p))
  :returns (val 4vec-assigns-p)
  (b* (((when (atom x)) x)
       ((unless (mbt (consp (car x))))
        (assigns-eval (cdr x) env))
       ((cons lhs driver) (car x)))
    (cons (cons (lhs-fix lhs)
                (driver-eval driver env))
          (assigns-eval (cdr x) env)))
  ///
  (local (in-theory (enable assigns-fix))))

(deflist 4vec-driverlist :elt-type 4vec-driver)

(defprojection driverlist-eval ((x driverlist-p) (env svex-env-p))
  :returns (val 4vec-driverlist-p)
  (driver-eval x env))

(defalist 4vec-netassigns :key-type svar :val-type 4vec-driverlist)



(define netassigns-eval ((x netassigns-p) (env svex-env-p))
  :returns (val 4vec-netassigns-p)
  (b* (((when (atom x)) x)
       ((unless (mbt (consp (car x))))
        (netassigns-eval (cdr x) env))
       ((cons svar drivers) (car x)))
    (cons (cons (svar-fix svar)
                (driverlist-eval drivers env))
          (netassigns-eval (cdr x) env)))
  ///
  (local (in-theory (enable netassigns-fix)))

  (defthm hons-assoc-equal-of-netassigns-eval
    (equal (hons-assoc-equal var (netassigns-eval x env))
           (and (hons-assoc-equal var (netassigns-fix x))
                (cons var (driverlist-eval (cdr (hons-assoc-equal var (netassigns-fix x))) env))))))


(define 4vec-assign->netassigns ((lhs lhs-p) (offset natp) (dr 4vec-driver-p)
                                 (acc 4vec-netassigns-p "accumulator"))
  :returns (assigns 4vec-netassigns-p)
  :measure (len lhs)
  (b* (((mv first rest) (lhs-decomp lhs))
       (acc (4vec-netassigns-fix acc))
       ((unless first) acc)
       ((lhrange first) first)
       (offset (lnfix offset))
       ((4vec-driver dr))
       ((when (eq (lhatom-kind first.atom) :z))
        (4vec-assign->netassigns rest (+ offset first.w) dr acc))
       ((lhatom-var first.atom))
       (new-driver (change-4vec-driver
                    dr :value (4vec-concat (2vec first.atom.rsh)
                                           (4vec-z)
                                           (4vec-concat (2vec first.w)
                                                        (4vec-rsh (2vec offset) dr.value)
                                                        (4vec-z)))))
       (rest-drivers (cdr (hons-get first.atom.name acc)))
       (acc (hons-acons first.atom.name (cons new-driver rest-drivers) acc)))
    (4vec-assign->netassigns rest (+ offset first.w) dr acc))
  ///
  (deffixequiv 4vec-assign->netassigns)

  (defthm 4vec-assign->netassigns-correct
    (equal (netassigns-eval (assign->netassigns lhs offset dr acc) env)
           (4vec-assign->netassigns
            lhs offset
            (driver-eval dr env)
            (netassigns-eval acc env)))
    :hints(("Goal" :in-theory (enable assign->netassigns
                                      netassigns-eval
                                      driver-eval
                                      svex-apply))))

  (defret vars-of-<fn>
    (implies (and (not (member v (lhs-vars lhs)))
                  (not (hons-assoc-equal v (4vec-netassigns-fix acc))))
             (not (hons-assoc-equal v assigns)))
    :hints(("Goal" :in-theory (enable lhs-vars lhatom-vars)))))

(define 4vec-assigns->netassigns-aux ((x 4vec-assigns-p) (acc 4vec-netassigns-p))
  :measure (len (4vec-assigns-fix x))
  :returns (netassigns 4vec-netassigns-p)
  (b* ((x (4vec-assigns-fix x))
       (acc (4vec-netassigns-fix acc))
       ((when (atom x)) acc))
    (4vec-assigns->netassigns-aux (cdr x)
                                  (4vec-assign->netassigns (caar x) 0 (cdar x) acc)))
  ///
  (local (defthm assigns-eval-in-terms-of-assigns-fix
           (equal (assigns-eval x env)
                  (let ((x (assigns-fix x)))
                    (if (atom x)
                        x
                      (cons (cons (caar x)
                                  (driver-eval (cdar x) env))
                            (assigns-eval (cdr x) env)))))
           :hints(("Goal" :in-theory (enable assigns-eval assigns-fix)))
           :rule-classes ((:definition :controller-alist ((assigns-eval t nil))))))

  (defthm 4vec-assigns->netassigns-aux-correct
    (equal (netassigns-eval (assigns->netassigns-aux x acc) env)
           (4vec-assigns->netassigns-aux (assigns-eval x env)
                                         (netassigns-eval acc env)))
    :hints(("Goal" :in-theory (enable netassigns-eval assigns-eval
                                      assigns->netassigns-aux)
            :induct t)))

  ;; (local (defthm caar-of-4vec-assigns-fix
  ;;          (equal (caar (4vec-assigns-fix 

  (local (defthm consp-of-4vec-assigns-fix
           (equal (consp (4vec-assigns-fix x))
                  (consp (alist-keys x)))
           :hints(("Goal" :in-theory (enable 4vec-assigns-fix alist-keys)))))

  (local (defthm caar-of-4vec-assigns-fix
           (equal (caar (4vec-assigns-fix x))
                  (lhs-fix (car (alist-keys x))))
           :hints(("Goal" :in-theory (enable 4vec-assigns-fix alist-keys)))))

  (local (defthm alist-keys-cdr-4vec-assigns-fix
           (equal (alist-keys (cdr (4vec-assigns-fix x)))
                  (lhslist-fix (cdr (alist-keys x))))
           :hints(("Goal" :in-theory (enable 4vec-assigns-fix lhslist-fix alist-keys)))))

  (defret vars-of-<fn>
    (implies (and (not (member v (lhslist-vars (alist-keys x))))
                  (not (hons-assoc-equal v (4vec-netassigns-fix acc))))
             (not (hons-assoc-equal v netassigns)))
    :hints(("Goal" :in-theory (enable lhslist-vars alist-keys 4vec-assigns-fix)
            :induct <call>
            :expand (<call>
                     (lhslist-vars (alist-keys x)))))))

(define 4vec-assigns->netassigns ((x 4vec-assigns-p))
  :returns (netassigns 4vec-netassigns-p)
  :prepwork ((local (include-book "std/lists/final-cdr" :dir :system))

             (local (defthm cdr-last-is-final-cdr
                      (implies (consp x)
                               (equal (cdr (last x))
                                      (acl2::final-cdr x))))))

  (fast-alist-free (fast-alist-clean (4vec-assigns->netassigns-aux x nil)))
  ///

  (local (defthm fast-alist-clean-redef
           (equal (fast-alist-clean x)
                  (fast-alist-fork x (acl2::final-cdr x)))))
  (local (in-theory (disable fast-alist-clean)))

  (local (defthm netassigns-eval-of-fast-alist-fork
           (implies (and (netassigns-p x)
                         (netassigns-p y))
                    (equal (netassigns-eval (fast-alist-fork x y) env)
                           (fast-alist-fork (netassigns-eval x env)
                                            (netassigns-eval y env))))
           :hints(("Goal" :in-theory (enable netassigns-eval)))))

  (local (defthm final-cdr-of-netassigns-eval
           (equal (acl2::final-cdr (netassigns-eval x env))
                  (acl2::final-cdr x))
           :hints(("Goal" :in-theory (enable netassigns-eval)))))

  (local (defthm netassigns-eval-of-fast-alist-clean
           (implies (netassigns-p x)
                    (equal (netassigns-eval (fast-alist-clean x) env)
                           (fast-alist-clean (netassigns-eval x env))))
           :hints(("Goal" :in-theory (enable netassigns-eval)))))

  (local (defthm hons-assoc-equal-of-fast-alist-fork
           (equal (hons-assoc-equal k (fast-alist-fork x y))
                  (or (hons-assoc-equal k y)
                      (hons-assoc-equal k x)))))


  (local (defthm hons-assoc-equal-of-fast-alist-clean
           (equal (hons-assoc-equal k (fast-alist-clean x))
                  (hons-assoc-equal k x))))

  (local (in-theory (disable fast-alist-fork fast-alist-clean-redef)))

  (defthm 4vec-assigns->netassigns-correct
    (equal (netassigns-eval (assigns->netassigns x) env)
           (4vec-assigns->netassigns (assigns-eval x env)))
    :hints(("Goal" :in-theory (enable assigns->netassigns
                                      netassigns-eval))))


  (defret vars-of-<fn>
    (implies (and (not (member v (lhslist-vars (alist-keys x)))))
             (not (hons-assoc-equal v netassigns)))))




(acl2::defsort 4vec-drivestrength-sort
  :prefix 4vec-drivestrength
  :comparablep 4vec-driver-p
  :comparable-listp 4vec-driverlist-p
  :compare< (lambda (x y) (< (4vec-driver->strength y) (4vec-driver->strength x))))

(deffixequiv 4vec-drivestrength-ordered-p
  :hints(("Goal" :in-theory (enable 4vec-drivestrength-ordered-p)))
  :args ((x 4vec-driverlist)))

(define 4veclist-resolve ((x 4veclist-p))
  :returns (res 4vec-p)
  :prepwork ((local (defthm 4vec-res-of-z
                      (equal (4vec-res x (4vec-z))
                             (4vec-fix x))
                      :hints(("Goal" :in-theory (enable 4vec-res))))))
  (if (atom x)
      (4vec-z)
    (mbe :logic (4vec-res (car x) (4veclist-resolve (cdr x)))
         :exec
         (if (atom (cdr x))
             (4vec-fix (car x))
           (4vec-res (car x) (4veclist-resolve (cdr x))))))
  ///

  (defthm svexlist-resolve-correct
    (equal (svex-eval (svexlist-resolve x) env)
           (4veclist-resolve (svexlist-eval x env)))
    :hints(("Goal" :in-theory (enable svexlist-resolve svexlist-eval
                                      svex-apply)))))


(define 4vec-driverlist-values-of-strength ((x 4vec-driverlist-p) (strength natp))
  ;; Works only when sorted!
  :guard (4vec-drivestrength-ordered-p x)
  :guard-hints (("goal" :in-theory (enable 4vec-drivestrength-ordered-p)))
  :returns (values 4veclist-p)
  (b* (((when (atom x)) nil)
       ((4vec-driver x1) (car x))
       (strength (lnfix strength))
       ((when (eql strength x1.strength))
        (cons x1.value (4vec-driverlist-values-of-strength (cdr x) strength))))
    nil)
  ///
  (defthm driverlist-values-of-strength-correct
    (equal (svexlist-eval (driverlist-values-of-strength x strength) env)
           (4vec-driverlist-values-of-strength (driverlist-eval x env) strength))
    :hints(("Goal" :in-theory (enable driverlist-values-of-strength
                                      driverlist-eval
                                      svexlist-eval)))))


(define 4vec-driverlist-rest-after-strength ((x 4vec-driverlist-p) (strength natp))
  :guard (4vec-drivestrength-ordered-p x)
  :guard-hints (("goal" :in-theory (enable 4vec-drivestrength-ordered-p)))
  :returns (rest 4vec-driverlist-p)
  (b* (((when (atom x)) nil)
       ((4vec-driver x1) (car x))
       (strength (lnfix strength))
       ((when (< x1.strength strength))
        (4vec-driverlist-fix x)))
    (4vec-driverlist-rest-after-strength (cdr x) strength))
  ///

  (defthm len-of-4vec-driverlist-rest-after-strength
    (implies (consp x)
             (< (len (4vec-driverlist-rest-after-strength x (4vec-driver->strength (car x))))
                (len x)))
    :rule-classes :linear)

  (defthm 4vec-drivestrength-ordered-p-of-driverlist-rest-after-strength
    (implies (4vec-drivestrength-ordered-p x)
             (4vec-drivestrength-ordered-p
              (4vec-driverlist-rest-after-strength x strength)))
    :hints(("Goal" :in-theory (enable 4vec-drivestrength-ordered-p))))

  (defthm driverlist-rest-after-strength-correct
    (equal (driverlist-eval (driverlist-rest-after-strength x strength) env)
           (4vec-driverlist-rest-after-strength (driverlist-eval x env) strength))
    :hints(("Goal" :in-theory (enable driverlist-eval driver-eval
                                      driverlist-rest-after-strength)))))



(define 4vec-driverlist-val ((x 4vec-driverlist-p))
  :measure (len x)
  :guard (4vec-drivestrength-ordered-p x)
  :verify-guards nil
  :returns (value 4vec-p)
  (b* (((when (atom x)) (4vec-z))
       (strength1 (4vec-driver->strength (car x)))
       (vals1 (4vec-driverlist-values-of-strength x strength1))
       (rest1 (4vec-driverlist-rest-after-strength x strength1))
       (res1 (4veclist-resolve vals1))
       ((when (atom rest1)) res1))
    (4vec-override res1 (4vec-driverlist-val rest1)))
  ///
  (verify-guards 4vec-driverlist-val)

  (local (defthm consp-of-driverlist-res-after-strength
           (iff (consp (4vec-driverlist-rest-after-strength
                        (driverlist-eval x env) strength))
                (consp (driverlist-rest-after-strength x strength)))
           :hints(("Goal" :in-theory (enable 4vec-driverlist-rest-after-strength
                                             driverlist-eval
                                             driverlist-rest-after-strength)))))
  (defthm driverlist->svex-correct
    (equal (svex-eval (driverlist->svex x) env)
           (4vec-driverlist-val (driverlist-eval x env)))
    :hints(("Goal" :in-theory (enable driverlist->svex svex-apply)
            :induct t))))





(define 4vec-netassigns->resolves-nrev ((x 4vec-netassigns-p) (nrev))
  :measure (len (4vec-netassigns-fix x))
  (b* ((x (4vec-netassigns-fix x))
       ((when (atom x)) (acl2::nrev-fix nrev))
       ((cons name drivers) (car x))
       (value (4vec-driverlist-val (4vec-drivestrength-sort (4vec-driverlist-fix drivers))))
       (nrev (acl2::nrev-push (cons name value) nrev)))
    (4vec-netassigns->resolves-nrev (cdr x) nrev)))


(defthm drivestrength-insert-correct
  (equal (driverlist-eval (drivestrength-insert d x) env)
         (4vec-drivestrength-insert (driver-eval d env) (driverlist-eval x env)))
  :hints(("Goal" :in-theory (enable driverlist-eval drivestrength-insert
                                    4vec-drivestrength-insert))))

(defthm drivestrength-insertsort-correct
  (equal (driverlist-eval (drivestrength-insertsort x) env)
         (4vec-drivestrength-insertsort (driverlist-eval x env)))
  :hints(("Goal" :in-theory (enable driverlist-eval drivestrength-insertsort
                                    4vec-drivestrength-insertsort))))

(define 4vec-netassigns->resolves ((x 4vec-netassigns-p))
  :measure (len (4vec-netassigns-fix x))
  :returns (assigns svex-env-p)
  :verify-guards nil
  (mbe :logic
       (b* ((x (4vec-netassigns-fix x))
            ((when (atom x)) nil)
            ((cons name drivers) (car x))
            (value (4vec-driverlist-val (4vec-drivestrength-sort (4vec-driverlist-fix drivers)))))
         (cons (cons name value)
               (4vec-netassigns->resolves (cdr x))))
       :exec
       (if (atom x)
           nil
         (acl2::with-local-nrev
           (4vec-netassigns->resolves-nrev x acl2::nrev))))
  ///
  (local (defthm 4vec-netassigns->resolves-nrev-elim
           (equal (4vec-netassigns->resolves-nrev x nrev)
                  (append nrev (4vec-netassigns->resolves x)))
           :hints(("Goal" :in-theory (enable 4vec-netassigns->resolves-nrev acl2::rcons)))))

  (verify-guards 4vec-netassigns->resolves)

  (local (defthm netassigns-eval-in-terms-of-netassigns-fix
           (equal (netassigns-eval x env)
                  (let ((x (netassigns-fix x)))
                    (if (atom x)
                        x
                      (cons (cons (caar x)
                                  (driverlist-eval (cdar x) env))
                            (netassigns-eval (cdr x) env)))))
           :hints(("Goal" :in-theory (enable netassigns-eval netassigns-fix)))
           :rule-classes ((:definition :controller-alist ((netassigns-eval t nil))))))

  (defthm netassigns->resolves-correct
    (equal (svex-alist-eval (netassigns->resolves x) env)
           (4vec-netassigns->resolves (netassigns-eval x env)))
    :hints(("Goal" :in-theory (enable netassigns->resolves
                                      svex-alist-eval))))

  (local (defthm consp-car-of-4vec-netassigns-fix-fwd
           (implies (consp (4vec-netassigns-fix x))
                    (consp (car (4vec-netassigns-fix x))))
           :rule-classes :forward-chaining))

  (defret keys-of-<fn>
    (iff (hons-assoc-equal k assigns)
         (hons-assoc-equal k (4vec-netassigns-fix x)))))

