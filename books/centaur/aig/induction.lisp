; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
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

(in-package "ACL2")

(include-book "eval-restrict")

(local (in-theory (disable append-of-nil)))

;; This book defines check-property, which checks that a safety property
;; on a FSM holds after some number of steps in which provided inputs are
;; applied.  The FSM is expressed as a set of AIG update functions and an AIG
;; property.

;; We prove that provided there exists an invariant, an AIG for which three
;; Boolean properties (checkable by SAT) and a side condition hold, then
;; check-property always holds.  This can be used to validate the result of a
;; model checking algorithm such as interpolation or property-driven
;; reachability that produces an invariant, given a method for validating UNSAT
;; proofs.

(defun check-property (updates prop curr-st inputs)
  (declare (Xargs :guard (consp inputs)))
  (b* ((assign (hons-shrink-alist
                (car inputs)
                (hons-shrink-alist curr-st nil)))
       ((when (atom (cdr inputs)))
        (b* ((res (aig-eval prop assign)))
          (fast-alist-free assign)
          res))
       (next-st (aig-eval-alist updates assign)))
    (fast-alist-free assign)
    (check-property updates prop next-st (cdr inputs))))

(defcong alist-equiv equal (check-property updates prop curr-st inputs) 3)
(defcong alist-equiv equal (check-property updates prop curr-st inputs) 1)

(defun check-property-strong (updates prop curr-st inputs)
  (declare (Xargs :measure (len inputs)
                  :guard t))
  (if (atom inputs)
      t
    (b* ((assign (hons-shrink-alist
                  (car inputs)
                  (hons-shrink-alist curr-st nil)))
         ((when (not (aig-eval prop assign)))
          (fast-alist-free assign)
          nil)
         (next-st (aig-eval-alist updates assign)))
      (fast-alist-free assign)
      (check-property-strong updates prop next-st (cdr inputs)))))

(defun-sk check-ag-property (updates prop curr-st)
  (forall inputs (check-property updates prop curr-st inputs)))

(defthm check-ag-property-implies-check-property-strong
  (implies (check-ag-property updates prop curr-st)
           (check-property-strong updates prop curr-st inputs))
  :hints (("goal" :in-theory (disable check-ag-property
                                      check-ag-property-necc)
           :induct (check-property-strong updates prop curr-st inputs))
          (and stable-under-simplificationp
               (cond
                ((member-equal
                  '(AIG-EVAL PROP (binary-APPEND CURR-ST (CAR INPUTS)))
                  clause)
                 '(:use ((:instance check-ag-property-necc
                          (inputs (list (car inputs)))))))
                (t
                 '(:expand
                   ((CHECK-AG-PROPERTY
                     UPDATES PROP
                     (AIG-EVAL-ALIST UPDATES (APPEND CURR-ST (CAR INPUTS)))))
                   :use ((:instance check-ag-property-necc
                          (inputs (cons (car inputs)
                                        (let ((rest (check-ag-property-witness
                                                     updates prop
                                                     (aig-eval-alist
                                                      updates
                                                      (append curr-st (car inputs))))))
                                          (if (consp rest)
                                              rest
                                            (list nil)))))))))))))



(defun-sk unsat-p (x)
  (forall env (not (aig-eval x env))))

(local
 (progn

   (defthm aig-eval-when-vars-subset-of-first-keys
     (implies (subsetp-equal (aig-vars x) (alist-keys a))
              (equal (aig-eval x (append a b))
                     (aig-eval x a)))
     :hints(("Goal" :in-theory (enable aig-env-lookup
                                       subsetp-equal))))

   (defthm invar-holds-after-apply-updates1
     (implies (and (unsat-p (aig-and invar
                                     (aig-not (aig-restrict invar updates))))
                   (unsat-p (aig-not (aig-partial-eval invar initst)))
                   (subsetp-equal (aig-vars invar)
                                  (alist-keys updates)))
              (aig-eval
               invar
               (aig-eval-alist updates (append initst inputs))))
     :hints(("Goal" :in-theory (disable unsat-p aig-eval aig-eval-alist)
             :do-not-induct t
             :use ((:instance unsat-p-necc
                    (x (aig-and invar
                                (aig-not (aig-restrict invar updates))))
                    (env (append initst inputs)))
                   (:instance unsat-p-necc
                    (x (aig-not (aig-partial-eval invar initst)))
                    (env inputs)))))
     :otf-flg t)


   (defthm invar-holds-after-apply-updates
     (implies (and (unsat-p (aig-and invar
                                     (aig-not (aig-restrict invar updates))))
                   (unsat-p (aig-not (aig-partial-eval invar initst)))
                   (subsetp-equal (aig-vars invar)
                                  (alist-keys updates)))
              (unsat-p (aig-not (aig-partial-eval
                                 invar
                                 (aig-eval-alist
                                  updates
                                  (append initst inputs))))))
     :hints(("Goal" :in-theory (disable unsat-p aig-eval aig-eval-alist)
             :expand ((unsat-p (aig-not (aig-partial-eval
                                         invar
                                         (aig-eval-alist
                                          updates
                                          (append initst inputs))))))
             :do-not-induct t))
     :otf-flg t)


   (defthm prop-holds-when-invar-holds
     (implies (and (unsat-p (aig-and invar (aig-not prop)))
                   (unsat-p (aig-not (aig-partial-eval invar initst))))
              (aig-eval prop (append initst input)))
     :hints(("Goal" :in-theory (disable unsat-p aig-eval)
             :do-not-induct t
             :use ((:instance unsat-p-necc
                    (x (aig-and invar (aig-not prop)))
                    (env (append initst input)))
                   (:instance unsat-p-necc
                    (x (aig-not (aig-partial-eval invar initst)))
                    (env input))))))))

;; If there exists an invariant that satisfies inducitivity, sufficiency, and
;; initialization, then check-property is always true.
;; One subtlety: here the initial state may be partial, i.e. an alist that does
;; not bind all the state variables.  In this case the full initial state
;; applied is determined by the first input vector.
(defthm inductive-invariant-impl-check-property
  (implies (and
            ;; The variables of the invariant must be state variables, not inputs
            (subsetp-equal (aig-vars invar)
                           (alist-keys updates))
            ;; The invariant is inductive, i.e. it is preserved by the update function
            (unsat-p (aig-and
                      invar
                      (aig-not
                       (aig-restrict invar updates))))
            ;; The invariant implies the property
            (unsat-p (aig-and invar (aig-not prop)))
            ;; The invariant holds under the initial state.
            (unsat-p (aig-not (aig-partial-eval invar initst))))
           (check-property updates prop initst inputs))
  :hints (("goal" :induct (check-property updates prop initst inputs)
           :in-theory (disable unsat-p))))

(defthm inductive-invariant-impl-check-ag-property
  (implies (and
            ;; The variables of the invariant must be state variables, not inputs
            (subsetp-equal (aig-vars invar)
                           (alist-keys updates))
            ;; The invariant is inductive, i.e. it is preserved by the update function
            (unsat-p (aig-and
                      invar
                      (aig-not
                       (aig-restrict invar updates))))
            ;; The invariant implies the property
            (unsat-p (aig-and invar (aig-not prop)))
            ;; The invariant holds under the initial state.
            (unsat-p (aig-not (aig-partial-eval invar initst))))
           (check-ag-property updates prop initst)))

(defthm inductive-invariant-impl-check-property-strong
  (implies (and
            ;; The variables of the invariant must be state variables, not inputs
            (subsetp-equal (aig-vars invar)
                           (alist-keys updates))
            ;; The invariant is inductive, i.e. it is preserved by the update function
            (unsat-p (aig-and
                      invar
                      (aig-not
                       (aig-restrict invar updates))))
            ;; The invariant implies the property
            (unsat-p (aig-and invar (aig-not prop)))
            ;; The invariant holds under the initial state.
            (unsat-p (aig-not (aig-partial-eval invar initst))))
           (check-property-strong updates prop initst inputs)))





