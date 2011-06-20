
(in-package "ACL2")

(include-book "centaur/aig/eval-restrict" :dir :system)

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
  (b* ((assign (append curr-st (car inputs)))
       ((when (atom (cdr inputs)))
        (aig-eval prop assign))
       (next-st (aig-eval-alist updates assign)))
    (check-property updates prop next-st (cdr inputs))))

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



