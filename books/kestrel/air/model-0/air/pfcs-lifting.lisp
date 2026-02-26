; AIR Library
; Model 0: PFCS Lifting
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

(include-book "pfcs-constraints")

(include-book "projects/pfcs/lifting" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pfcs-lifting
  :parents (model-0)
  :short "Lifting of the PFCS constraints to ACL2 predicates."
  :long
  (xdoc::topstring
   (xdoc::p
    "We lift the deeply embedded PFCS constraints
     defined in @(see pfcs-constraints)
     to shallowly embedded ACL2 predicates.")
   (xdoc::p
    "The fixed constraints are lifted automatically,
     with proofs of correctness.
     The parameterized constraints
     (i.e. the ones whose number and variables vary)
     are lifted manually for now;
     the proofs of correctness still need to be done."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pfcs-initial-lifting
  :short "Lifting of the first row constraints to a predicate."
  (pfcs::lift (pfcs-initial)
              :pred pfcs-initial-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pfcs-final-lifting
  :short "Lifting of the last row constraints to a predicate."
  (pfcs::lift (pfcs-final)
              :pred pfcs-final-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pfcs-pc-transition-lifting
  :short "Lifting of the program counter transition constraints to a predicate."
  (pfcs::lift (pfcs-pc-transition)
              :pred pfcs-pc-transition-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pfcs-acc-transition-lifting
  :short "Lifting of the accumulator transition constraints to a predicate."
  (pfcs::lift (pfcs-acc-transition)
              :pred pfcs-acc-transition-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pfcs-halted-transition-lifting
  :short "Lifting of the halted flag transition constraints to a predicate."
  (pfcs::lift (pfcs-halted-transition)
              :pred pfcs-halted-transition-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pfcs-transition-lifting
  :short "Lifting of the transition constraints to a predicate."
  (pfcs::lift (pfcs-transition)
              :pred pfcs-transition-pred
              :prime prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pfcs-all-transitions-lifting
  :short "Lifting of the constraints for all transitions to a predicate."

  (defund pfcs-all-transitions-pred (pcs ; pfield::fe-listp
                                     accs ; pfield::fe-listp
                                     ops ; pfield::fe-listp
                                     hlts ;  pfield::fe-listp
                                     prime) ; pfcs::primep
    ;; (len pcs) = (len accs) = (len ops) = (len hlts)
    (or (endp pcs)
        (endp (cdr pcs))
        (and (pfcs-transition-pred
              (car pcs) (car accs) (car ops) (car hlts)
              (cadr pcs) (cadr accs) (cadr ops) (cadr hlts)
              prime)
             (pfcs-all-transitions-pred (cdr pcs)
                                        (cdr accs)
                                        (cdr ops)
                                        (cdr hlts)
                                        prime))))

  ;; TODO: lifting theorem
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pfcs-execution-lifting
  :short "Lifting of the constraints for execution."

  (defund pfcs-execution-pred (pcs ; pfield::fe-listp
                               accs ; pfield::fe-listp
                               ops ; pfield::fe-listp
                               hlts ;  pfield::fe-listp
                               prime) ; pfcs::primep
    ;; (len pcs) = (len accs) = (len ops) = (len hlts)
    (and (pfcs-initial-pred (car pcs)
                            (car accs)
                            (car ops)
                            (car hlts)
                            prime)
         (pfcs-all-transitions-pred pcs accs ops hlts prime)
         (pfcs-final-pred (car (last pcs))
                          (car (last accs))
                          (car (last ops))
                          (car (last hlts))
                          prime)))

  ;; TODO: lifting theorem
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pfcs-path-lifting
  :short "Lifting of the path constraints to a predicate."

  (defund pfcs-path-pred (path ; nat-listp
                          pcs ; pfield::fe-listp
                          prime) ; pfcs::primep
    ;; (len pcs) = (len path)
    (or (endp path)
        (and (equal (pfield::sub (car pcs)
                                 (car path)
                                 prime)
                    0)
             (pfcs-path-pred (cdr path) (cdr pcs) prime))))

  ;; TODO: lifting theorem
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pfcs-opcodes-lifting
  :short "Lifting of the opcode constraints to a predicate."

  (defund pfcs-opcodes-pred (opcodes ; program-p
                             ops ; pfield::fe-listp
                             prime) ; pfcs::primep
    ;; (len ops) = (len opcodes)
    (or (endp opcodes)
        (and (equal (pfield::sub (car ops)
                                 (opcode-to-field (car opcodes))
                                 prime)
                    0)
             (pfcs-opcodes-pred (cdr opcodes) (cdr ops) prime))))

  ;; TODO: lifting theorem
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pfcs-table-lifting
  :short "Lifting of the table constraints to a predicate."

  (defund pfcs-table-pred (path ; nat-listp
                           opcodes ; program-p
                           pcs ; pfield::fe-listp
                           accs ; pfield::fe-listp
                           ops ; pfield::fe-listp
                           hlts ;  pfield::fe-listp
                           prime) ; pfcs::primep
    ;; (len pcs) = (len accs) = (len ops) = (len hlts) = (len opcodes)
    (and (pfcs-execution-pred pcs accs ops hlts prime)
         (pfcs-path-pred path pcs prime)
         (pfcs-opcodes-pred opcodes ops prime)))

  ;; TODO: lifting theorem
)
