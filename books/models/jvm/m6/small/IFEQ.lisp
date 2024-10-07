(in-package "ACL2")
(include-book "djvm-model")
(include-book "bcv-simple-model")
(include-book "generic")

(include-book "consistent-state-properties")
(include-book "bcv-method-properties")


;--- EXPORT ----

(encapsulate () 
  (local (include-book "djvm-IFEQ"))
  (defthm consistent-state-preserved-by-DJVM-IFEQ
    (implies (and (consistent-state st)
                  (equal (next-inst st) inst)
                  (equal (op-code inst) 'IFEQ)
                  (djvm-check-IFEQ inst st))
             (consistent-state
              (djvm-execute-IFEQ inst st)))))


;;(i-am-here) ;; Mon Nov 21 10:57:11 2005




(defthm bcv-simple-inst-implies-next-pc-bounded-IFEQ
  (implies (and (bcv-simple-inst pc inst sig-vector)
                (equal (g 'pc (cdr (assoc-equal pc sig-vector))) pc)
                (equal (op-code inst) 'IFEQ))
           (assoc-equal (+ 1 pc) sig-vector)))



(defthm bcv-simple-inst-implies-next-pc-bounded-IFEQ-2
  (implies (and (bcv-simple-inst pc inst sig-vector)
                (equal (op-code inst) 'IFEQ))
           (assoc-equal (cadr inst) sig-vector)))



(local (in-theory (disable collect-witness-bcv-method)))


(defthm bcv-simple-inst-implies-next-pc-bounded-IFEQ-specific
  (implies (and (bcv-simple-inst pc (next-inst st)
                                 (collect-witness-bcv-method 
                                  (current-method st)
                                  (g 'method-table st)))
                (equal (g 'pc (cdr (assoc-equal pc 
                                                (collect-witness-bcv-method 
                                                 (current-method st)
                                                 (g 'method-table st)))))
                       pc)
                (equal (op-code (next-inst st)) 'IFEQ))
           (assoc-equal (+ 1 pc) (collect-witness-bcv-method 
                                  (current-method st)
                                  (g 'method-table st)))))


(defthm bcv-simple-inst-implies-next-pc-bounded-IFEQ-specific-2
  (implies (and (bcv-simple-inst pc (next-inst st)
                                 (collect-witness-bcv-method 
                                  (current-method st)
                                  (g 'method-table st)))
                (equal (op-code (next-inst st)) 'IFEQ))
           (assoc-equal (cadr (next-inst st))
                        (collect-witness-bcv-method 
                         (current-method st)
                         (g 'method-table st)))))


;; (defthm consistent-state-implies-bcv-simple-inst
;;   (implies (consistent-state st)
;;            (bcv-simple-inst (g 'pc (car (g 'call-stack st))) 
;;                             (next-inst st)
;;                             (collect-witness-bcv-method
;;                              (current-method st)
;;                              (g 'method-table st)))))



(defthm bcv-simple-inst-implies-next-pc-bounded-IFEQ-specific-2-futher
  (implies (and (consistent-state st)
                (equal (op-code (next-inst st)) 'IFEQ))
           (assoc-equal (cadr (next-inst st))
                        (collect-witness-bcv-method 
                         (current-method st)
                         (g 'method-table st))))
  :hints (("Goal" :use ((:instance
                         bcv-simple-inst-implies-next-pc-bounded-IFEQ-specific-2
                         (pc (g 'pc (car (g 'call-stack st)))))
                        (:instance consistent-state-implies-bcv-simple-inst))
           :in-theory (disable consistent-state 
                               bcv-simple-inst
                               consistent-state-implies-bcv-simple-inst
                               collect-witness-bcv-method))))







(local (in-theory (disable current-method consistent-state 
                           collect-witness-bcv-method
                           bcv-simple-inst next-inst)))



;; (defthm bcv-method-implies-integerp-if-bound
;;   (implies (and (bcv-method method method-table)
;;                 (assoc-equal pc (collect-witness-bcv-method method method-table)))
;;            (integerp pc))
;;   :hints (("Goal" :in-theory (disable merged-code-safe
;;                                       ;;collect-witness-bcv-method
;;                                       extract-code
;;                                       sig-method-init-frame
;;                                       wff-code1)
;;            :cases ((member pc (collect-pc-merged-code 
;;                                (MERGESTACKMAPANDCODE (G 'STACKMAPS METHOD)
;;                                                      (PARSECODE1 0 (G 'CODE METHOD))
;;                                                      (G 'METHOD-NAME METHOD)
;;                                                      METHOD-TABLE))))))
;;   :rule-classes :forward-chaining)


(defthm bcv-simple-check-ifeq-implies-djvm-check
  (IMPLIES (AND (CONSISTENT-STATE DJVM-S)
                (equal (op-code (next-inst djvm-s)) 'IFEQ)
                (BCV-SIMPLE-CHECK-IFEQ (next-inst djvm-s)   
                                       (EXTRACT-SIG-FRAME (CAR (G 'CALL-STACK DJVM-S))
                                                          (G 'METHOD-TABLE DJVM-S))))
           (DJVM-CHECK-IFEQ (next-inst djvm-s) djvm-s))
  :hints (("Goal" :in-theory (disable consistent-state)
           :use ((:instance bcv-method-implies-integerp-if-bound
                            (method (current-method djvm-s))
                            (method-table (g 'method-table djvm-s))
                            (pc (cadr (next-inst djvm-s))))))))









