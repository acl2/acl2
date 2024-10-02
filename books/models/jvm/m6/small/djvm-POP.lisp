(in-package "ACL2")
(include-book "djvm-model")
(include-book "generic")
(include-book "consistent-state")
(include-book "consistent-state-properties")

(local (include-book "consistent-state-step"))
(local (in-theory (disable consistent-state)))

;----------------------------------------------------------------------

(local 
 (defthm consistent-state-op-code-POP-implies-pc-in-range
   (implies (and (consistent-state st)
                 (equal (op-code (next-inst st)) 'POP))
            (pc-in-range st))
   :hints (("Goal" :in-theory (enable next-inst)))))


(local (in-theory (disable next-inst bcv-simple-check-step-pre
                           extract-sig-frame pc-in-range
                           bcv-method collect-witness-bcv-method
                           op-code consistent-state
                           sig-frame-compatible
                           current-method)))



(local 
 (defthm current-method-normalize
   (equal (CDR (ASSOC-EQUAL (G 'METHOD-NAME
                               (CAR (G 'CALL-STACK ST)))
                            (G 'METHOD-TABLE ST)))
          (current-method st))
   :hints (("Goal" :in-theory (enable current-method)))))



(local 
 (defthm bcv-simple-execute-step-inst-POP-fact-1
   (implies (equal (op-code inst) 'POP)
            (equal (g 'pc (car (bcv-simple-execute-step inst pre)))
                   (+ 1 (g 'pc pre))))))


(local 
 (defthm bcv-simple-execute-step-inst-POP-fact-2
  (implies (equal (op-code inst) 'POP)
           (member (car (bcv-simple-execute-step inst pre))
                   (bcv-simple-execute-step inst pre)))))



(local 
 (defthm |Subgoal 4|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'POP))
   (EQUAL
    (G 'PC
       (CDR (ASSOC-EQUAL (+ 1 (G 'PC (CAR (G 'CALL-STACK ST))))
                                  (collect-witness-bcv-method
                                     (current-method st)
                                     (g 'method-table st)))))
    (+ 1 (G 'PC (CAR (G 'CALL-STACK ST))))))
  :hints (("Goal" 
           :in-theory (e/d () (bcv-simple-execute-step))
           :use ((:instance all-next-state-safe-implies-pc-equal
                            (x (car (bcv-simple-execute-step (next-inst st) 
                                                             (cdr (assoc-equal
                                                                   (g 'pc 
                                                                      (car 
                                                                       (g 'call-stack
                                                                          st)))
                                                                   (collect-witness-bcv-method (current-method st)
                                                                                               (g 'method-table st)))))))

                            (l (bcv-simple-execute-step 
                                (next-inst st) 
                                (cdr (assoc-equal
                                      (g 'pc 
                                         (car 
                                          (g 'call-stack
                                             st)))
                                      (collect-witness-bcv-method (current-method st)
                                                                  (g 'method-table st))))))
                            (sig-vector (collect-witness-bcv-method (current-method st)
                                                                    (g 'method-table st)))))))))





(local 
 (defthm bcv-simple-execute-step-inst-POP-fact-3
  (implies (equal (op-code inst) 'POP)
           (equal (g 'max-stack (car (bcv-simple-execute-step inst pre)))
                  (g 'max-stack pre)))))

(local
(defthm |Subgoal 3|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'POP))
   (EQUAL
    (G 'MAX-STACK
       (CDR (ASSOC-EQUAL (+ 1 (G 'PC (CAR (G 'CALL-STACK ST))))
                                  (collect-witness-bcv-method
                                     (current-method st)
                                     (g 'method-table st)))))
    (G 'MAX-STACK (CAR (G 'CALL-STACK ST)))))
  :hints (("Goal" 
           :in-theory (e/d () (bcv-simple-execute-step))
           :use ((:instance all-next-state-safe-implies-max-stack-equal
                            (x (car (bcv-simple-execute-step (next-inst st) 
                                                             (cdr (assoc-equal
                                                                   (g 'pc 
                                                                      (car 
                                                                       (g 'call-stack
                                                                          st)))
                                                                   (collect-witness-bcv-method (current-method st)
                                                                                               (g 'method-table st)))))))

                            (l (bcv-simple-execute-step 
                                (next-inst st) 
                                (cdr (assoc-equal
                                      (g 'pc 
                                         (car 
                                          (g 'call-stack
                                             st)))
                                      (collect-witness-bcv-method (current-method st)
                                                                  (g 'method-table st))))))
                            (sig-vector (collect-witness-bcv-method (current-method st)
                                                                    (g
                                                                     'method-table st))))))))
)




(local 
(defthm bcv-simple-execute-step-inst-POP-fact-4
  (implies (equal (op-code inst) 'POP)
           (equal (g 'method-table (car (bcv-simple-execute-step inst pre)))
                  (g 'method-table pre)))))


(local 
(defthm |Subgoal 2|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'POP))
   (EQUAL
    (G 'method-table
       (CDR (ASSOC-EQUAL (+ 1 (G 'PC (CAR (G 'CALL-STACK ST))))
                                  (collect-witness-bcv-method
                                     (current-method st)
                                     (g 'method-table st)))))
    (G 'method-table st)))
  :hints (("Goal" 
           :in-theory (e/d () (bcv-simple-execute-step
                               consistent-state-sig-frame-compatible))
           :use ((:instance consistent-state-sig-frame-compatible)
                 (:instance all-next-state-safe-implies-method-table-equal
                            (x (car (bcv-simple-execute-step (next-inst st) 
                                                             (cdr (assoc-equal
                                                                   (g 'pc 
                                                                      (car 
                                                                       (g 'call-stack
                                                                          st)))
                                                                   (collect-witness-bcv-method (current-method st)
                                                                                               (g 'method-table st)))))))

                            (l (bcv-simple-execute-step 
                                (next-inst st) 
                                (cdr (assoc-equal
                                      (g 'pc 
                                         (car 
                                          (g 'call-stack
                                             st)))
                                      (collect-witness-bcv-method (current-method st)
                                                                  (g 'method-table st))))))
                            (sig-vector (collect-witness-bcv-method (current-method st)
                                                                    (g 'method-table st)))))))))




(local 
 (defthm bcv-simple-check-step-pre-POP
   (implies (and (equal (op-code inst) 'POP)
                 (bcv-simple-check-step-pre inst
                                     (extract-sig-frame 
                                      (topx (g 'call-stack st))
                                      (g 'method-table st))))
            (<= 1 (len (g 'op-stack (car (g 'call-stack st))))))
   :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))


(local 
 (defthm bcv-simple-check-step-pre-POP-specific
   (implies (and (equal (op-code (next-inst st)) 'POP)
                 (bcv-simple-check-step-pre (next-inst st)
                                     (extract-sig-frame 
                                      (topx (g 'call-stack st))
                                      (g 'method-table st))))
            (<= 1  (len (g 'op-stack (car (g 'call-stack st))))))
   :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))
   :rule-classes :linear))


;; (local 
;;  (defthm bcv-simple-check-step-pre-POP-fact-5
;;    (implies (and (equal (op-code inst) 'POP)
;;                  (bcv-simple-check-step-pre inst
;;                                      (extract-sig-frame 
;;                                       (topx (g 'call-stack st))
;;                                       (g 'method-table st))))
;;             (equal (g 'op-stack (car (bcv-simple-execute-step inst 
                                                       
                                                       

;;                                      (extract-sig-frame 
;;                                       (topx (g 'call-stack st))
;;                                       (g 'method-table st)))))
;;                    (- (len (g 'op-stack (car (g 'call-stack st)))) 1)))
;;    :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))


;; (local 
;;  (defthm bcv-simple-check-step-pre-POP-fact-5-specific
;;    (implies (and (equal (op-code (next-inst st)) 'POP)
;;                  (bcv-simple-check-step-pre (next-inst st)
;;                                      (extract-sig-frame 
;;                                       (topx (g 'call-stack st))
;;                                       (g 'method-table st))))
;;             (equal (g 'op-stack (car (bcv-simple-execute-step 
;;                                       (next-inst st)
;;                                       (extract-sig-frame 
;;                                       (topx (g 'call-stack st))
;;                                       (g 'method-table st)))))
;;                    (- (len (g 'op-stack (car (g 'call-stack st)))) 1)))
;;    :hints (("Goal" :use ((:instance bcv-simple-check-step-pre-pop-fact-5
;;                                     (inst (next-inst st))))))))


(local 
(defthm bcv-simple-execute-step-inst-POP-fact-5
  (implies (equal (op-code inst) 'POP)
           (equal (g 'op-stack (car (bcv-simple-execute-step inst pre)))
                  (g 'op-stack (sig-frame-pop-value pre))))))




(local 
  (defthm |Subgoal 1|
   (implies (AND (CONSISTENT-STATE ST)
                 (EQUAL (op-code (NEXT-INST ST)) 'POP))
            (EQUAL
             (G 'OP-STACK
                (CDR (ASSOC-EQUAL (+ 1 (G 'PC (CAR (G 'CALL-STACK ST))))
                                  (collect-witness-bcv-method
                                     (current-method st)
                                     (g 'method-table st)))))
             (- (LEN (G 'OP-STACK (CAR (G 'CALL-STACK ST))))
                1)))
  :hints (("Goal" 
           :in-theory (e/d () (bcv-simple-execute-step
                               consistent-state-sig-frame-compatible))
           :use ((:instance consistent-state-sig-frame-compatible)
                 (:instance all-next-state-safe-implies-opstack-equal
                            (x (car (bcv-simple-execute-step (next-inst st) 
                                                             (cdr (assoc-equal
                                                                   (g 'pc 
                                                                      (car 
                                                                       (g 'call-stack
                                                                          st)))
                                                                   (collect-witness-bcv-method (current-method st)
                                                                                               (g 'method-table st)))))))

                            (l (bcv-simple-execute-step 
                                (next-inst st) 
                                (cdr (assoc-equal
                                      (g 'pc 
                                         (car 
                                          (g 'call-stack
                                             st)))
                                      (collect-witness-bcv-method (current-method st)
                                                                  (g 'method-table st))))))
                            (sig-vector (collect-witness-bcv-method (current-method st)
                                                                    (g 'method-table st)))))))))











(local 
(defthm bcv-simple-execute-step-inst-method-name-fact
  (implies (equal (op-code inst) 'POP)
           (equal (g 'method-name (car (bcv-simple-execute-step inst pre)))
                  (g 'method-name pre))))
)


(defthm invoke-produce-consp
   (implies (equal (op-code inst) 'POP)
            (CONSP (bcv-simple-execute-step inst any-frame))))

;;(i-am-here) ;; Thu Nov  3 22:26:11 2005

(local 
 (defthm |Subgoal 0|
   (implies (AND (CONSISTENT-STATE ST)
                 (EQUAL (op-code (NEXT-INST ST)) 'POP))
            (EQUAL
             (G 'method-name
                (CDR (ASSOC-EQUAL (+ 1 (G 'PC (CAR (G 'CALL-STACK ST))))
                                  (collect-witness-bcv-method 
                                   (current-method st)
                                   (g 'method-table st)))))
             (G 'method-name
                (CAR (G 'CALL-STACK ST)))))
  :hints (("Goal" 
           :in-theory (e/d () (bcv-simple-execute-step
                               consistent-state-sig-frame-compatible))
           :use ((:instance consistent-state-sig-frame-compatible)
                 (:instance all-next-state-safe-implies-method-name-equal
                            (x (car (bcv-simple-execute-step (next-inst st) 
                                                             (cdr (assoc-equal
                                                                   (g 'pc 
                                                                      (car 
                                                                       (g 'call-stack
                                                                          st)))
                                                                   (collect-witness-bcv-method (current-method st)
                                                                                               (g 'method-table st)))))))

                            (l (bcv-simple-execute-step 
                                (next-inst st) 
                                (cdr (assoc-equal
                                      (g 'pc 
                                         (car 
                                          (g 'call-stack
                                             st)))
                                      (collect-witness-bcv-method (current-method st)
                                                                  (g 'method-table st))))))
                            (sig-vector (collect-witness-bcv-method (current-method st)
                                                                    (g 'method-table st)))))))))   





(local 
 (defthm len-consp
   (implies (< 0 (len l))
            (consp l))))




(local 
 (defthm consistent-state-preserved-by-POP-lemma
   (implies (and (consistent-state st)
                 (equal (next-inst st) inst)
                 (equal (op-code inst) 'POP)
                 (djvm-check-POP inst st))
            (consistent-state-step
             (djvm-execute-POP inst st)))
   :hints (("Goal" :in-theory (enable sig-frame-compatible pc-in-range)))))


;----------------------------------------------------------------------




(local (in-theory (disable djvm-execute-POP consistent-state-step)))

(local 
 (defthm consistent-state-step-implies-consistent-state-djvm-execute-POP
   (implies (consistent-state-step (djvm-execute-POP inst st))
            (consistent-state (djvm-execute-POP inst st)))
   :hints (("Goal" :use ((:instance
                          consistent-state-step-implies-implies-consistent-state
                          (s (djvm-execute-POP inst st))))))))





(defthm consistent-state-preserved-by-DJVM-POP
  (implies (and (consistent-state st)
                (equal (next-inst st) inst)
                (equal (op-code inst) 'POP)
                (djvm-check-POP inst st))
           (consistent-state
            (djvm-execute-POP inst st))))
