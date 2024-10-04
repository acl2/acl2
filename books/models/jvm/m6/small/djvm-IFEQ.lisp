(in-package "ACL2")
(include-book "djvm-model")
(include-book "generic")
(include-book "consistent-state")
(include-book "consistent-state-properties")



(local (include-book "consistent-state-step"))
(local (in-theory (disable consistent-state)))

;----------------------------------------------------------------------

(local 
 (defthm consistent-state-op-code-IFEQ-implies-pc-in-range
   (implies (and (consistent-state st)
                 (equal (op-code (next-inst st)) 'IFEQ))
            (pc-in-range st))
   :hints (("Goal" :in-theory (enable next-inst)))))




(local (in-theory (disable next-inst bcv-simple-check-step-pre
                           extract-sig-frame pc-in-range
                           op-code consistent-state
                           bcv-method collect-witness-bcv-method
                           sig-frame-compatible
                           current-method)))


(local 
 (defthm current-method-normalize
   (equal (CDR (ASSOC-EQUAL (G 'METHOD-NAME
                               (CAR (G 'CALL-STACK ST)))
                            (G 'METHOD-TABLE ST)))
          (current-method st))
   :hints (("Goal" :in-theory (enable current-method)))))


;; (defthm consistent-state-len-opstack-in-limit-specific
;;    (implies (consistent-state st)
;;             (<= (len (cdr (g 'op-stack (car (g 'call-stack st)))))
;;                 (g 'max-stack (car (g 'call-stack st)))))
;;    :hints (("Goal" :use consistent-state-len-opstack-in-limit)))



(local 
 (defthm bcv-simple-execute-step-inst-IFEQ-fact-1
  (implies (equal (op-code inst) 'IFEQ)
           (equal (g 'pc (cadr (bcv-simple-execute-step inst pre)))
                  (cadr inst)))))

(local 
 (defthm bcv-simple-execute-step-inst-IFEQ-fact-1-2
  (implies (equal (op-code inst) 'IFEQ)
           (equal (g 'pc (car (bcv-simple-execute-step inst pre)))
                  (+ 1 (g 'pc pre))))))


(defthm IFEQ-produce-consp
   (implies (equal (op-code inst) 'IFEQ)
            (CONSP (bcv-simple-execute-step inst any-frame))))

(defthm IFEQ-produce-consp-2
   (implies (equal (op-code inst) 'IFEQ)
            (bcv-simple-execute-step inst any-frame)))


(defthm IFEQ-produce-consp-3
   (implies (equal (op-code inst) 'IFEQ)
            (CONSP (cdr (bcv-simple-execute-step inst any-frame)))))

(defthm IFEQ-produce-consp-4
   (implies (and (case-split (cadr inst))
                 (equal (op-code inst) 'IFEQ))
            (cadr (bcv-simple-execute-step inst any-frame))))



(defthm member-cadr
  (implies (consp (cdr l))
           (member (cadr l) l)))






(local 
 (defthm |Subgoal 5|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'IFEQ)
        (equal (car (g 'op-stack (car (g 'call-stack st)))) 0))
   (EQUAL
    (G 'PC
       (CDR (ASSOC-EQUAL (cadr (next-inst st))
                         (collect-witness-bcv-method 
                          (current-method st)
                          (g 'method-table st)))))
    (cadr (next-inst st))))
  :hints (("Goal" 
           :in-theory (e/d () (bcv-simple-execute-step))
           :use ((:instance all-next-state-safe-implies-pc-equal
                            (x (cadr (bcv-simple-execute-step (next-inst st) 
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
 (defthm bcv-simple-execute-step-inst-IFEQ-fact-2
  (implies (equal (op-code inst) 'IFEQ)
           (equal (g 'max-stack (car (bcv-simple-execute-step inst pre)))
                  (g 'max-stack pre)))))


(local 
 (defthm bcv-simple-execute-step-inst-IFEQ-fact-3
  (implies (equal (op-code inst) 'IFEQ)
           (equal (g 'max-stack (cadr (bcv-simple-execute-step inst pre)))
                  (g 'max-stack pre)))))

(local
(defthm |Subgoal 4|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'IFEQ)
        (equal (car (g 'op-stack (car (g 'call-stack st)))) 0))        
   (EQUAL
    (G 'MAX-STACK
       (CDR (ASSOC-EQUAL (cadr (next-inst st))
                         (collect-witness-bcv-method 
                            (current-method st)
                            (g 'method-table st)))))
    (G 'MAX-STACK (CAR (G 'CALL-STACK ST)))))
  :hints (("Goal" 
           :in-theory (e/d () (bcv-simple-execute-step))
           :use ((:instance all-next-state-safe-implies-max-stack-equal
                            (x (cadr (bcv-simple-execute-step (next-inst st) 
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
(defthm bcv-simple-execute-step-inst-IFEQ-fact-4
  (implies (equal (op-code inst) 'IFEQ)
           (equal (g 'method-table (car (bcv-simple-execute-step inst pre)))
                  (g 'method-table pre))))
)


(local 
(defthm bcv-simple-execute-step-inst-IFEQ-fact-5
  (implies (equal (op-code inst) 'IFEQ)
           (equal (g 'method-table (cadr (bcv-simple-execute-step inst pre)))
                  (g 'method-table pre)))))


(local 
(defthm |Subgoal 3|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'IFEQ))
   (EQUAL
    (G 'method-table
       (CDR (ASSOC-EQUAL (cadr (next-inst st))
                         (collect-witness-bcv-method 
                            (current-method st)
                            (g 'method-table st)))))
    (G 'method-table st)))
  :hints (("Goal" 
           :in-theory (e/d () (bcv-simple-execute-step
                               consistent-state-sig-frame-compatible))
           :use ((:instance consistent-state-sig-frame-compatible)
                 (:instance all-next-state-safe-implies-method-table-equal
                            (x (cadr (bcv-simple-execute-step (next-inst st) 
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
(defthm bcv-simple-execute-step-inst-IFEQ-fact-6
  (implies (equal (op-code inst) 'IFEQ)
           (equal (g 'op-stack (car (bcv-simple-execute-step inst pre)))
                  (g 'op-stack (sig-frame-pop-value pre))))))


(local 
(defthm bcv-simple-execute-step-inst-IFEQ-fact-7
  (implies (equal (op-code inst) 'IFEQ)
           (equal (g 'op-stack (cadr (bcv-simple-execute-step inst pre)))
                  (g 'op-stack (sig-frame-pop-value pre))))))



(local 
 (defthm bcv-simple-check-step-pre-IFEQ
   (implies (and (equal (op-code inst) 'IFEQ)
                 (bcv-simple-check-step-pre inst
                                     (extract-sig-frame 
                                      (topx (g 'call-stack st))
                                      (g 'method-table st))))
            (<= 1 (len (g 'op-stack (car (g 'call-stack st))))))
   :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))


(local 
 (defthm bcv-simple-check-step-pre-IFEQ-specific
   (implies (and (equal (op-code (next-inst st)) 'IFEQ)
                 (bcv-simple-check-step-pre (next-inst st)
                                     (extract-sig-frame 
                                      (topx (g 'call-stack st))
                                      (g 'method-table st))))
            (<= 1  (len (g 'op-stack (car (g 'call-stack st))))))
   :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))
   :rule-classes :linear))


(local 
(defthm |Subgoal 2|
   (implies (AND (CONSISTENT-STATE ST)
                 (EQUAL (op-code (NEXT-INST ST)) 'IFEQ))
            (EQUAL
             (G 'OP-STACK
                (CDR (ASSOC-EQUAL (cadr (next-inst st))
                         (collect-witness-bcv-method 
                            (current-method st)
                            (g 'method-table st)))))
             (+ -1 
                (LEN (G 'OP-STACK (CAR (G 'CALL-STACK ST)))))))
  :hints (("Goal" 
           :in-theory (e/d () (bcv-simple-execute-step
                               consistent-state-sig-frame-compatible))
           :use ((:instance consistent-state-sig-frame-compatible)
                 (:instance all-next-state-safe-implies-opstack-equal
                            (x (cadr (bcv-simple-execute-step (next-inst st) 
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
   

;----------------------------------------------------------------------

(local 
 (defthm |Subgoal 5-2|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'IFEQ)
        (not (equal (car (g 'op-stack (car (g 'call-stack st)))) 0)))
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
(defthm |Subgoal 4-2|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'IFEQ)
        (not (equal (car (g 'op-stack (car (g 'call-stack st)))) 0)))
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
                                                                    (g 'method-table st)))))))))


(local 
(defthm |Subgoal 3-2|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'IFEQ))
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
(defthm |Subgoal 2-2|
   (implies (AND (CONSISTENT-STATE ST)
                 (EQUAL (op-code (NEXT-INST ST)) 'IFEQ))
            (EQUAL
             (G 'OP-STACK
                (CDR (ASSOC-EQUAL (+ 1 (G 'PC (CAR (G 'CALL-STACK ST))))
                         (collect-witness-bcv-method 
                            (current-method st)
                            (g 'method-table st)))))
             (+ -1 
                (LEN (G 'OP-STACK (CAR (G 'CALL-STACK ST)))))))
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
;;(i-am-here)

(local 
(defthm bcv-simple-execute-step-inst-method-name-fact-1
  (implies (equal (op-code inst) 'IFEQ)
           (equal (g 'method-name (car (bcv-simple-execute-step inst pre)))
                  (g 'method-name pre)))))



(local 
(defthm bcv-simple-execute-step-inst-method-name-fact-2
  (implies (equal (op-code inst) 'IFEQ)
           (equal (g 'method-name (cadr (bcv-simple-execute-step inst pre)))
                  (g 'method-name pre)))))





(local 
 (defthm |Subgoal 1-1|
   (implies (AND (CONSISTENT-STATE ST)
                 (EQUAL (op-code (NEXT-INST ST)) 'IFEQ))
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
(defthm |Subgoal 1-2|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'IFEQ))
   (EQUAL
    (G 'method-name
       (CDR (ASSOC-EQUAL (cadr (next-inst st))
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
                            (x (cadr (bcv-simple-execute-step (next-inst st) 
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
;; (local 
;;  (defthm bcv-simple-check-step-pre-IFEQ-specific
;;    (implies (and (equal (op-code (next-inst st)) 'IFEQ)
;;                  (bcv-simple-check-step-pre (next-inst st)
;;                                      (extract-sig-frame 
;;                                       (topx (g 'call-stack st))
;;                                       (g 'method-table st))))
;;             (<= 1  (len (g 'op-stack (car (g 'call-stack st))))))
;;    :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))
;;    :rule-classes :linear))

(local 
 (defthm len-consp
   (implies (< 0 (len l))
            (consp l))))

;;(i-am-here) ;; Sun Nov 20 21:00:45 2005

(local 
 (defthm consistent-state-preserved-by-IFEQ-lemma
   (implies (and (consistent-state st)
                 (equal (next-inst st) inst)
                 (equal (op-code inst) 'IFEQ)
                 (djvm-check-IFEQ inst st))
            (consistent-state-step
             (djvm-execute-IFEQ inst st)))
   :hints (("Goal" :in-theory (enable sig-frame-compatible pc-in-range)))))



;----------------------------------------------------------------------


(local (in-theory (disable djvm-execute-IFEQ consistent-state-step)))

(local 
 (defthm consistent-state-step-implies-consistent-state-djvm-execute-IFEQ
   (implies (consistent-state-step (djvm-execute-IFEQ inst st))
            (consistent-state (djvm-execute-IFEQ inst st)))
   :hints (("Goal" :use ((:instance
                          consistent-state-step-implies-implies-consistent-state
                          (s (djvm-execute-IFEQ inst st))))))))




(defthm consistent-state-preserved-by-DJVM-IFEQ
  (implies (and (consistent-state st)
                (equal (next-inst st) inst)
                (equal (op-code inst) 'IFEQ)
                (djvm-check-IFEQ inst st))
           (consistent-state
            (djvm-execute-IFEQ inst st))))

