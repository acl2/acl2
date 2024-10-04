(in-package "ACL2")
(include-book "djvm-model")
(include-book "generic")
(include-book "consistent-state")
(include-book "consistent-state-properties")



(local (include-book "consistent-state-step"))
(local (in-theory (disable consistent-state)))




(local 
 (defthm bcv-simple-check-step-pre-PUSH
   (implies (and (equal (op-code inst) 'PUSH)
                 (bcv-simple-check-step-pre inst
                                     (extract-sig-frame 
                                      (topx (g 'call-stack st))
                                      (g 'method-table st))))
            (<= (+ 1 (len (g 'op-stack (car (g 'call-stack st)))))
                (g 'max-stack (car (g 'call-stack st)))))
   :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))


(local 
 (defthm bcv-simple-check-step-pre-PUSH-specific
   (implies (and (equal (op-code (next-inst st)) 'PUSH)
                 (bcv-simple-check-step-pre (next-inst st)
                                     (extract-sig-frame 
                                      (topx (g 'call-stack st))
                                      (g 'method-table st))))
            (<= (+ 1 (len (g 'op-stack (car (g 'call-stack st)))))
                (g 'max-stack (car (g 'call-stack st)))))
   :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))

;;(i-am-here) ;; Thu Oct 20 16:52:57 2005

 ;; should be easy if we add the assertion that pc is integerp in
 ;; consistent-frame 
(local 
 (defthm consistent-state-op-code-push-implies-pc-in-range
   (implies (and (consistent-state st)
                 (equal (op-code (next-inst st)) 'PUSH))
            (pc-in-range st))))


(local (in-theory (disable next-inst bcv-simple-check-step-pre
                           extract-sig-frame pc-in-range
                           collect-witness-bcv-method
                           bcv-method
                           op-code consistent-state
                           sig-frame-compatible
                           current-method)))



(local 
 (defthm bcv-simple-execute-step-inst-push-fact-1
   (implies (equal (op-code inst) 'PUSH)
            (equal (g 'pc (car (bcv-simple-execute-step inst pre)))
                   (+ 1 (g 'pc pre))))))
   

(local 
 (defthm bcv-simple-execute-step-inst-push-fact-2
  (implies (equal (op-code inst) 'PUSH)
           (member (car (bcv-simple-execute-step inst pre))
                   (bcv-simple-execute-step inst pre)))))




;; (local 
;;  (defthm consistent-state-implies-all-next-state-safe-PUSH
;;    (implies (and (consistent-state st)
;;                  (equal (op-code (next-inst st)) 'PUSH))
;;             (all-next-state-safe (bcv-simple-execute-step (next-inst st)
;;                                                    (cdr (assoc-equal 
;;                                                          (g 'pc (car (g
;;                                                                       'call-stack st)))
;;                                                          (g 'sig-vector
;;                                                             (current-method
;;                                                              st)))))
;;                                  (g 'sig-vector 
;;                                     (current-method st))))
;;    :hints (("Goal" :in-theory (disable bcv-simple-execute-step next-inst
;;                                        all-next-state-safe)))))




(local 
 (defthm |Subgoal 5|
   (IMPLIES
    (AND (CONSISTENT-STATE ST)
         (EQUAL (op-code (NEXT-INST ST)) 'PUSH))
    (EQUAL
     (G 'PC
        (CDR (ASSOC-EQUAL (+ 1 (g 'pc  (car (g 'call-stack st))))
                          (collect-witness-bcv-method (current-method st)
                                                      (g 'method-table st)))))
     (+ 1 (g 'pc (car (g 'call-stack st))))))
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
                                                            

;; this is true, because: 
;;
;;   1. we know bcv-simple-execute-step for push produce a frame of (+ pc 1) 
;;   2. we know consistent-state, we know sig-frame-compatible pc with
;;      registered sig-frame 
;;   3. from 2, we know (pc sig-frame) equal (pc st) 
;;   4. we know bcv-simple-inst at pc. 
;;   5. we know next-state's pc is (pc sig-frame) + 1 
;;
;; We could add an extra assertion about the consistent-state.
;; so that we can show that (g 'pc (binding pc vector)) == pc 
;; 
;; but it is not necessary! 
;;
;; the decision is that we need to do |Subgoal 2| in any case!! 
;;

(local 
 (defthm bcv-simple-execute-step-inst-push-fact-3
  (implies (equal (op-code inst) 'PUSH)
           (equal (g 'max-stack (car (bcv-simple-execute-step inst pre)))
                  (g 'max-stack pre)))))

(local
(defthm |Subgoal 4|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'PUSH))
   (EQUAL
    (G 'MAX-STACK
       (CDR (ASSOC-EQUAL (+ 1 (G 'PC (CAR (G 'CALL-STACK ST))))
                         (collect-witness-bcv-method (current-method st)
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

                                                            




;; 1. We know consistent-state, we know sig-frame-compatible pc with registered 
;;    sig-frame
;;  
;; 2. we know bcv-simple-execute-step does not change max-stack for push. 
;; 
;; 3. we know (max-stack sig-frame) is equal to (max-stack st) ...
;;
;; 4. we know ....
;;

(local 
(defthm bcv-simple-execute-step-inst-push-fact-4
  (implies (equal (op-code inst) 'PUSH)
           (equal (g 'method-table (car (bcv-simple-execute-step inst pre)))
                  (g 'method-table pre)))))


(local 
(defthm |Subgoal 3|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'PUSH))
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
(defthm bcv-simple-execute-step-inst-push-fact-5
  (implies (equal (op-code inst) 'PUSH)
           (equal (g 'op-stack (car (bcv-simple-execute-step inst pre)))
                  (+ 1 (g 'op-stack pre))))))


(local 
(defthm |Subgoal 2|
   (implies (AND (CONSISTENT-STATE ST)
                 (EQUAL (op-code (NEXT-INST ST)) 'PUSH))
            (EQUAL
             (G 'OP-STACK
                (CDR (ASSOC-EQUAL (+ 1 (G 'PC (CAR (G 'CALL-STACK ST))))
                                  (collect-witness-bcv-method (current-method st)
                                                              (g 'method-table st)))))
             (+ 1
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

                                                            
   



(local 
(defthm bcv-simple-execute-step-inst-method-name-fact
  (implies (equal (op-code inst) 'PUSH)
           (equal (g 'method-name (car (bcv-simple-execute-step inst pre)))
                  (g 'method-name pre)))))





(local 
 (defthm |Subgoal 1|
   (implies (AND (CONSISTENT-STATE ST)
                 (EQUAL (op-code (NEXT-INST ST)) 'PUSH))
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
 (defthm current-method-normalize
   (equal (CDR (ASSOC-EQUAL (G 'METHOD-NAME
                               (CAR (G 'CALL-STACK ST)))
                            (G 'METHOD-TABLE ST)))
          (current-method st))
   :hints (("Goal" :in-theory (enable current-method)))))

;;(i-am-here) ;; Thu Oct 20 17:14:34 2005

;;(local (include-book "arithmetic/top-with-meta" :dir :system))


(local 
 (defthm consistent-state-preserved-by-PUSH-lemma
   (implies (and (consistent-state st)
                 (equal (next-inst st) inst)
                 (equal (op-code inst) 'PUSH)
                 (djvm-check-PUSH inst st))
            (consistent-state-step
             (djvm-execute-PUSH inst st)))
   :hints (("Goal" :in-theory (enable sig-frame-compatible pc-in-range)))))


(local (in-theory (disable djvm-execute-PUSH djvm-check-PUSH 
                           consistent-state-step)))

(local 
 (defthm consistent-state-step-implies-consistent-state-djvm-execute-PUSH
   (implies (consistent-state-step (djvm-execute-PUSH inst st))
            (consistent-state (djvm-execute-PUSH inst st)))
   :hints (("Goal" :use ((:instance
                          consistent-state-step-implies-implies-consistent-state
                          (s (djvm-execute-PUSH inst st))))))))



;--- EXPORT ----

(defthm consistent-state-preserved-by-DJVM-PUSH
  (implies (and (consistent-state st)
                (equal (next-inst st) inst)
                (equal (op-code inst) 'PUSH)
                (djvm-check-PUSH inst st))
           (consistent-state
            (djvm-execute-PUSH inst st))))

