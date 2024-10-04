(in-package "ACL2")
(include-book "djvm-model")
(include-book "generic")
(include-book "consistent-state")
(include-book "consistent-state-properties")



(local (include-book "consistent-state-step"))
(local (in-theory (disable consistent-state)))



(local (in-theory (disable next-inst bcv-simple-check-step-pre
                           extract-sig-frame pc-in-range
                           bcv-method
                           collect-witness-bcv-method
                           op-code consistent-state
                           sig-frame-compatible
                           current-method)))


(local 
 (defthm bcv-simple-check-step-pre-INVOKE-1
   (implies (and (equal (op-code inst) 'INVOKE)
                 (bcv-simple-check-step-pre inst
                                     (extract-sig-frame 
                                      (topx (g 'call-stack st))
                                      (g 'method-table st))))
            (<= 0 (g 'max-stack (cdr (assoc-equal (cadr inst) 
                                                  (g 'method-table st))))))
   :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))


(local 
 (defthm bcv-simple-check-step-pre-INVOKE-1-specific
   (implies (and (equal (op-code (next-inst st)) 'INVOKE)
                 (bcv-simple-check-step-pre (next-inst st)
                                     (extract-sig-frame 
                                      (topx (g 'call-stack st))
                                      (g 'method-table st))))
            (<= 0 (g 'max-stack (cdr (assoc-equal (cadr (next-inst st))
                                                  (g 'method-table st))))))
   :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))




(local 
 (defthm consistent-state-op-code-INVOKE-implies-pc-in-range
   (implies (and (consistent-state st)
                 (equal (op-code (next-inst st)) 'INVOKE))
            (pc-in-range st))
   :hints (("Goal" :in-theory (enable next-inst)))))

(defthm bcv-simple-method-implies-pc-equal-zero
  (implies (bcv-simple-method method method-table)
           (equal (g 'pc (cdr (assoc-equal 0 (g 'sig-vector method))))
                  0))
  :hints (("Goal" :in-theory (enable sig-frame-compatible))))


(defthm bcv-simple-method-implies-opstack-equal-zero
  (implies (bcv-simple-method method method-table)
           (equal (g 'op-stack (cdr (assoc-equal 0 (g 'sig-vector method))))
                  0))
  :hints (("Goal" :in-theory (enable sig-frame-compatible))))


(defthm bcv-simple-method-implies-max-stack-equal
  (implies (bcv-simple-method method method-table)
           (equal (g 'max-stack (cdr (assoc-equal 0 (g 'sig-vector method))))
                  (g 'max-stack method)))
  :hints (("Goal" :in-theory (enable bcv-simple-method sig-frame-compatible))))


(defthm bcv-simple-method-implies-pc-equal-zero
  (implies (bcv-simple-method method method-table)
           (equal (g 'pc (cdr (assoc-equal 0 (g 'sig-vector method))))
                  0))
  :hints (("Goal" :in-theory (enable sig-frame-compatible))))


(defthm bcv-simple-method-implies-method-table-equal-method-table
  (implies (bcv-simple-method method method-table)
           (equal (g 'method-table (cdr (assoc-equal 0 (g 'sig-vector method))))
                  method-table))
  :hints (("Goal" :in-theory (enable sig-frame-compatible bcv-simple-method))))



(defthm bcv-simple-method-implies-method-table-equal-method-table
  (implies (bcv-simple-method method method-table)
           (equal (g 'method-table (cdr (assoc-equal 0 (g 'sig-vector method))))
                  method-table))
  :hints (("Goal" :in-theory (enable sig-frame-compatible bcv-simple-method))))


(defthm bcv-simple-method-implies-method-name-equal-method-name
  (implies (bcv-simple-method method method-table)
           (equal (g 'method-name (cdr (assoc-equal 0 (g 'sig-vector method))))
                  (g 'method-name method)))
  :hints (("Goal" :in-theory (enable sig-frame-compatible bcv-simple-method))))



;; (i-am-here) ;; Fri Nov 11 14:27:07 2005

;; (local 
;;  (defthm bcv-simple-check-step-pre-INVOKE-method-table
;;    (implies (and (equal (op-code inst) 'INVOKE)
;;                  (bcv-simple-check-step-pre inst
;;                                      (extract-sig-frame 
;;                                       (topx (g 'call-stack st))
;;                                       (g 'method-table st))))
;;             (equal (g 'method-table 
;;                       (cdr (assoc-equal 0 (g 'sig-vector 
;;                                              (cdr (assoc-equal (cadr inst)
;;                                                                (g 'method-table st)))))))
;;                    (g 'method-table st)))
;;   :hints (("Goal" :in-theory (enable bcv-simple-method sig-frame-compatible
;;                                      bcv-simple-check-step-pre))))))


;;(i-am-here) ;; Wed Nov  2 22:49:27 2005
(defthm all-method-verified1-implies-bound-bcv-method
  (implies (and (all-method-verified1 method-table1 method-table)
                (assoc-equal name method-table1))
           (bcv-method (cdr (assoc-equal name method-table1)) method-table)))


;; (defthm wff-method-table-implies-g-method-name-normalize
;;   (implies (and (wff-method-table method-table)
;;                 (assoc-equal name method-table))
;;            (equal (g 'method-name (cdr (assoc-equal name method-table)))
;;                   name)))



;; (local 
;;  (defthm all-verified1-implies-bcv-simple-method
;;    (implies (and (all-method-verified1 method-table1 method-table)
;;                  (wff-method-table method-table1)
;;                  (assoc-equal name method-table1))
;;             (bcv-simple-method (s 'sig-vector
;;                                   (collect-witness-bcv-method 
;;                                    (cdr (assoc-equal name method-table1))
;;                                    method-table)
;;                                   (cdr (assoc-equal name method-table1)))
;;                                method-table))
;;    :hints (("Goal" :in-theory (disable bcv-simple-method)))))
                  


(defthm all-verified-implies-bcv-simple-method
  (implies (and (all-method-verified method-table)
                (wff-method-table method-table)
                (assoc-equal name method-table))
           (bcv-simple-method (s 'sig-vector
                                 (collect-witness-bcv-method 
                                  (cdr (assoc-equal name method-table))
                                  method-table)
                                 (cdr (assoc-equal name method-table)))
                       method-table))
  :hints (("Goal" :in-theory (disable bcv-simple-method all-method-verified1))))

(local (in-theory (disable bcv-simple-method)))


;; Subgoal 2.10
;; (IMPLIES
;;  (AND (CONSISTENT-STATE ST)
;;       (EQUAL (OP-CODE (NEXT-INST ST)) 'INVOKE)
;;       (CDR (ASSOC-EQUAL (CADR (NEXT-INST ST))
;;                         (G 'METHOD-TABLE ST))))
;;  (EQUAL
;;       (G 'METHOD-TABLE ST)
;;       (G 'METHOD-TABLE
;;          (CDR (ASSOC-EQUAL 0
;;                            (G 'SIG-VECTOR
;;                               (CDR (ASSOC-EQUAL (CADR (NEXT-INST ST))
;;                                                 (G 'METHOD-TABLE ST))))))))).
;;; problematic!! 
;;; 

;; (defun bcv-check-INVOKE (inst sig-frame)
;;   (let* ((method-name (arg inst))
;;          (method-table (g 'method-table sig-frame))
;;          (method      (binding method-name method-table))
;;          (nargs       (g 'nargs method)))
;;     (and (bound? method-name method-table)
;;          (<= 0 (g 'max-stack (binding method-name method-table)))
;;          (equal (g 'method-table 
;;                    (cdr (assoc-equal 0 (g 'sig-vector (binding method-name
;;                                                                method-table)))))
;;                 method-table)
;;          (<= nargs (g 'op-stack sig-frame))
;;          (<= (+ 1 (- (g 'op-stack sig-frame) nargs))
;;              (max-stack sig-frame)))))


;; (local 
;;  (defthm bcv-simple-check-step-pre-INVOKE-3
;;    (implies (and (equal (op-code inst) 'INVOKE)
;;                  (bcv-simple-check-step-pre inst
;;                                      (extract-sig-frame 
;;                                       (topx (g 'call-stack st))
;;                                       (g 'method-table st))))
;;             (equal (g 'op-stack 
;;                       (cdr (assoc-equal 0 (g 'sig-vector 
;;                                              (cdr (assoc-equal (cadr inst) 
;;                                                                (g 'method-table
;;                                                                   st)))))))
;;                    0))
;;    :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))


;; (skip-proofs 
;;  (local 
;;   (defthm bcv-simple-check-step-pre-INVOKE-3-specific
;;    (implies (and (equal (op-code (next-inst st)) 'INVOKE)
;;                  (bcv-simple-check-step-pre (next-inst st)
;;                                      (extract-sig-frame 
;;                                       (topx (g 'call-stack st))
;;                                       (g 'method-table st))))
;;             (equal (g 'op-stack
;;                       (cdr (assoc-equal 0 (g 'sig-vector 
;;                                              (cdr (assoc-equal (cadr (next-inst st))
;;                                                                (g 'method-table
;;                                                                   st)))))))
;;                    0))
;;    :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre))))))


;; (defthm g-max-stack-popStack-n
;;   (equal (g 'max-stack (car (g 'call-stack (popStack-n st n))))
;;          (g 'max-stack (car (g 'call-stack st)))))



(defthm pop-stack-no-increase
  (<= (LEN
        (G 'OP-STACK
           (CAR (G 'CALL-STACK
                   (POPSTACK-N ST n)))))
      (len (g 'op-stack 
              (car (g 'call-stack st)))))
  :rule-classes :linear)


(defthm consistent-state-len-opstack-less-max-stack
   (implies (consistent-state st)
            (<= (len (g 'op-stack (car (g 'call-stack st))))
                (g 'max-stack (car (g 'call-stack st)))))
   :hints (("Goal" :in-theory (enable consistent-state)))
   :rule-classes :linear)


(defthm invoke-produce-consp
   (implies (equal (op-code inst) 'INVOKE)
            (CONSP (bcv-simple-execute-step inst any-frame))))

(defthm invoke-produce-consp-2
   (implies (equal (op-code inst) 'INVOKE)
            (bcv-simple-execute-step inst any-frame)))

(local 
(defthm bcv-simple-execute-step-inst-invoke-fact-5
  (implies (equal (op-code inst) 'INVOKE)
           (equal (g 'pc (car (bcv-simple-execute-step inst pre)))
                  (+ 1 (g 'pc pre))))
  :hints (("Goal" :in-theory (enable bcv-simple-execute-step)))))



(local 
(defthm bcv-simple-execute-step-inst-invoke-fact-6
  (implies (equal (op-code inst) 'INVOKE)
           (equal (g 'max-stack (car (bcv-simple-execute-step inst pre)))
                  (g 'max-stack pre)))))

(local
(defthm |Subgoal 4|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'INVOKE))
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
                                                            (collect-witness-bcv-method 
                                                             (current-method st)
                                                             (g 'method-table st)))))))
                            (l (bcv-simple-execute-step 
                                (next-inst st) 
                                (cdr (assoc-equal
                                      (g 'pc 
                                         (car 
                                          (g 'call-stack
                                             st)))
                                      (collect-witness-bcv-method 
                                       (current-method st)
                                       (g 'method-table st))))))

                            (sig-vector (collect-witness-bcv-method 
                                         (current-method st)
                                         (g 'method-table st)))))))))
                                                            



(local 
(defthm bcv-simple-execute-step-inst-INVOKE-fact-4
  (implies (equal (op-code inst) 'INVOKE)
           (equal (g 'method-table (car (bcv-simple-execute-step inst pre)))
                  (g 'method-table pre)))))


(local 
(defthm |Subgoal 3|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'INVOKE))
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
                                                            (collect-witness-bcv-method 
                                                             (current-method
                                                              st)
                                                             (g 'method-table st)))))))
                            (l (bcv-simple-execute-step 
                                (next-inst st) 
                                (cdr (assoc-equal
                                      (g 'pc 
                                         (car 
                                          (g 'call-stack
                                             st)))
                                      (collect-witness-bcv-method 
                                       (current-method st)
                                       (g 'method-table st))))))
                            (sig-vector 
                                      (collect-witness-bcv-method 
                                       (current-method st)
                                       (g 'method-table st)))))))))


(local 
(defthm bcv-simple-execute-step-inst-push-fact-5
  (implies (equal (op-code inst) 'INVOKE)
           (equal (g 'op-stack (car (bcv-simple-execute-step inst pre)))
                  (+ 1 (g 'op-stack
                          (SIG-FRAME-POP-N (G 'NARGS
                                              (CDR (ASSOC-EQUAL (cadr inst) (G 'METHOD-TABLE PRE))))
                                           PRE)))))))

(defthm len-popStack-n-is-sig-frame-pop-n-general
  (implies (sig-frame-compatible (extract-sig-frame (car (g 'call-stack st)) method-table)
                                 frame)
           (equal (g 'op-stack (sig-frame-pop-n n frame))
                  (len (g 'op-stack (car (g 'call-stack (popstack-n st n)))))))
  :hints (("Goal" :in-theory (enable sig-frame-pop-n 
                                     sig-frame-compatible
                                     extract-sig-frame))))


(defthm len-popStack-n-is-sig-frame-pop-n-specific
  (implies (sig-frame-compatible (extract-sig-frame (car (g 'call-stack st)) method-table)
                                 (cdr (assoc-equal pc vector)))
           (equal (g 'op-stack (sig-frame-pop-n n (cdr (assoc-equal pc vector))))
                  (len (g 'op-stack (car (g 'call-stack (popstack-n st n))))))))



(local 
 (defthm |Subgoal 2|
   (implies (AND (CONSISTENT-STATE ST)
                 (EQUAL (op-code (NEXT-INST ST)) 'INVOKE))
            (EQUAL
             (G 'OP-STACK
                (CDR (ASSOC-EQUAL (+ 1 (G 'PC (CAR (G 'CALL-STACK ST))))
                                  (collect-witness-bcv-method 
                                   (current-method st)
                                   (g 'method-table st)))))
             (+ 1 (LEN (G 'OP-STACK (CAR (G 'CALL-STACK 
                                            (popstack-n st 
                                                        (g 'nargs
                                                           (CDR (ASSOC-EQUAL (CADR (NEXT-INST ST))
                                                                             (G 'METHOD-TABLE ST))))))))))))
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
                                                            (collect-witness-bcv-method 
                                                             (current-method st)
                                                             (g 'method-table st)))))))
                            (l (bcv-simple-execute-step
                                (next-inst st) 
                                (cdr (assoc-equal
                                      (g 'pc 
                                         (car 
                                          (g 'call-stack
                                             st)))
                                      (collect-witness-bcv-method 
                                       (current-method st)
                                       (g 'method-table st))))))
                            (sig-vector 
                                      (collect-witness-bcv-method 
                                       (current-method st)
                                       (g 'method-table st)))))))))

   

(local 
 (defthm |Subgoal 5|
  (IMPLIES
   (AND (CONSISTENT-STATE ST)
        (EQUAL (op-code (NEXT-INST ST)) 'INVOKE))
   (EQUAL
    (G 'PC
       (CDR (ASSOC-EQUAL (+ 1 (g 'pc  (car (g 'call-stack st))))
                         (collect-witness-bcv-method 
                          (current-method st)
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
                                                            (collect-witness-bcv-method 
                                                             (current-method st)
                                                             (g 'method-table st)))))))
                            (l (bcv-simple-execute-step 
                                (next-inst st) 
                                (cdr (assoc-equal
                                      (g 'pc 
                                         (car 
                                          (g 'call-stack st)))
                                      (collect-witness-bcv-method 
                                       (current-method st)
                                       (g 'method-table st))))))
                            (sig-vector 
                             (collect-witness-bcv-method 
                              (current-method st)
                              (g 'method-table st)))))))))

                                                            



(local 
 (defthm current-method-normalize
   (equal (CDR (ASSOC-EQUAL (G 'METHOD-NAME
                               (CAR (G 'CALL-STACK ST)))
                            (G 'METHOD-TABLE ST)))
          (current-method st))
   :hints (("Goal" :in-theory (enable current-method)))))

;;(i-am-here) ;; Sun Oct 23 15:28:45 2005


;; (local 
;;  (defthm bcv-simple-check-step-pre-INVOKE-size-opstack
;;    (implies (and (equal (op-code inst) 'INVOKE)
;;                  (bcv-simple-check-step-pre inst
;;                                      (extract-sig-frame 
;;                                       (topx (g 'call-stack st))
;;                                       (g 'method-table st))))
;;             (<= (+ 1 (- (len (g 'op-stack (car (g 'call-stack st)))
;;                              (g 'nargs 


;;                 (g 'max-stack (cdr (assoc-equal (cadr inst) 
;;                                                   (g 'method-table st))))))
;;    :hints (("Goal" :in-theory (e/d (current-method
;;                                     bcv-simple-check-step-pre)
;;                                    (current-method-normalize))))))


;; (local 
;;  (defthm bcv-simple-check-step-pre-INVOKE-size-opstack-specific
;;    (implies (and (equal (op-code (next-inst st)) 'INVOKE)
;;                  (bcv-simple-check-step-pre (next-inst st)
;;                                      (extract-sig-frame 
;;                                       (topx (g 'call-stack st))
;;                                       (g 'method-table st))))
;;             (<= 0 (g 'max-stack (cdr (assoc-equal (cadr (next-inst st))
;;                                                   (g 'method-table st))))))
;;    :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))




(local 
  (defthm bcv-simple-check-step-pre-INVOKE-size-opstack-1
    (implies (and (equal (op-code inst) 'INVOKE)
                  (bcv-simple-check-step-pre inst
                                      (extract-sig-frame 
                                       (topx (g 'call-stack st))
                                       (g 'method-table st))))
             (<= (g 'nargs (cdr (assoc-equal (cadr inst) 
                                             (g 'method-table st))))
                 (len (g 'op-stack (car (g 'call-stack st))))))
    :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))
                              


(local 
  (defthm bcv-simple-check-step-pre-INVOKE-size-opstack-2
    (implies (and (equal (op-code inst) 'INVOKE)
                  (bcv-simple-check-step-pre inst
                                      (extract-sig-frame 
                                       (topx (g 'call-stack st))
                                       (g 'method-table st))))
             (<= 0 (g 'nargs (cdr (assoc-equal (cadr inst) 
                                             (g 'method-table st))))))
    :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))



(local 
  (defthm bcv-simple-check-step-pre-INVOKE-size-opstack-3
    (implies (and (equal (op-code inst) 'INVOKE)
                  (bcv-simple-check-step-pre inst
                                      (extract-sig-frame 
                                       (topx (g 'call-stack st))
                                       (g 'method-table st))))
             (integerp (g 'nargs (cdr (assoc-equal (cadr inst) 
                                                   (g 'method-table st))))))
    :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))



(local 
  (defthm bcv-simple-check-step-pre-INVOKE-size-opstack-4
    (implies (and (equal (op-code inst) 'INVOKE)
                  (bcv-simple-check-step-pre inst
                                      (extract-sig-frame 
                                       (topx (g 'call-stack st))
                                       (g 'method-table st))))
             (<= (+ 1 (- (len (g 'op-stack (car (g 'call-stack st))))
                         (g 'nargs (cdr (assoc-equal (cadr inst) 
                                                     (g 'method-table st))))))
                 (g 'max-stack (car (g 'call-stack st)))))
    :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))
                              


(local 
 (defthm len-opstack-pop-stack-n-is-lemma
  (implies (and (integerp n)
                (<= 0 n)
                (<= n (len (g 'op-stack (car (g 'call-stack st))))))
           (equal (len (g 'op-stack 
                          (car (g 'call-stack 
                                  (popstack-n st n)))))
                  (- (len (g 'op-stack 
                             (car (g 'call-stack st))))
                     n)))))


(local 
 (defthm len-len-minus
   (implies (and (<= x max-stack)
                 (integerp y)
                 (<= 0 y))
            (<= (+ x (- y)) max-stack))))


;;(i-am-here) ;; Wed Nov  2 23:26:55 2005

;; Thu Nov  3 17:09:33 2005

(defthm bcv-simple-method-implies-pc-equal-zero-specific
  (implies (bcv-simple-method (binding name method-table) method-table)
           (equal (g 'pc (cdr (assoc-equal 0 (g 'sig-vector (cdr (assoc-equal
                                                                  name method-table))))))
                  0))
  :hints (("Goal" :in-theory (enable sig-frame-compatible))))


(defthm bcv-simple-method-implies-opstack-equal-zero-specific
  (implies (bcv-simple-method (binding name method-table) method-table)
           (equal (g 'op-stack (cdr (assoc-equal 0 (g 'sig-vector 
                                                      (cdr (assoc-equal name method-table))))))
                  0))
  :hints (("Goal" :in-theory (enable sig-frame-compatible))))



(defthm bcv-simple-method-implies-max-stack-equal-specific
  (implies (bcv-simple-method (binding name method-table) method-table)
           (equal (g 'max-stack (cdr (assoc-equal 0 (g 'sig-vector 
                                                       (cdr (assoc-equal name method-table))))))
                  (g 'max-stack (cdr (assoc-equal name method-table)))))
  :hints (("Goal" :in-theory (enable bcv-simple-method sig-frame-compatible))))


(local (in-theory (disable all-method-verified)))


(defthm bcv-simple-method-implies-method-name-equal
  (implies (bcv-simple-method method method-table)
           (equal (g 'method-name (cdr (assoc-equal 0 (g 'sig-vector method))))
                  (g 'method-name method)))
  :hints (("Goal" :in-theory (enable bcv-simple-method sig-frame-compatible))))

(defthm bcv-simple-method-implies-method-name-equal-specific
  (implies (bcv-simple-method (binding name method-table) method-table)
           (equal (g 'method-name (cdr (assoc-equal 0 (g 'sig-vector 
                                                         (cdr (assoc-equal name
                                                                           method-table))))))
                  (g 'method-name (cdr (assoc-equal name method-table))))))




;; (local 
;;  (defthm bcv-simple-check-step-pre-INVOKE-5
;;    (implies (and (equal (op-code inst) 'INVOKE)
;;                  (bcv-simple-check-step-pre inst
;;                                      (extract-sig-frame 
;;                                       (topx (g 'call-stack st))
;;                                       (g 'method-table st))))
;;             (equal (g 'method-name (cdr (assoc-equal (cadr inst)
;;                                                      (g 'method-table st))))
;;                    (cadr inst)))
;;    :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))
;;
 


(local 
 (defthm bcv-simple-check-step-pre-INVOKE-1-specific
   (implies (and (equal (op-code (next-inst st)) 'INVOKE)
                 (bcv-simple-check-step-pre (next-inst st)
                                     (extract-sig-frame 
                                      (topx (g 'call-stack st))
                                      (g 'method-table st))))
            (<= 0 (g 'max-stack (cdr (assoc-equal (cadr (next-inst st))
                                                  (g 'method-table st))))))
   :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre)))))


;;(i-am-here) ;; Thu Nov  3 22:00:41 2005


(local 
(defthm bcv-simple-execute-step-inst-method-name-fact
  (implies (equal (op-code inst) 'INVOKE)
           (equal (g 'method-name (car (bcv-simple-execute-step inst pre)))
                  (g 'method-name pre)))))





(local 
 (defthm |Subgoal 1|
   (implies (AND (CONSISTENT-STATE ST)
                 (EQUAL (op-code (NEXT-INST ST)) 'INVOKE))
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
                                                            (collect-witness-bcv-method 
                                                             (current-method st)
                                                             (g 'method-table st)))))))
                            (l (bcv-simple-execute-step 
                                (next-inst st) 
                                (cdr (assoc-equal
                                      (g 'pc 
                                         (car 
                                          (g 'call-stack
                                             st)))
                                      (collect-witness-bcv-method 
                                       (current-method st)
                                       (g 'method-table st))))))
                            (sig-vector 
                             (collect-witness-bcv-method 
                              (current-method st)
                              (g 'method-table st)))))))))

   
;;(i-am-here);; 

;; (defthm all-verified-implies-bcv-simple-method
;;   (implies (and (all-method-verified method-table)
;;                 (cdr (assoc-equal name method-table)))
;;            (bcv-simple-method (cdr (assoc-equal name method-table))
;;                        method-table))
;;   :hints (("Goal" :in-theory (disable bcv-simple-method all-method-verified1))))


;;(i-am-here) ;; Thu Nov  3 21:40:34 2005


;; (local 
;;  (defthm consistent-state-preserved-by-INVOKE-lemma-weak
;;    (implies (and (consistent-state st)
;;                  (equal (next-inst st) inst)
;;                  (equal (op-code inst) 'INVOKE)
;;                  (bcv-simple-check-INVOKE inst
;;                                           (extract-sig-frame 
;;                                            (topx (g 'call-stack st))
;;                                            (g 'method-table st))))
;;                  ;;(djvm-check-INVOKE (next-inst st) st))
;;             (consistent-state-step
;;              (djvm-execute-INVOKE inst st)))
;;    :hints (("Goal" :in-theory (enable createinitframe sig-frame-compatible)))))

;;(i-am-here) ;; Sun Nov 20 19:35:13 2005

(defthm parsecode-consp-implies-consp-code
  (implies (consp (parsecode1 any code))
           (consp code))
  :rule-classes :forward-chaining)

(defthm implies-code-0-not-consp
  (implies (equal (LEN code) 0)
           (not (CONSP (PARSECODE1 0 code)))))


(defthm bcv-method-implies-not-code-len-zero
  (implies (bcv-method method method-table)
           (< 0 (len (g 'code method))))
  :hints (("Goal" :in-theory (enable bcv-method)))
  :rule-classes :linear)


(defthm bound-implies-bcv-method
  (implies (and (consistent-state st)
                (bound? name (g 'method-table st)))
           (bcv-method (cdr (assoc-equal name (g 'method-table st)))
                       (g 'method-table st)))
  :hints (("Goal" :in-theory (enable consistent-state all-method-verified))))


(defthm bound-implies-bcv-method-not-equal-len-zero
  (implies (and (consistent-state st)
                (bound? name (g 'method-table st)))
           (not (equal (len (g 'code 
                               (cdr (assoc-equal name 
                                                 (g 'method-table st)))))
                       0)))
  :hints (("Goal" :cases ((bcv-method (cdr (assoc-equal name (g 'method-table
                                                                st)))
                                      (g 'method-table st))))))


;; i-am-here 

;; (skip-proofs 
;;  (defthm g-method-table-is-method-table
;;    (implies (bcv-method method method-table)
;;             (equal (g 'method-table 
;;                       (cdr (assoc-equal 0 (collect-witness-bcv-method method
;;                                                                       method-table))))
;;                    method-table))))


;; (skip-proofs 
;;  (defthm g-method-name-is-method-name
;;    (implies (bcv-method method method-table)
;;             (equal (g 'method-name
;;                       (cdr (assoc-equal 0 (collect-witness-bcv-method method
;;                                                                       method-table))))
;;                    (g 'method-name method)))))




(defthm bcv-simple-method-implies-pc-equal-zero-v2
  (implies (bcv-simple-method (s 'sig-vector 
                                 (collect-witness-bcv-method method
                                                             method-table)
                                 method)
                              method-table)
           (equal (g 'pc (cdr (assoc-equal 0 (collect-witness-bcv-method method method-table))))
                  0))
  :hints (("Goal" 
           :use ((:instance bcv-simple-method-implies-pc-equal-zero
                            (method (s 'sig-vector 
                                       (collect-witness-bcv-method method
                                                                   method-table)
                                       method)))))))





(defthm bcv-simple-method-implies-opstack-equal-zero-v2
  (implies (bcv-simple-method (s 'sig-vector 
                                 (collect-witness-bcv-method method
                                                             method-table)
                                 method)
                              method-table)
           (equal (g 'op-stack (cdr (assoc-equal 0 (collect-witness-bcv-method method
                                                                               method-table))))
                  0))
  :hints (("Goal" 
           :use ((:instance bcv-simple-method-implies-opstack-equal-zero
                            (method (s 'sig-vector 
                                       (collect-witness-bcv-method method
                                                                   method-table)
                                       method)))))))




(defthm bcv-simple-method-implies-max-stack-equal-v2
  (implies (bcv-simple-method (s 'sig-vector 
                                 (collect-witness-bcv-method method
                                                             method-table)
                                 method)
                              method-table)
           (equal (g 'max-stack (cdr (assoc-equal 0 (collect-witness-bcv-method method
                                                                                method-table))))
                  (g 'max-stack method)))
  :hints (("Goal" 
           :use ((:instance bcv-simple-method-implies-max-stack-equal
                            (method (s 'sig-vector 
                                       (collect-witness-bcv-method method
                                                                   method-table)
                                       method)))))))




(defthm bcv-simple-method-implies-method-table-equal-method-table-v2
  (implies (bcv-simple-method (s 'sig-vector 
                                 (collect-witness-bcv-method method
                                                             method-table)
                                 method)
                              method-table)
           (equal (g 'method-table (cdr (assoc-equal 0 (collect-witness-bcv-method method
                                                                                   method-table))))
                  method-table))
  :hints (("Goal" 
           :use ((:instance bcv-simple-method-implies-method-table-equal-method-table
                            (method (s 'sig-vector 
                                       (collect-witness-bcv-method method
                                                                   method-table)
                                       method)))))))



(defthm bcv-simple-method-implies-method-name-equal-method-name-v2
  (implies (bcv-simple-method (s 'sig-vector 
                                 (collect-witness-bcv-method method
                                                             method-table)
                                 method)
                              method-table)
           (equal (g 'method-name (cdr (assoc-equal 0 (collect-witness-bcv-method method
                                                                                   method-table))))
                  (g 'method-name method)))
  :hints (("Goal" 
           :use ((:instance bcv-simple-method-implies-method-name-equal-method-name
                            (method (s 'sig-vector 
                                       (collect-witness-bcv-method method
                                                                   method-table)
                                       method)))))))


;;(i-am-here) ;; Sun Nov 20 21:16:13 2005

;; Sun Nov 20 22:51:34 2005
;;

(defthm consistent-state-implies-pc-in-range
  (implies (consistent-state st)
           (pc-in-range st))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)

(defthm consistent-state-implies-pc-greater-than-zero
  (implies (consistent-state st)
           (<= 0 (g 'pc (car (g 'call-stack st)))))
  :hints (("Goal" :in-theory (enable pc-in-range consistent-state)))
  :rule-classes :linear)


(local 
 (defthm consistent-state-preserved-by-INVOKE-lemma
   (implies (and (consistent-state st)
                 (equal (next-inst st) inst)
                 (equal (op-code inst) 'INVOKE)
                 (djvm-check-INVOKE (next-inst st) st))
            (consistent-state-step
             (djvm-execute-INVOKE inst st)))
   :hints (("Goal" :in-theory (e/d (pc-in-range 
                                    createinitframe sig-frame-compatible)
                                   ())))))



(local (in-theory (disable djvm-execute-INVOKE djvm-check-INVOKE consistent-state-step)))

(local 
 (defthm consistent-state-step-implies-consistent-state-djvm-execute-INVOKE
   (implies (consistent-state-step (djvm-execute-INVOKE inst st))
            (consistent-state (djvm-execute-INVOKE inst st)))
   :hints (("Goal" :use ((:instance
                          consistent-state-step-implies-implies-consistent-state
                          (s (djvm-execute-INVOKE inst st))))))))



;--- EXPORT ----

(defthm consistent-state-preserved-by-DJVM-INVOKE
  (implies (and (consistent-state st)
                (equal (next-inst st) inst)
                (equal (op-code inst) 'INVOKE)
                (djvm-check-INVOKE (next-inst st) st))
           (consistent-state
            (djvm-execute-INVOKE inst st))))

