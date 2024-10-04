(in-package "ACL2")
(include-book "consistent-state")
(include-book "bcv-simple-model")
(include-book "bcv-model")

(defthm consistent-call-stack1-top-frame-pc-modication-no-change
  (implies (consistent-call-stack1 call-stack top-frame method-table)
           (consistent-call-stack1 call-stack (s 'pc anypc top-frame)
                                   method-table)))


(defthm consistent-call-stack1-top-frame-opstack-modication-no-change
  (implies (consistent-call-stack1 call-stack top-frame method-table)
           (consistent-call-stack1 call-stack (s 'op-stack anyopstack top-frame)
                                   method-table)))


(defthm consistent-state-consistent-call-stack1
  (implies (CONSISTENT-STATE ST)
           (CONSISTENT-CALL-STACK1 (CDR (G 'CALL-STACK ST))
                                   (car (g 'call-stack st))
                                   (g 'method-table st)))
  :hints (("Goal" :in-theory (enable consistent-state))))



(defthm consistent-state-consistent-call-stack1-f
  (implies (CONSISTENT-STATE ST)
           (CONSISTENT-CALL-STACK1 (CDR (G 'CALL-STACK ST))
                                   (car (g 'call-stack st))
                                   (g 'method-table st)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)


;----------------------------------------------------------------------

(encapsulate () 
  (local (include-book "bcv-succeed-implies-bcv-simple-succeed"))
  (defthm bcv-succeed-implies-bcv-simple-succeed
  (implies (and (bcv-method method method-table)
                (equal method (binding (g 'method-name method)
                                       method-table))
                (bcv-verified-method-table method-table))
           (bcv-simple-method
            (s 'sig-vector
               (collect-witness-bcv-method
                method method-table)
               method)
            method-table))))

(defthm bcv-verified-method-table1-is-all-method-verified1-normalize
  (equal (BCV-VERIFIED-METHOD-TABLE1 method-table1 method-table)
         (all-method-verified1 method-table1 method-table)))


(defthm bcv-verified-method-table-is-all-method-verified-normalize
  (equal (BCV-VERIFIED-METHOD-TABLE method-table)
         (all-method-verified method-table)))


(defthm consistent-state-implies-current-method-verified
  (implies (and (consistent-state st)
                (equal (g 'method-table st) method-table))
           (bcv-simple-method (s 'sig-vector (collect-witness-bcv-method
                                              (current-method st) method-table)
                                 (current-method st))
                       method-table))
  :hints (("Goal" :in-theory (disable bcv-simple-method bcv-method 
                                      collect-witness-bcv-method))))

;----------------------------------------------------------------------

(local (include-book "bcv-simple-method-properties"))

(local (in-theory (disable bcv-simple-check-step-pre extract-sig-frame
                           current-method next-inst consistent-state)))



(local (include-book "generic"))

(local 
 (defthm consistent-state-consistent-callee-frame
   (implies (consistent-state st)
            (consistent-callee-frame 
               (car (g 'call-stack st))
               (g 'method-table st)))
   :hints (("Goal" :in-theory (e/d (consistent-state)
                                   (consistent-callee-frame))))))


(local 
 (defthm current-method-normalize
   (equal (CDR (ASSOC-EQUAL (G 'METHOD-NAME
                               (CAR (G 'CALL-STACK ST)))
                            (G 'METHOD-TABLE ST)))
          (current-method st))
   :hints (("Goal" :in-theory (enable current-method)))))


(defthm consistent-state-sig-frame-compatible
  (implies (consistent-state st)
           (sig-frame-compatible
            (extract-sig-frame 
             (car (g 'call-stack st))
             (g 'method-table st))
            (cdr (assoc-equal (g 'pc (car (g 'call-stack st)))
                              (collect-witness-bcv-method 
                               (current-method st) 
                               (g 'method-table st))))))
  :hints (("Goal" :in-theory (e/d () (sig-frame-compatible
                                      consistent-state-consistent-callee-frame))
           :use ((:instance consistent-state-consistent-callee-frame)))))
                                   


(local (in-theory (disable sig-frame-compatible collect-witness-bcv-method)))

;; (i-am-here) ;; Wed Nov  2 22:43:41 2005

(defthm consistent-state-bcv-simple-check-step-pre-if-pc-in-range
  (implies (and (consistent-state st)
                (pc-in-range st))
           (bcv-simple-check-step-pre 
            (next-inst st)
            (extract-sig-frame 
             (car (g 'call-stack st))
             (g 'method-table st))))
  :hints (("Goal" :in-theory (e/d (next-inst)
                                  (bcv-simple-check-step-pre
                                   bcv-simple-check-step-pre-if-sig-frame-compatible
                                   bcv-simple-execute-step))
           :use ((:instance
                  bcv-simple-method-implies-next-inst-verified
                  ;; from bcv-simple-method-properties.lisp
                  (pc (g 'pc (car (g 'call-stack st))))
                  (method (s 'sig-vector (collect-witness-bcv-method 
                                          (current-method st)
                                          (g 'method-table st))
                             (current-method st)))
                  (method-table (g 'method-table st)))
                 (:instance bcv-simple-check-step-pre-if-sig-frame-compatible
                            (sframe  (extract-sig-frame 
                                      (car (g 'call-stack st))
                                      (g 'method-table st)))
                            (gframe  (cdr (assoc-equal (g 'pc (car (g 'call-stack st)))
                                                       (collect-witness-bcv-method 
                                                          (current-method st)
                                                          (g 'method-table st)))))
                            (inst (next-inst st)))))))

;;; because from consistent-state we know bcv-simple-method
;;;         from consistent-state we know extract-sig-frame from st
;;;                                     is more specific than recorded
;;;                                     sig-frame
;;;         from (bcv-simple-method (current-method st)) we know 
;;;                 bcv-simple-check-step-pre inst on recorded (more general) sig-frame!! 
;;;         we proved that bcv-simple-check-step-pre succeed on more specific frame 


(defthm consistent-state-all-next-state-safe-if-pc-in-range
  (implies (and (consistent-state st)
                (pc-in-range st))
           (all-next-state-safe 
            (bcv-simple-execute-step (next-inst st)
                              (extract-sig-frame 
                               (car (g 'call-stack st))
                               (g 'method-table st)))
            (collect-witness-bcv-method (current-method st)
                                        (g 'method-table st))))
  :hints (("Goal" :in-theory (e/d (next-inst)
                                  (all-next-state-safe
                                   collect-witness-bcv-method
                                   bcv-simple-method-implies-next-inst-verified
                                   bcv-check-step-post-if-sig-frame-compatible
                                   bcv-simple-execute-step))
           :use ((:instance
                  bcv-simple-method-implies-next-inst-verified
                  (pc (g 'pc (car (g 'call-stack st))))
                  (method (s 'sig-vector 
                             (collect-witness-bcv-method (current-method st)
                                                         (g 'method-table st))
                             (current-method st)))
                  (method-table (g 'method-table st)))
                 (:instance bcv-check-step-post-if-sig-frame-compatible
                            (sframe  (extract-sig-frame 
                                      (car (g 'call-stack st))
                                      (g 'method-table st)))
                            (gframe  (cdr (assoc-equal (g 'pc (car (g 'call-stack st)))
                                                       (collect-witness-bcv-method (current-method st)
                                                                                   (g 'method-table st)))))
                            (inst (next-inst st))
                            (vector (collect-witness-bcv-method 
                                     (current-method st)
                                     (g 'method-table st))))))))
                                                                


(defthm consistent-state-all-next-state-safe-if-pc-in-range-weak
  (implies (and (consistent-state st)
                (pc-in-range st))
           (all-next-state-safe 
            (bcv-simple-execute-step (next-inst st)
                              (cdr (assoc-equal 
                                    (g 'pc (car (g 'call-stack st)))
                                    (collect-witness-bcv-method 
                                     (current-method st)
                                     (g 'method-table st)))))
            (collect-witness-bcv-method (current-method st)
                                        (g 'method-table st))))
  :hints (("Goal" :in-theory (e/d (next-inst)
                                  (all-next-state-safe
                                   bcv-simple-method-implies-next-inst-verified
                                   bcv-check-step-post-if-sig-frame-compatible
                                   bcv-simple-execute-step))
           :use ((:instance
                  bcv-simple-method-implies-next-inst-verified
                  (pc (g 'pc (car (g 'call-stack st))))
                  (method (s 'sig-vector 
                             (collect-witness-bcv-method (current-method st)
                                                         (g 'method-table st))
                             (current-method st)))
                  (method-table (g 'method-table st)))))))


;; notes: this kind of rule does not fire too easily!!
;; because we have rewrite rules that rewrite (g 'method-table st) into ....
;; 
;; Let's see how it works!! Sun Nov 20 18:07:53 2005



(defthm consistent-state-max-stack-equal
  (IMPLIES (CONSISTENT-STATE ST)
           (EQUAL (G 'MAX-STACK
                     (current-method st))
                  (G 'MAX-STACK (CAR (G 'CALL-STACK ST)))))
  :hints (("Goal" :in-theory (enable consistent-state current-method))))

;----------------------------------------------------------------------


(local 
 (defthm sig-frame-compatible-equal-pc
   (implies (sig-frame-compatible frame1 frame2)
            (equal (g 'pc frame2)
                   (g 'pc frame1)))
   :hints (("Goal" :in-theory (enable sig-frame-compatible)))))


(defthm consistent-state-implies-sig-frame-pc-is-pc
  (implies (consistent-state st)
           (equal (g 'pc 
                     (cdr (assoc-equal (g 'pc (car (g 'call-stack st)))
                                       (collect-witness-bcv-method
                                        (current-method st)
                                        (g 'method-table st)))))
                  (g 'pc (car (g 'call-stack st)))))
  :hints (("Goal" 
           :use ((:instance 
                  consistent-state-sig-frame-compatible)
                 (:instance sig-frame-compatible-equal-pc
                            (frame1  (extract-sig-frame (car (g 'call-stack st))
                                                        (g 'method-table st)))
                            (frame2 (cdr (assoc-equal (g 'pc (car (g 'call-stack st)))
                                                      (collect-witness-bcv-method 
                                                       (current-method st)
                                                       (g 'method-table st))))))))))


;----------------------------------------------------------------------


(defthm all-next-state-safe-implies-sig-frame-compatible
  (implies (and (all-next-state-safe l sig-vector)
                (member x l))
           (sig-frame-compatible x 
                                 (cdr (assoc-equal 
                                       (g 'pc x) sig-vector)))))


(defthm all-next-state-safe-implies-pc-equal
  (implies (and (all-next-state-safe l sig-vector)
                (member x l))
           (equal (g 'pc (cdr (assoc-equal (g 'pc x) sig-vector)))
                  (g 'pc x)))
  :hints (("Goal" :use ((:instance sig-frame-compatible-equal-pc
                                   (frame1 x)
                                   (frame2 (cdr (assoc-equal (g 'pc x) sig-vector))))))))


;----------------------------------------------------------------------

                   
(local 
 (defthm sig-frame-compatible-equal-max-stack
   (implies (sig-frame-compatible frame1 frame2)
            (equal (g 'max-stack frame2)
                   (g 'max-stack frame1)))
   :hints (("Goal" :in-theory (enable sig-frame-compatible)))))


(defthm consistent-state-implies-sig-frame-max-stack-is-max-stack
  (implies (consistent-state st)
           (equal (g 'max-stack
                     (cdr (assoc-equal (g 'pc (car (g 'call-stack st)))
                                       (collect-witness-bcv-method
                                        (current-method st)
                                        (g 'method-table st)))))
                  (g 'max-stack (car (g 'call-stack st)))))
   :hints (("Goal" 
            :use ((:instance 
                          consistent-state-sig-frame-compatible)
                  (:instance sig-frame-compatible-equal-max-stack
                             (frame1  (extract-sig-frame (car (g 'call-stack st))
                                                         (g 'method-table st)))
                             (frame2 (cdr (assoc-equal (g 'pc (car (g 'call-stack st)))
                                                       (collect-witness-bcv-method (current-method st)
                                                                                   (g 'method-table st))))))))))


(defthm all-next-state-safe-implies-max-stack-equal
  (implies (and (all-next-state-safe l sig-vector)
                (member x l))
           (equal (g 'max-stack (cdr (assoc-equal (g 'pc x) sig-vector)))
                  (g 'max-stack x)))
  :hints (("Goal" :use ((:instance sig-frame-compatible-equal-max-stack
                                   (frame1 x)
                                   (frame2 (cdr (assoc-equal (g 'pc x)
                                                             sig-vector))))))))

;----------------------------------------------------------------------

(local 
 (defthm sig-frame-compatible-equal-method-table
   (implies (sig-frame-compatible frame1 frame2)
            (equal (g 'method-table frame2)
                   (g 'method-table frame1)))
   :hints (("Goal" :in-theory (enable sig-frame-compatible)))))


(defthm all-next-state-safe-implies-method-table-equal
  (implies (and (all-next-state-safe l sig-vector)
                (member x l))
           (equal (g 'method-table (cdr (assoc-equal (g 'pc x) sig-vector)))
                  (g 'method-table x)))
   :hints (("Goal" :use ((:instance sig-frame-compatible-equal-method-table
                                    (frame1 x)
                                    (frame2 (cdr (assoc-equal (g 'pc x) sig-vector))))))))


;;(i-am-here) ;; Thu Oct 20 16:26:26 2005
(local 
 (defthm sig-frame-compatible-extract-sig-frame-general
   (implies (sig-frame-compatible 
             (extract-sig-frame any-frame method-table)
             frame)
            (equal (g 'method-table frame)
                   method-table))))


(defthm sig-frame-compatible-extract-sig-frame
  (implies (sig-frame-compatible 
            (extract-sig-frame any-frame method-table)
            (cdr (assoc-equal pc vector)))
           (equal (g 'method-table (cdr (assoc-equal pc vector)))
                  method-table)))



;;; this is a bad rewrite rule 




;----------------------------------------------------------------------

                   
(local 
 (defthm sig-frame-compatible-equal-op-stack
   (implies (sig-frame-compatible frame1 frame2)
            (equal (g 'op-stack frame2)
                   (g 'op-stack frame1)))
   :hints (("Goal" :in-theory (enable sig-frame-compatible)))))


(defthm all-next-state-safe-implies-opstack-equal
  (implies (and (all-next-state-safe l sig-vector)
                (member x l))
           (equal (g 'op-stack (cdr (assoc-equal (g 'pc x) sig-vector)))
                  (g 'op-stack x)))
  :hints (("Goal" :use ((:instance sig-frame-compatible-equal-op-stack
                                   (frame1 x)
                                   (frame2 (cdr (assoc-equal (g 'pc x) sig-vector))))))))




;;(i-am-here) ;; Thu Oct 20 16:26:26 2005
(local 
 (defthm sig-frame-compatible-extract-sig-frame-general-opstack
   (implies (sig-frame-compatible 
             (extract-sig-frame any-frame method-table)
             frame)
            (equal (g 'op-stack frame)
                   (len (g 'op-stack any-frame))))))


(defthm sig-frame-compatible-extract-sig-frame-opstack
  (implies (sig-frame-compatible 
            (extract-sig-frame any-frame method-table)
            (cdr (assoc-equal pc vector)))
           (equal (g 'op-stack (cdr (assoc-equal pc vector)))
                  (len (g 'op-stack any-frame)))))

;----------------------------------------------------------------------

(local 
 (defthm sig-frame-compatible-equal-method-name
   (implies (sig-frame-compatible frame1 frame2)
            (equal (g 'method-name frame2)
                   (g 'method-name frame1)))
   :hints (("Goal" :in-theory (enable sig-frame-compatible)))))

(defthm all-next-state-safe-implies-method-name-equal
  (implies (and (all-next-state-safe l sig-vector)
                (member x l))
           (equal (g 'method-name (cdr (assoc-equal (g 'pc x) sig-vector)))
                  (g 'method-name x)))
   :hints (("Goal" :use ((:instance sig-frame-compatible-equal-method-name
                                    (frame1 x)
                                    (frame2 (cdr (assoc-equal (g 'pc x) sig-vector))))))))

;----------------------------------------------------------------------

(local 
 (defthm sig-frame-compatible-extract-sig-frame-general-method-name
   (implies (sig-frame-compatible 
             (extract-sig-frame any-frame method-table)
             frame)
            (equal (g 'method-name frame)
                   (g 'method-name any-frame)))))





(defthm sig-frame-compatible-extract-sig-frame-method-name
  (implies (sig-frame-compatible 
            (extract-sig-frame any-frame method-table)
            (cdr (assoc-equal pc vector)))
           (equal (g 'method-name (cdr (assoc-equal pc vector)))
                  (g 'method-name any-frame))))

;----------------------------------------------------------------------

;;(i-am-here) ;; Thu Nov  3 23:55:53 2005

(local 
 (defthm sig-frame-compatible-extract-sig-frame-general-method-name-2
   (implies (sig-frame-compatible 
             (sig-frame-push-value any any-frame)
             frame)
            (equal (g 'method-name frame)
                   (g 'method-name any-frame)))
   :hints (("Goal" :in-theory (enable sig-frame-compatible)))))



(defthm sig-frame-compatible-extract-sig-frame-method-name-2
  (implies (sig-frame-compatible 
            (sig-frame-push-value any any-frame)
            (cdr (assoc-equal pc vector)))
           (equal (g 'method-name (cdr (assoc-equal pc vector)))
                  (g 'method-name any-frame)))
  :hints (("Goal" :in-theory (disable sig-frame-push-value))))

;----------------------------------------------------------------------




;----------------------------------------------------------------------


(defthm cdr-g-call-stack-popStack-n
  (equal (cdr (g 'call-stack (popstack-n st n)))
         (cdr (g 'call-stack st))))


(defthm consistent-call-stack1-top-frame-opstack-popStack-n-no-change
  (implies (consistent-call-stack1 call-stack (car (g 'call-stack st)) method-table)
           (consistent-call-stack1 call-stack (car (g 'call-stack 
                                                      (popstack-n st n)))
                                   method-table)))

;----------------------------------------------------------------------

;;(i-am-here);; Fri Oct 21 13:13:08 2005

(defthm consistent-state-len-opstack-in-limit
  (implies (consistent-state st)
           (<= (len (g 'op-stack (car (g 'call-stack st))))
               (g 'max-stack (car (g 'call-stack st)))))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :linear)

;----------------------------------------------------------------------

(defthm consistent-state-len-opstack-in-limit-specific
  (implies (consistent-state st)
           (<= (len (cdr (g 'op-stack (car (g 'call-stack st)))))
               (g 'max-stack (car (g 'call-stack st)))))
  :hints (("Goal" :use consistent-state-len-opstack-in-limit)))
;----------------------------------------------------------------------

;;(i-am-here) ;; Thu Nov  3 22:39:51 2005

(defthm consistent-state-implies-method-name-equal
  (IMPLIES (CONSISTENT-STATE ST)
           (EQUAL (G 'METHOD-NAME (CURRENT-METHOD ST))
                  (G 'METHOD-NAME
                     (CAR (G 'CALL-STACK ST)))))
  :hints (("Goal" :in-theory (enable consistent-state))))


;----------------------------------------------------------------------

(defthm consistent-state-implies-name-equal-2
  (IMPLIES (AND (CONSISTENT-STATE ST)
                (CONSP (CDR (G 'CALL-STACK ST))))
           (EQUAL (G 'METHOD-NAME
                     (CDR (ASSOC-EQUAL (G 'METHOD-NAME
                                          (CADR (G 'CALL-STACK ST)))
                                       (G 'METHOD-TABLE ST))))
                  (G 'METHOD-NAME
                     (CADR (G 'CALL-STACK ST)))))
  :hints (("Goal" :in-theory (enable consistent-state))))


;----------------------------------------------------------------------

;;; (i-am-here) ;; Sun Nov 20 20:04:39 2005

(defthm consistent-state-bcv-method-current-method
  (implies (consistent-state st)
           (bcv-method (current-method st) (g 'method-table st)))
  :hints (("Goal" :in-theory (e/d (consistent-state current-method)
                                  (bcv-method))))
  :rule-classes :forward-chaining)


;----------------------------------------------------------------------

;;(i-am-here) ;; Sun Nov 20 22:17:37 2005

(defthm wff-method-table-implies-g-method-name-normalize
  (implies (and (wff-method-table method-table)
                (assoc-equal name method-table))
           (equal (g 'method-name (cdr (assoc-equal name method-table)))
                  name)))


(defthm consistent-state-implies-wff-method-table
  (implies (consistent-state djvm-s)
           (wff-method-table (g 'method-table djvm-s)))
  :hints (("Goal" :in-theory (enable consistent-state))))


;----------------------------------------------------------------------

(defthm consistent-state-implies-pc-in-range-f
  (implies (consistent-state st)
           (pc-in-range st))
  :hints (("Goal" :in-theory (e/d (consistent-state) (pc-in-range))))
  :rule-classes :forward-chaining)


;----------------------------------------------------------------------

;;(i-am-here) ;; Mon Nov 21 02:05:40 2005

;; (local (include-book "bcv-simple-method-properties"))

(encapsulate () 
  (local 
   (encapsulate () 
      (local (include-book "bcv-simple-method-properties"))
      (defthm bcv-simple-method-implies-next-inst-verified
      (implies (and (bcv-simple-method method method-table)
                    (integerp pc)
                    (<= 0 pc)
                    (< pc (len (g 'code method))))
               (bcv-simple-inst pc 
                                (nth pc (g 'code method))
                                (g 'sig-vector method))))))
  
(defthm consistent-state-implies-bcv-simple-inst
  (implies (consistent-state st)
           (bcv-simple-inst (g 'pc (car (g 'call-stack st))) 
                            (next-inst st)
                            (collect-witness-bcv-method
                             (current-method st)
                             (g 'method-table st))))
  :hints (("Goal" :in-theory (e/d (consistent-state
                                   next-inst
                                   pc-in-range)
                                  (bcv-simple-inst
                                   bcv-simple-method
                                   bcv-method
                                   consistent-call-stack
                                   collect-witness-bcv-method))
           :use ((:instance bcv-simple-method-implies-next-inst-verified
                            (method (s 'sig-vector (collect-witness-bcv-method 
                                                    (current-method st)
                                                    (g 'method-table st))
                                       (current-method st)))
                            (pc (g 'pc (car (g 'call-stack st))))
                            (method-table (g 'method-table st))))))))

;----------------------------------------------------------------------

(defthm consistent-state-implies-integerp-pc
  (implies (consistent-state st)
           (integerp (g 'pc (car (g 'call-stack st)))))
  :hints (("Goal" :in-theory (enable consistent-state pc-in-range))))

(defthm consistent-state-implies-greater-than-zero
  (implies (consistent-state st)
           (<=  0 (g 'pc (car (g 'call-stack st)))))
  :hints (("Goal" :in-theory (enable consistent-state pc-in-range)))
  :rule-classes :linear)

(defthm consistent-state-implies-less-than-len
  (implies (consistent-state st)
           (<  (g 'pc (car (g 'call-stack st)))
               (len (g 'code (current-method st)))))
  :hints (("Goal" :in-theory (enable consistent-state pc-in-range)))
  :rule-classes :linear)

;----------------------------------------------------------------------



(defthm consistent-state-bcv-method-current-method-b
  (implies (consistent-state st)
           (bcv-method (current-method st) 
                       (g 'method-table st))))


;----------------------------------------------------------------------

(defthm current-method-normalize-x
  (equal (CDR (ASSOC-EQUAL (G 'METHOD-NAME
                              (CAR (G 'CALL-STACK DJVM-S)))
                           (G 'METHOD-TABLE DJVM-S)))
         (current-method djvm-s))
  :hints (("Goal" :in-theory (enable current-method))))

  


;----------------------------------------------------------------------
