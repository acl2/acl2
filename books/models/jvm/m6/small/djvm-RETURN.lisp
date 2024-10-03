(in-package "ACL2")
(include-book "djvm-model")
(include-book "generic")
(include-book "consistent-state")
(include-book "consistent-state-properties")


(local (include-book "consistent-state-step"))
(local (in-theory (disable consistent-state)))

;----------------------------------------------------------------------

(local 
 (defthm consistent-state-op-code-RETURN-implies-pc-in-range
   (implies (and (consistent-state st)
                 (equal (op-code (next-inst st)) 'RETURN))
            (pc-in-range st))
   :hints (("Goal" :in-theory (enable next-inst)))))




(local (in-theory (disable next-inst bcv-simple-check-step-pre
                           extract-sig-frame pc-in-range
                           op-code consistent-state
                           bcv-method collect-witness-bcv-method
                           sig-frame-compatible
                           current-method)))




(local 
 (defthm consistent-state-implies-consistent-caller-frame-f
   (implies (and (consp (cdr (g 'call-stack st)))
                 (consistent-state st))
            (consistent-caller-frame (cadr (g 'call-stack st))
                                     (car (g 'call-stack st))
                                     (g 'method-table st)))
   :hints (("Goal" :in-theory (e/d (consistent-state) 
                                   (consistent-caller-frame))))
   :rule-classes :forward-chaining))



(local (in-theory (disable consistent-caller-frame)))


(local 
 (defthm consistent-frame-implies-max-stack-equal-f
   (implies (consistent-frame frame method-table)
            (equal (g 'max-stack frame)
                   (g 'max-stack (cdr (assoc-equal (g 'method-name frame)
                                                   method-table)))))
   :hints (("Goal" :in-theory (enable consistent-frame)))
   :rule-classes :forward-chaining))





(local 
 (defthm consistent-state-implies-consistent-frame-f
   (implies (and (consp (cdr (g 'call-stack st)))
                 (consistent-state st))
            (consistent-frame (cadr (g 'call-stack st))
                              (g 'method-table st)))
   :hints (("Goal" :in-theory (e/d (consistent-state)
                                   (consistent-frame))))
   :rule-classes :forward-chaining))


(local 
(defthm consistent-state-implies-bcv-simple-method-f
  (implies (and (consp (cdr (g 'call-stack st)))
                (consistent-state st))
           (bcv-simple-method (s 'sig-vector
                                 (collect-witness-bcv-method 
                                  (cdr (assoc-equal (g 'method-name (cadr (g 'call-stack
                                                                  st)))
                                                    (g 'method-table st)))
                                  (g 'method-table st))
                                 (cdr (assoc-equal (g 'method-name (cadr (g 'call-stack
                                                                            st)))
                                                   (g 'method-table st))))
                       (g 'method-table st)))
  :hints (("Goal" :in-theory (e/d (consistent-caller-frame) (bcv-simple-method))
           :use consistent-state-implies-consistent-caller-frame-f))
  :rule-classes :forward-chaining))



(local 
 (defthm consistent-state-implies-bcv-simple-method
   (implies (and (consp (cdr (g 'call-stack st)))
                 (consistent-state st)
                 (equal (g 'method-table st) method-table))
           (bcv-simple-method (s 'sig-vector
                                 (collect-witness-bcv-method 
                                  (cdr (assoc-equal (g 'method-name (cadr (g 'call-stack
                                                                             st)))
                                                    method-table))
                                  method-table)
                                 (cdr (assoc-equal (g 'method-name (cadr (g 'call-stack
                                                                            st)))
                                                   method-table)))
                              method-table))))



(local 
 (defthm consistent-caller-frame-implies-pc-pc-equal-f
   (implies (consistent-caller-frame caller callee method-table)
            (equal (g 'pc caller)
                   (g 'pc (cdr (assoc-equal (g 'pc caller)
                                            (collect-witness-bcv-method 
                                             (cdr (assoc-equal 
                                                   (g 'method-name caller)
                                                   method-table))
                                             method-table))))))
   :hints (("Goal" :in-theory (enable 
                               sig-frame-compatible
                               consistent-caller-frame)))
   :rule-classes :forward-chaining))



(local 
 (defthm consistent-caller-frame-implies-max-stack-max-stack-equal-f
   (implies (consistent-caller-frame caller callee method-table)
            (equal (g 'max-stack caller)
                   (g 'max-stack (cdr (assoc-equal (g 'pc caller)
                                            (collect-witness-bcv-method 
                                             (cdr (assoc-equal 
                                                   (g 'method-name caller)
                                                   method-table))
                                             method-table))))))
   :hints (("Goal" :in-theory (enable 
                               sig-frame-compatible
                               consistent-caller-frame)))
   :rule-classes :forward-chaining))


(local 
 (defthm consistent-caller-frame-implies-method-table-method-table-equal-f
   (implies (consistent-caller-frame caller callee method-table)
            (equal method-table
                   (g 'method-table (cdr (assoc-equal (g 'pc caller)
                                            (collect-witness-bcv-method 
                                             (cdr (assoc-equal 
                                                   (g 'method-name caller)
                                                   method-table))
                                             method-table))))))
   :hints (("Goal" :in-theory (enable 
                               sig-frame-compatible
                               consistent-caller-frame)))
   :rule-classes :forward-chaining))

;;;
;;; in fact all this forward chainings rules can be derived from the fact 
;;; that 
;;;      consistent-caller-frame implies sig-frame-compatible
;;;
;;; However, we want sig-frame-compatible to be enabled in our main proof! 
;;;


;; (skip-proofs 
;;  (defthm consistent-caller-frame-implies-sig-frame-compatible-f
;;    (implies (consistent-caller-frame caller callee method-table)
;;             (sig-frame-compatible (sig-frame-push-value (g 'ret callee) 
;;                                                         caller)
;;                                   (cdr (assoc-equal (g 'pc caller)
;;                                                     (g 'sig-vector
;;                                                        (cdr (assoc-equal 
;;                                                              (g 'method-name
;;                                                                 caller)
;;                                                              method-table)))))))
;;    :rule-classes :forward-chaining))

;; moved in front. 

(local 
 (defthm consistent-caller-frame-sig-frame-push-value-f
   (implies (consistent-caller-frame caller callee method-table)
            (equal (+ 1 (len (g 'op-stack caller)))
                   (g 'op-stack   (cdr (assoc-equal (g 'pc caller)
                                            (collect-witness-bcv-method 
                                             (cdr (assoc-equal 
                                                   (g 'method-name caller)
                                                   method-table))
                                             method-table))))))
   :hints (("Goal" :in-theory (enable 
                               sig-frame-compatible
                               consistent-caller-frame)))
   :rule-classes :forward-chaining))



(local 
  (defthm consistent-caller-frame-implies-op-stack-ok-f
    (implies (consistent-caller-frame caller callee method-table)
             (<= (+ 1 (len (g 'op-stack caller)))
                 (g 'max-stack caller)))
    :hints (("Goal" :in-theory (enable  consistent-caller-frame)))
    :rule-classes :forward-chaining))
 
;; this is a bit difficult! We will first prove that 




(defthm consistent-call-stack1-consistent-call-stack1
  (implies (and (consistent-call-stack1 (cdr call-stack) top-frame method-table)
                (consp (cdr call-stack)))
           (consistent-call-stack1 (cddr call-stack) (cadr call-stack)
                                   method-table))
  :rule-classes :forward-chaining)
            

(defthm consistent-state-consp-call-stack
  (implies (and (consistent-state st)
                (consp (cdr (g 'call-stack st))))
           (consistent-call-stack1 (cddr (g 'call-stack st))
                                   (cadr (g 'call-stack st))
                                   (g 'method-table st)))
  :hints (("Goal" :in-theory (enable consistent-state))))
                                   
           

;;(i-am-here) ;; Thu Nov  3 22:27:31 2005
(local (in-theory (disable sig-frame-push-value)))

(local 
  (defthm consistent-caller-frame-implies-sig-frame-compatible-ok-f
    (implies (consistent-caller-frame caller callee method-table)
             (sig-frame-compatible 
              (sig-frame-push-value (g 'ret (cdr (assoc-equal 
                                                  (g 'method-name callee)
                                                  method-table)))
                                    (extract-sig-frame caller method-table))
              (cdr (assoc-equal (g 'pc caller)
                                (collect-witness-bcv-method 
                                 (cdr (assoc-equal 
                                       (g 'method-name caller)
                                       method-table))
                                 method-table)))))
    :hints (("Goal" :in-theory (e/d (consistent-caller-frame)
                                    (bcv-simple-method))
             :do-not-induct t))
    :rule-classes :forward-chaining))
   


(local 
  (defthm consistent-caller-frame-implies-method-name-ok-f
    (implies (consistent-caller-frame caller callee method-table)
             (equal (g 'method-name 
                       (cdr (assoc-equal (g 'pc caller)
                                (collect-witness-bcv-method 
                                 (cdr (assoc-equal 
                                       (g 'method-name caller)
                                       method-table))
                                 method-table))))
                    (g 'method-name caller)))
    :hints (("Goal" :in-theory (e/d () (consistent-caller-frame))))
    :rule-classes :forward-chaining))
   

;; (i-am-here) ;; Sun Nov 20 21:25:17 2005


(local 
  (defthm consistent-caller-frame-implies-pc-ok-f-1
    (implies (consistent-caller-frame caller callee method-table)
             (integerp (g 'pc caller)))
    :hints (("Goal" :in-theory (e/d (consistent-caller-frame) ())))
    :rule-classes :forward-chaining))


(local 
  (defthm consistent-caller-frame-implies-pc-ok-f-2
    (implies (consistent-caller-frame caller callee method-table)
             (<= 1 (g 'pc caller)))
    :hints (("Goal" :in-theory (e/d (consistent-caller-frame) ())))
    :rule-classes :forward-chaining))


(local 
  (defthm consistent-caller-frame-implies-pc-ok-f-3
    (implies (consistent-caller-frame caller callee method-table)
             (< (g 'pc caller)
                (len (g 'code (cdr (assoc-equal (g 'method-name caller)
                                                method-table))))))
    :hints (("Goal" :in-theory (e/d (consistent-caller-frame) ())))
    :rule-classes :forward-chaining))



(local 
  (defthm consistent-caller-frame-implies-bcv-method
    (implies (consistent-caller-frame caller callee method-table)
             (bcv-method (cdr (assoc-equal (g 'method-name caller)
                                           method-table))
                         method-table))
    :hints (("Goal" :in-theory (e/d (consistent-caller-frame) ())))
    :rule-classes :forward-chaining))



(local 
 (defthm consistent-state-preserved-by-RETURN-lemma
   (implies (and (consistent-state st)
                 (equal (next-inst st) inst)
                 (equal (op-code inst) 'RETURN)
                 (djvm-check-RETURN inst st))
            (consistent-state-step
             (djvm-execute-RETURN inst st)))
   :hints (("Goal" :in-theory (enable sig-frame-compatible pc-in-range)))))


; ----- Export ------

(local (in-theory (disable djvm-execute-RETURN consistent-state-step)))

(local 
 (defthm consistent-state-step-implies-consistent-state-djvm-execute-RETURN
   (implies (consistent-state-step (djvm-execute-RETURN inst st))
            (consistent-state (djvm-execute-RETURN inst st)))
   :hints (("Goal" :use ((:instance
                          consistent-state-step-implies-implies-consistent-state
                          (s (djvm-execute-RETURN inst st))))))))




(defthm consistent-state-preserved-by-DJVM-RETURN
  (implies (and (consistent-state st)
                (equal (next-inst st) inst)
                (equal (op-code inst) 'RETURN)
                (djvm-check-RETURN inst st))
           (consistent-state
            (djvm-execute-RETURN inst st))))



;; this may have something new!! 
;;
;;
;; how the check done by INVOKE can be "noticed". The result of check is
;; registered in the consistent-state, already!
;;

