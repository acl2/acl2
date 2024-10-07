(in-package "ACL2")
(include-book "jvm-model")
(include-book "djvm-model")
(include-book "bcv-simple-model")
(include-book "bcv-model")
(include-book "generic")
(include-book "state-equiv-def")

;; in this example, the only difference between djvm-s and a jvm-s is that
;; jvm-s does not contain the stack map annotations not jvm-s checks for such
;; annotations. 
;;
;; m-step does not check whether preconditions are met!! 
;;



;;
;; usually we would assert class-table-equiv is pairwise method-equiv
;; However this is not the property that we really want, 
;; 
;; We want all method defined in djvm-method, looking up the method in the
;; jvm-class-table, we get a method-equiv method! 
;;

;----------------------------------------------------------------------

(encapsulate () 
 (local (include-book "bcv-simple-check-implies-djvm-check"))
 (defthm bcv-simple-check-implies-djvm-check
   (implies (and (consistent-state djvm-s)
                 (bcv-simple-check-step-pre (next-inst djvm-s) 
                                            (extract-sig-frame
                                             (TOPX (G 'CALL-STACK DJVM-S))
                                             (G 'METHOD-TABLE DJVM-S))))
            (djvm-check-step djvm-s))))


;; (encapsulate () 
;;  (local (include-book "bcv-simple-check-implies-djvm-check"))
;;  (defthm bcv-simple-check-implies-djvm-check
;;    (implies (bcv-simple-check-step-pre (next-inst djvm-s) 
;;                                        (extract-sig-frame
;;                                         (TOPX (G 'CALL-STACK DJVM-S))
;;                                         (G 'METHOD-TABLE DJVM-S)))
;;             (djvm-check-step djvm-s))))
;; Sat Nov 19 15:08:28 2005
;;
;; wrong conjecture! 


(encapsulate () 
 (local (include-book "djvm-check-succeed-implies-jvm-equiv-state"))
 (defthm djvm-check-succeed-implies-jvm-equiv-state
   (implies (and (state-equiv jvm-s djvm-s)
                 (djvm-check-step djvm-s))
            (state-equiv (m-step jvm-s)
                         (djvm-step djvm-s)))))


(encapsulate () 
 (local (include-book "bcv-simple-check-monotonic"))
 (defthm bcv-simple-check-step-pre-bcv-simple-check-step-pre
   (implies (and (sig-frame-compatible frame1 frame2)
                 (bcv-simple-check-step-pre inst frame2))
            (bcv-simple-check-step-pre inst frame1))))

;;;
;;; this following are top level properties. 
;;;

(encapsulate () 
 (local (include-book "bcv-simple-method-implies-bcv-simple-check-step-pre"))
 (defthm method-verified-implies-bcv-simple-check-step-pre-on-recorded-signature-lemma                 
   (implies (and (bcv-simple-method method method-table)
                 (integerp pc)
                 (<= 0 pc)
                 (< pc (len (g 'code method)))
                 (equal inst (nth pc (g 'code method)))
                 (member inst (g 'code method)))
            (bcv-simple-check-step-pre inst 
                                       (cdr (assoc-equal pc (g 'sig-vector method)))))))


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

;;; the above lemma is the most difficult one! Tue Nov 29 10:23:10 2005


(defthm method-verified-implies-bcv-simple-check-step-pre-on-recorded-signature                 
  (implies (and (bcv-method method method-table)
                (equal method (binding (g 'method-name method) method-table))
                (bcv-verified-method-table method-table)
                (integerp pc)
                (<= 0 pc)
                (< pc (len (g 'code method)))
                (equal inst (nth pc (g 'code method)))
                (member inst (g 'code method)))
           (bcv-simple-check-step-pre inst 
                                      (cdr (assoc-equal pc 
                                                        (collect-witness-bcv-method method method-table)))))
  :hints (("Goal" :in-theory (disable collect-witness-bcv-method
                                      bcv-verified-method-table
                                      bcv-method
                                      bcv-simple-method)
           :use ((:instance
                  method-verified-implies-bcv-simple-check-step-pre-on-recorded-signature-lemma
                  (method (s 'sig-vector 
                             (collect-witness-bcv-method method method-table) method))))
           :do-not-induct t)))


 
;----------------------------------------------------------------------

(encapsulate () 
 (local (include-book "djvm-is-safe"))
 (defthm method-table-does-not-change
   (equal (g 'method-table (djvm-step st))
          (g 'method-table st))))


;----------------------------------------------------------------------

(encapsulate () 
  (local (include-book "djvm-is-safe"))

  (defthm djvm-step-preserve-consistent-state
    (implies (consistent-state st)
             (consistent-state (djvm-step st))))

  (defthm djvm-run-preserve-consistent-state
    (implies (consistent-state st)
             (consistent-state (djvm-run st any)))))

;----------------------------------------------------------------------



(in-theory (disable state-equiv 
                    m-step
                    djvm-step
                    djvm-check-step
                    bcv-simple-check-step-pre
                    next-inst
                    extract-sig-frame
                    consistent-state
                    bcv-verified-method-table
                    bcv-simple-method))


;; (i-am-here) ;; Fri Nov 18 22:24:27 2005

(defthm consistent-state-implies-pc-in-range
  (implies (consistent-state djvm-s)
           (pc-in-range djvm-s))
  :hints (("Goal" :in-theory (enable consistent-state))))

;;;
;;; Sat Nov 19 14:56:39 2005 need to extend the consistent-state definition!! 
;;; to assert that PC is in range! 
;;;
;;; Will need to redo that bcv-simple-check-step-pre will ensure that!! 
;;;


(defthm consistent-state-implies-bcv-method
  (implies (consistent-state djvm-s)
           (bcv-method (cdr (assoc-equal (g 'method-name (car (g 'call-stack djvm-s)))
                                         (g 'method-table djvm-s)))
                       (g 'method-table djvm-s)))
  :hints (("Goal" :in-theory (e/d (consistent-state current-method) (bcv-method)))))





(defthm consistent-state-implies-sig-frame-compatible
  (implies (consistent-state djvm-s)
           (SIG-FRAME-COMPATIBLE
            (EXTRACT-SIG-FRAME (CAR (G 'CALL-STACK DJVM-S))
                               (G 'METHOD-TABLE DJVM-S))
            (CDR (ASSOC-EQUAL (G 'PC (CAR (G 'CALL-STACK DJVM-S)))
                              (COLLECT-WITNESS-BCV-METHOD
                               (CDR (ASSOC-EQUAL (G 'METHOD-NAME
                                                    (CAR (G 'CALL-STACK DJVM-S)))
                                                 (G 'METHOD-TABLE DJVM-S)))
                               (G 'METHOD-TABLE DJVM-S))))))
  :hints (("Goal" :in-theory (e/d (consistent-state current-method) (bcv-method)))))


(defthm consistent-state-method-name-equal
  (implies (consistent-state djvm-s)
           (equal (G 'METHOD-NAME
                     (CDR (ASSOC-EQUAL (G 'METHOD-NAME
                                          (CAR (G 'CALL-STACK DJVM-S)))
                                       (G 'METHOD-TABLE DJVM-S))))
                  (g 'method-name (car (g 'call-stack djvm-s)))))
  :hints (("Goal" :in-theory (e/d (consistent-state current-method) (bcv-method)))))

(defthm in-range-then-member
  (implies (and (<= 0 pc)
                (< pc (len l)))
           (member (nth pc l) l)))



(defthm pc-in-range-implies-member
  (implies (pc-in-range djvm-s)
           (member (nth (g 'pc (car (g 'call-stack djvm-s)))
                        (g 'code (cdr (assoc-equal
                                       (g 'method-name (car (g 'call-stack
                                                               djvm-s)))
                                       (g 'method-table djvm-s)))))
                   (g 'code (cdr (assoc-equal (g 'method-name (car (g
                                                                    'call-stack djvm-s)))
                                              (g 'method-table djvm-s))))))
  :hints (("Goal" :in-theory (enable pc-in-range))))


(defthm consistent-state-implies-pc-in-range-f
  (implies (consistent-state djvm-s)
           (pc-in-range djvm-s)))


(defthm pc-in-range-f-pc-f
  (implies (pc-in-range djvm-s)
           (integerp (g 'pc (car (g 'call-stack djvm-s)))))
  :rule-classes :forward-chaining)

(defthm pc-in-range-f-pc-b
  (implies (pc-in-range djvm-s)
           (integerp (g 'pc (car (g 'call-stack djvm-s))))))



(defthm pc-in-range-f-pc-f-2
  (implies (pc-in-range djvm-s)
           (<= 0 (g 'pc (car (g 'call-stack djvm-s)))))
  :hints (("Goal" :in-theory (enable pc-in-range)))
  :rule-classes :forward-chaining)

(defthm pc-in-range-f-pc-b-2
  (implies (pc-in-range djvm-s)
           (<= 0 (g 'pc (car (g 'call-stack djvm-s)))))
  :hints (("Goal" :in-theory (enable pc-in-range))))



(defthm pc-in-range-f-pc-f-3
  (implies (pc-in-range djvm-s)
           (< (g 'pc (car (g 'call-stack djvm-s)))
              (len (g 'code 
                      (cdr (assoc-equal 
                            (g 'method-name 
                               (car (g 'call-stack djvm-s)))
                            (g 'method-table djvm-s)))))))
  :hints (("Goal" :in-theory (enable pc-in-range)))
  :rule-classes :forward-chaining)


(defthm pc-in-range-f-pc-b-3
  (implies (pc-in-range djvm-s)
           (< (g 'pc (car (g 'call-stack djvm-s)))
              (len (g 'code 
                      (cdr (assoc-equal 
                            (g 'method-name 
                               (car (g 'call-stack djvm-s)))
                            (g 'method-table djvm-s))))))))



(defthm bcv-simple-check-succeed-in-consistent-state
  (implies (and (CONSISTENT-STATE DJVM-S)
                (bcv-verified-method-table (g 'method-table djvm-s)))
           (BCV-SIMPLE-CHECK-STEP-PRE (NEXT-INST DJVM-S)
                                      (EXTRACT-SIG-FRAME (CAR (G 'CALL-STACK DJVM-S))
                                                         (G 'METHOD-TABLE
                                                            DJVM-S))))
  :hints (("Goal" 
           :in-theory (e/d (next-inst)
                           (pc-in-range bcv-method
                                        sig-frame-compatible
                                        bcv-simple-check-step-pre-bcv-simple-check-step-pre
                                        collect-witness-bcv-method))
           :use ((:instance bcv-simple-check-step-pre-bcv-simple-check-step-pre
                            (frame1 (EXTRACT-SIG-FRAME (CAR (G 'CALL-STACK DJVM-S))
                                                       (G 'METHOD-TABLE
                                                          DJVM-S)))
                            (frame2 (cdr (assoc-equal 
                                          (g 'pc (car (g 'call-stack djvm-s)))
                                          (collect-witness-bcv-method 
                                           (binding (g 'method-name 
                                                       (car (g 'call-stack djvm-s)))
                                                    (g 'method-table djvm-s))
                                           (g 'method-table djvm-s)))))
                            (inst (next-inst djvm-s)))))))


;;; we need consistent-state to assert pc-in-range!!
;;; currently this assertion is missing. Fri Nov 18 18:54:26 2005
;;; 


;;----------------------------------------------------------------------

(defthm djvm-check-succeed-in-consistent-state
  (implies (and (CONSISTENT-STATE DJVM-S)
                (bcv-verified-method-table (g 'method-table djvm-s)))
           (djvm-check-step djvm-s)))



(defthm verified-program-execute-safely-lemma
  (implies (and (CONSISTENT-STATE DJVM-S)
                (STATE-EQUIV JVM-S DJVM-S)
                (BCV-VERIFIED-METHOD-TABLE (G 'METHOD-TABLE DJVM-S)))
           (STATE-EQUIV (M-STEP JVM-S)
                        (DJVM-STEP DJVM-S))))



(defthm verified-program-executes-safely
  (implies (and (consistent-state djvm-s)
                (state-equiv jvm-s djvm-s)
                (bcv-verified-method-table (g 'method-table djvm-s)))
           (state-equiv (m-run jvm-s n)
                        (djvm-run djvm-s n))))


;----------------------------------------------------------------------

;; (i-am-here);; Mon May 22 15:30:10 2006


(defthm method-name-equal-state-equiv
  (implies (state-equiv jvm-s djvm-s)
           (equal (g 'method-name (topx (g 'call-stack jvm-s)))
                  (g 'method-name (topx (g 'call-stack djvm-s)))))
  :hints (("Goal" :in-theory (enable state-equiv))))


(defthm class-table-equiv-max-stack-equal
  (implies (and (class-table-equiv jvm-cl djvm-cl)
                (bound? name djvm-cl))
           (equal (max-stack (binding name jvm-cl))
                  (max-stack (binding name djvm-cl)))))



(defthm max-stack-binding-same-name
  (implies (and (state-equiv jvm-s djvm-s)
                (bound? name (g 'method-table djvm-s)))
           (equal (max-stack (binding name (g 'method-table jvm-s)))
                  (max-stack (binding name (g 'method-table djvm-s)))))
  :hints (("Goal" :in-theory (enable state-equiv)
           :use ((:instance class-table-equiv-max-stack-equal
                            (jvm-cl  (g 'method-table jvm-s))
                            (djvm-cl (g 'method-table djvm-s)))))))


(defthm consistent-state-implies-bound-method-name
  (implies (and (consistent-state stx)
                (equal (g 'method-table stx) stx-cl))
           (bound? (g 'method-name (topx (g 'call-stack stx)))
                   stx-cl))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm op-stack-equal-state-equiv
  (implies (state-equiv jvm-s djvm-s)
           (equal (g 'op-stack (topx (g 'call-stack jvm-s)))
                  (g 'op-stack (topx (g 'call-stack djvm-s)))))
  :hints (("Goal" :in-theory (enable state-equiv))))


(local 
 (defthm all-method-verified1-bcv-verified-method1
   (iff (all-method-verified1 mt mtable)
        (bcv-verified-method-table1 mt mtable))))

(defthm consistent-state-implies-bcv-verified-method-table
   (implies (consistent-state stx)
            (bcv-verified-method-table (g 'method-table stx)))
   :hints (("Goal" :in-theory (enable consistent-state bcv-verified-method-table)))
   :rule-classes :forward-chaining)

(defthm consistent-state-implies-all-method-verified
  (implies (consistent-state stx)
           (all-method-verified (g 'method-table stx)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)



(encapsulate ()
  (local (include-book "djvm-is-safe"))
  (defthm verified-program-never-overflow-operand-stack-in-m
    (implies (and (consistent-state stx)
                  (state-equiv st stx))
             (<= (len (g 'op-stack (topx (g 'call-stack (m-run st n)))))
                 (max-stack (binding (g 'method-name 
                                        (topx (g 'call-stack (m-run st n))))
                                     (g 'method-table st)))))
    :hints (("Goal" :in-theory (disable binding topx max-stack bound?
                                        m-run djvm-run all-method-verified)
             :use ((:instance
                    verified-program-never-overflow-operand-stack-in-djvm
                    (st stx))
                   (:instance method-name-equal-state-equiv
                              (jvm-s (m-run st n))
                              (djvm-s (djvm-run stx n)))
                   (:instance verified-program-executes-safely
                               (jvm-s st)
                               (djvm-s stx))
                   (:instance op-stack-equal-state-equiv
                              (jvm-s (m-run st n))
                              (djvm-s (djvm-run stx n)))
                   (:instance max-stack-binding-same-name
                              (name (g 'method-name 
                                       (topx (g 'call-stack (m-run st n)))))
                              (jvm-s (m-run st n))
                              (djvm-s (djvm-run stx n))))))))

;----------------------------------------------------------------------


