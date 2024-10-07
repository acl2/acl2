(in-package "DJVM")
(include-book "../main/djvm-simple")
(include-book "../main/m6-simple")
(include-book "../DJVM/consistent-state-bcv-on-track")
(include-book "../BCV/typechecker-simple")

;;; the way of introducing make it is not easy to use
;;; 
;;; Instead we should have asserted suitable properties on the scl
;;; 

;; (encapsulate ()
;;     (local (include-book "base-bcv-check-monotonic"))
;;     (defthm sig-check-AALOAD-on-more-general-implies-more-specific
;;       (implies (and (bcv::good-icl icl)
;;                     (bcv::good-scl (bcv::classtableEnvironment env1))
;;                     (bcv::sig-frame-more-general gframe sframe env1)
;;                     (bcv::consistent-sig-stack (bcv::frameStack gframe) icl)
;;                     (bcv::consistent-sig-stack (bcv::frameStack sframe) icl)
;;                     (not (equal (bcv::nth1OperandStackIs 2 sframe) 'NULL)) ;; added
;;                     (not (equal (bcv::nth1OperandStackIs 2 gframe) 'NULL))
;;                     (bcv::check-AALOAD inst env1 gframe)
;;                     (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
;;                (bcv::check-AALOAD inst env1 sframe))))
;;
;;  How to use the above lemma!!! we need to come up with an ICL that
;;  consistent-sig-stack can be established!! 
;;
;;
;;  not easily to be monotonic.... ?? Sat Jan  7 00:01:44 2006
;;  
;;  when it is not monotonic, it throws an exception...
;;  
;;  if the specific is of NULL type BCV::check-AALOAD may fail, even though
;;  BCV::check-AALOAD succeed on the general type, however, we know that during
;;  execution, such cases will be caught by runtime checking. 
;;
;;  So even the type::checking is not purely monotonic, that is OK!! 
;;
;;  
;; (encapsulate ()
;;   (local (include-book "base-bcv"))
;;   (defthm bcv-check-aaload-ensures-djvm-check-aaload
;;     (implies (and (bcv::check-AALOAD inst (env-sig s) 
;;                                      (frame-sig  (current-frame s)
;;                                                  (instance-class-table s)
;;                                                  (heap s)
;;                                                  (heap-init-map (aux s))))
;;                   (wff-inst inst)
;;                   (not (mem '*native* (method-accessflags (current-method s))))
;;                   (consistent-state s))
;;              (djvm::check-AALOAD inst s))))


;; (defthm check-AALOAD-implies-guard-succeeds
;;   (implies (and (consistent-state-strong s)
;;                 (check-AALOAD inst s))
;;           (AALOAD-guard inst s)))

;; (encapsulate ()
;;    (local (include-book "base-state-equiv"))
;;     (defthm equal-AALOAD-when-guard-succeeds
;;       (implies (and (AALOAD-guard inst djvm::djvm-s)
;;                     (state-equiv m6::m6-s djvm::djvm-s))
;;                (state-equiv (m6::execute-AALOAD inst m6::m6-s)
;;                             (djvm::execute-AALOAD inst djvm::djvm-s)))))



(defthm consistent-state-bcv-on-track-implies-bcv-good-scl-strong
  (implies (consistent-state-bcv-on-track s)
           (bcv::good-scl-strong (env-class-table (env s)))))



(defthm consistent-state-bcv-on-track-implies-good-icl
  (implies (consistent-state-bcv-on-track s)
           (bcv::good-icl (bcv::icl-witness-x (env-class-table (env s)))))
  :hints (("Goal" :in-theory (disable bcv::good-icl
                                      consistent-state-bcv-on-track))))


(defthm consistent-state-bcv-on-track-implies-icl-scl-compatible
  (implies (consistent-state-bcv-on-track s)
           (bcv::icl-scl-compatible 
            (bcv::icl-witness-x (env-class-table (env s)))
            (bcv::classtableEnvironment (env-sig s))))
  :hints (("Goal" :in-theory (disable bcv::good-icl
                                      bcv::icl-scl-compatible
                                      consistent-state-bcv-on-track))))

;
; intuitively icl-witness-x will be the instance class table that has
; everything loaded!!! 
;

;
; in the process of the making use of 
;
;   sig-check-AALOAD-on-more-general-implies-more-specific
;
; we will relieve the hypothesis that uses icl!! 
;


(skip-proofs 
 (defthm consistent-state-bcv-on-track-implies-instructionIsTypeSafe
   (implies (consistent-state-bcv-on-track djvm::djvm-s)
            (bcv::instructionIsTypeSafe (next-inst djvm::djvm-s)
                                        (env-sig djvm::djvm-s)
                                        (bcv::searchStackFrame 
                                         (pc djvm::djvm-s)
                                         (bcv::stack-map-wrap 
                                          (stack-maps-witness (method-ptr
                                                               (current-frame s)) 
                                                              (env-class-table (env s)))))))))



(skip-proofs 
 (defthm consistent-state-bcv-on-track-consistent-state-strong-sig-frame-more-general
   (implies (and (consistent-state-bcv-on-track s)
                 (consistent-state-strong s))
            (bcv::sig-frame-more-general 
             (bcv::searchStackFrame 
              (pc s)
              (bcv::stack-map-wrap 
               (stack-maps-witness (method-ptr
                                    (current-frame s)) 
                                   (env-class-table (env s)))))
             (frame-sig  (current-frame s)
                         (instance-class-table s)
                         (heap s)
                         (heap-init-map (aux s)))
             (env-sig s)))))


;----------------------------------------------------------------------

(skip-proofs 
 (defthm consistent-state-strong-implies-consistent-sig-operand-stack
   (implies (and (consistent-state-strong s)
                 (consistent-state-bcv-on-track s))
            (bcv::consistent-sig-stack 
             (bcv::frameStack (frame-sig
                               (current-frame s)
                               (instance-class-table s)
                               (heap s)
                               (heap-init-map (aux s))))
             (bcv::icl-witness-x (env-class-table (env s)))))))


(skip-proofs 
 (defthm consistent-state-strong-implies-consistent-sig-operand-stack-recorded-frame
   (implies (and (consistent-state-strong s)
                 (consistent-state-bcv-on-track s))
            (bcv::consistent-sig-stack 
             (bcv::framestack 
              (bcv::searchStackFrame 
               (pc djvm::djvm-s)
               (bcv::stack-map-wrap 
                (stack-maps-witness (method-ptr
                                     (current-frame s)) 
                                    (env-class-table (env s))))))
             (bcv::icl-witness-x (env-class-table (env s)))))))


;----------------------------------------------------------------------

;; still need to do a case split on when frame-sig is null
;; 


(skip-proofs 
 (defthm not-nullp-not-sig-value-NULL
   (implies (case-split (not (nullp (topStack (popstack s)))))
            (not (equal (bcv::nth1OperandStackIs 2 
                                                 (frame-sig (current-frame s)
                                                            (instance-class-table s)
                                                            (heap s)
                                                            (heap-init-map (aux s))))
                        'NULL)))))





(skip-proofs 
 (defthm sig-frame-more-general-not-null-not-null
   (implies (and  (not (equal (bcv::nth1OperandStackIs 2 
                                                       (frame-sig (current-frame s)
                                                                  (instance-class-table s)
                                                                  (heap s)
                                                                  (heap-init-map (aux s))))
                              'NULL))
                  (bcv::sig-frame-more-general 
                      gframe
                      (frame-sig (current-frame s)
                                 (instance-class-table s)
                                 (heap s)
                                 (heap-init-map (aux s)))
                      (env-sig s)))
            (not (equal (bcv::nth1OperandStackIs 2 gframe) 'NULL)))))

; now we can make use of the leaf lemmas! 


(defthm sig-frame-more-general-not-null-not-null-specific
  (implies (and  (not (equal (bcv::nth1OperandStackIs 2 
                                                      (frame-sig (current-frame s)
                                                                 (instance-class-table s)
                                                                 (heap s)
                                                                 (heap-init-map (aux s))))
                             'NULL))
                 (bcv::sig-frame-more-general 
                  (bcv::searchStackFrame (pc s)
                                         (bcv::stack-map-wrap 
                                          (stack-maps-witness (method-ptr
                                                               (current-frame s)) 
                                                              (env-class-table (env s)))))                                    
                  (frame-sig (current-frame s)
                                 (instance-class-table s)
                                 (heap s)
                                 (heap-init-map (aux s)))
                  (env-sig s)))
           (not (equal (bcv::nth1OperandStackIs 2 
                                                (bcv::searchStackFrame (pc s)                                                
                                                                       (bcv::stack-map-wrap 
                                                                        (stack-maps-witness (method-ptr
                                                                                             (current-frame s)) 
                                                                                            (env-class-table
                                                                                             (env
                                                                                              s))))))
                       'NULL)))
  :hints (("Goal" :use ((:instance sig-frame-more-general-not-null-not-null
                                   (gframe (bcv::searchStackFrame (pc s)
                                                                  (bcv::stack-map-wrap 
                                                                   (stack-maps-witness (method-ptr
                                                                                        (current-frame s)) 
                                                                                       (env-class-table (env s)))))))))))

(local (in-theory (disable sig-frame-more-general-not-null-not-null)))






(skip-proofs 
 (defthm consistent-state-strong-implies-good-scl
   (implies (consistent-state-strong s)
            (bcv::good-scl (bcv::classtableEnvironment (env-sig s))))))


(encapsulate () 
  (local (include-book "on-track-with-bcv-implies-next-inst-in-range"))
  (defthm consistent-state-strong-implies-wff-inst-next-inst
    (IMPLIES (and (CONSISTENT-STATE-STRONG djvm-S)
                  (consistent-state-bcv-on-track djvm-s))
             (WFF-INST (NEXT-INST djvm-S)))))

(skip-proofs
 (defthm consistent-state-strong-implies-not-native-code
   (implies (consistent-state-strong djvm-s)
            (NOT (MEM '*NATIVE* (METHOD-ACCESSFLAGS (CURRENT-METHOD DJVM-S)))))))


;----------------------------------------------------------------------
;----------------------------------------------------------------------

(local (in-theory (disable consistent-state-bcv-on-track
                           state-equiv
                           next-inst
                           frame-sig
                           env-sig
                           consistent-state-strong
                           bcv::classtableEnvironment
                           bcv::sig-frame-more-general
                           bcv::good-icl
                           bcv::nth1OperandStackIs
                           (bcv::nth1OperandStackIs)
                           bcv::good-scl
                           bcv::op-code
                           env-class-table 
                           bcv::framestack
                           bcv::searchStackFrame
                           stack-maps-witness
                           bcv::icl-scl-compatible
                           m6::execute-AALOAD
                           djvm::execute-AALOAD
                           djvm::check-AALOAD
                           bcv::check-AALOAD
                           code-instrs
                           AALOAD-guard)))



;;     (defthm sig-check-AALOAD-on-more-general-implies-more-specific
;;       (implies (and (bcv::good-icl icl)
;;                     (bcv::good-scl (bcv::classtableEnvironment env1))
;;                     (bcv::sig-frame-more-general gframe sframe env1)
;;                     (bcv::consistent-sig-stack (bcv::frameStack gframe) icl)
;;                     (bcv::consistent-sig-stack (bcv::frameStack sframe) icl)
;;                     (not (equal (bcv::nth1OperandStackIs 2 sframe) 'NULL)) ;; added
;;                     (not (equal (bcv::nth1OperandStackIs 2 gframe) 'NULL))
;;                     (bcv::check-AALOAD inst env1 gframe)
;;                     (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
;;                (bcv::check-AALOAD inst env1 sframe))))



(defthm instructionIsTypeSafe-and-is-inst-aaload-check-aaload
  (implies (and (bcv::instructionIsTypeSafe inst env cur)
                (equal (bcv::op-code inst) 'AALOAD))
           (bcv::check-AALOAD inst env cur)))


(skip-proofs 
  (defthm if-nullp-reduce-aaload
    (implies (and (nullp (topStack (popstack s)))
                  (equal (bcv::op-code inst) 'AALOAD))
             (equal (execute-aaload inst s)
                    (raise-exception "java.lang.NullPointerException" s)))))



(skip-proofs 
  (defthm if-nullp-reduce-aaload-m6
    (implies (and (equal (topStack (popstack s)) -1)
                  (equal (bcv::op-code inst) 'AALOAD))
             (equal (m6::execute-aaload inst s)
                    (m6::raise-exception "java.lang.NullPointerException" s)))))


(skip-proofs 
  (defthm nullp-implies-value-1
    (implies (and (state-equiv m6::m6-s djvm::djvm-s)
                  (nullp (topStack (popstack djvm::djvm-s))))
             (equal (topStack (popstack m6::m6-s)) -1))))

(skip-proofs 
 (defthm state-equiv-raise-exception
   (implies (state-equiv m6::m6-s djvm::djvm-s)
            (state-equiv (jvm::raise-exception any m6::m6-s)
                         (djvm::raise-exception any djvm::djvm-s)))))


(defthm on-track-with-BCV-implies-step-AALOAD 
  (implies (and (consistent-state-strong djvm::djvm-s)
                (consistent-state-bcv-on-track djvm::djvm-s)
                (equal (next-inst djvm::djvm-s) inst)
                (equal (bcv::op-code inst) 'AALOAD)
                (state-equiv m6::m6-s djvm::djvm-s))
       (state-equiv (m6::execute-AALOAD inst m6::m6-s)
                    (djvm::execute-AALOAD inst djvm::djvm-s)))
  :hints (("Goal" :cases ((nullp (topStack (popstack djvm::djvm-s))))
           :restrict
           ((sig-check-AALOAD-on-more-general-implies-more-specific
             ((icl (bcv::icl-witness-x (env-class-table (env djvm::djvm-s))))
              (gframe (bcv::searchStackFrame 
                       (pc djvm::djvm-s)
                       (bcv::stack-map-wrap 
                        (stack-maps-witness (method-ptr
                                             (current-frame djvm::djvm-s))
                                            (env-class-table (env
                                            djvm::djvm-s))))))))))))
           
;----------------------------------------------------------------------


(skip-proofs 
 (defthm step-preserve-state-equiv
   (implies (and (consistent-state-strong djvm-s)
                 (consistent-state-bcv-on-track djvm-s)
                 (state-equiv m6::m6-s djvm::djvm-s)
                 (bcv::verifyAll (external-class-table djvm-s)
                                 (external-class-table djvm-s))
                 (equal (next-inst djvm::djvm-s) inst))
   (state-equiv (m6::m6-step inst m6::m6-s)
                (djvm::djvm-step inst djvm::djvm-s)))))






