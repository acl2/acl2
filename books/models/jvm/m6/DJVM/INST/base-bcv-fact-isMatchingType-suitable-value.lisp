(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")

;; (i-am-here) ;; Tue May 17 14:10:25 2005


(local 
 (defthm consistent-state-implies-consistent-opstack
   (implies (and (consistent-state s)
                 (equal (instance-class-table s) cl)
                 (equal (heap s) hp))
            (consistent-opstack (operand-stack (current-frame s))
                                cl hp))))

(local 
 (defthm consistent-opstack-implies-top-consistent-value-x
   (implies (and (canPopCategory1 stk)
                 (consistent-opstack stk cl hp))
            (consistent-value-x (car stk) cl hp))))


(local 
 (defthm consistent-state-consistent-value-x-general
   (implies (and (consistent-state s)
                 (canPopCategory1 (operand-stack (current-frame s)))
                 (equal (instance-class-table s) cl)
                 (equal (heap s) hp))
            (consistent-value-x (topstack s) cl hp))
   :hints (("Goal" :in-theory (enable topstack)))))

;;; this comes from base-consistent-state.lisp 

;----------------------------------------------------------------------

;; (i-am-here) ;; Tue May 17 15:14:34 2005

(local 
 (encapsulate () 
   (local (include-book "base-bcv-support"))
   (defthm value-sig-isAssignable-to-ARRRAY-implies-being-REFp
    (implies (and (bcv::isAssignable (value-sig v cl hp hp-init method-ptr)
                                     '(array (class "java.lang.Object"))
                                     env)
                  (consistent-value-x v cl hp))
             (REFp v hp)))))




(defthm value-sig-isAssignable-to-ARRRAY-implies-being-REFp-specific
  (implies (and (bcv::isAssignable (value-sig (topstack s)
                                              (instance-class-table s) 
                                              (heap s)
                                              (heap-init-map (aux s))
                                              (method-ptr (current-frame s)))
                                   '(array (class "java.lang.Object"))
                                   (env-sig s))
                (consistent-value-x (topStack s) (instance-class-table s) 
                                    (heap s))
                (equal (heap s) hp))
           (REFp (topStack s) hp))
  :hints (("Goal" :in-theory (disable REFp bcv::isAssignable value-sig))))



;; these will be of a finite set of this for concluding (REFp v hp)
;; We will want the specific version. 
;;

;----------------------------------------------------------------------

;; note this is what DJVM::check-* interested in.
;;   (tag-of (topStack s))

(local 
 (encapsulate () 
    (local (include-book "base-bcv-support"))
    (defthm REFp-implies-not-tag-of-specific
      (implies (REFp (topStack s) (heap s))
               (equal (tag-of (topStack s)) 'REF))
      :hints (("Goal" :in-theory (disable tag-of topStack REFp))))))


(local (include-book "base-bcv-fact-isMatchingType-canPopCategory1"))
(local (include-book "base-bcv-fact-isMatchingType-isAssignable"))


(encapsulate ()
    (local (include-book "base-bcv-support"))
    (defthm topstack-guard-strong-implied-by-canPopCategory1
      (implies (and  (canPopCategory1 (operand-stack (current-frame s)))
                     (consistent-state s)
                     (NOT (MEM '*NATIVE*
                               (METHOD-ACCESSFLAGS (CURRENT-METHOD S)))))
               (topstack-guard-strong s))))





 
;;; we want "weaker hyp" instead of topstack-guard-strong, we want only
;;; canPopCategory1!! 

;----------------------------------------------------------------------

(defthm isMatchingType-array-java-lang-class-implies-tag-of-REF 
  (implies (and (bcv::isMatchingType '(array (class "java.lang.Object"))
                                      (opstack-sig (operand-stack (current-frame s))
                                                   (instance-class-table s)
                                                   (heap s)
                                                   (heap-init-map (aux s))
                                                   (method-ptr (current-frame s)))
                                      (env-sig s))
                (consistent-state s))
            (equal (tag-of (topStack s)) 'REF))
  :hints (("Goal" :in-theory (disable REFp consistent-state
                                      bcv::isAssignable env-sig
                                      value-sig))))



;;; FIX ME HERE!! Tue May 17 16:07:42 2005
(skip-proofs 
 (defthm isMatchingType-java-lang-Object-implies-tag-of-REF 
   (implies (and (bcv::isMatchingType '(class "java.lang.Object")
                                      (opstack-sig (operand-stack (current-frame s))
                                                   (instance-class-table s)
                                                   (heap s)
                                                   (heap-init-map (aux s))
                                                   (method-ptr (current-frame s)))
                                      (env-sig s))
                (consistent-state s))
            (equal (tag-of (topStack s)) 'REF))
  :hints (("Goal" :in-theory (disable REFp consistent-state
                                      bcv::isAssignable env-sig
                                      value-sig)))))







(encapsulate ()
 (local 
  (encapsulate ()
               (local (include-book "base-bcv-support"))
                           
               (defthm primitive-type-then-not-REFp-specific
                 (implies (and (primitive-type? (value-sig (topStack s) (instance-class-table s)
                                                           (heap s) (heap-init-map (aux s))
                                                           (method-ptr (current-frame s))))
                               (consistent-state s)
                               (equal (heap s) hp))
                          (not (REFp (topStack s) hp)))
                 :hints (("Goal" :cases ((nullp (topStack s))))))



               (defthm isMatchingType-INT-not-REFp
                 (implies (and (bcv::isassignable (value-sig (topStack s)
                                                             (instance-class-table s)
                                                             (HEAP S)
                                                             (HEAP-INIT-MAP (AUX S))
                                                             (METHOD-PTR (CURRENT-FRAME S)))
                                                  'INT
                                                  (ENV-SIG S))
                               (consistent-state s)
                               (equal (heap s) hp))
                          (not (REFp (topStack s) hp))))

               (defthm not-REFp-value-sig-is-tag-of-specific
                 (implies (not (REFp (topStack s) (heap s)))
                          (equal (djvm-translate-int-type (tag-of (topStack s)))
                                 (value-sig (topStack s)
                                            (instance-class-table s)
                                            (heap s)
                                            (heap-init-map (aux s))
                                            (method-ptr (current-frame s)))))
                 :hints (("Goal" :in-theory (enable value-sig))))


   
               (defthm isAssignable-INT-INT-f
                 (implies (bcv::isAssignable type 'INT env)
                          (equal (equal type 'INT) t))
                 :rule-classes :forward-chaining)))

  (local 
   (defthm canPopCategory1-implies-consp
     (implies (canPopCategory1 stk)
              (consp stk))
     :rule-classes :forward-chaining))


  (local 
   (defthm car-opstack-sig-normalize
    (implies (canPopCategory1 (operand-stack (current-frame s)))
             (equal (CAR (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                      cl hp hp-init method-ptr))
                    (value-sig (topStack s)
                               cl hp hp-init method-ptr)))
    :hints (("Goal" :in-theory (e/d (opstack-sig topStack current-frame 
                                                 opstack-sig) (value-sig canPopCategory1))
             :cases ((consp (operand-stack (current-frame s)))))
            ("Subgoal 1" :expand (opstack-sig (OPERAND-STACK (CURRENT-FRAME S))
                                              cl hp hp-init method-ptr)))))


  (defthm isMatchingType-INT-implies-tag-of-INT
    (implies (and (bcv::isMatchingType 'INT
                                       (opstack-sig (operand-stack (current-frame s))
                                                    (instance-class-table s)
                                                    (heap s)
                                                    (heap-init-map (aux s))
                                                    (method-ptr (current-frame s)))
                                       (env-sig s))
                  (consistent-state s))
             (equal (djvm-translate-int-type (tag-of (topStack s))) 'INT))
    :hints (("Goal" :in-theory (disable REFp consistent-state
                                        bcv::isAssignable
                                        djvm-translate-int-type
                                        ;;bcv::isMatchingType
                                        env-sig
                                        value-sig)
             :cases ((canPopCategory1 (operand-stack (current-frame s))))))))

                            
            


;----------------------------------------------------------------------
;
;
; Some thing about concluding "array-type-s"


;; why we want keep asking about bcv::isAssignable? 

(local 
 (encapsulate () 
   (local (include-book "base-bcv-support"))
   
   (defthm isAssignable-to-AARRAY-implies-array-type
     (implies (and (bcv::isAssignable 
                    (value-sig v (instance-class-table s)
                               (heap s)
                               (heap-init-map (aux s))
                               (method-ptr (current-frame s)))
                    '(array (class "java.lang.Object"))
                    (env-sig s))
                   (not (nullp v))
                   (consistent-state s)
                   (REFp v (heap s)))
              (isArrayType (obj-type (deref2 v (heap s))))))

   (defthm array-type-value-sig-implies-array-type-runtime
     (implies (and (isArrayType  (obj-type (deref2 v (heap s))))
                   (REFp v (heap s)) 
                   (not (nullp v))
                   ;; still need to relying on previous rules.  
                   (consistent-state s))
              (array-type-s (obj-type (deref2 v (heap s))) 
                            (instance-class-table s)))
     :hints (("Goal" :in-theory (disable REFp reference-type-s))))))


(defthm isMatchingType-array-java-lang-Object-implies-array-type-s
  (implies (and (bcv::isMatchingType '(array (class "java.lang.Object"))
                                     (opstack-sig (operand-stack (current-frame s))
                                                  (instance-class-table s)
                                                  (heap s)
                                                  (heap-init-map (aux s))
                                                  (method-ptr (current-frame s)))
                                     (env-sig s))
                (not (NULLp (topStack s)))
                (consistent-state s)
                (equal (heap s) hp)
                (equal (instance-class-table s) cl))
           (array-type-s (obj-type (deref2 (topStack s) hp)) cl))
  :hints (("Goal" :in-theory (disable array-type-s bcv::isMatchingType 
                                      bcv::isarraytype REFp
                                      value-sig
                                      opstack-sig env-sig NULLp
                                      consistent-state))))




(local 
 (encapsulate ()
              (local (include-book "base-bcv-support"))
              (defthm isAssignable-to-array-class-java-lang-Object-not-primitive-type
                (implies (and (bcv::isAssignable (value-sig v  (instance-class-table s)
                                                            (heap s)
                                                            (heap-init-map (aux s))
                                                            (method-ptr (current-frame s)))
                                                 '(array (class "java.lang.Object"))
                                                 (env-sig s))
                              (not (nullp v))
                              (consistent-value-x v (instance-class-table s) (heap s)))
                         (not (primitive-type? (array-component-type 
                                                (obj-type (deref2 v (heap s))))))))))
   

(defthm isMatchingType-array-java-lang-Object-implies-component-type-not-primitive-type
  (implies (and (bcv::isMatchingType '(array (class "java.lang.Object"))
                                     (opstack-sig (operand-stack (current-frame s))
                                                  (instance-class-table s)
                                                  (heap s)
                                                  (heap-init-map (aux s))
                                                  (method-ptr (current-frame s)))
                                      (env-sig s))
                (not (NULLp (topStack s)))
                (consistent-state s)
                (equal (heap s) hp))
           (NOT (PRIMITIVE-TYPE?
                 (ARRAY-COMPONENT-TYPE (OBJ-TYPE (DEREF2 (TOPSTACK s) hp))))))
  :hints (("Goal" :in-theory (disable bcv::isMatchingType
                                      bcv::isAssignable
                                      value-sig
                                      opstack-sig NULLp))))


;----------------------------------------------------------------------

;;; (i-am-here) ;;; Fri Jun 17 13:25:30 2005


(local 
 (defthm bcv-isAssignable-never-nil-class 
   (not (BCV::ISASSIGNABLE NIL (LIST 'CLASS ANY) env))))





(local 
 (defthm isMatchingType-prefix-class-implies-canPopCategory1-fact-specific
   (implies (and (bind-free (acl2::default-bind-free 'any 'any
                                                     (acl2::pkg-witness "DJVM")))
                 (bcv::isMatchingType (BCV::PREFIX-CLASS any)
                                      (opstack-sig (operand-stack (current-frame s))
                                                   (instance-class-table s)
                                                   (heap s)
                                                   (heap-init-map (aux s))
                                                   (method-ptr (current-frame s)))
                                      (env-sig s)))
            (canPopCategory1 (operand-stack (current-frame s))))
   :hints (("Goal" :in-theory (e/d (bcv::sizeof) (canpopcategory1
                                                  bcv::prefix-class
                                                  env-sig
                                                  bcv::isMatchingType))))))




(local 
  (defthm canPopCategory1-implies-consp
    (implies (canPopCategory1 stk)
             (consp stk))
    :rule-classes :forward-chaining))


(local 
 (defthm car-opstack-sig-normalize
   (implies (canPopCategory1 (operand-stack (current-frame s)))
            (equal (CAR (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                     cl hp hp-init method-ptr))
                   (value-sig (topStack s)
                              cl hp hp-init method-ptr)))
   :hints (("Goal" :in-theory (e/d (opstack-sig topStack current-frame 
                                                opstack-sig) (value-sig canPopCategory1))
            :cases ((consp (operand-stack (current-frame s)))))
           ("Subgoal 1" :expand (opstack-sig (OPERAND-STACK (CURRENT-FRAME S))
                                             cl hp hp-init method-ptr)))))

;; (defthm isAssignable-prefix-class-not-primitivie-type
;;   (implies (bcv::isAssignable type (bcv::prefix-class any) env)
;;            (not (primitive-type? type)))
;;   :hints (("Goal" :in-theory (enable primitive-type?)))
;;   :rule-classes :forward-chaining)


(local 
 (defthm isAssignable-prefix-class-not-primitivie-type-b
   (implies (bcv::isAssignable type (bcv::prefix-class any) env)
            (not (primitive-type? type)))
   :hints (("Goal" :in-theory (enable primitive-type?)))))


(local 
 (defthm isAssignable-prefix-class-not-primitivie-type-b-specific
   (implies (and (bind-free (acl2::default-bind-free 's 's (acl2::pkg-witness "DJVM")))
                 (bind-free (acl2::default-bind-free 'any 'any (acl2::pkg-witness "DJVM")))
                 (bcv::isAssignable type (bcv::prefix-class any) (env-sig s)))
            (not (primitive-type? type)))
   :hints (("Goal" :in-theory (disable bcv::isAssignable bcv::prefix-class)))))
                          

(local 
 (defthm value-sig-not-primitive-type-implies-tag-of-REF
   (implies (and (not (primitive-type? (value-sig v cl hp hp-init method-ptr)))
                 (consistent-value-x v cl hp))
            (equal (tag-of v) 'REF))
   :hints (("Goal" :in-theory (enable consistent-value-x consistent-value)))))


;;; a set forward chaining rule will make sense here!! 
;;; however!!  Fri Jun 17 14:54:58 2005


;; (defthm consistent-state-topStack-guard-strong-implies-consistent-value-x-b
;;   (implies (and (topstack-guard-strong s)
;;                 (consistent-state s))
;;            (consistent-value-x (topStack s) (instance-class-table s) (heap s)))
;;   :hints (("Goal" :in-theory (e/d (safe-topstack) (consistent-value-x)))))

;; (defthm consistent-state-canPopCategory1-implies-topStack-guard-strong
;;   (implies (and (consistent-state s)
;;                 (canPopCategory1 (operand-stack (current-frame s))))
;;            (topstack-guard-strong s))
;;   :hints (("Goal" :in-theory (enable topstack-guard-strong))))

;; (local 
;;  (encapsulate () 
;;   (local    
;;    (defthm consistent-opstack-consp-opstack-implies-consistent-value-x
;;      (implies (and (consistent-opstack stk cl hp)
;;                    (consp stk))
;;               (consistent-value-x (car stk) cl hp))))
                               
;;   (local (defthm consistent-frame-implies-consistent-opstack-b
;;            (implies (consistent-frame frame cl hp)
;;                     (consistent-opstack (operand-stack frame) cl hp))))

;;   (local (defthm canPopCategory1-implies-consp-b
;;            (implies (canPopCategory1 stk)
;;                     (consp stk))))

;;   (local (defthm topStack-is-car-operandstack-current-frame
;;            (equal (topStack s) 
;;                   (car (operand-stack (current-frame s))))
;;            :hints (("Goal" :in-theory (enable topStack)))))


(local 
 (defthm consistent-state-consistent-value-x-canPop1-strong
   (implies (and (consistent-state s)
                 (canPopCategory1 (operand-stack (current-frame s))))
            (consistent-value-x (topStack s) (instance-class-table s) 
                                (heap s)))
   :hints (("Goal" :in-theory (e/d (topStack) 
                                   (consistent-frame
                                    canPopCategory1))))))



(defthm isMatchingType-INT-implies-tag-of-prefix-class
  (implies (and (bcv::isMatchingType (bcv::prefix-class any)
                                     (opstack-sig (operand-stack (current-frame s))
                                                  (instance-class-table s)
                                                  (heap s)
                                                  (heap-init-map (aux s))
                                                  (method-ptr (current-frame s)))
                                     (env-sig s))
                (consistent-state s))
           (equal (tag-of (topStack s)) 'REF))
  :hints (("Goal"
           :use ((:instance
                  value-sig-not-primitive-type-implies-tag-of-REF
                  (v (topStack s))
                  (cl (instance-class-table s))
                  (hp (heap s))
                  (hp-init (heap-init-map (aux s)))
                  (method-ptr (method-ptr (current-frame s)))))
           :in-theory (disable REFp consistent-state
                               bcv::isAssignable
                               canpopcategory1
                               opstack-sig
                               bcv::prefix-class
                               bcv::isMatchingType
                               value-sig-not-primitive-type-implies-tag-of-REF
                               REFP-IMPLIES-NOT-TAG-OF-SPECIFIC
                               env-sig
                               value-sig))))
                            

;----------------------------------------------------------------------

;;; fix me!! Fri Jul 29 15:55:00 2005                              
                            
(skip-proofs 
 (defthm isMatchingType-reference-implies-tag-of-REF 
   (implies (and (bcv::isMatchingType 'REFERENCE
                                      (opstack-sig (operand-stack (current-frame s))
                                                   (instance-class-table s)
                                                   (heap s)
                                                   (heap-init-map (aux s))
                                                   (method-ptr (current-frame s)))
                                      (env-sig s))
                (consistent-state s))
            (equal (tag-of (topStack s)) 'REF))
  :hints (("Goal" :in-theory (disable REFp consistent-state
                                      bcv::isAssignable env-sig
                                      value-sig)))))



