(in-package "DJVM")
(include-book "../../BCV/typechecker")
(include-book "../../DJVM/consistent-state-to-sig-state")


(defthm bcv-array-type-only-assignable-to-java-lang-Object-or-interface-type
  (implies (and (bcv::isassignable type (bcv::prefix-class classname)
                                   env)
                (bcv::isarraytype type)
                (not (equal classname "java.lang.Object")))
           (BCV::CLASSISINTERFACE
            (BCV::CLASS-BY-NAME classname
                                (bcv::classtableenvironment env)))))
                                
;;; the following is a very specific fact! 


;; (defthm bcv-array-type-only-assignable-to-java-lang-Object-or-interface-type
;;   (implies (and (bcv::isassignable type (bcv::prefix-class classname)
;;                                    env)
;;                 (bcv::isarraytype type)
;;                 (not (equal classname "java.lang.Object")))
;;            (BCV::CLASSISINTERFACE
;;             (BCV::CLASS-BY-NAME classname
;;                                 (bcv::classtableenvironment env)))))

;;;;
;;;; First it is difficult to reduce (bcv::isMatchingType type2 (opstack-sig  ..))
;;;; into bcv::isassignable ...
;;;; 
;;;; second we need to show that 
;;;;     bcv::classisinterface
;;;; implies 
;;;;     (isInterface (class-by-name ...))
;;;;  
;;;; for this to hold
;;;;
;;;; we need 
;;;;    1) instance-class-table is loaded from static class-table
;;;;       (consistent-state will give that)
;;;; 
;;;;    2) we also need to assert that class is ready loaded!! 
;;;; 


(encapsulate () 
 (local (include-book "base-consistent-state-lookupfield-bcv"))
 (defthm classIsInterface-implies-isInterface
   (implies (and (class-table-is-loaded-from cl scl)
                 (bcv::classIsInterface 
                  (bcv::class-by-name name 
                                      (bcv::scl-jvm2bcv scl)))
                 (class-by-name name cl))
            (isInterface (class-by-name name cl)))
   :hints (("Goal" :in-theory (e/d ( isInterface 
                                     bcv::classIsInterface
                                     class-exists?)
                                   (class-accessflags))
            :do-not '(generalize)))))

(local 
 (defthm consistent-state-implies-class-table-is-loaded-from
   (implies (consistent-state s)
            (class-table-is-loaded-from 
             (instance-class-table s)
             (env-class-table (env s))))
   :hints (("Goal" :in-theory (enable consistent-state)))))
             

(local 
 (defthm isClassTerm-implies-not-null
   (implies (isClassTerm (class-by-name name cl))
            (class-by-name name cl))
   :rule-classes :forward-chaining))


(defthm bcv-is-interface-implies-isInterface
  (implies (and (bcv::classisinterface (bcv::class-by-name classname 
                                                           (bcv::classtableenvironment (env-sig s))))
                (isClassTerm (class-by-name classname (instance-class-table s)))
                (consistent-state s))
           (isInterface (class-by-name classname (instance-class-table s))))
  :hints (("Goal" :in-theory (e/d (bcv::classtableenvironment env-sig)
                                  (isInterface consistent-state
                                               isClassTerm
                                               bcv::classisinterface))
           :use ((:instance classIsInterface-implies-isInterface
                            (cl (instance-class-table s))
                            (name classname)
                            (scl (env-class-table (env s))))))))
                

(encapsulate () 
 (local (include-book "base-bcv-support"))
 (defthm bcv-isMatchingType-bcv-isAssignable-specific
   (implies (and (bcv::isMatchingType typ (opstack-sig 
                                           (operand-stack (current-frame s))
                                           cl hp hp-init method-ptr) env)
                 (canPopCategory1 (operand-stack (current-frame s)))
                 (equal (bcv::sizeof typ) 1))
            (bcv::isAssignable (value-sig (topStack s)
                                          cl hp hp-init method-ptr) typ env)))) 



(encapsulate () 
   (local (include-book "base-bcv"))

   (defthm isArrayType-bcv-isArrayType
     (implies (and (ISARRAYTYPE (OBJ-TYPE (DEREF2 v hp)))
                   (not (deref2-init v hp-init))
                   (REFp v hp)
                   (not (NULLp v)))
              (bcv::isarraytype (value-sig v cl hp hp-init method-ptr)))
     :hints (("Goal" :in-theory (e/d (isarraytype bcv::isarraytype tag-of 
                                                  fix-sig NULLp REFp wff-REFp
                                                  rREF deref isarraytype
                                                  deref2 
                                                  primitive-type? fix-sig
                                                  value-of wff-tagged-value 
                                                  value-sig)
                                     (binding-rREF-normalize)))
             ("Subgoal 3" :expand (FIX-SIG (OBJ-TYPE (BINDING (CDR V) HP))))
             ("Subgoal 2" :expand (FIX-SIG (OBJ-TYPE (BINDING (CDR V) HP))))
             ("Subgoal 1" :expand (FIX-SIG (OBJ-TYPE (BINDING (CDR V) HP)))))))

;;; Mon Jul 11 18:14:05 2005. 
;;;
;;; this is quite difficult. Just to relate 
;;;     (isArrayType (obj-type (deref2 v hp)))
;;; with 
;;;    (bcv::isArrayType (value-sig ....))
;;;
;;; because value-sig is complicated!! 
;;;

;;
;;                 (canPopCategory1 (operand-stack (current-frame s)))
;;                 (equal (bcv::sizeof typ) 1))
;;

(defthm bcv-array-type-only-assignable-to-java-lang-Object-or-interface-type-specific
  (implies (and (bcv::isassignable (value-sig (topStack s)
                                              (instance-class-table s)
                                              (heap s)
                                              (heap-init-map (aux s))
                                              (method-ptr (current-frame s)))
                                    (bcv::prefix-class classname)
                                   (env-sig s))
                (consistent-state s)
                (not (NULLp (topStack s))) ;; new hyps
                (REFp (topStack s) (heap s)) ;; 
                (not (deref2-init (topStack s) ;; new hyps 
                                  (heap-init-map (aux s))))
                (isClassTerm (class-by-name classname (instance-class-table s)))
                (isarraytype (obj-type (deref2 (topStack s) (heap s))))
                (not (equal classname "java.lang.Object")))
           (isInterface (class-by-name classname (instance-class-table s))))
  :hints (("Goal" :in-theory (e/d () (bcv::isassignable env-sig
                                                        value-sig
                                                        obj-type
                                                        topStack
                                                        bcv::prefix-class
                                                        heap-init-map
                                                        aux
                                                        NULLp
                                                        deref2-init
                                                        bcv::isArrayType
                                                        current-frame
                                                        method-ptr
                                                        bcv::classtableenvironment
                                                        isClassTerm
                                                        isarraytype
                                      consistent-state isInterface))
           :restrict ((bcv-array-type-only-assignable-to-java-lang-Object-or-interface-type
                       ((type (value-sig (topStack s) (instance-class-table s)
                                         (heap s) (heap-init-map (aux s))
                                         (method-ptr (current-frame s))))))))))



(defthm ismatching-type-implies-isAssignable-prefix-class
  (implies (and (BCV::ISMATCHINGTYPE (BCV::PREFIX-CLASS type)
                                     (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                                  (INSTANCE-CLASS-TABLE S)
                                                  (HEAP S)
                                                  (HEAP-INIT-MAP (AUX S))
                                                  (METHOD-PTR (CURRENT-FRAME S)))
                                     (ENV-SIG S))
                (canPopCategory1 (operand-stack (current-frame s))))
            (BCV::ISASSIGNABLE (VALUE-SIG (TOPSTACK S)
                                          (INSTANCE-CLASS-TABLE S)
                                          (HEAP S)
                                          (HEAP-INIT-MAP (AUX S))
                                          (METHOD-PTR (CURRENT-FRAME S)))
                               (BCV::PREFIX-CLASS type)
                               (ENV-SIG S)))
  :hints (("Goal" :in-theory (e/d () (bcv::isassignable env-sig value-sig 
                                                        topstack
                                                        bcv::ismatchingtype
                                                        heap-init-map
                                                        aux
                                                        bcv::prefix-class
                                                        method-ptr
                                                        canPopCategory1
                                                        current-frame)))))











(defthm isMatchingType-to-Array-Type-not-isInterface-then-class-table
  (implies (and (BCV::ISMATCHINGTYPE (BCV::PREFIX-CLASS (FIELDCP-CLASSNAME fieldcp))
                                      (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                                   (INSTANCE-CLASS-TABLE S)
                                                   (HEAP S)
                                                   (HEAP-INIT-MAP (AUX S))
                                                   (METHOD-PTR (CURRENT-FRAME S)))
                                      (ENV-SIG S))
                 (isarraytype (obj-type (deref2 (topstack s) (heap s))))
                 (isClassTerm (class-by-name (fieldcp-classname fieldcp)
                                             (instance-class-table s)))
                 ;;; Mon Jul 11 17:45:13 2005
                 (canPopCategory1 (operand-stack (current-frame s)))
                 (not (isInterface (class-by-name (fieldcp-classname fieldcp)
                                                  (instance-class-table s))))
                 (not (NULLp (topStack s))) ;; new hyps
                 (REFp (topStack s) (heap s)) ;; 
                 (not (deref2-init (topStack s) ;; new hyps 
                                   (heap-init-map (aux s))))
                 (consistent-state s))
           (equal (fieldcp-classname fieldcp) "java.lang.Object"))
  :hints (("Goal" :in-theory (e/d () (bcv::isassignable env-sig
                                                        value-sig
                                                        obj-type
                                                        topStack
                                                        canPopCategory1
                                                        bcv::prefix-class
                                                        heap-init-map
                                                        aux
                                                        NULLp
                                                        deref2-init
                                                        fieldcp-classname
                                                        bcv::isArrayType
                                                        current-frame
                                                        method-ptr
                                                        bcv::classtableenvironment
                                                        isClassTerm
                                                        isarraytype
                                      consistent-state isInterface))
           :restrict ((bcv-array-type-only-assignable-to-java-lang-Object-or-interface-type
                       ((type (value-sig (topStack s) (instance-class-table s)
                                         (heap s) (heap-init-map (aux s))
                                         (method-ptr (current-frame s))))))))))

            
