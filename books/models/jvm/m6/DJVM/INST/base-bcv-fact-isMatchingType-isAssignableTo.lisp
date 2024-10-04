(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")




(local (include-book "base-bcv-fact-isMatchingType-isAssignableTo-support"))

;; we do know that Thu Jun 23 15:35:26 2005
;; 

(defthm isMatchingType-isAssignableTo
  (implies 
   (and (BCV::ISMATCHINGTYPE
         (BCV::PREFIX-CLASS (BCV::FIELDCLASSNAMECP (BCV::ARG1 INST)))
         (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                      (INSTANCE-CLASS-TABLE S)
                      (HEAP S)
                      (HEAP-INIT-MAP (AUX S))
                      (METHOD-PTR (CURRENT-FRAME S)))
         (ENV-SIG S))
        (not (NULLp (topStack s)))
        (consistent-state s)
        (no-fatal-error? s)
        (isClassTerm (class-by-name (fieldcp-classname (arg inst))
                                    (instance-class-table s))) 
        (bcv::class-by-name (bcv::fieldclassnamecp (bcv::arg1 inst))
                            (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S)))
        (not (bcv::classisinterface  (bcv::class-by-name (bcv::fieldclassnamecp (bcv::arg1 inst))
                                                         (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S))))))
    (CAR (ISASSIGNABLETO (OBJ-TYPE (DEREF2 (TOPSTACK S) (HEAP S)))
                         (FIELDCP-CLASSNAME (ARG INST))
                         S))))

;;; Mon Jun 20 15:55:30 2005
;;;
;;; Note this above is NOT TRUE!!! Fri Jun 17 15:53:40 2005
;;; 

;;; Because BCV's check assume that every object is assignable to 
;;; any interface!!! 
;;; However isassignableto does not expect so!!! 
;;; 
;;; Why BCV works, is because if resolution succeeds.  
;;;
;;; when resolution succeeds, then we know fieldcp-classname is assignable to
;;; some actual class. 
;;; And object-type is Assignable to some actual type!!!! 
;;;;
;;;;
;;;; Because resolution will never succeed if the fieldcp-classname is a
;;;; interface type!! 
;;;; ....


;;
;; (skip-proofs 
;;  (defthm isMatchingType-isAssignableTo
;;   (implies 
;;    (BCV::ISMATCHINGTYPE
;;     (BCV::PREFIX-CLASS (BCV::FIELDCLASSNAMECP (BCV::ARG1 INST)))
;;     (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
;;                  (INSTANCE-CLASS-TABLE S)
;;                  (HEAP S)
;;                  (HEAP-INIT-MAP (AUX S))
;;                  (METHOD-PTR (CURRENT-FRAME S)))
;;     (ENV-SIG S))
;;     (CAR (ISASSIGNABLETO (OBJ-TYPE (DEREF2 (TOPSTACK S) (HEAP S)))
;;                          (FIELDCP-CLASSNAME (ARG INST))
;;                          S)))))