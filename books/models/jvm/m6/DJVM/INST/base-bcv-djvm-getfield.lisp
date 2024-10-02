(in-package "DJVM")

(include-book "base-bcv")
(in-theory (disable BCV::PREFIX-CLASS 
                    BCV::FIELDNAMECP
                    BCV::FIELDCLASSNAMECP
                    BCV::FIELDTYPECP
                    BCV::TRANSLATE-TYPE
                    BCV::FIELDTYPECP
                    BCV::NAME-OF
                    bcv::isarraytype
                    BCV::PASSESPROTECTEDFIELDCHECK
                    BCV::ISPROTECTEDFIELD
                    BCV::CLASSENVIRONMENT
                    bcv::arg1 arg))


(defthm type-size-either-2-or-1
  (implies (NOT (EQUAL (TYPE-SIZE type) 1))
           (equal (type-size type) 2))
  :hints (("Goal" :in-theory (enable type-size))))



(defthm car-opstack-sig-normalize
  (Implies (canPopCategory1 (operand-stack (current-frame s)))
           (equal (CAR (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                    cl hp hp-init method-ptr))
                  (value-sig (topStack s)
                             cl hp hp-init method-ptr)))
  :hints (("Goal" :in-theory (e/d (opstack-sig topStack current-frame 
                                               opstack-sig) (value-sig))
           :cases ((consp (operand-stack (current-frame s)))))
          ("Subgoal 1" :expand (opstack-sig (OPERAND-STACK (CURRENT-FRAME S))
                                            cl hp hp-init method-ptr))))




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
          ("Subgoal 1" :expand (FIX-SIG (OBJ-TYPE (BINDING (CDR V) HP))))))



;; (defthm type-size-either-2-or-1
;;   (implies (NOT (EQUAL (TYPE-SIZE type) 1))
;;            (equal (type-size type) 2))
;;   :hints (("Goal" :in-theory (enable type-size))))


(defthm len-bcv-pushOperandStack-size-2-is
  (implies (equal (type-size type) 2)
           (equal (len (BCV::PUSHOPERANDSTACK
                        (BCV::TRANSLATE-TYPE type)
                        stack))
                  (+ 2 (len stack))))
  :hints (("Goal" :in-theory (enable type-size
                                     bcv::pushoperandstack))))


(defthm bcv::fieldtypecp-normalize
  (equal (fieldcp-fieldtype (arg inst))
         (normalize-type-rep (BCV::FIELDTYPECP (BCV::ARG1 INST))))
  :hints (("Goal" :in-theory (enable bcv::fieldtypecp
                                     fieldcp-fieldtype
                                     bcv::arg1 
                                     arg))))


(defthm len-bcv-popOperandStack-size-2-is
  (implies (consp stack)
           (equal (len (BCV::POPMATCHINGTYPE
                        (BCV::PREFIX-CLASS any)
                        stack))
                  (- (len stack) 1)))
  :hints (("Goal" :in-theory (enable bcv::sizeof
                                     bcv::prefix-class
                                     bcv::pop
                                     bcv::popmatchingtype))))

;;; this is wrong need extra hyps!! 
;;;
;;; Making use of type of object in ACL2 to distinguish the 
;;; well-formed of types!! 
;;;

;; (i-am-here)  ;; Thu Jun 16 22:11:19 2005

(include-book "base-valid-type-s")

(encapsulate () 
  (local (include-book "base-type-size-normalize-fix-type"))
  (defthm type-size-equal-specific
    (implies (and (consistent-state s)
                  (valid-type-strong type (instance-class-table s)))
             (equal (type-size (normalize-type-rep (fix-sig type)))
                    (type-size type)))))


;; (defthm type-size-normal-type-rep
;;   (implies (not (primitive-type? type))
;;            (not (EQUAL (TYPE-SIZE (NORMALIZE-TYPE-REP type) 1))
;;   :hints (("Goal" :in-theory (enable type-size primitive-type?))))
;;          


(include-book "base-bcv-fact-isMatchingType-isAssignableTo")

;;; from this we have.


;; (defthm isMatchingType-isAssignableTo
;;   (implies 
;;    (and (BCV::ISMATCHINGTYPE
;;          (BCV::PREFIX-CLASS (BCV::FIELDCLASSNAMECP (BCV::ARG1 INST)))
;;          (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
;;                       (INSTANCE-CLASS-TABLE S)
;;                       (HEAP S)
;;                       (HEAP-INIT-MAP (AUX S))
;;                       (METHOD-PTR (CURRENT-FRAME S)))
;;          (ENV-SIG S))
;;         (not (NULLp (topStack s)))
;;         (consistent-state s)
;;         (no-fatal-error? s)
;;         (isClassTerm (class-by-name (fieldcp-classname (arg inst))
;;                                     (instance-class-table s))) 
;;         (bcv::class-by-name (bcv::fieldclassnamecp (bcv::arg1 inst))
;;                             (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S)))
;;         (not (bcv::classisinterface  (bcv::class-by-name (bcv::fieldclassnamecp (bcv::arg1 inst))
;;                                                          (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S))))))
;;     (CAR (ISASSIGNABLETO (OBJ-TYPE (DEREF2 (TOPSTACK S) (HEAP S)))
;;                          (FIELDCP-CLASSNAME (ARG INST))
;;                          S))))

;;
;; (i-am-here) ;; Mon Jun 20 15:58:26 2005
;;

(encapsulate () 
  (local (include-book "base-consistent-state-lookupfield-bcv"))
  (defthm consistent-state-implies-if-found-field-then-not-interface
    (implies (and (consistent-state s)
                  (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp)
                               (RESOLVECLASSREFERENCE (FIELDCP-CLASSNAME fieldcp)
                                                      S)))
             (not (bcv::ClassIsInterface  (bcv::class-by-name 
                                           (fieldcp-classname fieldcp)
                                           (BCV::CLASSTABLEENVIRONMENT
                                            (ENV-SIG S))))))))


(encapsulate ()
 (local (include-book "base-consistent-state-lookupfield-bcv"))
 (defthm consistent-state-implies-if-found-field-then-class-found
   (implies (and (consistent-state s)
                 (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp) 
                              (resolveclassreference (fieldcp-classname fieldcp) s)))
            (BCV::CLASS-BY-NAME (fieldcp-classname fieldcp)
                                (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S))))))



(defthm consistent-heap-array-init-state1-implies-not-dere2-init
  (implies (and (consistent-heap-array-init-state1 hp cl acl hp-init)
                (isarraytype (obj-type (deref2 v hp))))
           (not (deref2-init v hp-init)))
  :hints (("Goal" :in-theory (e/d (deref2 deref2-init rREF
                                          isarraytype
                                          common-info
                                          obj-type
                                          binding bound?) 
                                  (binding-rREF-normalize)))))

(defthm consistent-state-implies-consistent-heap-array-init1
  (implies (consistent-state s)
           (consistent-heap-array-init-state1 (heap s) 
                                              (instance-class-table s)
                                              (array-class-table s)
                                              (heap-init-map (aux s))))
  :hints (("Goal" :in-theory (enable consistent-state))))
                                     

(defthm consistent-state-implies-array-type-never-uninitialized
  (implies (and (consistent-state s)
                (isarraytype (obj-type (deref2 v (heap s)))))
           (not (deref2-init v (heap-init-map (aux s)))))
  :hints (("Goal" :use ((:instance
                         consistent-heap-array-init-state1-implies-not-dere2-init
                         (hp (heap s))
                         (cl (instance-class-table s))
                         (acl (array-class-table s))
                         (hp-init (heap-init-map (aux s))))))))


(defthm type-size-wff-type-rep
  (implies (wff-type-rep type)
           (equal (type-size (normalize-type-rep type))
                  (type-size type)))
  :hints (("Goal" :in-theory (enable wff-type-rep 
                                     type-size
                                     normalize-type-rep))))


(defthm bcv-arg1-normalize
  (equal (bcv::arg1 inst)
         (arg inst))
  :hints (("Goal" :in-theory (enable bcv::arg1 arg))))


(defthm bcv-fieldclassnamecp-normalize
  (equal (bcv::fieldclassnamecp cp)
         (fieldcp-classname cp))
  :hints (("Goal" :in-theory (enable bcv::fieldclassnamecp 
                                     fieldcp-classname))))


(defthm wff-fieldcp-implies-wff-type-rep
  (implies (wff-fieldcp cp)
           (wff-type-rep (bcv::fieldtypecp cp)))
  :hints (("Goal" :in-theory (enable wff-fieldcp bcv::fieldtypecp))))


;; (i-am-here) ;; Tue Jun 21 16:26:59 2005
;;
;; (i-am-here) ;; Thu Jun 23 16:15:01 2005
;;;
;;; I thought that we can avoid proving that fieldcp-classname is already
;;; loaded, however it can not be done! 
;;;
;;; The following reasoning is a bit twisted!!  if lookupfield succeeds and the
;;; obj is assignable to the field
;;;
;;; then we know the class is already loaded!!
;;; 
;;; and we know the class is not an interface. 

;;; from base-bcv-fact-isMatchingType-isAssignableTo.lisp 
;;; we have: 


(local 
 (encapsulate ()
  (local (include-book "base-consistent-state-lookupfield-bcv"))
  (defthm consistent-state-implies-if-found-field-then-not-interface-lemma
    (implies (and (consistent-state s)
                  (isInterface (class-by-name (field-ptr-classname field-ptr)
                                              (instance-class-table s))))
             (not  (LOOKUPFIELD field-ptr s))))))


(defthm consistent-state-implies-interface-class-no-field
  (implies (and (consistent-state s)
                (isInterface (class-by-name (fieldcp-classname fieldcp) (instance-class-table s))))
           (not (lookupfield 
                 (FIELDCP-TO-FIELD-PTR fieldcp) s))))





(encapsulate () 
  (local (include-book "base-bcv-fact-array-type-assignable"))
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
                (not (deref2-init (topStack s) ;; new hyps  ;; Mon Jul 11 20:50:23 2005
                                  (heap-init-map (aux s))))
                (consistent-state s))
            (equal (fieldcp-classname fieldcp) "java.lang.Object"))))


(in-theory (disable isClassTerm))

(local 
 (encapsulate () 
  (local (include-book "base-consistent-state-lookupfield-bcv"))
  (defthm consistent-state-implies-if-class-not-found-not-nil
    (implies (and (consistent-state s)
                  (not (class-by-name (field-ptr-classname field-ptr) 
                                      (instance-class-table s))))
             (not  (LOOKUPFIELD field-ptr s))))))



(defthm consistent-state-lookupfield-implies-loaded
  (implies (and (lookupfield (fieldcp-to-field-ptr fieldcp) s)
                (consistent-state s))
           (isClassTerm (class-by-name (fieldcp-classname fieldcp) 
                                       (instance-class-table s)))))


(encapsulate ()
 (local (include-book "base-valid-object-type-assignable-to-java-lang-Object"))
 (defthm consistent-state-implies-obj-type-assignable-java-lang-Object
   (implies (and (consistent-state s)
                 (ISARRAYTYPE (OBJ-TYPE (DEREF2 v  (heap s)))))
            (CAR (ISASSIGNABLETO (OBJ-TYPE (DEREF2 v (HEAP S)))
                                 "java.lang.Object" S)))))

