(in-package "DJVM")
(include-book "../../M6-DJVM-shared/jvm-linker")
(include-book "../../M6-DJVM-shared/jvm-class-table")
(include-book "../../M6-DJVM-shared/jvm-object-type-hierachy")
(include-book "../../DJVM/consistent-state")


(local (include-book "base-consistent-state-lookupfield-support"))

(encapsulate () 
  (local (include-book "base-lookupfield-fieldname-normalize"))

  (defthm field-fieldname-reduce
    (implies (LOOKUPFIELD field-ptr s)
             (equal (FIELD-FIELDNAME (LOOKUPFIELD field-ptr s))
                    (field-ptr-fieldname field-ptr))))

  (defthm field-fieldtype-reduce
    (implies (LOOKUPFIELD field-ptr s)
             (equal (FIELD-FIELDTYPE (LOOKUPFIELD field-ptr s))
                    (field-ptr-type field-ptr)))))

;;; Mon Jun 20 13:55:06 2005 
;;; wasted my time not asserting fieldcp-classname could not be
;;; "java.lang.Object"!! 
;;; 

;; (defthm
;;   consistent-object-and-field-found-in-lookup-implies-jvm-field-access-guard
;;   (implies (and (consistent-state s)
;;                 (consistent-object obj (heap s) (instance-class-table s))
;;                 (or (not (isArrayType (obj-type obj)))
;;                     ;;(and (equal (fieldcp-classname fieldcp) "java.lang.Object")
;;                     (consistent-array-object obj (heap s)
;;                                              (instance-class-table s)
;;                                              (array-class-table s)))
;;                 ;; need to strengthen GUARD 
;;                 ;; and check for GETFIELD ;; Thu Jun  9 15:43:06 2005
;;                 ;; done!! 
;;                 (car (isAssignableTo (obj-type obj) (fieldCP-classname fieldcp) s))
;;                 (lookupField (fieldcp-to-field-ptr fieldCP) s))
;;            (jvm::jvp-access-field-guard (field-classname 
;;                                          (lookupField (fieldcp-to-field-ptr
;;                                                        fieldCP) s))
;;                                         (fieldcp-fieldname fieldcp)
;;                                         (java-visible-portion obj))))



(defthm
  consistent-object-and-field-found-in-lookup-implies-jvm-field-access-guard
  (implies (and (consistent-state s)
                (consistent-object obj (heap s) (instance-class-table s))
                (car (isAssignableTo (obj-type obj) (fieldCP-classname fieldcp) s))
                (lookupField (fieldcp-to-field-ptr fieldCP) s))
           (jvm::jvp-access-field-guard (field-classname 
                                         (lookupField (fieldcp-to-field-ptr
                                                       fieldCP) s))
                                        (fieldcp-fieldname fieldcp)
                                        (java-visible-portion obj))))




(defthm consistent-state-field-found-wff-field-rep 
  (implies (and (consistent-state s)
                (lookupField field-ptr s))
           (wff-field (lookupField field-ptr s)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d () (wff-field 
                               consistent-state
                               fields)))))


(defthm reduce-field-ptr-field-name
  (equal (FIELD-PTR-FIELDNAME (FIELDCP-TO-FIELD-PTR FIELDCP))
         (fieldcp-fieldname fieldcp))
  :hints (("Goal" :in-theory (enable fieldcp-fieldname field-ptr-fieldname
                                     make-field-ptr
                                     fieldcp-to-field-ptr))))





(defthm field-ptr-classname-reduce
   (equal (FIELD-PTR-CLASSNAME (FIELDCP-TO-FIELD-PTR FIELDCP))
          (fieldcp-classname fieldcp))
   :hints (("Goal" :in-theory (enable fieldcp-classname
                                      fieldcp-to-field-ptr))))



(defthm field-ptr-fieldname-reduce
  (equal (field-ptr-fieldname (FIELDCP-TO-FIELD-PTR FIELDCP))
         (fieldcp-fieldname fieldcp))
  :hints (("Goal" :in-theory (enable fieldcp-classname fieldcp-to-field-ptr))))


(defthm field-ptr-fieldtype-reduce
  (equal (field-ptr-type (FIELDCP-TO-FIELD-PTR FIELDCP))
         (fieldcp-fieldtype fieldcp))
  :hints (("Goal" :in-theory (enable fieldcp-classname fieldcp-to-field-ptr))))


(in-theory (disable wff-field))






(defthm consistent-state-lookupfield-fail-if-array-type-assignable-into
  (implies (and  (consistent-state s)
                 (isArrayType typ1) 
                 (car (isAssignableTo typ1 (fieldcp-classname fieldcp) s)))
           (not (lookupField (fieldcp-to-field-ptr fieldcp) s)))
  :hints (("Goal" :in-theory (e/d () (consistent-state 
                                      isClassTerm
                                      fieldcp-classname)))))

