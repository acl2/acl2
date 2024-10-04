(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")
(include-book "../../M6-DJVM-shared/jvm-object-type-hierachy")

(local (in-theory (disable consistent-value)))

(defthm consistent-jvp-if-bound-then-consistent-fields
  (implies (and (consistent-jvp type jvp cl hp)
                (bound? classname jvp))
           (consistent-fields (binding classname jvp)
                              (fields (class-by-name classname cl))
                              cl hp))
  :hints (("Goal" :in-theory (e/d (binding bound?)
                                  (fields))
           :do-not '(generalize))))

;;; skip one step so ACL2 will do more work proving the above theorem. two
;;; inductions.


(acl2::set-verify-guards-eagerness 0)
(defun field-decl-with-name (name fields-decls)
  (if (not (consp fields-decls))
      nil
    (if (equal (field-fieldname (car fields-decls)) name)
        (car fields-decls)
      (field-decl-with-name name (cdr fields-decls)))))
(acl2::set-verify-guards-eagerness 2)


(defthm consistent-fields-if-bound-then-binding-consistent-value
  (implies (and (consistent-fields fields fields-decls cl hp)
                (bound? fieldname fields))
           (consistent-value (tag (binding fieldname fields)
                                  (field-fieldtype 
                                   (field-decl-with-name fieldname fields-decls)))
                             (field-fieldtype 
                              (field-decl-with-name fieldname fields-decls))
                             cl hp))
  :hints (("Goal" :in-theory (e/d (binding bound? field-fieldname 
                                           fieldname
                                           fieldvalue)
                                  (fields))
           :do-not '(generalize))))


;; (i-am-here) ;;

;; now we just prove that bound? 

;;(i-am-here) ;; Thu Jun 16 16:59:34 2005


(encapsulate () 
  (local (include-book "base-consistent-state-lookupfield"))
  ;; if field found,  we know fieldname, fieldclass bound in the object!!!
  (local 
   (defthm
     consistent-object-and-field-found-in-lookup-implies-jvm-field-access-guard
     (implies (and (consistent-state s)
                   (consistent-object obj (heap s) (instance-class-table s))
                   (car (isAssignableTo (obj-type obj) (fieldCP-classname fieldcp) s))
                   (lookupField (fieldcp-to-field-ptr fieldCP) s))
              (jvm::jvp-access-field-guard (field-classname 
                                            (lookupField (fieldcp-to-field-ptr
                                                          fieldCP) s))
                                           (FIELDCP-FIELDNAME fieldcp)
                                           (java-visible-portion obj)))))

  (local (in-theory (enable jvm::jvp-access-field-guard)))

  (defthm consistent-object-and-field-found-implies-class-name-bound-in-jvp
     (implies (and (consistent-state s)
                   (consistent-object obj (heap s) (instance-class-table s))
                   (car (isAssignableTo (obj-type obj) (fieldCP-classname fieldcp) s))
                   (lookupField (fieldcp-to-field-ptr fieldCP) s))
              (bound? (field-classname 
                       (lookupField (fieldcp-to-field-ptr
                                     fieldCP) s))
                      (java-visible-portion obj)))
     :hints (("Goal" :in-theory (disable bound? field-classname isAssignableTo
                                         fieldcp-to-field-ptr obj-type
                                         java-visible-portion
                                         consistent-object)
              :use  consistent-object-and-field-found-in-lookup-implies-jvm-field-access-guard)))
                                           
    
  (defthm consistent-object-and-field-found-implies-field-name-bound-in-immediate-instance
     (implies (and (consistent-state s)
                   (consistent-object obj (heap s) (instance-class-table s))
                   (car (isAssignableTo (obj-type obj) (fieldCP-classname fieldcp) s))
                   (lookupField (fieldcp-to-field-ptr fieldCP) s))
              (bound? (fieldcp-fieldname fieldcp)
                      (binding (field-classname
                                (lookupField (fieldcp-to-field-ptr
                                              fieldCP) s))
                               (java-visible-portion obj))))
     :hints (("Goal" :in-theory (disable bound? field-classname isAssignableTo
                                         fieldcp-to-field-ptr
                                         binding
                                         CONSISTENT-OBJECT-AND-FIELD-FOUND-IN-LOOKUP-IMPLIES-JVM-FIELD-ACCESS-GUARD
                                         fieldcp-fieldname
                                         java-visible-portion
                                         consistent-object)
              :use  consistent-object-and-field-found-in-lookup-implies-jvm-field-access-guard))))


(defthm consistent-value-implies-consistent-value-x-b-specific
  (implies (consistent-value (tag v type) type cl hp)
           (consistent-value-x (tag v type) cl hp))
  :hints (("Goal" :use ((:instance CONSISTENT-VALUE-IMPLIES-CONSISTENT-VALUE-X
                                   (v (tag v type)))))))



(defthm consistent-fields-if-bound-then-binding-consistent-value-general
  (implies (and (consistent-fields fields fields-decls cl hp)
                (equal (field-decl-with-name fieldname fields-decls)
                       field-decl)
                (bound? fieldname fields))
           (consistent-value (tag (binding fieldname fields)
                                  (field-fieldtype field-decl))
                             (field-fieldtype field-decl)
                             cl hp))
  :hints (("Goal" :in-theory (e/d ()
                                  (fields
                                   field-decl-with-name
                                   primitive-type?
                                   tag
                                   consistent-value
                                   field-fieldtype
                                   consistent-fields
                                   binding bound? field-fieldname 
                                   fieldname
                                   fieldvalue)))))




(defthm consistent-fields-if-bound-then-binding-consistent-value-general-specific
  (implies (and (consistent-fields (binding name jvp)
                                   (fields (class-by-name name cl)) cl hp)
                (equal (field-decl-with-name 
                        fieldname 
                        (fields (class-by-name name cl)))
                       field-decl)
                (bound? fieldname (binding name jvp)))
           (consistent-value (tag (binding fieldname (binding name jvp))
                                  (field-fieldtype field-decl))
                             (field-fieldtype field-decl)
                             cl hp))
  :hints (("Goal" :in-theory (e/d ()
                                  (fields
                                   field-decl-with-name
                                   primitive-type?
                                   consistent-value
                                   field-fieldtype
                                   consistent-fields
                                   binding bound? field-fieldname 
                                   fieldname
                                   tag
                                   class-by-name
                                   fieldvalue)))))


(defthm consistent-jvp-if-bound-then-consistent-fields-specific
  (implies (and (consistent-jvp (obj-type obj) (java-visible-portion obj) cl hp)
                (bound? classname (java-visible-portion obj)))
           (consistent-fields (binding classname (java-visible-portion obj))
                              (fields (class-by-name classname cl))
                              cl hp))
  :hints (("Goal" :in-theory (e/d ()  (consistent-fields 
                                       binding java-visible-portion
                                       fields)))))



(defthm consistent-object-implies-consistent-jvp
  (implies (and (consistent-object obj hp cl)
                (not (isArrayType (obj-type obj))))
           (CONSISTENT-JVP (OBJ-TYPE obj)
                           (JAVA-VISIBLE-PORTION obj)
                           cl hp)))



;; (include-book "base-consistent-state")
;;
;;
;; Don't really want to depend on 
;;                   base-consistent-state.lisp
;;
;; but maybe we should 
;; 
;; base-consistent-state is no longer clean. 
;; 
;;

(local 
 (defthm binding-rREF-normalize
   (equal (binding (rREF v) hp)
          (deref2 v hp))
   :hints (("Goal" :in-theory (enable deref2)))))


(defthm consistent-heap1-implies-if-bound-then-consistent-object
  (implies (and (consistent-heap1 hp1 hp cl id)
                (bound? v hp1))
           (consistent-object (binding v hp1) hp cl))
  :hints (("Goal" :in-theory (e/d () (consistent-object)))))
  

(defthm consistent-state-consistent-heap1
  (implies (consistent-state s)
           (consistent-heap1 (heap s) 
                             (heap s)
                             (instance-class-table s)
                             0))
  :hints (("Goal" :in-theory (enable consistent-state 
                                     consistent-heap)))
  :rule-classes :forward-chaining)


(defthm consistent-state-REFp-not-NULLp-implies-consistent-object
  (implies (and (consistent-state s)
                (REFp v (heap s))
                (not (NULLp v)))
           (consistent-object (deref2 v (heap s))
                              (heap s)
                              (instance-class-table s)))
  :hints (("Goal" :in-theory (e/d (deref2)
                                  (binding-rREF-normalize
                                   binding bound?
                                   consistent-object)))))

;;; Mon Jun 13 14:56:51 2005



(defthm searchFields-implies-equal-field-classname-equal
  (implies (searchFields field-ptr fields)
           (equal (field-classname (searchFields field-ptr fields))
                  (field-ptr-classname field-ptr))))



(local 
  (defthm field-fieldname-search-fields
    (implies (searchfields field-ptr fields)
             (equal (field-fieldname (searchfields field-ptr fields))
                    (field-ptr-fieldname field-ptr)))))



(defthm field-fieldname-reduce
  (implies (LOOKUPFIELD field-ptr s)
           (equal (FIELD-FIELDNAME (LOOKUPFIELD field-ptr s))
                  (field-ptr-fieldname field-ptr)))
  :hints (("Goal" :in-theory (e/d (lookupfield) (LOOKUPFIELD-INV
                                                 searchfields 
                                                 fields
                                                 consistent-state
                                                 field-fieldname 
                                                 isClassTerm
                                                 superclass-no-loop))
           :do-not '(generalize))))

;;;
;;; we know fields from a consistent-class-decl is all from a same class So
;;; searchfields will return the same results as just looking for fieldnames!!
;;;


;; (acl2::set-verify-guards-eagerness 0)

;; (defun fields-all-from-class (field-decls classname)
;;   (if (endp field-decls) t
;;     (and (equal (field-fieldname (car field-decls)) classname)
;;          (fields-all-from-class (cdr field-decls)
;;                                 classname))))
;; (acl2::set-verify-guards-eagerness 2)

;; (i-am-here) 
(local (in-theory (disable JVM::WFF-FIELDS-X-EQUAL-WFF-CLASS-FIELDS)))

(defthm not-mem-not-searchfields
  (implies (not (mem (field-ptr-fieldname field-ptr)
                     (COLLECT-FIELD-NAMES FIELD-DECLS)))
           (not (searchfields field-ptr field-decls))))


(defthm field-decl-with-name-is-searchfield-if-fields-from-the-same-class
  (implies  (and (SEARCHFIELDS FIELD-PTR  FIELD-decls)
                 (nodup-set (collect-field-names field-decls)))
            (EQUAL (FIELD-DECL-WITH-NAME  (FIELD-PTR-FIELDNAME FIELD-PTR)
                                          field-decls)
                   (SEARCHFIELDS FIELD-PTR  field-decls)))
  :hints (("Goal" 
           :in-theory (disable field-fieldname)
           :do-not '(generalize))))


;;; need to assert that when name is equal, type is equal!!! 
;;; otherwise searchfields will not return the same result as
;;; field-decl-with-name returns!! 
;;;
;;; However our object representation depends on this!!  need to add the
;;; assertion into the wff-static-class-rep!!
;;;
;;; good way is to assert that there is no duplicate in name. 
;;;
;;; Mon Jun 13 15:39:16 2005




(defthm field-decl-with-name-equal-lookupfield-lemma
  (implies (and (lookupfield field-ptr s)
                (nodup-set (collect-field-names 
                            (fields (class-by-name 
                                     (field-classname (lookupfield field-ptr s))
                                     (instance-class-table s))))))
           (EQUAL
            (FIELD-DECL-WITH-NAME
             (field-ptr-fieldname field-ptr)
             (FIELDS (CLASS-BY-NAME
                      (FIELD-CLASSNAME (LOOKUPFIELD field-ptr s))
                      (INSTANCE-CLASS-TABLE S))))
            (LOOKUPFIELD field-ptr s)))
  :hints (("Goal" :in-theory (e/d ()(LOOKUPFIELD-INV
                                     searchfields 
                                     fields
                                     field-classname
                                     consistent-state
                                     field-fieldname 
                                     isClassTerm
                                     superclass-no-loop))
           :do-not '(generalize))))
                                  


(defthm class-loaded-from-wff-static-class-rep
  (implies (and (class-is-loaded-from-helper class-rep
                                             class-rep-static)
                (WFF-CLASS-REP-STATIC-STRONG  class-rep-static))
           (nodup-set (collect-field-names (fields class-rep))))
  :hints (("Goal" :in-theory (e/d ()  (nodup-set fields fields-s
                                                 NODUP-SET-FIELDS-S-NODUP-SET-FIELDS
                                                 RUNTIME-INSTANCE-FIELDS-REP))
           :use ((:instance nodup-set-fields-s-nodup-set-fields
                            (fields-s (fields-s class-rep-static))
                            (classname (classname class-rep)))))))




(local 
 (defthm if-exists-then-loaded-from-some-class-file
   (implies (and (class-by-name name cl) 
                 (class-table-is-loaded-from cl scl))
            (class-is-loaded-from-helper 
             (class-by-name name cl)
             (mv-nth 1 (class-by-name-s name scl))))))

;;; used force!! 

(local 
 (defthm consistent-state-implies-wff-static-class-table-strong
   (implies (consistent-state s)
            (wff-static-class-table-strong (env-class-table (env s))))
   :hints (("Goal" :in-theory (enable consistent-state)))))




(local 
 (defthm consistent-state-implies-class-table-is-loaded-from
   (implies (consistent-state s)
            (class-table-is-loaded-from (instance-class-table s)
                                        (env-class-table (env s))))
   :hints (("Goal" :in-theory (enable consistent-state)))))


           
(defthm searchfields-implies-class-by-name-classname-found
  (implies (not (class-by-name name cl))
           (not (searchfields field-ptr (fields (class-by-name name cl))))))


(defthm lookupfield-implies-class-by-name-classname-found
  (implies (lookupfield field-ptr s)
           (class-by-name (field-classname (lookupfield field-ptr s))
                          (instance-class-table s)))
  :hints (("Goal" :in-theory (disable field-classname)
           :do-not '(generalize))))



;; (local 
;;  (defthm if-exists-then-loaded-from-some-class-file
;;    (implies (and (class-by-name name cl) 
;;                  (class-table-is-loaded-from cl scl))
;;             (class-is-loaded-from-helper 
;;              (class-by-name name cl)
;;              (mv-nth 1 (class-by-name-s name scl))))))


;;; put it together!! 


(local 
 (defthm
   wff-static-class-table-strong-implies-exists-implies-wff-static-class-rep-strong
   (implies (and (wff-static-class-table-strong scl)
                 (car (class-by-name-s name scl)))
            (wff-class-rep-static-strong (mv-nth 1 (class-by-name-s name
                                                                    scl))))
   :hints (("Goal" :in-theory (e/d () (wff-class-rep-static-strong))))))

(local 
 (defthm if-class-loaded-from-implies-car-class-by-name-s
   (implies (and (class-is-loaded-from-helper class-rep
                                              (mv-nth 1 (class-by-name-s name
                                                                         scl)))
                 (stringp (classname class-rep)))
            (car (class-by-name-s name scl)))
   :hints (("Goal" :in-theory (enable isInterface)))))




(local 
 (defthm if-class-loaded-from-implies-car-class-by-name-s-specific
   (implies (and (class-is-loaded-from-helper (class-by-name name
                                                             (instance-class-table s))
                                              (mv-nth 1 (class-by-name-s name
                                                                         (env-class-table (env s)))))
                 (stringp (classname (class-by-name name (instance-class-table s)))))
            (car (class-by-name-s name (env-class-table (env s)))))
   :hints (("Goal" :in-theory (e/d () (class-by-name-s class-is-loaded-from-helper))))))



(encapsulate () 
  (local (include-book "base-consistent-state-class-names-are-string"))
  (defthm consistent-state-class-name-is-stringp
    (implies (and (class-by-name name (instance-class-table s))
                  (consistent-state s))
             (stringp name))
    :rule-classes :forward-chaining))


(defthm classname-class-by-name-is-name
  (implies (isClassTerm (class-by-name name cl))
           (equal (classname (class-by-name name cl))
                  name)))

(local 
 (defthm wff-instance-class-table-implies-isClassTerm-equiv
   (implies (wff-instance-class-table cl)
            (iff (isClassTerm (class-by-name name cl))
                 (class-by-name name cl)))
   :hints (("Goal" :in-theory (e/d (wff-class-rep isClassTerm) ())))))


(defthm field-decl-with-name-equal-lookupfield
  (implies (and (lookupfield field-ptr s)
                (consistent-state s))
           (EQUAL
            (FIELD-DECL-WITH-NAME
             (field-ptr-fieldname field-ptr)
             (FIELDS (CLASS-BY-NAME
                      (FIELD-CLASSNAME (LOOKUPFIELD field-ptr s))
                      (INSTANCE-CLASS-TABLE S))))
            (LOOKUPFIELD field-ptr s)))
  :hints (("Goal" :in-theory (e/d ()(LOOKUPFIELD-INV
                                     searchfields 
                                     fields
                                     field-classname
                                     consistent-state
                                     WFF-CLASS-REP-STATIC-STRONG
                                     field-fieldname 
                                     lookupfield
                                     class-is-loaded-from-helper
                                     isClassTerm
                                     superclass-no-loop))
           :do-not '(generalize)
           :use ((:instance class-loaded-from-wff-static-class-rep
                            (class-rep (class-by-name 
                                        (field-classname 
                                         (lookupfield field-ptr s))
                                        (instance-class-table s)))
                            (class-rep-static 
                             (mv-nth 1 (class-by-name-s 
                                        (field-classname 
                                         (lookupfield field-ptr s))
                                        (env-class-table (env s))))))
                 (:instance consistent-state-class-name-is-stringp
                            (name (field-classname (lookupfield field-ptr s))))))))


(defthm field-ptr-fieldname-fieldcp-to-field-ptr
  (equal (field-ptr-fieldname (fieldcp-to-field-ptr fieldcp))
         (fieldcp-fieldname fieldcp))
  :hints (("Goal" :in-theory (enable field-ptr-fieldname
                                     make-field-ptr
                                     fieldcp-to-field-ptr))))

                                        

(defthm field-decl-with-name-equal-lookupfield-specific
  (implies (and (lookupfield (fieldcp-to-field-ptr fieldcp) s)
                (consistent-state s))
           (EQUAL
            (FIELD-DECL-WITH-NAME
             (fieldcp-fieldname fieldcp)
             (FIELDS (CLASS-BY-NAME
                      (FIELD-CLASSNAME (LOOKUPFIELD (fieldcp-to-field-ptr fieldcp) s))
                      (INSTANCE-CLASS-TABLE S))))
            (LOOKUPFIELD (fieldcp-to-field-ptr fieldcp) s)))
  :hints (("Goal" :in-theory (e/d ()(LOOKUPFIELD-INV
                                     searchfields 
                                     fields
                                     field-classname
                                     consistent-state
                                     fieldcp-fieldname
                                     WFF-CLASS-REP-STATIC-STRONG
                                     field-fieldname 
                                     fieldcp-to-field-ptr
                                     lookupfield
                                     class-is-loaded-from-helper
                                     isClassTerm
                                     superclass-no-loop))
           :do-not '(generalize)
           :use ((:instance field-decl-with-name-equal-lookupfield
                            (field-ptr (fieldcp-to-field-ptr fieldcp)))))))





(defthm consistent-object-consistent-state-m6-getfield-consistent-value-x-lemma
  (implies (and (consistent-state s)
                (car (isAssignableTo (obj-type (deref2 v (heap s)))
                                     (fieldcp-classname fieldCP)
                                     s))
                (not (isArrayType (obj-type (deref2 v (heap s)))))
                (REFp v (heap s))
                (lookupField (fieldcp-to-field-ptr fieldCP) s)
                (not (NULLp v)))
           (CONSISTENT-VALUE-X
            (TAG (M6-GETFIELD
                  (FIELD-CLASSNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp)
                                                S))
                  (fieldcp-fieldname fieldcp)
                  (RREF v)
                  S)
                 (FIELD-FIELDTYPE (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp)
                                                S)))
            (INSTANCE-CLASS-TABLE S)
            (HEAP S)))
  :hints (("Goal" :in-theory (disable consistent-value-x
                                      consistent-value
                                      isAssignableTo
                                      REFp NULLp
                                      deref2
                                      rREF
                                      fields
                                      fieldcp-fieldname
                                      java-visible-portion
                                      fieldcp-to-field-ptr
                                      fieldcp-classname
                                      field-classname
                                      field-fieldname
                                      field-fieldtype
                                      tag binding bound?
                                      isArrayType obj-type
                                      lookupfield))))


;;
;;
;; (defthm consistent-jvp-if-bound-then-consistent-fields
;;   (implies (and (consistent-jvp type jvp cl hp)
;;                 (bound? classname jvp))
;;            (consistent-fields (binding classname jvp)
;;                               (fields (class-by-name classname cl))
;;                               cl hp))
;;   :hints (("Goal" :in-theory (e/d (binding bound?)
;;                                   (fields))

;;            :do-not '(generalize))))


(defthm consistent-jvp-if-bound-then-consistent-fields-more-specific
  (implies (and (consistent-jvp classname jvp cl hp)
                (bound? classname jvp))
           (consistent-fields (binding classname jvp)
                              (fields (class-by-name classname cl))
                              cl hp))
  :hints (("Goal" :in-theory (e/d (binding bound?)
                                  (fields))
           :do-not '(generalize))))




;; (defthm isArrayType-implies-consistent-array-object
;;   (implies (and (consistent-state s)
;;                 (not (NULLp v))
;;                 (REFp v (heap s))
;;                 (isArrayType (obj-type (deref2 v (heap s)))))
;;            (consistent-array-object (deref2 v (heap s))
;;                                     (heap s) (instance-class-table s)
;;                                     (array-class-table s)))
;;   :hints (("Goal" :in-theory (e/d (consistent-state consistent-heap consistent-heap)
;;                                   (consistent-array-object nullp)))))


(defthm consistent-heap2-implies-isArrayType-is-consistent-array-object
  (implies (and (consistent-heap2 hp1 hp cl acl id)
                (isArrayType (obj-type (binding v hp1))))
           (consistent-array-object (binding v hp1) hp cl acl))
  :hints (("Goal" :in-theory (disable consistent-array-object))))

(defthm isArrayType-implies-consistent-array-object-strong
  (implies (and (consistent-state s)
                (isArrayType (obj-type (deref2 v (heap s)))))
           (consistent-array-object (deref2 v (heap s))
                                    (heap s) (instance-class-table s)
                                    (array-class-table s)))
  :hints (("Goal" :in-theory (e/d (consistent-state 
                                   deref2 
                                   consistent-heap consistent-heap)
                                  (consistent-array-object
                                   binding-rREF-normalize
                                   obj-type
                                   binding
                                   nullp))
           :use ((:instance
                  consistent-heap2-implies-isArrayType-is-consistent-array-object
                  (hp1 (heap s)) 
                  (hp (heap s))
                  (cl (instance-class-table s))
                  (acl (array-class-table s))
                  (id 0))))))


;;(i-am-here) ;; Fri Jul 15 01:47:01 2005

(defthm consistent-array-object-implies-consistent-jvp-java-lang-Object
  (implies (consistent-array-object obj hp cl acl)
           (consistent-jvp "java.lang.Object" (java-visible-portion obj) cl
                           hp))
  :hints (("Goal" :in-theory (enable consistent-array-object))))

(local (in-theory (enable consistent-array-object)))

(defthm consistent-jvp-impies-bound
  (implies (consistent-jvp type jvp cl hp)
           (bound? type jvp)))



(defthm consistent-array-object-implies-consistent-jvp-java-lang-Object-specific
  (implies (consistent-array-object obj (heap s) (instance-class-table s)
                                    (array-class-table s))
           (consistent-jvp "java.lang.Object" (java-visible-portion obj)
                           (instance-class-table s)
                           (heap s))))


(local (include-book "base-bind-free"))

(local 
 (defthm consistent-array-object-bound-java-lang-Object-specific
   (implies (and (bind-free (acl2::default-bind-free 's 's (acl2::pkg-witness "DJVM")))
                 (consistent-array-object obj (heap s) (instance-class-table s) 
                                          (array-class-table s)))
            (bound? "java.lang.Object" (java-visible-portion obj)))
   :hints (("Goal" :in-theory (disable bound? consistent-jvp)))))


;; (i-am-here) ;; 

(encapsulate () 
  (local (include-book "base-consistent-state-lookupfield-support"))
  (defthm java-lang-Object-lookup-field-if-found-then-found-in-java-lang-Object
    (implies (and (consistent-state s)
                  (EQUAL (FIELDCP-CLASSNAME FIELDCP)
                         "java.lang.Object")
                  (lookupField (FIELDCP-TO-FIELD-PTR FIELDCP) s))
             (EQUAL (FIELD-CLASSNAME (lookupField (FIELDCP-TO-FIELD-PTR FIELDCP) s))
                    "java.lang.Object"))
    :hints (("Goal" :in-theory (e/d () (consistent-state))))))


(defthm field-decl-with-name-equal-lookupfield-specific-general
  (implies (and (lookupfield (fieldcp-to-field-ptr fieldcp) s)
                (equal (FIELD-CLASSNAME (LOOKUPFIELD (fieldcp-to-field-ptr
                                                      fieldcp) s))
                       classname)
                (consistent-state s))
           (EQUAL
            (FIELD-DECL-WITH-NAME
             (fieldcp-fieldname fieldcp)
             (FIELDS (CLASS-BY-NAME
                      classname
                      (INSTANCE-CLASS-TABLE S))))
            (LOOKUPFIELD (fieldcp-to-field-ptr fieldcp) s)))
  :hints (("Goal" :in-theory (e/d ()(LOOKUPFIELD-INV
                                     searchfields 
                                     fields
                                     field-classname
                                     consistent-state
                                     fieldcp-fieldname
                                     WFF-CLASS-REP-STATIC-STRONG
                                     field-fieldname 
                                     fieldcp-to-field-ptr
                                     lookupfield
                                     class-is-loaded-from-helper
                                     isClassTerm
                                     superclass-no-loop))
           :do-not '(generalize)
           :use ((:instance field-decl-with-name-equal-lookupfield
                            (field-ptr (fieldcp-to-field-ptr fieldcp)))))))


    
(defthm consistent-object-and-field-found-implies-field-name-bound-in-immediate-instance-general
   (implies (and (consistent-state s)
                 (consistent-object obj (heap s) (instance-class-table s))
                 (or (not (isArrayType (obj-type obj)))
                     (and (equal (fieldcp-classname fieldcp)
                                 "java.lang.Object")
                          (consistent-array-object obj (heap s)
                                                   (instance-class-table s)
                                                   (array-class-table s))))
                 (equal (field-classname
                         (lookupField (fieldcp-to-field-ptr
                                       fieldCP) s)) classname)
                 (car (isAssignableTo (obj-type obj) (fieldCP-classname fieldcp) s))
                 (lookupField (fieldcp-to-field-ptr fieldCP) s))
            (bound? (fieldcp-fieldname fieldcp)
                    (binding classname
                             (java-visible-portion obj))))
   :hints (("Goal" :in-theory (disable bound? field-classname isAssignableTo
                                       fieldcp-to-field-ptr
                                       binding
                                       fieldcp-fieldname
                                       java-visible-portion
                                       consistent-object)
            :use  consistent-object-and-field-found-implies-field-name-bound-in-immediate-instance)))





(defthm consistent-object-consistent-state-m6-getfield-consistent-value-x-lemma-2
  (implies (and (consistent-state s)
                (car (isAssignableTo (obj-type (deref2 v (heap s)))
                                     (fieldcp-classname fieldCP)
                                     s))
                (isArrayType (obj-type (deref2 v (heap s))))
                (equal (fieldcp-classname fieldcp) "java.lang.Object")
                (REFp v (heap s))
                (lookupField (fieldcp-to-field-ptr fieldCP) s)
                (not (NULLp v)))
           (CONSISTENT-VALUE-X
            (TAG (M6-GETFIELD 
                  "java.lang.Object"
                  (fieldcp-fieldname fieldcp)
                  (RREF v)
                  S)
                 (FIELD-FIELDTYPE (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp)
                                                S)))
            (INSTANCE-CLASS-TABLE S)
            (HEAP S)))
  :hints (("Goal" :in-theory (disable consistent-value-x
                                      consistent-value
                                      isAssignableTo
                                      REFp NULLp
                                      deref2
                                      rREF
                                      fields
                                      fieldcp-fieldname
                                      java-visible-portion
                                      fieldcp-to-field-ptr
                                      fieldcp-classname
                                      field-classname
                                      field-fieldname
                                      field-fieldtype
                                      tag binding bound?
                                      isArrayType obj-type
                                      lookupfield))))




(encapsulate () 
  (local (include-book "base-lookupfield-fieldname-normalize"))
  (defthm field-fieldtype-reduce
    (implies (LOOKUPFIELD field-ptr s)
             (equal (FIELD-FIELDTYPE (LOOKUPFIELD field-ptr s))
                    (field-ptr-type field-ptr)))
    :hints (("Goal" :in-theory (e/d (lookupfield) (LOOKUPFIELD-INV
                                                   searchfields 
                                                   fields
                                                   field-fieldtype
                                                   isClassTerm
                                                   superclass-no-loop))
             :do-not '(generalize)))))

(defthm field-ptr-type-fieldcp-to-ptr
  (equal (field-ptr-type (fieldcp-to-field-ptr fieldcp))
         (fieldcp-fieldtype fieldcp))
  :hints (("Goal" :in-theory (enable fieldcp-to-field-ptr fieldcp-to-field-ptr
                                     make-field-ptr
                                     field-ptr-type))))


(defthm consistent-object-consistent-state-m6-getfield-consistent-value-x-weak
   (implies (and (consistent-state s)
                (car (isAssignableTo (obj-type (deref2 v (heap s)))
                                     (fieldcp-classname fieldCP)
                                     s))
                (or (not (isArrayType (obj-type (deref2 v (heap s)))))
                    (equal (fieldcp-classname fieldcp) "java.lang.Object"))
                (REFp v (heap s))
                (equal (FIELD-CLASSNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp)
                                                     S))
                       classname)
                (lookupField (fieldcp-to-field-ptr fieldCP) s)
                (not (NULLp v)))
           (CONSISTENT-VALUE-X
            (TAG (M6-GETFIELD classname
                  (fieldcp-fieldname fieldcp)
                  (RREF v)
                  S)
                 (fieldcp-fieldtype fieldcp))
            (INSTANCE-CLASS-TABLE S)
            (HEAP S)))
  :hints (("Goal" :in-theory (disable consistent-value-x
                                      consistent-value
                                      lookupfield
                                      isAssignableTo
                                      REFp NULLp
                                      deref2
                                      rREF
                                      fields
                                      fieldcp-fieldname
                                      java-visible-portion
                                      fieldcp-to-field-ptr
                                      fieldcp-classname
                                      field-classname
                                      field-fieldname
                                      field-fieldtype
                                      tag binding bound?
                                      isArrayType obj-type
                                      lookupfield)
          :use ((:instance
                 consistent-object-consistent-state-m6-getfield-consistent-value-x-lemma)
                (:instance
                 consistent-object-consistent-state-m6-getfield-consistent-value-x-lemma-2)))))



;----------------------------------------------------------------------

(encapsulate ()
 (local (include-book "base-consistent-state-lookupfield-support"))
 (defthm consistent-state-lookupfield-fail-if-array-type-assignable-into
          (implies (and  (consistent-state s)
                 (isArrayType typ1) 
                 (car (isAssignableTo typ1 (fieldcp-classname fieldcp) s)))
           (not (lookupField (fieldcp-to-field-ptr fieldcp) s)))
  :hints (("Goal" :in-theory (e/d () (consistent-state 
                                      isClassTerm
                                      fieldcp-classname))))))




(defthm consistent-object-consistent-state-m6-getfield-consistent-value-x
   (implies (and (consistent-state s)
                (car (isAssignableTo (obj-type (deref2 v (heap s)))
                                     (fieldcp-classname fieldCP)
                                     s))
                (REFp v (heap s))
                (equal (FIELD-CLASSNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp)
                                                     S))
                       classname)
                (lookupField (fieldcp-to-field-ptr fieldCP) s)
                (not (NULLp v)))
           (CONSISTENT-VALUE-X
            (TAG (M6-GETFIELD classname
                  (fieldcp-fieldname fieldcp)
                  (RREF v)
                  S)
                 (fieldcp-fieldtype fieldcp))
            (INSTANCE-CLASS-TABLE S)
            (HEAP S)))
  :hints (("Goal" :in-theory (disable consistent-value-x
                                      consistent-value
                                      lookupfield
                                      consistent-array-object
                                      isAssignableTo
                                      REFp NULLp
                                      deref2
                                      rREF
                                      fields
                                      fieldcp-fieldname
                                      java-visible-portion
                                      fieldcp-to-field-ptr
                                      fieldcp-classname
                                      field-classname
                                      field-fieldname
                                      field-fieldtype
                                      tag binding bound?
                                      isArrayType obj-type
                                      lookupfield)
           :cases ((isArrayType (obj-type (deref2 v (heap s))))))
          ("Subgoal 2" :use consistent-object-consistent-state-m6-getfield-consistent-value-x-weak)))
           


;----------------------------------------------------------------------

; continue to prove some results here? Thu Jul 21 19:01:19 2005
;
; We really want to conclude that consistent-value, not only the
; consistent-value-x!! 
;
; needed in base-m6-getfield-consistent-value.lisp! 



;; (defthm consistent-jvp-if-bound-then-consistent-fields-specific
;;   (implies (and (consistent-jvp (obj-type obj) (java-visible-portion obj) cl hp)
;;                 (bound? classname (java-visible-portion obj)))
;;            (consistent-fields (binding classname (java-visible-portion obj))
;;                               (fields (class-by-name classname cl))
;;                               cl hp))
;;   :hints (("Goal" :in-theory (e/d ()  (consistent-fields 
;;                                        binding java-visible-portion
;;                                        fields)))))



;; (defthm consistent-object-implies-consistent-jvp
;;   (implies (and (consistent-object obj hp cl)
;;                 (not (isArrayType (obj-type obj))))
;;            (CONSISTENT-JVP (OBJ-TYPE obj)
;;                            (JAVA-VISIBLE-PORTION obj)
;;                            cl hp)))




;; (defthm consistent-fields-if-bound-then-binding-consistent-value-general-specific
;;   (implies (and (consistent-fields (binding name jvp)
;;                                    (fields (class-by-name name cl)) cl hp)
;;                 (equal (field-decl-with-name 
;;                         fieldname 
;;                         (fields (class-by-name name cl)))
;;                        field-decl)
;;                 (bound? fieldname (binding name jvp)))
;;            (consistent-value (tag (binding fieldname (binding name jvp))
;;                                   (field-fieldtype field-decl))
;;                              (field-fieldtype field-decl)
;;                              cl hp))
;;   :hints (("Goal" :in-theory (e/d ()
;;                                   (fields
;;                                    field-decl-with-name
;;                                    primitive-type?
;;                                    consistent-value
;;                                    field-fieldtype
;;                                    consistent-fields
;;                                    binding bound? field-fieldname 
;;                                    fieldname
;;                                    tag
;;                                    class-by-name
;;                                    fieldvalue)))))

(local 
  (defthm consistent-object-bound-field-implies-consistent-value
    (implies (and (consistent-object obj hp cl)
                (not (isArrayType (obj-type obj)))
                (bound? classname (java-visible-portion obj))
                (bound? fieldname (binding classname
                                           (java-visible-portion obj)))
                (equal (field-decl-with-name
                        fieldname  
                        (fields
                         (class-by-name classname cl))) field-decl))
           (consistent-value (tag (binding fieldname (binding classname 
                                                              (java-visible-portion obj)))
                                  (field-fieldtype field-decl))
                             (field-fieldtype field-decl)
                             cl hp))
  :hints (("Goal" :in-theory (disable consistent-value 
                                      obj-type binding bound?
                                      field-fieldtype
                                      fields tag isArrayType
                                      java-visible-portion
                                      consistent-object)))))
                                                    


;; (encapsulate () 
;;   (local (include-book "base-lookupfield-fieldname-normalize"))
;;   (defthm field-fieldtype-reduce
;;     (implies (LOOKUPFIELD field-ptr s)
;;              (equal (FIELD-FIELDTYPE (LOOKUPFIELD field-ptr s))
;;                     (field-ptr-type field-ptr)))
;;     :hints (("Goal" :in-theory (e/d (lookupfield) (LOOKUPFIELD-INV
;;                                                    searchfields 
;;                                                    fields
;;                                                    field-fieldtype
;;                                                    isClassTerm
;;                                                    superclass-no-loop))
;;              :do-not '(generalize)))))

;; (defthm field-ptr-type-fieldcp-to-ptr
;;   (equal (field-ptr-type (fieldcp-to-field-ptr fieldcp))
;;          (fieldcp-fieldtype fieldcp))
;;   :hints (("Goal" :in-theory (enable fieldcp-to-field-ptr fieldcp-to-field-ptr
;;                                      make-field-ptr
;;                                      field-ptr-type))))

;; (defthm field-decl-with-name-equal-lookupfield-specific-general
;;   (implies (and (lookupfield (fieldcp-to-field-ptr fieldcp) s)
;;                 (equal (FIELD-CLASSNAME (LOOKUPFIELD (fieldcp-to-field-ptr
;;                                                       fieldcp) s))
;;                        classname)
;;                 (consistent-state s))
;;            (EQUAL
;;             (FIELD-DECL-WITH-NAME
;;              (fieldcp-fieldname fieldcp)
;;              (FIELDS (CLASS-BY-NAME
;;                       classname
;;                       (INSTANCE-CLASS-TABLE S))))
;;             (LOOKUPFIELD (fieldcp-to-field-ptr fieldcp) s)))
;;   :hints (("Goal" :in-theory (e/d ()(LOOKUPFIELD-INV
;;                                      searchfields 
;;                                      fields
;;                                      field-classname
;;                                      consistent-state
;;                                      fieldcp-fieldname
;;                                      WFF-CLASS-REP-STATIC-STRONG
;;                                      field-fieldname 
;;                                      fieldcp-to-field-ptr
;;                                      lookupfield
;;                                      class-is-loaded-from-helper
;;                                      isClassTerm
;;                                      superclass-no-loop))
;;            :do-not '(generalize)
;;            :use ((:instance field-decl-with-name-equal-lookupfield
;;                             (field-ptr (fieldcp-to-field-ptr fieldcp)))))))


(local 
 (defthm consistent-object-bound-field-implies-consistent-value-specific
  (implies (and (consistent-object obj (heap s) (instance-class-table s))
                (not (isArrayType (obj-type obj)))
                (bound? (field-classname
                         (lookupfield (fieldcp-to-field-ptr fieldcp) s))
                        (java-visible-portion obj))
                (bound? (fieldcp-fieldname fieldcp)
                        (binding (field-classname
                                            (lookupfield (fieldcp-to-field-ptr fieldcp) s))
                                           (java-visible-portion obj)))
                (lookupfield (fieldcp-to-field-ptr fieldcp) s)
                (consistent-state s))
           (consistent-value (tag (binding (fieldcp-fieldname fieldcp)
                                           (binding (field-classname 
                                                               (lookupfield
                                                                (fieldcp-to-field-ptr 
                                                                 fieldcp) s))
                                                              (java-visible-portion obj)))
                                  (fieldcp-fieldtype fieldcp))
                             (fieldcp-fieldtype fieldcp)
                             (instance-class-table s)
                             (heap s)))
  :hints (("Goal" :in-theory (disable consistent-value 
                                      obj-type binding bound?
                                      field-fieldtype
                                      fieldcp-fieldname
                                      field-classname
                                      fieldcp-to-field-ptr
                                      fieldcp-fieldtype
                                      consistent-object-bound-field-implies-consistent-value
                                      fields tag isArrayType
                                      java-visible-portion
                                      consistent-object)
           :use ((:instance
                  consistent-object-bound-field-implies-consistent-value
                  (classname (field-classname (lookupfield
                                               (fieldcp-to-field-ptr 
                                                fieldcp) s)))
                  (field-decl (lookupfield (fieldcp-to-field-ptr fieldcp) s))
                  (cl (instance-class-table s))
                  (hp (heap s))
                  (fieldname (fieldcp-fieldname fieldcp))))))))
                                                    


    
;; (defthm consistent-object-and-field-found-implies-field-name-bound-in-immediate-instance
;;    (implies (and (consistent-state s)
;;                  (consistent-object obj (heap s) (instance-class-table s))
;;                  (car (isAssignableTo (obj-type obj) (fieldCP-classname fieldcp) s))
;;                  (lookupField (fieldcp-to-field-ptr fieldCP) s))
;;             (bound? (fieldcp-fieldname fieldcp)
;;                     (binding (field-classname
;;                               (lookupField (fieldcp-to-field-ptr
;;                                             fieldCP) s))
;;                              (java-visible-portion obj))))
;;    :hints (("Goal" :in-theory (disable bound? field-classname isAssignableTo
;;                                        fieldcp-to-field-ptr
;;                                        binding
;;                                        CONSISTENT-OBJECT-AND-FIELD-FOUND-IN-LOOKUP-IMPLIES-JVM-FIELD-ACCESS-GUARD
;;                                        fieldcp-fieldname
;;                                        java-visible-portion
;;                                        consistent-object)
;;             :use  consistent-object-and-field-found-in-lookup-implies-jvm-field-access-guard))))


(local 
 (defthm bound-in-binding-implies-bound
   (implies (not (bound? name jvp))
            (not (bound? fieldname (binding name jvp))))))
                 
(local 
 (defthm consistent-object-bound-field-implies-consistent-value-specific-simplify
  (implies (and (consistent-object obj (heap s) (instance-class-table s))
                (not (isArrayType (obj-type obj)))
                (car (isAssignableTo (obj-type obj) (fieldcp-classname fieldcp) s))
                (lookupfield (fieldcp-to-field-ptr fieldcp) s)
                (consistent-state s))
           (consistent-value (tag (binding (fieldcp-fieldname fieldcp)
                                           (binding (field-classname 
                                                               (lookupfield
                                                                (fieldcp-to-field-ptr 
                                                                 fieldcp) s))
                                                              (java-visible-portion obj)))
                                  (fieldcp-fieldtype fieldcp))
                             (fieldcp-fieldtype fieldcp)
                             (instance-class-table s)
                             (heap s)))
  :hints (("Goal" :in-theory (disable consistent-value 
                                      obj-type binding bound?
                                      field-fieldtype
                                      fieldcp-fieldname
                                      field-classname
                                      fieldcp-to-field-ptr
                                      fieldcp-fieldtype
                                      consistent-object-bound-field-implies-consistent-value
                                      fields tag isArrayType
                                      java-visible-portion
                                      consistent-object)))))


(defthm consistent-object-consistent-state-m6-getfield-consistent-value
   (implies (and (consistent-state s)
                 (car (isAssignableTo (obj-type (deref2 v (heap s)))
                                      (fieldcp-classname fieldCP)
                                      s))
                 (REFp v (heap s))
                 (equal (FIELD-CLASSNAME (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp)
                                                      S))
                        classname)
                 (lookupField (fieldcp-to-field-ptr fieldCP) s)
                 (not (NULLp v)))
            (CONSISTENT-VALUE
             (TAG (M6-GETFIELD classname
                               (fieldcp-fieldname fieldcp)
                               (RREF v)
                               S)
                  (fieldcp-fieldtype fieldcp))
             (fieldcp-fieldtype fieldcp)
             (INSTANCE-CLASS-TABLE S)
             (HEAP S)))
   :hints (("Goal" :in-theory (disable consistent-value-x
                                      consistent-value
                                      lookupfield
                                      fieldcp-fieldtype
                                      consistent-array-object
                                      isAssignableTo
                                      REFp NULLp
                                      deref2
                                      rREF
                                      obj-type
                                      fields
                                      fieldcp-fieldname
                                      java-visible-portion
                                      fieldcp-to-field-ptr
                                      fieldcp-classname
                                      field-classname
                                      field-fieldname
                                      field-fieldtype
                                      tag binding bound?
                                      isArrayType obj-type
                                      lookupfield)
            :cases ((isArrayType (obj-type (deref2 v (heap s))))))))



