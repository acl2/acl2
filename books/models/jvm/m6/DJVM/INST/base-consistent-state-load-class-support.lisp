(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")
(include-book "../../M6-DJVM-shared/jvm-bytecode")



(local (include-book "base-loader-preserve-consistent-state"))
(local (include-book "base-consistent-state-make-state"))

(local 
 (defthm consistent-heap-array-init-state3-adding-new-obj
   (implies (and (consistent-heap-array-init-state3 hp hp-init)
                 (not (bound? ref hp-init))
                 (wff-internal-array obj)
                 (or (primitive-type? (array-component-type (obj-type obj)))
                     (array-content-initialized (array-data obj) hp-init))
                 (valid-array-type (obj-type obj) cl acl))
            (consistent-heap-array-init-state3 (bind ref obj hp)
                                               hp-init))
   :hints (("Goal" :do-not '(generalize)))))


(local 
 (defthm consistent-heap-array-init-state2-adding-new-obj
   (implies (consistent-heap-array-init-state2 hp hp-init)
            (consistent-heap-array-init-state2 (bind ref obj hp)
                                               hp-init))))


(local 
 (defthm consistent-heap-array-init-state1-adding-new-obj
   (implies (and (consistent-heap-array-init-state1 hp cl acl hp-init)
                 (not (bound? ref hp-init))
                 (valid-array-type (obj-type obj) cl acl))
            (consistent-heap-array-init-state1 (bind ref obj hp)
                                               cl acl
                                               hp-init))
   :hints (("Goal" :do-not '(generalize)))))
    

(local 
 (defthm consistent-state-implies-not-bound-len-heap
   (implies (consistent-state s)
            (not (bound? (len (heap s)) (heap s))))))


(local 
 (defthm consistent-state-implies-consistent-heap-init-state3
   (implies (consistent-state s)
            (consistent-heap-array-init-state3 (heap s)
                                               (heap-init-map (aux s))))
   :hints (("Goal" :in-theory (enable consistent-state consistent-heap-array-init-state)))))



(local 
 (defthm consistent-state-implies-consistent-heap-init-state2
   (implies (consistent-state s)
            (consistent-heap-array-init-state2 (heap s)
                                               (heap-init-map (aux s))))
   :hints (("Goal" :in-theory (enable consistent-state consistent-heap-array-init-state)))))


(local 
 (defthm consistent-state-implies-consistent-heap-init-state1
   (implies (consistent-state s)
            (consistent-heap-array-init-state1 (heap s)
                                               (instance-class-table s)
                                               (array-class-table s)
                                               (heap-init-map (aux s))))
   :hints (("Goal" :in-theory (enable consistent-state consistent-heap-array-init-state)))))
    
(local 
 (defthm consistent-array-object-implies-wff-internal-array
   (implies (consistent-array-object obj hp cl acl)
            (wff-internal-array obj))
   :hints (("Goal" :in-theory (enable consistent-array-object)))
   :rule-classes :forward-chaining))


(local 
 (defthm consistent-heap-array-init-state-adding-new-obj
   (IMPLIES (AND (CONSISTENT-STATE S)
                 (CONSISTENT-OBJECT OBJ (HEAP S)
                                    (INSTANCE-CLASS-TABLE S))
                 (CONSISTENT-ARRAY-OBJECT OBJ (HEAP S)
                                          (INSTANCE-CLASS-TABLE S)
                                          (ARRAY-CLASS-TABLE S))
                 (array-content-initialized (array-data obj) (heap-init-map
                                                              (aux s))))
            (CONSISTENT-HEAP-ARRAY-INIT-STATE (BIND (LEN (HEAP S)) OBJ (HEAP S))
                                              (INSTANCE-CLASS-TABLE S)
                                              (ARRAY-CLASS-TABLE S)
                                              (HEAP-INIT-MAP (AUX S))))
   :hints (("Goal" :in-theory (enable consistent-heap-array-init-state)))))
                                           


;; (i-am-here) ;; Thu Jul 21 15:54:44 2005

(skip-proofs 
 (local 
  (defthm consistent-state-add-new-object-consistent-heap-init-state
    (IMPLIES (AND (CONSISTENT-STATE S)
                  (CONSISTENT-OBJECT OBJ (HEAP S)
                                     (INSTANCE-CLASS-TABLE S)))
             (CONSISTENT-HEAP-INIT-STATE (BIND (LEN (HEAP S)) OBJ (HEAP S))
                                         (INSTANCE-CLASS-TABLE S)
                                         (HEAP-INIT-MAP (AUX S)))))))

;;; this will be useful in showing load_class2-preserve-consistency! 

;;; but skip all of them now. 


(local 
 (defthm consistent-state-add-new-object-generalized-step
  (implies (and (consistent-state s)
                (consistent-object obj hp (instance-class-table s))
                (equal (heap s) hp)
                (or (not (isArrayType (obj-type obj)))
                    (and (consistent-array-object obj hp
                                                  (instance-class-table s)
                                                  (array-class-table s))
                         (or (primitive-type? (array-component-type (obj-type obj)))
                             (array-content-initialized (array-data obj) (heap-init-map
                                                                          (aux s)))))))
           (consistent-state-step  (state-set-heap 
                                    (bind (len hp)
                                          obj hp) s)))
  :hints (("Goal" :in-theory (e/d (instance-class-table-inv
                                   array-class-table-inv
                                   boot-strap-class-okp
                                   consistent-class-table
                                   loader-inv wff-heap
                                   class-loaded?
                                   )
                                  (consistent-array-object
                                   BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD
                                   consistent-object))
           :do-not-induct t
           :do-not '(generalize)))))



(local 
 (defthm state-set-heap-preserve-consistency-1
   (implies (consistent-state-step (state-set-heap hp s))
            (consistent-state (state-set-heap hp s)))
   :hints (("Goal" :use ((:instance
                         consistent-state-step-implies-consistent-state
                         (s (state-set-heap hp s))))))))





(defthm consistent-state-add-new-object-generalized-x
  (implies (and (consistent-state s)
                (consistent-object obj hp (instance-class-table s))
                (equal (heap s) hp)
                (or (not (isArrayType (obj-type obj)))
                    (and (consistent-array-object obj hp
                                                  (instance-class-table s)
                                                  (array-class-table s))
                         (or (primitive-type? (array-component-type (obj-type obj)))
                             (array-content-initialized (array-data obj) (heap-init-map
                                                                          (aux s)))))))
            (consistent-state  (state-set-heap 
                                (bind (len hp)
                                      obj hp) s)))
  :hints (("Goal" :in-theory (disable state-set-heap))))















(local 
 (defthm init-array-array-consistent1
   (IMPLIES (and (AND (INTEGERP BOUND) (<= 0 BOUND))
                 (or (primitive-type? basetype)
                     (reference-type basetype)
                     (Array-type? basetype)))
            (ARRAY-OBJ-CONSISTENT1 (INIT-ARRAY BASETYPE BOUND)
                                   BASETYPE 
                                   hp cl))
   :hints (("Goal" :in-theory (e/d () (consistent-value default-value tag (default-value)))))))



(local 
 (defthm primitive-type-array-type-s-fact
   (implies (PRIMITIVE-TYPE? BASETYPE)
            (ARRAY-TYPE-S (LIST 'ARRAY BASETYPE)
                          (INSTANCE-CLASS-TABLE S)))))


(local 
 (defthm valid-array-type-implies-array-type-s
   (implies (valid-array-type type cl acl)
            (array-type-s type cl))
   :hints (("Goal" :in-theory (enable valid-array-type)))
   :rule-classes :forward-chaining))


(local 
 (defthm array-class-by-name-implies-assoc-equal
   (implies (ARRAY-CLASS-BY-NAME type ACL)
            (assoc-equal type acl))))


;; (i-am-here) 

(local 
  (defthm valid-array-type-implies-array-class-exists
    (implies (valid-array-type type cl acl)
             (array-class-exists? type acl))
    :hints (("Goal" :in-theory (e/d (valid-array-type bound?)
                                    (primitive-type?))))
    :rule-classes :forward-chaining))


(local 
 (defthm len-init-array-fact
   (implies (and (integerp bound)
                 (<= 0 bound))
            (EQUAL (LEN (INIT-ARRAY BASETYPE BOUND))
                   BOUND))))

;; (i-am-here) ;; Thu Jun 16 23:47:02 2005

(local 
  (defthm build-an-array-intance-consistent-array-object
    (implies (and (equal (heap s) hp)
                  (integerp bound)
                  (<= 0 bound)
                  (or (primitive-type? basetype) 
                      (reference-type basetype)
                      (Array-type? basetype))
                ;;; this above hyp should be releaseable when we know 
                ;;; valid-array-type base-type
                ;;; and we know wff-instance-class-table
                  (consistent-jvp "java.lang.Object" 
                                  '(("java.lang.Object"))
                                  (instance-class-table s)
                                  (heap s))
                  (equal (instance-class-table s) cl)
                  (equal (array-class-table s) acl)
                  (valid-array-type (make-array-type basetype) cl acl))
             (consistent-array-object (car (build-an-array-instance basetype bound s))
                                      hp cl acl))
    :hints (("Goal" :in-theory (e/d (isArrayType obj-type
                                                 valid-array-type
                                                 array-data
                                                 wff-obj-strong
                                                 wff-internal-array
                                                 array-class-by-name
                                                 consistent-array-object
                                                 build-an-array-instance 
                                                 common-info) 
                                    (array-type-s
                                     valid-array-type
                                     consistent-jvp
                                     primitive-type?
                                     bound? array-class-exists?
                                     ))))))




(local 
 (defthm consistent-class-decls-implies-stringp
   (implies (and (consistent-class-decls cl1 cl hp)
                 (wff-instance-class-table cl1)
                 (class-by-name name cl1))
            (stringp name))
   :hints (("Goal" :in-theory (enable consistent-class-decl)))
   :rule-classes :forward-chaining))
                

(local 
 (defthm array-type-s-implies-base-type-category
   (implies (and (not (or (primitive-type? basetype)
                          (reference-type basetype)
                          (Array-Type? basetype)))
                 (wff-instance-class-table cl)
                 (consistent-class-decls cl cl hp))
            (not (array-type-s (list 'ARRAY basetype) cl)))
   :hints (("Goal" :expand (array-type-s (list 'ARRAY basetype) cl)))))




(local 
 (defthm array-type-s-implies-base-type-category-specific
   (implies (and (not (or (primitive-type? basetype)
                          (reference-type basetype)
                          (Array-Type? basetype)))
                 (consistent-state s))
            (not (array-type-s (list 'ARRAY basetype) (instance-class-table s))))
   :hints (("Goal" :expand (array-type-s (list 'ARRAY basetype) 
                                         (instance-class-table s))))))

       


(local 
  (defthm build-an-array-intance-consistent-array-object-simplified
    (implies (and (equal (heap s) hp)
                  (integerp bound)
                  (<= 0 bound)
                  ;(or (primitive-type? basetype) 
                  ;    (reference-type basetype)
                  ;    (Array-type? basetype))
                ;;; this above hyp should be releaseable when we know 
                ;;; valid-array-type base-type
                ;;; and we know wff-instance-class-table
                  (consistent-state s)
                  (equal (instance-class-table s) cl)
                  (equal (array-class-table s) acl)
                  (valid-array-type (make-array-type basetype) cl acl))
             (consistent-array-object (car (build-an-array-instance basetype bound s))
                                      hp cl acl))
    :hints (("Goal" :in-theory (e/d (valid-array-type)
                                    (array-type-s
                                     consistent-array-object
                                     build-an-array-instance
                                     primitive-type?
                                     bound? array-class-exists?
                                     ))
             :cases ((or (primitive-type? basetype) 
                         (reference-type basetype)
                         (Array-type? basetype)))))))
             



(local 
 (encapsulate ()
   (local (include-book "base-loader-preserve-consistent-state"))
   (defthm getArrayClass-preserve-consistency
     (implies (consistent-state s)
              (consistent-state (getArrayClass any s))))))

(local 
  (defthm array-correctly-loaded-implies-valid-array-type-general
    (implies (and (array-type? type)
                  (not (class-loaded? 'NULL s))
                  (jvm::array-class-correctly-loaded?
                   (jvm::base-types type) s))
             (valid-array-type type (instance-class-table s)
                               (array-class-table s)))
    :hints (("Goal" :in-theory (e/d (valid-array-type
                                     array-base-type
                                     class-loaded?
                                     isArrayType)
                                    (primitive-type?
                                     isClassTerm))))))


(local 
  (defthm array-correctly-loaded-implies-valid-array-type
    (implies (and (not (class-loaded? 'NULL s))
                  (jvm::array-class-correctly-loaded? 
                   (jvm::base-types (make-array-type type)) s))
             (valid-array-type (make-array-type type) 
                               (instance-class-table s)
                               (array-class-table s)))
    :hints (("Goal" :in-theory (e/d () (valid-array-type))))))


(local (in-theory (enable consistent-class-table)))


(local 
 (defthm consistent-state-not-class-loaded-NULL
   (implies (consistent-state s)
            (not (class-loaded? 'NULL s)))
   :hints (("Goal" :in-theory (enable consistent-state class-loaded?)))))


(local 
 (defthm array-class-table-helper-inv-implies-mem
   (implies (and (jvm::array-class-table-inv-helper l s)
                 (mem type l))
            (jvm::array-class-correctly-loaded? (jvm::base-types type) s))))
             
(local (in-theory (enable bound?))) ;; Sun Jun  5 00:10:01 2005



(local 
 (defthm consistent-state-array-class-exists-implies-mem
   (implies (array-class-exists? type l)
            (mem type (jvm::all-array-sigs l)))))


(local 
 (defthm consistent-state-array-class-inv
   (implies (consistent-state s)
            (jvm::array-class-table-inv-helper (jvm::all-array-sigs
                                                (array-class-table s)) s))
 :hints (("Goal" :in-theory (enable consistent-state)))))


(local 
 (defthm consistent-state-loaded-mean-correctly-loaded
   (implies (and (consistent-state s)
                 (array-class-exists? type (array-class-table s)))
            (jvm::array-class-correctly-loaded? 
             (jvm::base-types type) s))
   :hints (("Goal" :do-not '(generalize)
            :restrict ((array-class-table-helper-inv-implies-mem
                        ((l (jvm::all-array-sigs (array-class-table s))))))))))


(local (in-theory (disable make-array-type)))


(local 
 (defthm getArrayClass-no-error-implies-loaded
   (implies (no-fatal-error? (getArrayClass basetype s))
            (array-class-exists? (make-array-type basetype) 
                                 (array-class-table (getArrayClass basetype s))))))

;;; proof this is easy. to make it contributes to the proof of the next lemma
;;; we really need that getArrayClass preserve the consistent-state so that we
;;; could make use of the previous lemma
;;;
;;;            consistent-state-loaded-mean-correctly-loaded
;;;
;;; and 
;;;           array-correctly-loaded-implies-valid-array-type-general
;;;            

(in-theory (disable  JVM::BASE-TYPES-MAKE-TYPE))

(local 
 (defthm getArrayClass-implies-valid-array-type
   (implies (and (no-fatal-error? (getArrayClass basetype s))
                 (consistent-state s))
            (valid-array-type (make-array-type basetype) 
                              (instance-class-table (getArrayClass basetype s))
                              (array-class-table (getArrayClass basetype s))))
   :hints (("Goal" :in-theory (e/d () (make-array-type 
                                       valid-array-type
                                       jvm::array-class-correctly-loaded? 
                                       jvm::base-types
                                       JVM::BASE-TYPES-MAKE-TYPE
                                       (make-array-type)
                                       getarrayclass
                                       array-class-exists?))))))




(defthm build-an-array-instance-consistent-array-object-specific
  (implies (and (consistent-state s)
                (no-fatal-error? (getArrayClass basetype s))
                (equal (heap (getArrayClass basetype s)) hp)
                (equal (instance-class-table (getArrayClass basetype s)) cl)
                (equal (array-class-table (getArrayClass basetype s)) acl)
                (integerp bound)
                (<= 0 bound))
           (consistent-array-object 
            (car (build-an-array-instance basetype
                                          bound
                                          (getArrayClass basetype s)))
            hp cl acl))
  :hints (("Goal" :in-theory (e/d () (consistent-array-object
                                      getArrayClass
                                      JVM::ARRAY-CLASS-CORRECTLY-LOADED?
                                      array-class-exists?
                                      make-array-type
                                      build-an-array-instance)))))

