(in-package "DJVM")
(include-book "../../M6-DJVM-shared/jvm-linker")
(include-book "../../M6-DJVM-shared/jvm-class-table")
(include-book "../../M6-DJVM-shared/jvm-object-type-hierachy")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-to-sig-state")


(defthm bcv-class-is-interface-normalize
  (equal (bcv::classIsInterface
          (BCV::CLASS-BY-NAME name (BCV::SCL-JVM2BCV SCL)))
         (mem '*interface* (accessflags-s 
                            (mv-nth 1 (class-by-name-s name scl)))))
  :hints (("Goal" :in-theory (enable bcv::classisinterface
                                     BCV::MAKE-CLASS-TERM
                                     bcv::class-by-name
                                     classname-s
                                     accessflags-s
                                     bcv::classclassname
                                     )
           :do-not '(generalize))))


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
           :do-not '(generalize))))

;; Tue Jun 21 16:28:22 2005


(encapsulate () 
  (local (include-book "base-consistent-state-lookupfield-support"))
  (defthm consistent-state-implie-super-of-interface-is-java-lang-Object
    (implies (and (consistent-state s)
                  (isInterface (class-by-name name (instance-class-table s))))
             (equal (super (class-by-name name (instance-class-table s)))
                    "java.lang.Object"))
    :hints (("Goal" :in-theory (e/d () (consistent-state
                                        WFF-CLASS-REP-STATIC-STRONG
                                        JVM::WFF-STATIC-CP-OK-S))))))


(defthm consistent-class-decl-interface-implies-no-fields
  (implies (and (consistent-class-decl class-rep cl hp)
                (isInterface class-rep))
           (equal (fields class-rep) nil)))


(defthm consistent-class-decls-class-by-name
  (implies (and (consistent-class-decls cl1 cl hp)
                (class-by-name name cl1))
           (consistent-class-decl (class-by-name name cl1) cl hp))
  :hints (("Goal" :in-theory (disable consistent-class-decl))))

(defthm isInterface-type-class-by-name
  (implies (isInterface (class-by-name name cl))
           (class-by-name name cl)))


(defthm consistent-state-implies-consistent-class-decl
  (implies (consistent-state s)
           (consistent-class-decls (instance-class-table s)
                                   (instance-class-table s)
                                   (heap s))))
  


(defthm consistent-state-interface-implies-no-fields
  (implies (and (consistent-state s)
                (isInterface (class-by-name name (instance-class-table s))))
           (equal (fields (class-by-name name (instance-class-table s))) nil))
  :hints (("Goal" :in-theory (e/d () (fields consistent-state))
           :cases ((consistent-class-decl (class-by-name name
                                                         (instance-class-table
                                                          s))
                                          (instance-class-table s)
                                          (heap s))))))



(encapsulate ()
  (local (include-book "base-consistent-state-lookupfield-support"))
  (defthm consistent-state-implies-java-lang-Object-not-fields
    (implies (consistent-state s)
             (not (fields (class-by-name "java.lang.Object" (instance-class-table s)))))))



(encapsulate ()
 (local (include-book "base-loader-preserve-consistent-state"))
 (defthm consistent-state-super-java-lang-object
   (implies (consistent-state s)
            (equal (super (class-by-name "java.lang.Object"
                                         (instance-class-table s)))
                   ""))))



(defthm consistent-state-lookfield-java-lang-Object-nil
  (implies (consistent-state s)
           (not (lookupField (make-field-ptr "java.lang.Object"
                                             anyname
                                             anytype)
                             s)))
  :hints (("Goal" :in-theory (e/d (lookupField 
                                   searchfields
                                   deref-field) (consistent-state))
           :expand (lookupField (make-field-ptr "java.lang.Object"
                                             anyname
                                             anytype)
                             s))))
                                   
            






(defthm consistent-state-implies-if-found-field-then-not-interface-lemma
  (implies (and (consistent-state s)
                (isInterface (class-by-name (field-ptr-classname field-ptr)
                                            (instance-class-table s))))
           (not  (LOOKUPFIELD field-ptr s)))
  :hints (("Goal" :in-theory (e/d (lookupfield 
                                   deref-field 
                                   searchfields) (fields
                                                  consistent-state
                                                  )))))


(defthm consistent-state-implies-if-class-not-found-not-nil
  (implies (and (consistent-state s)
                (not (class-by-name (field-ptr-classname field-ptr) 
                                    (instance-class-table s))))
           (not  (LOOKUPFIELD field-ptr s)))
  :hints (("Goal" :in-theory (e/d (lookupfield 
                                   deref-field 
                                   searchfields) 
                                  (fields
                                   consistent-state)))))
                                   


(defthm consistent-state-implies-class-table-loaded-from
  (implies (and (equal (env-class-table (env s)) scl)
                (consistent-state s))
           (CLASS-TABLE-IS-LOADED-FROM
            (INSTANCE-CLASS-TABLE s)
            scl))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm classtable-from-env-sig-normalize
  (equal (BCV::CLASSTABLEENVIRONMENT (ENV-SIG s))
         (bcv::scl-jvm2bcv (env-class-table (env s))))
  :hints (("Goal" :in-theory (enable env-sig bcv::classtableenvironment
                                     makeEnvironment))))



(encapsulate () 
   (local (include-book "base-consistent-state-load-class"))
   (defthm resolveClassReference-preserve-consistency
     (implies (consistent-state s)
              (consistent-state (resolveClassReference any s)))))

(defthm env-resolveClassReference-no-change
   (equal (env (resolveClassReference any s))
          (env s)))


;;(i-am-here)

(defthm consistent-state-implies-if-found-field-then-not-interface
  (implies (and (consistent-state s)
                (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp) 
                             (RESOLVECLASSREFERENCE (FIELDCP-CLASSNAME fieldcp)
                                                    S)))
             (not (bcv::ClassIsInterface  (bcv::class-by-name 
                                         (fieldcp-classname fieldcp)
                                         (BCV::CLASSTABLEENVIRONMENT
                                          (ENV-SIG S))))))
  :hints (("Goal" 
           :in-theory (e/d (env-sig)
                           (bcv::classisinterface
                            fieldcp-classname
                            resolveclassreference
                            consistent-state))
           :cases ((consistent-state (resolveclassreference 
                                      (FIELDCP-CLASSNAME fieldcp)
                                      s))))
          ("Subgoal 1"  :use ((:instance classIsInterface-implies-isInterface
                                         (cl (instance-class-table 
                                              (resolveclassreference 
                                               (FIELDCP-CLASSNAME fieldcp) s)))
                                         (scl (env-class-table 
                                               (env (resolveclassreference 
                                                     (FIELDCP-CLASSNAME
                                                     fieldcp) s))))
                                         (name (fieldcp-classname
                                                fieldcp)))))))


;----------------------------------------------------------------------


(defthm bcv-class-by-name-is-normalize
  (implies (car (class-by-name-s name scl))
           (equal (bcv::class-by-name name (bcv::scl-jvm2bcv scl))
                  (bcv::make-class-def (mv-nth 1 (class-by-name-s name scl)))))
  :hints (("Goal" :in-theory (e/d (bcv::make-class-term
                                   bcv::classclassname
                                   classname-s
                                   bcv::class-by-name) ()))))


(defthm class-not-bound-in-bcv-class-table-not-bound-in-internal-table
  (implies (and (class-table-is-loaded-from cl scl)
                ;;(wff-static-class-table-strong scl)
                (class-by-name name cl))
           (bcv::class-by-name name (bcv::scl-jvm2bcv scl)))
  :hints (("Goal" :in-theory (e/d (classname 
                                   bcv::make-class-term
                                   classname-s
                                   bcv::class-by-name
                                   bcv::classclassname) (isClassTerm))
           :do-not '(generalize))))


(defthm if-not-found-not-lookupfield
  (implies (and (consistent-state s)
                (not (class-by-name (fieldcp-classname fieldcp)
                                    (instance-class-table s))))
           (not (lookupfield (fieldcp-to-field-ptr fieldcp) s)))
  :hints (("Goal" :in-theory (e/d () (consistent-state)))))


(defthm consistent-state-implies-if-found-field-then-class-found
  (implies (and (consistent-state s)
                (LOOKUPFIELD (FIELDCP-TO-FIELD-PTR fieldcp) 
                             (resolveclassreference (fieldcp-classname fieldcp) s)))
           (BCV::CLASS-BY-NAME (fieldcp-classname fieldcp)
                               (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S))))
  :hints (("Goal" :in-theory (e/d () (consistent-state 
                                      resolveclassreference
                                      fieldcp-classname))
           :use ((:instance
                  class-not-bound-in-bcv-class-table-not-bound-in-internal-table
                  (cl (instance-class-table (resolveclassreference
                                             (fieldcp-classname fieldcp) s)))
                  (scl (env-class-table (env s)))
                  (name (fieldcp-classname fieldcp)))))))
           



