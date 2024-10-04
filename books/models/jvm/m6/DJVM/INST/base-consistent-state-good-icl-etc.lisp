(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../BCV/bcv-functions")
(include-book "../../DJVM/consistent-state-to-sig-state")
(include-book "../../DJVM/consistent-state-properties")

;; (i-am-here) ;; Fri Jul 15 15:55:30 2005



;; (BCV::ALL-SUBCLASS-OF-JAVA-LANG-OBJECT
;;  (ALL-CLASS-NAMES BCV::ICL)
;;  BCV::ICL)


(local 
 (defthm
   class-hierachy-consistent1-class-n-implies-not-java-lang-Object-super-bounded
   (implies 
    (and (jvm::class-hierachy-consistent1-class-n name cl)
         (not (equal name "java.lang.Object")))
    (jvm::isClassTerm (jvm::class-by-name (jvm::super (jvm::class-by-name name cl))
                                          cl)))
   :hints (("Goal" :in-theory (e/d (jvm::class-exists? jvm::class-loaded?) (jvm::isClassTerm))))))


(local 
 (defthm isClassTerm-implies-class-hierachy-consistent1-class-n
   (implies (and (isClassTerm (class-by-name n cl1))
                 (class-hierachy-consistent1-aux cl1 cl))
            (class-hierachy-consistent1-class-n n cl))))
   

(local (defthm consistent-state-implies-good-icl-lemma
  (implies (and (SUPERCLASS-CHAIN-NO-LOOP-CLASS-N n cl seen)
                (isClassTerm (class-by-name n cl))
                (CLASS-HIERACHY-CONSISTENT1 cl))
           (mem "java.lang.Object" (collect-superclass-list1 n cl seen)))
  :hints (("Goal" :in-theory (disable isClassTerm super)
           :do-not '(generalize)))))



(local 
 (defthm isClassTerm-implies-superclass-chain-no-loop-class-n
   (implies (and (class-hierachy-consistent2-aux cl1 cl)
                 (isClassTerm (class-by-name n cl1)))
            (superclass-chain-no-loop-class-n n cl nil))))


(defthm consistent-class-hierachy-implies-bcv-all-subclass-of-java-lang-Object
  (implies (and (class-hierachy-consistent1-aux cl1 cl)
                (class-hierachy-consistent1 cl)
                (class-hierachy-consistent2-aux cl cl)
                (wff-instance-class-table cl1))
           (bcv::all-subclass-of-java-lang-object 
            (all-class-names cl1) cl))
  :hints (("Goal" :in-theory (e/d () (class-hierachy-consistent1
                                      isClassTerm)))))



;; (defthm consistent-state-consistent-class-decls
;;   (implies (consistent-state s)
;;            (consistent-class-decls (instance-class-table s)
;;                                    (instance-class-table s)
;;                                    (heap s)))
;;   :hints (("Goal" :in-theory (enable consistent-state
;;                                      consistent-class-table)))
;;   :rule-classes :forward-chaining)


(defthm consistent-class-decls-implies-wff-icl
  (implies (consistent-class-decls cl1 cl hp)
           (bcv::wff-icl cl1))
  :rule-classes :forward-chaining)
  
(defthm boot-strap-class-okp-implies-consp-class-by-name-java-lang-Object
  (implies (boot-strap-class-okp s)
           (isClassTerm (class-by-name "java.lang.Object" (instance-class-table
                                                           s))))
  :rule-classes :forward-chaining)

(defthm isClassTerm-implies-consp
  (implies (isClassTerm term)
           (consp term))
  :rule-classes :forward-chaining)

(defthm consistent-state-implies-bootstrap-class-okp
  (implies (consistent-state s)
           (boot-strap-class-okp s))
  :hints (("Goal" :in-theory (e/d (consistent-state) 
                                  (boot-strap-class-okp))))
  :rule-classes :forward-chaining)

(local 
 (defthm bcv-class-by-name-is-class-by-name
   (equal (bcv::class-by-name name cl)
          (class-by-name name cl))
   :hints (("Goal" :in-theory (enable bcv::class-by-name 
                                      classname
                                      bcv::classclassname)))))
 
(defthm consistent-state-implies-class-hierachy-consistent1
  (implies (consistent-state s)
           (class-hierachy-consistent1-aux (instance-class-table s)
                                           (instance-class-table s)))
  :hints (("Goal" :in-theory (enable consistent-state consistent-class-hierachy)))
  :rule-classes :forward-chaining)

(defthm consistent-state-implies-class-hierachy-consistent2
  (IMPLIES (CONSISTENT-STATE S)
           (CLASS-HIERACHY-CONSISTENT2-AUX (INSTANCE-CLASS-TABLE S)
                                           (INSTANCE-CLASS-TABLE S)))
  :hints (("Goal" :in-theory (enable consistent-state consistent-class-hierachy)))
  :rule-classes :forward-chaining)


;; (local 
;;  (defthm
;;    class-hierachy-consistent1-class-n-implies-not-java-lang-Object-super-bounded
;;    (implies 
;;     (and (jvm::class-hierachy-consistent1-class-n name cl)
;;          (not (equal name "java.lang.Object")))
;;     (jvm::isClassTerm (jvm::class-by-name (jvm::super (jvm::class-by-name name cl))
;;                                           cl)))
;;    :hints (("Goal" :in-theory (e/d (jvm::class-exists? jvm::class-loaded?) (jvm::isClassTerm))))))

(local 
 (defthm
   class-hierachy-consistent1-class-n-implies-not-java-lang-Object-super-bounded-2
   (implies 
    (and (jvm::class-hierachy-consistent1-class-n name cl)
         (equal name "java.lang.Object"))
    (not (jvm::isClassTerm (jvm::class-by-name (jvm::super (jvm::class-by-name name cl))
                                               cl))))
   :hints (("Goal" :in-theory (e/d (jvm::class-exists? jvm::class-loaded?) (jvm::isClassTerm))))))


(defthm consistent-state-implies-good-icl
  (implies (consistent-state s)
           (bcv::good-icl (instance-class-table s)))
  :hints (("Goal" :in-theory (e/d (class-loaded?
                                   bcv::class-by-name
                                   consistent-class-hierachy
                                   class-exists?)
                                  (bcv::all-subclass-of-java-lang-object
                                   isClassTerm
                                   super
                                   boot-strap-class-okp)))))

;;(i-am-here) ;; Fri Jul 15 20:23:19 2005




(defthm consistent-state-implies-equal-scl-bcv2jvm-jvm2bcv-identity
   (implies (consistent-state s)
            (equal (bcv::scl-bcv2jvm (bcv::scl-jvm2bcv (env-class-table (env s))))
                   (env-class-table (env s))))
   :hints (("Goal" :in-theory (e/d (consistent-state bcv::good-scl) ())
            :do-not '(generalize fertilize))))


(defthm consistent-state-implies-wff-static-class-table
  (implies (CONSISTENT-STATE S)
           (WFF-STATIC-CLASS-TABLE-STRONG (ENV-CLASS-TABLE (ENV S))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ())))
  :rule-classes :forward-chaining)

(defthm consistent-state-implies-class-table-loaded-from
  (IMPLIES (CONSISTENT-STATE S)
           (CLASS-TABLE-IS-LOADED-FROM (INSTANCE-CLASS-TABLE S)
                                       (ENV-CLASS-TABLE (ENV S))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ())))
  :rule-classes :forward-chaining)

(defthm consistent-state-implies-good-scl
  (IMPLIES (CONSISTENT-STATE S)
           (BCV::GOOD-SCL (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S)))))
  :hints (("Goal" :in-theory (e/d (consistent-state) (bcv::good-scl))))
  :rule-classes :forward-chaining)

(defthm consistent-state-implies-icl-scl-compatible
  (implies (consistent-state s)
           (BCV::ICL-SCL-COMPATIBLE (INSTANCE-CLASS-TABLE S)
                                    (BCV::CLASSTABLEENVIRONMENT (env-sig s))))
  :hints (("Goal" :in-theory (e/d (BCV::CLASSSUPERCLASSNAME 
                                   bcv::icl-scl-compatible) 
                                  (bcv::isClassTerm
                                   consistent-state
                                   bcv::good-scl
                                   isClassTerm))
           :do-not '(generalize fertilize))))
