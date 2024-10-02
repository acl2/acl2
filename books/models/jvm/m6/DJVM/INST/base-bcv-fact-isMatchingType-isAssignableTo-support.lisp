(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")
(include-book "base-valid-type-s")

(local (in-theory (enable bcv::class-by-name
                   isassignableto isSuperClass1 class-exists? 
                   class-loaded?)))




(defthm bcv-class-by-name-class-by-name-s-normalize
  (equal  (bcv::classsuperclassname (BCV::CLASS-BY-NAME name (BCV::SCL-JVM2BCV SCL)))
          (super-s (MV-NTH 1 (CLASS-BY-NAME-S name scl))))
  :hints (("Goal" :in-theory (enable bcv::classsuperclassname 
                                     bcv::make-class-def
                                     bcv::classclassname
                                     classname-s
                                     BCV::MAKE-CLASS-TERM
                                     super-s)
           :do-not '(generalize))))

;;              (DEFTHM JVM::FOUND-IMPLIES-CLASSNAME-S-EQUAL
;;                       (MV-LET (JVM::DEF-FOUND JVM::CLASS-DESC)
;;                               (CLASS-BY-NAME-S CLASSNAME JVM::ENV-CL)
;;                               (IMPLIES JVM::DEF-FOUND
;;                                        (EQUAL (CLASSNAME-S JVM::CLASS-DESC)
;;                                               CLASSNAME))))
;;; we have this. 

(defthm bcv-classSuperClassname-is-super-lemma
  (implies (and (class-table-is-loaded-from cl scl)
                (isClassTerm (class-by-name typ1 cl)))
           (equal (bcv::classsuperclassname
                   (bcv::class-by-name typ1 (bcv::scl-jvm2bcv scl)))
                  (super (class-by-name typ1 cl))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable class-by-name-s))))




           
(defthm bcv-classSuperClassname-is-super
  (implies (and (class-table-is-loaded-from (instance-class-table s) 
                                            (env-class-table (env s)))
                (isClassTerm (class-by-name typ1 (instance-class-table s))))
           (equal (bcv::classsuperclassname
                   (bcv::class-by-name typ1 (bcv::scl-jvm2bcv (env-class-table
                                                               (env s)))))
                  (super (class-by-name typ1 (instance-class-table s)))))
  :hints (("Goal" :in-theory (disable bcv-class-by-name-class-by-name-s-normalize))))
           
;;; this is the lemma that we want! 


(defthm typ1-mem-all-class-name-if-loaded-lemma
  (implies  (and (isclassterm (class-by-name typ1 cl))
                 (class-table-is-loaded-from cl scl))
            (MEM TYP1 (ALL-CLASS-NAMES-S scl))))


(defthm typ1-mem-all-class-name-if-loaded
  (implies  (and (isclassterm (class-by-name typ1 (instance-class-table s)))
                 (class-table-is-loaded-from (instance-class-table s)
                                             (env-class-table (env s))))
            (MEM TYP1 (ALL-CLASS-NAMES-S (env-class-table (env s)))))
  :hints (("Goal" :in-theory (disable isclassterm))))


(defthm isSuperClass1-order-in-seen-does-not-matter
  (implies (set-equal l2 l1)
           (equal (car (isSuperClass1 name typ s l2))
                  (car (isSuperClass1 name typ s l1)))))


(defthm cons-x-y-set-equal
  (set-equal (cons y (cons x l))
             (cons x (cons y l))))




(defthm isSuperClass1-order-in-seen-does-not-matter-specific
  (equal (car (isSuperClass1 name typ s (cons x (cons y l))))
         (car (isSuperClass1 name typ s (cons y (cons x l)))))
  :hints (("Goal" :use ((:instance isSuperClass1-order-in-seen-does-not-matter
                                   (l2 (cons x (cons y l)))
                                   (l1 (cons y (cons x l))))))))




(defthm if-bound-but-super-not-bound-then-java-lang-Object
  (implies (and (consistent-state s)
                (isclassterm (class-by-name name (instance-class-table s)))
                (not (equal name "java.lang.Object")))
           (isclassterm (class-by-name 
                         (super (class-by-name name (instance-class-table s)))
                         (instance-class-table s)))))


;; (i-am-here) ;;; Sat Jun 18 13:24:43 2005

(defthm isSuperClass1-reduce-if-no-loop
  (implies (and (consistent-state s)
                (not (mem x (collect-superclass-list1 name
                                                      (instance-class-table s)
                                                      l)))
                (isclassterm (class-by-name name (instance-class-table s))))
           (equal (CAR (ISSUPERCLASS1 name TYP2 S (cons x l)))
                  (CAR (ISSUPERCLASS1 name TYP2 S l))))
  :hints (("Goal" :in-theory (e/d () (isclassterm))
           :do-not '(generalize fertilize))))


;; skip-proofs the following -- Tue Jun 21 20:32:13 2005

;; Wed Jun 22 20:45:14 2005

(defthm not-mem-not-mem-collect-superclass-list1
  (implies (and (not (mem x (collect-superclass-list1 n cl seen)))
                (not (equal x y)))
           (not (mem x (collect-superclass-list1 n cl (cons y seen))))))



(defthm superclass-chain-no-loop-class-n-implies-not-in-supers-of-super
  (implies (and (SUPERCLASS-CHAIN-NO-LOOP-CLASS-N n cl ss1)
                (mem x ss1)
                (not (mem x ss2)))
           (not (mem x (collect-superclass-list1 n cl ss2))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isclassterm))
          ("Subgoal *1/6" :expand (COLLECT-SUPERCLASS-LIST1 N CL SS2))))


(defthm class-hierachy-consistent2-aux-implies-superclass-chain-no-loop
  (implies (and (class-hierachy-consistent2-aux cl1 cl)
                (class-by-name n cl1))
           (superclass-chain-no-loop-class-n n cl nil))
  :hints (("Goal" :in-theory (disable superclass-chain-no-loop-class-n))))


(defthm consistent-state-implies-superclass-chain-no-loop
  (implies (and (consistent-state s)
                (class-by-name n (instance-class-table s)))
           (superclass-chain-no-loop-class-n n (instance-class-table s)
                                             nil))
  :hints (("Goal" :in-theory (e/d (consistent-state consistent-class-hierachy)
                                  (superclass-chain-no-loop-class-n))
           :use ((:instance
                  class-hierachy-consistent2-aux-implies-superclass-chain-no-loop
                  (cl1 (instance-class-table s))
                  (cl (instance-class-table s)))))))



(defthm consistent-state-implies-name-not-in-supers-of-super
  (implies (and (consistent-state s)
                (isclassterm (class-by-name name (instance-class-table s))))
           (not (mem name 
                     (collect-superclass-list1 
                      (super (class-by-name name (instance-class-table s)))
                      (instance-class-table s)
                      nil))))
  :hints (("Goal" :use ((:instance
                         superclass-chain-no-loop-class-n-implies-not-in-supers-of-super
                         (n (super (class-by-name name (instance-class-table
                                                        s))))
                         (ss1 (list name))
                         (ss2 nil)
                         (x   name))
                        (:instance
                         consistent-state-implies-superclass-chain-no-loop
                         (n name)))
           :in-theory (disable isclassterm))))
             

   

(defthm isSuperClass1-reduce-if-no-loop-specific
  (implies (and (consistent-state s)
                (not (mem x (collect-superclass-list1 name
                                                      (instance-class-table s)
                                                      l)))
                (isclassterm (class-by-name name (instance-class-table s))))
           (equal (CAR (ISSUPERCLASS1 name TYP2 S (cons x l)))
                  (CAR (ISSUPERCLASS1 name TYP2 S l))))
  :hints (("Goal" :in-theory (e/d () (isclassterm))
           :do-not '(generalize fertilize))))



(encapsulate ()
 (local (include-book "base-loader-preserve-consistent-state"))
 (defthm consistent-state-super-java-lang-object
   (implies (consistent-state s)
            (equal (super (class-by-name "java.lang.Object"
                                         (instance-class-table s)))
                   ""))))
                      

;; (defthm consistent-state-implies-null-string-not-bound
;;   (implies (consistent-state s)
;;            (not (class-by-name "" (instance-class-table s))))
;;   :hints (("Goal" :in-theory (enable consistent-state
;;                                      boot-strap-class-okp))))



(defthm implies-not-found-static-not-found
  (implies (and (not (car (class-by-name-s "" scl)))
                (wff-instance-class-table cl)
                (class-table-is-loaded-from cl scl))
           (not (isclassterm (class-by-name "" cl)))))



(defthm never-isSuperClass-by-name
  (implies (and (consistent-state s)
                (not (equal typ2 "")))
           (not (CAR (ISSUPERCLASS1 "" TYP2 S NIL))))
  :hints (("Goal" :expand (ISSUPERCLASS1 "" TYP2 S NIL)
           :in-theory (e/d (consistent-state)
                           (isclassterm))
           :use ((:instance implies-not-found-static-not-found
                            (cl (instance-class-table s))
                            (scl (env-class-table (env s))))))))
  

;;; Wed Jun 22 22:17:14 2005
;;; not very good. 
;;; 

(defthm class-is-loaded-from-helper-implies-super-s-equal-super
  (implies (class-is-loaded-from-helper class-rep class-rep-static)
           (equal (super-s class-rep-static)
                  (super class-rep))))


(defthm class-loaded-implies-class-is-loaded-from
  (implies (and (class-table-is-loaded-from cl scl)
                (isclassterm (class-by-name name cl)))
           (class-is-loaded-from-helper (class-by-name name cl)
                                        (mv-nth 1 (class-by-name-s name scl))))
  :hints (("Goal" :in-theory (disable class-is-loaded-from-helper))))



(defthm equal-super-s-super
  (implies (and (isclassterm (class-by-name typ1 (instance-class-table s)))
                (consistent-state s))
           (equal (super-s (mv-nth 1 (class-by-name-s typ1 (env-class-table
                                                            (env s)))))
                  (super (class-by-name typ1 (instance-class-table s)))))
  :hints (("Goal" :in-theory (enable consistent-state)
           :use ((:instance
                  class-is-loaded-from-helper-implies-super-s-equal-super
                  (class-rep-static (mv-nth 1 (class-by-name-s typ1
                                                               (env-class-table
                                                                (env s)))))
                  (class-rep (class-by-name typ1 (instance-class-table s))))))))




;; (skip-proofs  ;;; something relates to no loop!! ;; missing hyps.
;;  (defthm isSuperClass1-reduce-if-no-loop
;;    (equal (CAR (ISSUPERCLASS1 (SUPER (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S)))
;;                               TYP2 S (cons x l)))
;;           (CAR (ISSUPERCLASS1 (SUPER (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S)))
;;                               TYP2 S l)))))



;; (skip-proofs ;; missing hyps!! 
;;  (defthm not-super-bounded-implies-not-subclassof
;;   (implies (and (isclassterm (class-by-name typ1 (instance-class-table s)))
;;                 (NOT
;;                  (ISCLASSTERM
;;                   (CLASS-BY-NAME            
;;            (not (BCV::ISJAVASUBCLASSOF
;;                  (SUPER (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S)))
;;                  TYP2
;;                  (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S))))))))


(defthm boot-strap-class-okp-implies-not-bound
  (implies (boot-strap-class-okp s)
           (not (car (class-by-name-s "" (env-class-table (env s)))))))


(defthm consistent-state-implies-not-bound
  (implies (consistent-state s)
           (not (car (class-by-name-s "" (env-class-table (env s))))))
    :hints (("Goal" :in-theory (e/d (consistent-state)
                                    (boot-strap-class-okp))
             :use ((:instance boot-strap-class-okp-implies-not-bound)))))



(defthm not-car-class-by-name-s-not-bcv-isClassTerm
  (implies (not (car (class-by-name-s name scl)))
           (not (bcv::isclassterm (bcv::class-by-name name 
                                                      (bcv::scl-jvm2bcv scl)))))
                                                      
  :hints (("Goal" :in-theory (enable classname-s)
           :do-not '(generalize))))

;;;
;;; isSuperclass quit early!! 

(defthm bcv-isSuperclass1-djvm-isSubclass1
  (implies (and (bcv::isJavaSubclassof typ1 typ2 (bcv::scl-jvm2bcv
                                                  (env-class-table (env s))))
                (isClassTerm (class-by-name typ1 (instance-class-table s)))
                (isClassTerm (class-by-name typ2 (instance-class-table s)))
                (class-table-is-loaded-from (instance-class-table s)
                                            (env-class-table (env s)))
                (no-fatal-error? s)
                (consistent-state s))
           (car (isSuperClass1 typ1 typ2 s nil)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (class-exists? class-loaded?) (isClassTerm)))
          ("Subgoal *1/4" :expand (ISSUPERCLASS1 TYP1 TYP2 S NIL))
          ("Subgoal *1/3" :expand (ISSUPERCLASS1 TYP1 TYP2 S NIL))))


(defthm isClassType-then-name-of-fix-sig
  (implies (bcv::isclasstype (fix-sig any))
           (equal (bcv::name-of (fix-sig any))
                  any))
  :hints (("Goal" :in-theory (e/d (bcv::isclasstype 
                                   primitive-type?
                                   bcv::name-of) ()))))


;; (skip-proofs 
;;  (defthm bcv-classisInterface-judgement-equal
;;    (implies (and (consistent-state s)
;;                  (isClassTerm (class-by-name typ2 (instance-class-table s))))
;;             (equal 
;;              (BCV::CLASSISINTERFACE
;;               (BCV::CLASS-BY-NAME TYP2
;;                                   (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S)))))
;;              (isInterface (class-by-name typ2 (instance-class-table s)))))))




;;          (NOT (EQUAL TYP2 "java.lang.Object"))
;;          (ISINTERFACE (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S)))

;;          (NOT (EQUAL TYP2 "java.lang.Object"))

;;;; Tue Jun 21 20:33:47 2005

;; (skip-proofs 
;;  (defthm Interface-is-only-subclass-of-java-lang-Object
;;    (implies (and (ISINTERFACE (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S)))
;;                  (not (equal typ1 typ2))
;;                  (consistent-state s)
;;                  (not (equal typ2 "java.lang.Object")))
;;             (not (BCV::ISJAVASUBCLASSOF TYP1 TYP2
;;                                         (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S))))))))

(encapsulate ()
 (local (include-book "base-consistent-state-class-names-are-string"))
 (defthm consistent-state-class-name-is-stringp
   (implies (and (class-by-name name (instance-class-table s))
                 (consistent-state s))
            (stringp name))
   :rule-classes :forward-chaining))


(defthm array-type-not-bound?
  (implies (and (consistent-state s)
                (ARRAY-TYPE? TYP1))
           (not (isClassTerm (class-by-name typ1 (instance-class-table s))))))


(defthm primitive-type-not-bound?
  (implies (and (consistent-state s)
                (primitive-type? typ1))
           (not (isClassTerm (class-by-name typ1 (instance-class-table s)))))
  :hints (("Goal" :in-theory (enable primitive-type?))))



(encapsulate ()
 (local (include-book "base-consistent-state-lookupfield-support"))
 (defthm consistent-state-implie-super-of-interface-is-java-lang-Object
   (implies (and (consistent-state s)
                 (isInterface (class-by-name name (instance-class-table s))))
            (equal (super (class-by-name name (instance-class-table s)))
                   "java.lang.Object"))))


;; (defthm bcv-isSuperclass1-djvm-isSubclass1
;;   (implies (and (bcv::isJavaSubclassof typ1 typ2 (bcv::scl-jvm2bcv
;;                                                   (env-class-table (env s))))
;;                 (isClassTerm (class-by-name typ1 (instance-class-table s)))
;;                 (isClassTerm (class-by-name typ2 (instance-class-table s)))
;;                 (class-table-is-loaded-from (instance-class-table s)
;;                                             (env-class-table (env s)))
;;                 (no-fatal-error? s)
;;                 (consistent-state s))
;;            (car (isSuperClass1 typ1 typ2 s nil)))
;;   :hints (("Goal" :do-not '(generalize)
;;            :in-theory (e/d (class-exists? class-loaded?) (isClassTerm)))
;;           ("Subgoal *1/4" :expand (ISSUPERCLASS1 TYP1 TYP2 S NIL))
;;           ("Subgoal *1/3" :expand (ISSUPERCLASS1 TYP1 TYP2 S NIL))))



;;; need to show that "java.lang.Object" is superclass of everyone.
;;;
;;; we then show that issuperclass1 is not symentric
;;;
;;; when there is no loop!! 
;;;

(defthm java-lang-Object-not-isSuperClass1
  (implies (not (equal any "java.lang.Object"))
           (not (car (isSuperClass1 "java.lang.Object" any s seen)))))

(defthm consistent-state-implies-isClassTerm-java-lang-Object
  (implies (consistent-state s)
           (isClassTerm (class-by-name "java.lang.Object" 
                                       (instance-class-table s))))
  :hints (("Goal" :in-theory (e/d (consistent-state boot-strap-class-okp)
                                  (isClassTerm)))))


(defthm consistent-state-implies-class-table-is-loaded-from
  (implies (consistent-state s)
           (class-table-is-loaded-from (instance-class-table s)
                                       (env-class-table (env s))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))
  


(defthm java-lang-Object-not-java-subclass
  (implies (and (consistent-state s)
                (no-fatal-error? s)
                (isClassTerm (class-by-name any (instance-class-table s)))
                (not (equal any "java.lang.Object")))
           (not (bcv::isjavasubclassof "java.lang.Object" any 
                                       (bcv::scl-jvm2bcv (env-class-table (env s))))))
  :hints (("Goal" :use ((:instance bcv-isSuperclass1-djvm-isSubclass1
                                   (typ1 "java.lang.Object")
                                   (typ2 any)))
           :in-theory (disable isClassTerm))))



(defthm |Subgoal *1/5''|
  (IMPLIES
   (AND
    (BCV::SUPERCLASS-NO-LOOP1 TYP1
                              (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S)))
                              NIL)
    (BCV::ISCLASSTERM
     (BCV::CLASS-BY-NAME TYP1
                         (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S)))))
    (NOT (EQUAL TYP1 TYP2))
    (CAR (ISASSIGNABLETO (SUPER (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S)))
                         TYP2 S))
    (BCV::ISJAVASUBCLASSOF
     (SUPER (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S)))
     TYP2
     (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S))))
    (BCV::ISCLASSTYPE (FIX-SIG TYP1))
    (BCV::ISCLASSTYPE (FIX-SIG TYP2))
    (ISCLASSTERM (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S)))
    (ISCLASSTERM (CLASS-BY-NAME TYP2 (INSTANCE-CLASS-TABLE S)))
    (NOT (ISINTERFACE (CLASS-BY-NAME TYP2 (INSTANCE-CLASS-TABLE S))))
    (CONSISTENT-STATE S)
    (NO-FATAL-ERROR? S)
    (CLASS-TABLE-IS-LOADED-FROM (INSTANCE-CLASS-TABLE S)
                                (ENV-CLASS-TABLE (ENV S))))
   (CAR (ISASSIGNABLETO TYP1 TYP2 S)))
  :hints (("Goal" :expand (ISASSIGNABLETO TYP1 TYP2 S)
           :in-theory (e/d () (isClassTerm
                               bcv::isArrayType
                               array-type?
                               bcv::isClassType)))))


(defthm |Subgoal *1/4''|
  (IMPLIES
   (AND
    (BCV::SUPERCLASS-NO-LOOP1 TYP1
                              (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S)))
                              NIL)
    (BCV::ISCLASSTERM
     (BCV::CLASS-BY-NAME TYP1
                         (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S)))))
    (NOT (EQUAL TYP1 TYP2))
    (NOT
     (ISCLASSTERM
      (CLASS-BY-NAME (SUPER (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S)))
                     (INSTANCE-CLASS-TABLE S))))
    (BCV::ISJAVASUBCLASSOF
     (SUPER (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S)))
     TYP2
     (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S))))
    (BCV::ISCLASSTYPE (FIX-SIG TYP1))
    (BCV::ISCLASSTYPE (FIX-SIG TYP2))
    (ISCLASSTERM (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S)))
    (ISCLASSTERM (CLASS-BY-NAME TYP2 (INSTANCE-CLASS-TABLE S)))
    (NOT (ISINTERFACE (CLASS-BY-NAME TYP2 (INSTANCE-CLASS-TABLE S))))
    (CONSISTENT-STATE S)
    (NO-FATAL-ERROR? S)
    (CLASS-TABLE-IS-LOADED-FROM (INSTANCE-CLASS-TABLE S)
                                (ENV-CLASS-TABLE (ENV S))))
   (CAR (ISASSIGNABLETO TYP1 TYP2 S)))
  :hints (("Goal" :expand (ISASSIGNABLETO TYP1 TYP2 S)
           :in-theory (e/d () (isClassTerm
                               bcv::isArrayType
                               array-type?
                               bcv::isClassType)))))



(defthm |Subgoal *1/3''|
  (IMPLIES
   (AND
    (BCV::SUPERCLASS-NO-LOOP1 TYP1
                              (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S)))
                              NIL)
    (BCV::ISCLASSTERM
     (BCV::CLASS-BY-NAME TYP1
                         (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S)))))
    (NOT (EQUAL TYP1 TYP2))
    (NOT (BCV::ISCLASSTYPE
          (FIX-SIG (SUPER (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S))))))
    (BCV::ISJAVASUBCLASSOF
     (SUPER (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S)))
     TYP2
     (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S))))
    (BCV::ISCLASSTYPE (FIX-SIG TYP1))
    (BCV::ISCLASSTYPE (FIX-SIG TYP2))
    (ISCLASSTERM (CLASS-BY-NAME TYP1 (INSTANCE-CLASS-TABLE S)))
    (ISCLASSTERM (CLASS-BY-NAME TYP2 (INSTANCE-CLASS-TABLE S)))
    (NOT (ISINTERFACE (CLASS-BY-NAME TYP2 (INSTANCE-CLASS-TABLE S))))
    (CONSISTENT-STATE S)
    (NO-FATAL-ERROR? S)
    (CLASS-TABLE-IS-LOADED-FROM (INSTANCE-CLASS-TABLE S)
                                (ENV-CLASS-TABLE (ENV S))))
   (CAR (ISASSIGNABLETO TYP1 TYP2 S)))
  :hints (("Goal" :expand (ISASSIGNABLETO TYP1 TYP2 S)
           :in-theory (e/d () (isClassTerm
                               bcv::isArrayType
                               array-type?
                               bcv::isClassType)))))



(defthm bcv-isJavaAssignable-djvm-isJavaAssignable-lemma
  (implies (and (bcv::isJavaAssignable (fix-sig typ1) (fix-sig typ2)
                                       (BCV::SCL-JVM2BCV (env-class-table (env s))))
                (bcv::isClassType (fix-sig typ1))
                (bcv::isClassType (fix-sig typ2))
                (isClassTerm (class-by-name typ1 (instance-class-table s)))
                (isClassTerm (class-by-name typ2 (instance-class-table s)))
                (not (ISINTERFACE (CLASS-BY-NAME TYP2 (INSTANCE-CLASS-TABLE
                                                       S))))
                (not (BCV::CLASSISINTERFACE
                      (BCV::CLASS-BY-NAME TYP2
                                          (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S))))))
                (consistent-state s)
                (no-fatal-error? s))
           (car (djvm::isAssignableTo typ1 typ2 s)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d () (isClassTerm
                               bcv::isArrayType
                               array-type?
                               bcv::isClassType)))))

;; (defthm bcv-isAssignable-implies-djvm-isAssignableTo-if-not-interface
;;   (implies (bcv::isAssignable (fix-sig typ1) (fix-sig typ2) env)
;;            (car (djvm::isAssignableTo typ1 typ2 s))))


(defthm not-bcv-isAssignable-nil-into-any-class-type
  (not (BCV::ISASSIGNABLE
         NIL
         (BCV::PREFIX-CLASS (BCV::FIELDCLASSNAMECP (BCV::ARG1 INST)))
         any)))



(defthm bcv-isAssignable-expander
  (implies (syntaxp (equal (car bcv::t1) 'quote))
           (equal (BCV::ISASSIGNABLE
                   BCV::T1 BCV::T2 BCV::ENV)
                  (LET
                   ((BCV::CL (BCV::CLASSTABLEENVIRONMENT BCV::ENV)))
                   (IF
                    (EQUAL BCV::T1 BCV::T2)
                    T
                    (COND
                     ((AND (EQUAL BCV::T1 'ONEWORD)
                           (EQUAL BCV::T2 'TOPX))
                      T)
                     ((AND (EQUAL BCV::T1 'TWOWORD)
                           (EQUAL BCV::T2 'TOPX))
                      T)
                     ((EQUAL BCV::T1 'INT)
                      (BCV::ISASSIGNABLE 'ONEWORD
                                         BCV::T2 BCV::ENV))
                     ((EQUAL BCV::T1 'FLOAT)
                      (BCV::ISASSIGNABLE 'ONEWORD
                                         BCV::T2 BCV::ENV))
                     ((EQUAL BCV::T1 'LONG)
                      (BCV::ISASSIGNABLE 'TWOWORD
                                         BCV::T2 BCV::ENV))
                     ((EQUAL BCV::T1 'DOUBLE)
                      (BCV::ISASSIGNABLE 'TWOWORD
                                         BCV::T2 BCV::ENV))
                     ((EQUAL BCV::T1 'REFERENCE)
                      (BCV::ISASSIGNABLE 'ONEWORD
                                         BCV::T2 BCV::ENV))
                     ((EQUAL 'UNINITIALIZED BCV::T1)
                      (BCV::ISASSIGNABLE 'REFERENCE
                                         BCV::T2 BCV::ENV))
                     ((BCV::ISCLASSTYPE BCV::T1)
                      (OR (BCV::ISASSIGNABLE 'REFERENCE
                                             BCV::T2 BCV::ENV)
                          (BCV::ISJAVAASSIGNABLE BCV::T1 BCV::T2 BCV::CL)))
                     ((BCV::ISARRAYTYPE BCV::T1)
                      (OR
                       (BCV::ISASSIGNABLE 'REFERENCE
                                          BCV::T2 BCV::ENV)
                       (AND (BCV::ISCLASSTYPE BCV::T2)
                            (BCV::ISJAVAASSIGNABLE BCV::T1 BCV::T2 BCV::CL))
                       (AND (BCV::ISARRAYTYPE BCV::T2)
                            (BCV::ISJAVAASSIGNABLE BCV::T1 BCV::T2 BCV::CL))))
                     ((EQUAL BCV::T1 'UNINITIALIZEDTHIS)
                      (BCV::ISASSIGNABLE 'UNINITIALIZED
                                         BCV::T2 BCV::ENV))
                     ((BCV::ISUNINITIALIZEDOBJECT BCV::T1)
                      (BCV::ISASSIGNABLE 'UNINITIALIZED
                                         BCV::T2 BCV::ENV))
                     ((BCV::ISNULLTYPE BCV::T1)
                      (OR (BCV::ISCLASSTYPE BCV::T2)
                          (BCV::ISARRAYTYPE BCV::T2)
                          (BCV::ISASSIGNABLE '(CLASS "java.lang.Object")
                                             BCV::T2 BCV::ENV)))
                     (T NIL)))))))

(defthm not-class-type-or-array-type-implies-not-bcv-isAssignable-into-any-class-type
  (implies (and (not (bcv::isClassType type))
                (not (bcv::isArrayType type))
                (not (bcv::isnulltype type)))
           (not (BCV::ISASSIGNABLE type
                                   (BCV::PREFIX-CLASS typ2)
                                   env))))




;; (defthm bcv-isJavaAssignable-djvm-isJavaAssignable-lemma
;;   (implies (and (bcv::isJavaAssignable (fix-sig typ1) (fix-sig typ2)
;;                                        (BCV::SCL-JVM2BCV (env-class-table (env s))))
;;                 (bcv::isClassType (fix-sig typ1))
;;                 (bcv::isClassType (fix-sig typ2))
;;                 (isClassTerm (class-by-name typ1 (instance-class-table s)))
;;                 (isClassTerm (class-by-name typ2 (instance-class-table s)))
;;                 (not (ISINTERFACE (CLASS-BY-NAME TYP2 (INSTANCE-CLASS-TABLE
;;                                                        S))))
;;                 (not (BCV::CLASSISINTERFACE
;;                       (BCV::CLASS-BY-NAME TYP2
;;                                           (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S))))))
;;                 (consistent-state s)
;;                 (no-fatal-error? s))
;;            (car (djvm::isAssignableTo typ1 typ2 s)))
;;   :hints (("Goal" :do-not '(generalize)
;;            :in-theory (e/d () (isClassTerm
;;                                bcv::isArrayType
;;                                array-type?
;;                                bcv::isClassType)))))


(defthm value-sig-consistent-value-x-reduce-if-class-type
  (implies  (and (bcv::isClassType (value-sig v cl hp hp-init method-ptr))
                 (consistent-value-x v cl hp))
            (equal (value-sig v cl hp hp-init method-ptr)
                   (fix-sig (obj-type (deref2 v hp)))))
  :hints (("Goal" :in-theory (e/d (consistent-value-x consistent-value) ()))))


(defthm value-sig-consistent-value-x-reduce-if-array-type
  (implies  (and (bcv::isArrayType (value-sig v cl hp hp-init method-ptr))
                 (consistent-value-x v cl hp))
            (equal (value-sig v cl hp hp-init method-ptr)
                   (fix-sig (obj-type (deref2 v hp)))))
  :hints (("Goal" :in-theory (e/d (consistent-value-x consistent-value) ()))))
   


(defthm bcv-isAssignable-value-sig-bcv-isAssignable-fix-sig
  (implies (and (bcv::isassignable (value-sig v cl hp hp-init method-ptr)
                                   type env)
                (consistent-value-x v cl hp)
                (bcv::isClassType typ)
                (bcv::isClassType (value-sig v cl hp hp-init method-ptr)))
           (bcv::isassignable (fix-sig (obj-type (deref2 v hp)))
                              type
                              env))
  :hints (("Goal" :in-theory (e/d () (bcv::isClassType 
                                      bcv::isassignable)))))



(defthm bcv-isJavaAssignable-value-sig-bcv-isJavaAssignable-fix-sig
  (implies (and (bcv::isJavaAssignable (value-sig v cl hp hp-init method-ptr)
                                   type scl)
                (consistent-value-x v cl hp)
                (bcv::isClassType typ)
                (bcv::isClassType (value-sig v cl hp hp-init method-ptr)))
           (bcv::isJavaAssignable (fix-sig (obj-type (deref2 v hp)))
                                  type
                                  scl))
  :hints (("Goal" :in-theory (e/d () (bcv::isClassType 
                                      bcv::isassignable)))))



(defthm bcv-isJavaAssignable-value-sig-bcv-isJavaAssignable-fix-sig-specific
  (implies (and (bcv::isJavaAssignable (value-sig v (instance-class-table s)
                                                  (heap s) (heap-init-map
                                                                 (aux s))
                                                  (method-ptr
                                                   (current-frame s)))
                                   type scl)
                (consistent-value-x v (instance-class-table s) (heap s))
                (bcv::isClassType typ)
                (bcv::isClassType (value-sig v (instance-class-table s)
                                             (heap s) 
                                             (heap-init-map (aux s))
                                             (method-ptr (current-frame s)))))
           (bcv::isJavaAssignable (fix-sig (obj-type (deref2 v (heap s))))
                                  type
                                  scl))
  :hints (("Goal" :in-theory (e/d () (bcv::isClassType 
                                      value-sig fix-sig
                                      bcv::isJavaAssignable
                                      bcv::isassignable)))))


;;;
;;; judged more complicated!! 
;;;

;; (defthm bcv-isJavaAssignable-djvm-isJavaAssignable-lemma
;;   (implies (and (bcv::isJavaAssignable (fix-sig typ1) (fix-sig typ2)
;;                                        (BCV::SCL-JVM2BCV (env-class-table (env s))))
;;                 (bcv::isClassType (fix-sig typ1))
;;                 (bcv::isClassType (fix-sig typ2))
;;                 (isClassTerm (class-by-name typ1 (instance-class-table s)))
;;                 (isClassTerm (class-by-name typ2 (instance-class-table s)))
;;                 (not (ISINTERFACE (CLASS-BY-NAME TYP2 (INSTANCE-CLASS-TABLE
;;                                                        S))))
;;                 (not (BCV::CLASSISINTERFACE
;;                       (BCV::CLASS-BY-NAME TYP2
;;                                           (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S))))))
;;                 (consistent-state s)
;;                 (no-fatal-error? s))
;;            (car (djvm::isAssignableTo typ1 typ2 s)))
;;   :hints (("Goal" :do-not '(generalize)
;;            :in-theory (e/d () (isClassTerm
;;                                bcv::isArrayType
;;                                array-type?
;;                                bcv::isClassType)))))


(defthm consistent-state-implies-fix-sig-is-prefix-class-lemma
  (implies (stringp name)
           (equal (bcv::prefix-class name)
                  (fix-sig name)))
  :hints (("Goal" :in-theory (enable primitive-type? isarraytype))))


(defthm consistent-state-implies-fix-sig-is-prefix-class
  (implies (and (consistent-state s)
                (isClassTerm (class-by-name name (instance-class-table s))))
           (equal (bcv::prefix-class name)
                  (fix-sig name)))
  :hints (("Goal" :in-theory (enable primitive-type? isarraytype))))

(defthm fix-equal-equal
  (implies (bcv::isClassType (fix-sig typ1))
           (equal (EQUAL (FIX-SIG typ2)
                         (FIX-SIG TYP1))
                  (equal typ2 typ1)))
  :hints (("Goal" :in-theory (enable primitive-type?))))
            

(defthm isClassTerm-class-by-name
  (implies (isClassTerm (class-by-name name cl))
           (class-by-name name cl))
  :rule-classes :forward-chaining)


(defthm isassignableto-equal-equal-t
  (CAR (ISASSIGNABLETO TYP TYP S)))

;; (defthm NULL-is-bcv-assignable-to-value
;;   (BCV::ISJAVAASSIGNABLE 'NULL
;;                          (FIX-SIG TYP)
;;                          (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S)))))

(local 
 (defthm bcv-class-isinterface-normlaize
   (equal (BCV::CLASSISINTERFACE
           (BCV::CLASS-BY-NAME TYP (BCV::SCL-JVM2BCV scl)))
          (mem '*interface* (accessflags-s (mv-nth 1 (class-by-name-s typ scl)))))
   :hints (("Goal" :in-theory (enable bcv::classisinterface
                                      bcv::make-class-term
                                      accessflags-s
                                      bcv::classclassname
                                      classname-s
                                      bcv::class-by-name)
            :do-not '(generalize)))))



(defthm not-interface-implies-not-interface-lemma
  (implies (and (class-table-is-loaded-from cl scl)
                (NOT (BCV::CLASSISINTERFACE
                      (BCV::CLASS-BY-NAME TYP (BCV::SCL-JVM2BCV scl)))))
           (not (ISINTERFACE (CLASS-BY-NAME TYP cl))))
  :hints (("Goal" :in-theory (enable bcv::classisinterface
                                     isinterface
                                     bcv::class-by-name
                                     classname
                                     bcv::make-class-term)
           :do-not '(generalize))))

(local (in-theory (disable bcv-class-isinterface-normlaize)))

(defthm not-interface-implies-not-interface
  (implies (and (consistent-state s)
                (NOT
                 (BCV::CLASSISINTERFACE
                  (BCV::CLASS-BY-NAME TYP
                                      (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV
                                                                          S)))))))
           (not (ISINTERFACE (CLASS-BY-NAME TYP (INSTANCE-CLASS-TABLE S)))))
  :hints (("Goal" :in-theory (enable consistent-state)
           :use ((:instance not-interface-implies-not-interface-lemma
                            (cl (instance-class-table s))
                            (scl (env-class-table (env s))))))))







(defthm fix-sig-never-null
  (not (EQUAL (FIX-SIG any) 'NULL)))


;; (defthm |Subgoal 8'''|
;;   (IMPLIES
;;    (AND
;;     (EQUAL (FIX-SIG (OBJ-TYPE (DEREF2 V (HEAP S))))
;;            (FIX-SIG TYP))
;;     (NOT (WFF-REFP V))
;;     (BCV::ISCLASSTYPE (VALUE-SIG V (INSTANCE-CLASS-TABLE S)
;;                                  (HEAP S)
;;                                  (HEAP-INIT-MAP (AUX S))
;;                                  (METHOD-PTR (CURRENT-FRAME S))))
;;     (ISCLASSTERM (CLASS-BY-NAME (OBJ-TYPE (DEREF2 V (HEAP S)))
;;                                 (INSTANCE-CLASS-TABLE S)))
;;     (ISCLASSTERM (CLASS-BY-NAME TYP (INSTANCE-CLASS-TABLE S)))
;;     (NO-FATAL-ERROR? S)
;;     (bcv::isClassType (fix-sig typ))
;;     (CONSISTENT-VALUE-X V (INSTANCE-CLASS-TABLE S)
;;                         (HEAP S))
    
;;     (CONSISTENT-STATE S)
;;     (BCV::CLASS-BY-NAME TYP
;;                         (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S))))
;;     (NOT
;;      (BCV::CLASSISINTERFACE
;;       (BCV::CLASS-BY-NAME TYP
;;                           (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S)))))))
;;    (CAR (ISASSIGNABLETO (OBJ-TYPE (DEREF2 V (HEAP S)))
;;                         TYP S)))
;;   :hints (("Goal" :in-theory (disable isassignableto 
;;                                       isclassterm
;;                                       bcv::isclasstype
;;                                       fix-sig
;;                                       bcv::isjavaassignable))))



;;   (BCV::ISCLASSTYPE (VALUE-SIG V (INSTANCE-CLASS-TABLE S)
;;                                (HEAP S)
;;                                (HEAP-INIT-MAP (AUX S))
;;                                (METHOD-PTR (CURRENT-FRAME S))))



;; (defthm value-sig-consistent-value-x-reduce-if-class-type
;;   (implies  (and (bcv::isClassType (value-sig v cl hp hp-init method-ptr))
;;                  (consistent-value-x v cl hp))
;;             (equal (value-sig v cl hp hp-init method-ptr)
;;                    (fix-sig (obj-type (deref2 v hp)))))
;;   :hints (("Goal" :in-theory (e/d (consistent-value-x consistent-value)
;;   ()))))



(defthm value-sig-consistent-value-x-reduce-isClassType-not-arrayType
   (implies  (and (bcv::isClassType (value-sig v cl hp hp-init method-ptr))
                  (consistent-value-x v cl hp))
             (not (bcv::isArrayType (fix-sig (obj-type (deref2 v hp))))))
   :hints (("Goal" :in-theory (e/d (consistent-value-x consistent-value) ()))))



(defthm isMatchingType-isAssignableTo-lemma-1
  (implies 
   (and (bcv::isassignable
         (value-sig v 
                    (instance-class-table s)
                    (heap s)
                    (heap-init-map (aux s))
                    (method-ptr (current-frame s)))
         (BCV::PREFIX-CLASS typ)
         (ENV-SIG S))
        (not (NULLp v))
        (bcv::isClassType (fix-sig typ))
        (bcv::isClassType (value-sig v 
                                      (instance-class-table s)
                                      (heap s)
                                      (heap-init-map (aux s))
                                      (method-ptr
                                      (current-frame s))))
        (isClassTerm (class-by-name (obj-type (deref2 v (heap s)))
                                    (instance-class-table s)))
        (isClassTerm (class-by-name typ
                                    (instance-class-table s)))
        (no-fatal-error? s)
        (consistent-value-x v (instance-class-table s) (heap s))
        (consistent-state s)
        (bcv::class-by-name typ
                            (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S)))
        (not (bcv::classisinterface  (bcv::class-by-name typ
                                                         (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S))))))
   (CAR (ISASSIGNABLETO (OBJ-TYPE (DEREF2 v (HEAP S)))
                        typ S)))
  :hints (("Goal" 
           :in-theory (e/d ()(isassignableto
                              bcv::isClassType
                              bcv::isArrayType
                              bcv::prefix-class
                              fix-sig
                              value-sig
                              (value-sig)
                              (fix-sig)
                              isClassTerm
                              bcv::isJavaAssignable))
           :do-not '(generalize fertilize))))

(defthm bcv-isAssignable-array-to-non-interface-class-must-be-java-lang-Object
  (implies (and (bcv::isassignable typ1 (bcv::prefix-class typ2) env)
                (not (equal typ2 "java.lang.Object"))
                (bcv::isArrayType typ1))
           (bcv::classisinterface 
            (bcv::class-by-name typ2 
                                (bcv::classtableenvironment env)))))
;;;
;;; if array is assignable to prefix-class. 
;;;
;;; the fielclassname is java.lang.Object or some interface type!! 
;;;


(defthm isassignableto-java-lang-Object
  (implies (and (consistent-state s)
                (isClassTerm (class-by-name typ (instance-class-table s))))
           (car (isassignableto typ "java.lang.Object" s)))
  :hints (("Goal" :in-theory (disable isClassTerm))))


(defthm isassignableto-java-lang-Object-2
  (implies (and (consistent-state s)
                (isArrayType typ))
           (car (isassignableto typ "java.lang.Object" s)))
  :hints (("Goal" :in-theory (e/d (primitive-type? isArrayType)
                                  (isClassTerm)))))


(defthm consistent-value-x-bcv-arraytype-then-isArrayType
  (implies (and (consistent-value-x v cl hp)
                (bcv::isarraytype (value-sig v cl hp hp-init method-ptr)))
           (isArrayType (obj-type (deref2 v hp))))
  :hints (("Goal" :in-theory (enable consistent-value-x
                                     isArrayType
                                     obj-type fix-sig
                                     consistent-value))))



(defthm consistent-value-x-bcv-arraytype-then-isArrayType-f
  (implies (and (bcv::isarraytype (value-sig v cl hp hp-init method-ptr))
                (consistent-value-x v cl hp))
           (isArrayType (obj-type (deref2 v hp))))
  :hints (("Goal" :in-theory (enable consistent-value-x
                                     isArrayType
                                     obj-type fix-sig
                                     consistent-value)))
  :rule-classes :forward-chaining)


(defthm isMatchingType-isAssignableTo-lemma-2
  (implies 
   (and (bcv::isassignable
         (value-sig v 
                    (instance-class-table s)
                    (heap s)
                    (heap-init-map (aux s))
                    (method-ptr (current-frame s)))
         (BCV::PREFIX-CLASS typ)
         (ENV-SIG S))
        (not (NULLp v))
        (bcv::isArrayType (value-sig v 
                                     (instance-class-table s)
                                     (heap s)
                                     (heap-init-map (aux s))
                                     (method-ptr
                                      (current-frame s))))
        (isClassTerm (class-by-name typ
                                    (instance-class-table s)))
        (no-fatal-error? s)
        (consistent-value-x v (instance-class-table s) (heap s))
        (consistent-state s)
        (bcv::class-by-name typ
                            (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S)))
        (not (bcv::classisinterface  (bcv::class-by-name typ
                                                         (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S))))))
   (CAR (ISASSIGNABLETO (OBJ-TYPE (DEREF2 v (HEAP S)))
                        typ S)))
  :hints (("Goal" 
           :in-theory (e/d ()(isassignableto
                              bcv::isClassType
                              bcv::isArrayType
                              bcv::prefix-class
                              fix-sig
                              value-sig
                              (value-sig)
                              (fix-sig)
                              env-sig
                              bcv::isassignable
                              isClassTerm
                              VALUE-SIG-CONSISTENT-VALUE-X-REDUCE-IF-ARRAY-TYPE
                              bcv::classtableenvironment
                              bcv::isJavaAssignable))
           :do-not '(generalize fertilize)
           :cases ((equal typ "java.lang.Object")))
          ("Subgoal 2" :use ((:instance
                              bcv-isAssignable-array-to-non-interface-class-must-be-java-lang-Object
                              (typ2 typ)
                              (typ1 (VALUE-SIG V (INSTANCE-CLASS-TABLE S)
                                               (HEAP S)
                                               (HEAP-INIT-MAP (AUX S))
                                               (METHOD-PTR (CURRENT-FRAME S))))
                              (env (env-sig s)))))))



;;; very twisted!! 

(defthm not-NULLp-implies-not-bcv-is
  (implies (and (not (NULLp v))
                (consistent-value-x v cl hp))
           (not (bcv::isnulltype (value-sig v 
                                            cl hp hp-init method-ptr))))
  :hints (("Goal" :in-theory (enable consistent-value-x consistent-value))))


(defthm consistent-object-not-array-type-implies-class-loaded
  (implies (and (consistent-object obj hp cl)
                (not (isArrayType (obj-type obj))))
           (isClassTerm (class-by-name (obj-type obj) cl)))
  :hints (("Goal" :in-theory (enable consistent-object))))




(defthm consistent-value-x-bcv-class-type-then-REFp
  (implies (and (consistent-value-x v cl hp)
                (bcv::isClassType (value-sig v cl hp hp-init method-ptr)))
           (REFp v hp))
  :hints (("Goal" :in-theory (enable consistent-value-x consistent-value))))


(defthm consistent-value-x-bcv-class-type-then-not-NULL
  (implies (and (consistent-value-x v cl hp)
                (bcv::isClassType (value-sig v cl hp hp-init method-ptr)))
           (not (NULLp v)))
  :hints (("Goal" :in-theory (enable consistent-value-x consistent-value))))


(defthm consistent-value-x-bcv-class-type-then-not-array-type
  (implies (and (consistent-value-x v cl hp)
                (bcv::isClassType (value-sig v cl hp hp-init method-ptr)))
           (not (isArrayType (obj-type (deref2 v hp)))))
  :hints (("Goal" :in-theory (enable consistent-value-x
                                     isArrayType
                                     obj-type fix-sig
                                     consistent-value))
          ("Subgoal 9" :expand (FIX-SIG (NTH 3 (COMMON-INFO (DEREF2 V HP)))))))



;; (defthm consistent-object-not-array-type-implies-class-loaded
;;   (implies (and (consistent-object obj hp cl)
;;                 (not (isArrayType (obj-type obj))))
;;            (isClassTerm (class-by-name (obj-type obj) cl)))
;;   :hints (("Goal" :in-theory (enable consistent-object))))



(defthm consistent-heap1-implies-if-bound-then-consistent-object
  (implies (and (consistent-heap1 hp1 hp cl id)
                (bound? v hp1))
           (consistent-object (binding v hp1) hp cl))
  :hints (("Goal" :in-theory (e/d (bound? binding) (consistent-object)))))
  

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




(defthm consistent-value-x-bcv-class-type-then-REFp-f
  (implies (and (bcv::isClassType (value-sig v cl hp hp-init method-ptr))
                (consistent-value-x v cl hp))
           (REFp v hp))
  :hints (("Goal" :in-theory (disable bcv::isClassType REFp value-sig)))
  :rule-classes :forward-chaining)


(defthm consistent-value-x-bcv-class-type-then-not-NULL-f
  (implies (and (bcv::isClassType (value-sig v cl hp hp-init method-ptr))
                (consistent-value-x v cl hp))
           (not (NULLp v)))
  :hints (("Goal" :in-theory (enable bcv::isClassType REFp value-sig)))
  :rule-classes :forward-chaining)
  


(defthm consistent-value-x-bcv-class-type-then-not-array-type-f
  (implies (and (bcv::isClassType (value-sig v cl hp hp-init method-ptr))
                (consistent-value-x v cl hp))
           (not (isArrayType (obj-type (deref2 v hp)))))
  :hints (("Goal" :in-theory (disable consistent-value-x
                                      bcv::isClassType
                                      isArrayType value-sig
                                      obj-type fix-sig
                                      consistent-value)))
  :rule-classes :forward-chaining)



(defthm consistent-state-consistent-value-x-implies-class-loaded
  (implies (and (consistent-state s)
                (consistent-value-x v (instance-class-table s) (heap s))
                (bcv::isClassType (value-sig v (instance-class-table s)
                                             (heap s)
                                             (heap-init-map (aux s))
                                             (method-ptr (current-frame s)))))
           (isClassTerm (class-by-name (obj-type (deref2 v (heap s)))
                                       (instance-class-table s))))
  :hints (("Goal" :in-theory (e/d ()
                                  (value-sig 
                                   REFp NULLp
                                   bcv::isClassType
                                   isClassTerm))
           :use ((:instance
                  consistent-object-not-array-type-implies-class-loaded
                  (obj (deref2 v (heap s)))
                  (cl (instance-class-table s))
                  (hp (heap s)))))))
  


;; (defthm |Subgoal 1.3|
;;   (IMPLIES
;;    (AND
;;     (BCV::ISARRAYTYPE (VALUE-SIG V (INSTANCE-CLASS-TABLE S)
;;                                  (HEAP S)
;;                                  (HEAP-INIT-MAP (AUX S))
;;                                  (METHOD-PTR (CURRENT-FRAME S))))
;;     (BCV::ISASSIGNABLE (FIX-SIG (OBJ-TYPE (DEREF2 V (HEAP S))))
;;                        (BCV::PREFIX-CLASS TYP)
;;                        (ENV-SIG S))
;;     (NOT (NULLP V))
;;     (ISCLASSTERM (CLASS-BY-NAME TYP (INSTANCE-CLASS-TABLE S)))
;;     (NO-FATAL-ERROR? S)
;;     (CONSISTENT-VALUE-X V (INSTANCE-CLASS-TABLE S)
;;                         (HEAP S))
;;     (CONSISTENT-STATE S)
;;     (BCV::CLASS-BY-NAME TYP (NTH 6 (ENV-SIG S)))
;;     (NOT (BCV::CLASSISINTERFACE (BCV::CLASS-BY-NAME TYP (NTH 6 (ENV-SIG S))))))
;;    (CAR (ISASSIGNABLETO (OBJ-TYPE (DEREF2 V (HEAP S)))
;;                         TYP S)))
;;   :hints (("Goal" :in-theory (e/d () 
;;                                   (isassignableto
;;                                    isClassTerm
;;                                    bcv::isArrayType
;;                                    value-sig
;;                                    bcv::isnulltype
;;                                    NULLp
;;                                    bcv::prefix-class
;;                                    bcv::isClassType
;;                                    bcv::isassignable
;;                                    env-sig)))))

(encapsulate () 
  (local (include-book "base-consistent-state-class-names-are-string"))
  (defthm consistent-state-class-name-is-stringp
    (implies (and (class-by-name name (instance-class-table s))
                  (consistent-state s))
             (stringp name))
    :rule-classes :forward-chaining))



(defthm isClassTerm-then-fix-sig-bcv-isClassType
  (implies (and (isClassTerm (class-by-name typ (instance-class-table s)))
                (consistent-state s))
           (bcv::isClassType (fix-sig typ)))
  :hints (("Goal" :cases ((or (primitive-type? typ)
                              (isArrayType typ)))
           :in-theory (enable primitive-type? isArrayType)))
  :rule-classes :forward-chaining)



(defthm bcv-isAssignable-value-sig-djvm-isAssignableTo
  (implies 
   (and (bcv::isassignable
         (value-sig v 
                    (instance-class-table s)
                    (heap s)
                    (heap-init-map (aux s))
                    (method-ptr (current-frame s)))
         (BCV::PREFIX-CLASS typ)
         (ENV-SIG S))
        (not (NULLp v))
        (isClassTerm (class-by-name typ
                                    (instance-class-table s)))
        (no-fatal-error? s)
        (consistent-value-x v (instance-class-table s) (heap s))
        (consistent-state s)
        (bcv::class-by-name typ
                            (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S)))
        (not (bcv::classisinterface  (bcv::class-by-name typ
                                                         (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S))))))
   (CAR (ISASSIGNABLETO (OBJ-TYPE (DEREF2 v (HEAP S)))
                        typ S)))
  :hints (("Goal" :in-theory (e/d () 
                                  (isassignableto
                                   isClassTerm
                                   bcv::isArrayType
                                   value-sig
                                   bcv::isnulltype
                                   NULLp
                                   fix-sig
                                   consistent-state-implies-fix-sig-is-prefix-class-lemma
                                   CONSISTENT-STATE-IMPLIES-FIX-SIG-IS-PREFIX-CLASS
                                   bcv::prefix-class
                                   bcv::isClassType
                                   bcv::isassignable
                                   env-sig))
           :cases ((or (bcv::isArrayType (value-sig v 
                                                    (instance-class-table s)
                                                    (heap s)
                                                    (heap-init-map (aux s))
                                                    (method-ptr (current-frame
                                                                 s))))
                       (bcv::isclassType (value-sig v 
                                                    (instance-class-table s)
                                                    (heap s)
                                                    (heap-init-map (aux s))
                                                    (method-ptr (current-frame
                                                                 s))))
                       (bcv::isnullType (value-sig v 
                                                   (instance-class-table s)
                                                   (heap s)
                                                   (heap-init-map (aux s))
                                                   (method-ptr (current-frame
                                                                s)))))))))
          



(defthm bcv-fieldclassnamecp-normalize
  (equal (bcv::fieldclassnamecp (bcv::arg1 inst))
         (fieldcp-classname (arg inst))))
  


(encapsulate () 
  (local (include-book "base-bcv-fact-isAssignable-prefixclass-not-category2"))
  (defthm isAssignable-car-opstack-sig-to-class-implies-car-opstack-reduce-to-value-sig
    (implies (bcv::isAssignable (car (opstack-sig stk cl hp hp-init method-ptr))
                                (bcv::prefix-class any) 
                                env)
             (not (canPopCategory2 stk)))
    :hints (("Goal" :in-theory (disable bcv-isAssignable-expander)))))

;; ;; Warnings:  Free and Non-rec
;; ;; Time:  148.52 seconds (prove: 148.30, print: 0.20, other: 0.02)
;; ;;  ISASSIGNABLE-CAR-OPSTACK-SIG-TO-CLASS-IMPLIES-CAR-OPSTACK-REDUCE-TO-VALUE-SIG

;; ;;; too slow moved to some other book!! 



(defthm isMatchingType-isAssignableTo-lemma
  (implies 
   (and (bcv::isassignable
         (value-sig (topstack s)
                    (instance-class-table s)
                    (heap s)
                    (heap-init-map (aux s))
                    (method-ptr (current-frame s)))
         (BCV::PREFIX-CLASS (BCV::FIELDCLASSNAMECP (BCV::ARG1 INST)))
         (ENV-SIG S))
        (not (NULLp (topstack s)))
        (consistent-value-x (topstack s)
                            (instance-class-table s) 
                            (heap s))
        (no-fatal-error? s)
        (consistent-state s)
        (isClassTerm (class-by-name (fieldcp-classname (arg inst))
                                    (instance-class-table s)))
        (bcv::class-by-name (bcv::fieldclassnamecp (bcv::arg1 inst))
                            (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S)))
        (not (bcv::classisinterface  (bcv::class-by-name (bcv::fieldclassnamecp (bcv::arg1 inst))
                                                         (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S))))))
   (CAR (ISASSIGNABLETO (OBJ-TYPE (DEREF2 (TOPSTACK S) (HEAP S)))
                        (FIELDCP-CLASSNAME (ARG INST))
                         S)))
  :hints (("Goal" :in-theory (e/d ()
                                  (isassignableto 
                                   bcv::isassignable
                                   arg 
                                   NULLp
                                   value-sig
                                   bcv::isJavaAssignable
                                   bcv::arg1
                                   bcv::fieldclassnamecp
                                   bcv::prefix-class
                                   isClassTerm
                                   fieldcp-classname
                                   bcv::classtableenvironment
                                   bcv::prefix-class 
                                   env-sig
                                   )))))









(defthm isAssignable-car-opstack-sig-to-class-implies-car-opstack-reduce-to-value-sig-specific
  (implies (bcv::isAssignable (car (opstack-sig (operand-stack (current-frame
                                                                s)) cl hp hp-init method-ptr))
                              (bcv::prefix-class any) 
                              env)
           (not (canPopCategory2 (operand-stack (current-frame s)))))
  :hints (("Goal" :in-theory (e/d () (canPopCategory2 
                                      current-frame
                                      bcv::isAssignable
                                      bcv::prefix-class)))))




(defthm isAssignable-car-opstack-sig-to-class-implies-car-opstack-reduce-to-value-sig-specific-further
  (implies (bcv::isAssignable (car (opstack-sig (operand-stack (current-frame
                                                                s)) 
                                                (instance-class-table s)
                                                (heap s)
                                                (heap-init-map (aux s))
                                                (method-ptr (current-frame s))))
                              (bcv::prefix-class any)
                              (env-sig s))
           (not (canPopCategory2 (operand-stack (current-frame s)))))
  :hints (("Goal" :in-theory (e/d () (canPopCategory2 
                                      current-frame
                                      bcv::isAssignable
                                      bcv::prefix-class)))))




(defthm consp-not-canPopCategory2-implies-car-opstack-is-value-stack
  (implies (and (not (canPopCategory2 (operand-stack (current-frame s))))
                (consp (opstack-sig (operand-stack (current-frame s)) cl hp
                                    hp-init method-ptr)))
           (equal (car (opstack-sig  (operand-stack (current-frame s)) cl hp
                                    hp-init method-ptr))
                  (value-sig (topstack s) cl hp hp-init method-ptr)))
  :hints (("Goal" :in-theory (e/d (opstack-sig topStack push) (value-sig
                                                               canPopCategory2))
           :expand (opstack-sig  (operand-stack (current-frame s)) cl hp
                                    hp-init method-ptr))))





(defthm not-canPopCategor1-consistent-opstack-implies-canPopCategory1
  (implies (and  (not (canPopCategory2 opstack))
                 (consp opstack)
                 (consistent-opstack  opstack cl hp))
           (canPopCategory1 opstack))
  :hints (("Goal" :in-theory (e/d (consistent-opstack) 
                                  (canPopCategory2
                                      current-frame
                                      bcv::isAssignable
                                      bcv::prefix-class)))))



(defthm not-canPopCategor1-consistent-opstack-implies-canPopCategory1-specific
  (implies (and  (not (canPopCategory2 (operand-stack (current-frame s))))
                 (consp (operand-stack (current-frame s)))
                 (consistent-opstack  (operand-stack (current-frame s))
                                      (instance-class-table s)
                                      (heap s)))
           (canPopCategory1 (operand-stack (current-frame s))))
  :hints (("Goal" :in-theory (e/d (consistent-opstack) 
                                  (canPopCategory2
                                      current-frame
                                      bcv::isAssignable
                                      bcv::prefix-class)))))



(defthm consistent-opstack-implies-consistent-value-x-top
  (implies (and (canPopCategory1 opstack)
                (consistent-opstack opstack cl hp))
           (consistent-value-x (car opstack) cl hp)))




(defthm consistent-state-implies-consistent-value-x-topStack
  (implies (and (canPopCategory1 (operand-stack (current-frame s)))
                (consistent-state s))
           (consistent-value-x (topStack s)
                               (instance-class-table s)
                               (heap s)))
  :hints (("Goal" :in-theory (e/d (topStack) ()))))




(defthm isAssignable-car-opstack-sig-to-class-implies-topStack-consistent-value-x
  (implies (and (bcv::isAssignable (car (opstack-sig (operand-stack (current-frame s)) 
                                                     (instance-class-table s)
                                                     (heap s)
                                                     (heap-init-map (aux s))
                                                     (method-ptr (current-frame s))))
                                   (bcv::prefix-class any)
                                   (env-sig s))
                (consp (opstack-sig (operand-stack (current-frame s)) 
                                                     (instance-class-table s)
                                                     (heap s)
                                                     (heap-init-map (aux s))
                                                     (method-ptr (current-frame s))))
                (consistent-state s))
           (consistent-value-x (topStack s) (instance-class-table s) (heap s)))
  :hints (("Goal" :in-theory (e/d () (canPopCategory2 
                                      current-frame
                                      canPopCategory1
                                      bcv::isAssignable
                                      env-sig
                                      CONSP-NOT-CANPOPCATEGORY2-IMPLIES-CAR-OPSTACK-IS-VALUE-STACK
                                      bcv::prefix-class))
           :use ((:instance 
                  isAssignable-car-opstack-sig-to-class-implies-car-opstack-reduce-to-value-sig-specific-further)
                 (:instance not-canPopCategor1-consistent-opstack-implies-canPopCategory1-specific)))))



(defthm bcv-is-Assignable-prefix-class-bcv-isAssignable-value-sig
  (implies (and (consp (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                    (INSTANCE-CLASS-TABLE S)
                                    (HEAP S)
                                    (HEAP-INIT-MAP (AUX S))
                                    (METHOD-PTR (CURRENT-FRAME S))))
                (BCV::ISASSIGNABLE
                 (CAR (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                   (INSTANCE-CLASS-TABLE S)
                                   (HEAP S)
                                   (HEAP-INIT-MAP (AUX S))
                                   (METHOD-PTR (CURRENT-FRAME S))))
                 (BCV::PREFIX-CLASS any)
                 (ENV-SIG S)))
           (BCV::ISASSIGNABLE
            (value-sig (topStack s)
                       (INSTANCE-CLASS-TABLE S)
                       (HEAP S)
                       (HEAP-INIT-MAP (AUX S))
                       (METHOD-PTR (CURRENT-FRAME S)))
            (BCV::PREFIX-CLASS any)
            (ENV-SIG S)))
  :hints (("Goal" :in-theory (e/d () (bcv::isassignable 
                                      bcv::prefix-class
                                      env-sig
                                      consp-not-canPopCategory2-implies-car-opstack-is-value-stack
                                      canPopCategory2
                                      value-sig))
           :use ((:instance
                  consp-not-canPopCategory2-implies-car-opstack-is-value-stack
                  (cl (instance-class-table s))
                  (hp (heap s))
                  (hp-init (heap-init-map (aux s)))
                  (method-ptr (method-ptr (current-frame s))))))))


;;(i-am-here) ;; Tue Aug 16 17:03:20 2005


(local 
 (defthm isMatchingType-consp
    (implies (and (bcv::isMatchingType type stk env)
                  type)
             (consp stk))
    :hints (("Goal" :in-theory (enable bcv::isMatchingType)))
    :rule-classes :forward-chaining))


(defthm |Subgoal 1.2|
  (IMPLIES
   (AND
    (NOT (BCV::ISASSIGNABLE (VALUE-SIG (TOPSTACK S)
                                       (INSTANCE-CLASS-TABLE S)
                                       (HEAP S)
                                       (HEAP-INIT-MAP (AUX S))
                                       (METHOD-PTR (CURRENT-FRAME S)))
                            (BCV::PREFIX-CLASS (FIELDCP-CLASSNAME (ARG INST)))
                            (ENV-SIG S)))
    (BCV::ISASSIGNABLE (CAR (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                         (INSTANCE-CLASS-TABLE S)
                                         (HEAP S)
                                         (HEAP-INIT-MAP (AUX S))
                                         (METHOD-PTR (CURRENT-FRAME S))))
                       (BCV::PREFIX-CLASS (FIELDCP-CLASSNAME (ARG INST)))
                       (ENV-SIG S))
    (NOT (NULLP (TOPSTACK S)))
    (CONSISTENT-STATE S)
    (NO-FATAL-ERROR? S)
    (ISCLASSTERM (CLASS-BY-NAME (FIELDCP-CLASSNAME (ARG INST))
                                (INSTANCE-CLASS-TABLE S)))
    (BCV::CLASS-BY-NAME (FIELDCP-CLASSNAME (ARG INST))
                        (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S)))
    (NOT (BCV::CLASSISINTERFACE
          (BCV::CLASS-BY-NAME (FIELDCP-CLASSNAME (ARG INST))
                              (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S))))))
 (CAR (ISASSIGNABLETO (OBJ-TYPE (DEREF2 (TOPSTACK S) (HEAP S)))
                      (FIELDCP-CLASSNAME (ARG INST))
                      S)))
  :hints (("Goal" :in-theory (e/d (opstack-sig)
                                  (isassignableto 
                                   NULLp
                                   isClassTerm
                                   arg 
                                   bcv::isassignable
                                   value-sig
                                   bcv::arg1
                                   bcv::fieldclassnamecp
                                   bcv::prefix-class
                                   fieldcp-classname
                                   bcv::classtableenvironment
                                   bcv::prefix-class 
                                   CONSISTENT-STATE-IMPLIES-FIX-SIG-IS-PREFIX-CLASS-LEMMA
                                   CONSISTENT-STATE-IMPLIES-FIX-SIG-IS-PREFIX-CLASS
                                   VALUE-SIG-CONSISTENT-VALUE-X-REDUCE-IF-CLASS-TYPE
                                   canPopCategory2
                                   env-sig
                                   bcv::isAssignable))
           :cases ((consp  (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                        (INSTANCE-CLASS-TABLE S)
                                        (HEAP S)
                                        (HEAP-INIT-MAP (AUX S))
                                        (METHOD-PTR (CURRENT-FRAME S))))))))



;; (defthm isAssignable-car-opstack-sig-to-class-implies-topStack-consistent-value-x
;;   (implies (and (bcv::isAssignable (car (opstack-sig (operand-stack (current-frame s)) 
;;                                                      (instance-class-table s)
;;                                                      (heap s)
;;                                                      (heap-init-map (aux s))
;;                                                      (method-ptr (current-frame s))))
;;                                    (bcv::prefix-class any)
;;                                    (env-sig s))
;;                 (consp (opstack-sig (operand-stack (current-frame s)) 
;;                                                      (instance-class-table s)
;;                                                      (heap s)
;;                                                      (heap-init-map (aux s))
;;                                                      (method-ptr (current-frame s))))
;;                 (consistent-state s))
;;            (consistent-value-x (topStack s) (instance-class-table s) (heap s)))
;;   :hints (("Goal" :in-theory (e/d () (canPopCategory2 
;;                                       current-frame
;;                                       canPopCategory1
;;                                       bcv::isAssignable
;;                                       env-sig
;;                                       CONSP-NOT-CANPOPCATEGORY2-IMPLIES-CAR-OPSTACK-IS-VALUE-STACK
;;                                       bcv::prefix-class))
;;            :use ((:instance 
;;                   isAssignable-car-opstack-sig-to-class-implies-car-opstack-reduce-to-value-sig-specific-further)
;;                  (:instance not-canPopCategor1-consistent-opstack-implies-canPopCategory1-specific)))))


(defthm |Subgoal 1.1|
  (IMPLIES
   (AND
    (NOT (CONSISTENT-VALUE-X (TOPSTACK S)
                             (INSTANCE-CLASS-TABLE S)
                             (HEAP S)))
    (BCV::ISASSIGNABLE (CAR (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                         (INSTANCE-CLASS-TABLE S)
                                         (HEAP S)
                                         (HEAP-INIT-MAP (AUX S))
                                         (METHOD-PTR (CURRENT-FRAME S))))
                       (BCV::PREFIX-CLASS (FIELDCP-CLASSNAME (ARG INST)))
                       (ENV-SIG S))
    (NOT (NULLP (TOPSTACK S)))
    (CONSISTENT-STATE S)
    (NO-FATAL-ERROR? S)
    (ISCLASSTERM (CLASS-BY-NAME (FIELDCP-CLASSNAME (ARG INST))
                                (INSTANCE-CLASS-TABLE S)))
    (BCV::CLASS-BY-NAME (FIELDCP-CLASSNAME (ARG INST))
                        (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S)))
    (NOT (BCV::CLASSISINTERFACE
          (BCV::CLASS-BY-NAME (FIELDCP-CLASSNAME (ARG INST))
                              (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S))))))
   (CAR (ISASSIGNABLETO (OBJ-TYPE (DEREF2 (TOPSTACK S) (HEAP S)))
                        (FIELDCP-CLASSNAME (ARG INST))
                        S)))
  :hints (("Goal" :in-theory (e/d (opstack-sig)
                                  (isassignableto 
                                   NULLp
                                   isClassTerm
                                   arg 
                                   bcv::isassignable
                                   value-sig
                                   bcv::arg1
                                   bcv::fieldclassnamecp
                                   bcv::prefix-class
                                   fieldcp-classname
                                   bcv::classtableenvironment
                                   bcv::prefix-class 
                                   CONSISTENT-STATE-IMPLIES-FIX-SIG-IS-PREFIX-CLASS-LEMMA
                                   CONSISTENT-STATE-IMPLIES-FIX-SIG-IS-PREFIX-CLASS
                                   VALUE-SIG-CONSISTENT-VALUE-X-REDUCE-IF-CLASS-TYPE
                                   canPopCategory2
                                   env-sig
                                   bcv::isAssignable))
           :cases ((consp  (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                        (INSTANCE-CLASS-TABLE S)
                                        (HEAP S)
                                        (HEAP-INIT-MAP (AUX S))
                                        (METHOD-PTR (CURRENT-FRAME S))))))))





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
                         S)))
  :hints (("Goal" :in-theory (e/d (opstack-sig)
                                  (isassignableto 
                                   NULLp
                                   isClassTerm
                                   arg 
                                   bcv::isassignable
                                   value-sig
                                   bcv::arg1
                                   bcv::fieldclassnamecp
                                   bcv::prefix-class
                                   fieldcp-classname
                                   bcv::classtableenvironment
                                   bcv::prefix-class 
                                   CONSISTENT-STATE-IMPLIES-FIX-SIG-IS-PREFIX-CLASS-LEMMA
                                   CONSISTENT-STATE-IMPLIES-FIX-SIG-IS-PREFIX-CLASS
                                   VALUE-SIG-CONSISTENT-VALUE-X-REDUCE-IF-CLASS-TYPE
                                   canPopCategory2
                                   env-sig
                                   bcv::isAssignable))
           :cases ((consp  (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                        (INSTANCE-CLASS-TABLE S)
                                        (HEAP S)
                                        (HEAP-INIT-MAP (AUX S))
                                        (METHOD-PTR (CURRENT-FRAME S))))))
          ("Subgoal 1" :use ((:instance isMatchingType-isAssignableTo-lemma)))))


;;; Do we  want some change? 
;;; Do we want to get rid of the 
;;;
;;;         (bcv::class-by-name (bcv::fieldclassnamecp (bcv::arg1 inst))
;;;                            (BCV::CLASSTABLEENVIRONMENT (ENV-SIG S)))


(in-theory (disable 
            CONSISTENT-STATE-IMPLIES-FIX-SIG-IS-PREFIX-CLASS-LEMMA
            CONSISTENT-STATE-IMPLIES-FIX-SIG-IS-PREFIX-CLASS))
          
