(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")


(defthm consistent-state-wff-env
  (implies (consistent-state s)
           (wff-env (env s)))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm consistent-state-wff-instance-class-table-strong
  (implies (consistent-state s)
           (WFF-INSTANCE-CLASS-TABLE-STRONG (INSTANCE-CLASS-TABLE S)))
  :hints (("Goal" :in-theory (enable consistent-state))))

(defthm consistent-state-wff-array-class-table
  (implies (consistent-state s)
           (WFF-ARRAY-CLASS-TABLE (ARRAY-CLASS-TABLE S)))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm consistent-state-wff-static-class-table-strong
  (implies (consistent-state s)
           (WFF-STATIC-CLASS-TABLE-STRONG (ENV-CLASS-TABLE (ENV S))))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm consistent-state-wff-methods-instance-class-table-strong
    (implies (consistent-state s)
             (WFF-METHODS-INSTANCE-CLASS-TABLE-STRONG (INSTANCE-CLASS-TABLE
                                                       S)))
    :hints (("Goal" :in-theory (enable consistent-state))))



(defthm consistent-state-consistent-class-hierachy
    (implies (consistent-state s)
             (CONSISTENT-CLASS-HIERACHY (INSTANCE-CLASS-TABLE S)))
    :hints (("Goal" :in-theory (enable consistent-state))))



(defthm consistent-state-wff-heap-strong
  (implies (consistent-state s)
           (wff-heap-strong (heap s)))
    :hints (("Goal" :in-theory (enable consistent-state))))



(defthm consistent-state-consistent-heap
  (implies (consistent-state s)
           (consistent-heap (heap s) (instance-class-table s)
                            (array-class-table s)))
  :hints (("Goal" :in-theory (e/d (consistent-state)
                                  (consistent-heap)))))


(defthm consistent-state-class-table-is-loaded-from
  (implies (consistent-state s)
           (CLASS-TABLE-IS-LOADED-FROM (INSTANCE-CLASS-TABLE S)
                                       (ENV-CLASS-TABLE (ENV S))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))
                                    

(defthm consistent-state-consistent-thread-entries
  (implies (consistent-state s)
           (CONSISTENT-THREAD-ENTRIES (THREAD-TABLE S)
                                      (INSTANCE-CLASS-TABLE S)
                                      (heap s)))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))



(defthm consistent-state-nodup-set-threads
  (implies (consistent-state s)
           (NODUP-SET (COLLECT-THREAD-ID (THREAD-TABLE S))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))



(defthm consistent-state-loader-inv
  (implies (consistent-state s)
           (loader-inv s))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))





(defthm wff-heap-bind-wff-heap
  (implies (wff-heap hp)
           (wff-heap (bind ref obj hp)))
  :hints (("Goal" :in-theory (enable wff-heap bind))))



(defthm consistent-state-class-loaded-java-lang-Object
  (implies (consistent-state s)
           (class-loaded? "java.lang.Object" s))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))



(defthm consistent-state-class-loaded-java-lang-Class
  (implies (consistent-state s)
           (class-loaded? "java.lang.Class" s))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))



(defthm consistent-state-class-loaded-java-lang-String
  (implies (consistent-state s)
           (class-loaded? "java.lang.String" s))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))


(defthm consistent-state-wff-static-class-table
  (implies (consistent-state s)
           (WFF-STATIC-CLASS-TABLE (ENV-CLASS-TABLE (ENV S))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))



(defthm consistent-state-array-class-table-inv-helper
  (implies (consistent-state s)
           (JVM::ARRAY-CLASS-TABLE-INV-HELPER
            (JVM::ALL-ARRAY-SIGS (ARRAY-CLASS-TABLE S))
            S))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))




(defthm consistent-state-super-java-lang-Object
  (implies (consistent-state s)
           (EQUAL (SUPER (CLASS-BY-NAME "java.lang.Object"
                                        (INSTANCE-CLASS-TABLE S)))
                  ""))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))




(defthm consistent-state-correctly-loaded-java-lang-Object
  (implies (consistent-state s)
           (correctly-loaded? "java.lang.Object" 
                              (instance-class-table s)
                              (env-class-table (env s))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))



(defthm consistent-state-correctly-loaded-java-lang-Class
  (implies (consistent-state s)
           (correctly-loaded? "java.lang.Class" 
                              (instance-class-table s)
                              (env-class-table (env s))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))



(defthm consistent-state-correctly-loaded-java-lang-String
  (implies (consistent-state s)
           (correctly-loaded? "java.lang.String"
                              (instance-class-table s)
                              (env-class-table (env s))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))


(defthm consistent-state-bound-array-char
  (implies (consistent-state s)
           (BOUND? '(ARRAY CHAR)
                   (ARRAY-CLASS-TABLE S)))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))




(defthm consistent-and-found-implies-not-equal-empty-string
  (implies (boot-strap-class-okp s)
           (not (car (class-by-name-s "" (env-class-table (env s))))))
  :hints (("Goal" :in-theory (enable boot-strap-class-okp)))
  :rule-classes :forward-chaining)



(defthm consistent-state-not-bound-empty-string-x
  (implies (consistent-state s)
           (NOT (CAR (CLASS-BY-NAME-S "" (ENV-CLASS-TABLE (ENV S))))))
  :hints (("Goal" :in-theory (e/d (consistent-state) (boot-strap-class-okp)))))



(defthm consistent-state-not-env-class-table-normal
  (implies (consistent-state s)
           (EQUAL (BCV::SCL-BCV2JVM (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S))))
                  (ENV-CLASS-TABLE (ENV S))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))


;----------------------------------------------------------------------


(defthm consistent-state-implies-consistent-jvp
  (implies (consistent-state s)
           (CONSISTENT-JVP "java.lang.Object"
                           '(("java.lang.Object"))
                           (INSTANCE-CLASS-TABLE S)
                           (HEAP S)))
  :hints (("Goal" :in-theory (e/d (consistent-state)
                                  (consistent-jvp)))))

;----------------------------------------------------------------------

(defthm consistent-state-implies-java-lang-Object-no-fields
  (implies (consistent-state s)
           (NOT (FIELDS (CLASS-BY-NAME "java.lang.Object"
                                       (INSTANCE-CLASS-TABLE S)))))
  :hints (("Goal" :in-theory (e/d (consistent-state boot-strap-class-okp)
                                  ()))))

;----------------------------------------------------------------------

(defthm consistent-state-implies-heap-init-state
  (IMPLIES (CONSISTENT-STATE S)
           (CONSISTENT-HEAP-INIT-STATE (HEAP S)
                                       (INSTANCE-CLASS-TABLE S)
                                       (HEAP-INIT-MAP (AUX s))))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))


;----------------------------------------------------------------------


(defthm consistent-state-implies-java-lang-Object-loaded
  (IMPLIES (CONSISTENT-STATE S)
           (class-loaded? "java.lang.Object" s))
  :hints (("Goal" :in-theory (e/d (consistent-state) ()))))


(defthm consistent-state-implies-java-lang-Object-loaded-2
  (IMPLIES (CONSISTENT-STATE S)
           (isClassTerm (class-by-name "java.lang.Object" (instance-class-table s))))
  :hints (("Goal" :in-theory (e/d (consistent-state class-loaded?)
                                  (isClassTerm)))))



(defthm consistent-state-implies-java-lang-Class-loaded-2
  (IMPLIES (CONSISTENT-STATE S)
           (isClassTerm (class-by-name "java.lang.Class" (instance-class-table s))))
  :hints (("Goal" :in-theory (e/d (consistent-state class-loaded?) (isClassTerm)))))



(defthm consistent-state-implies-java-lang-String-loaded-2
  (IMPLIES (CONSISTENT-STATE S)
           (isClassTerm (class-by-name "java.lang.String" (instance-class-table s))))
  :hints (("Goal" :in-theory (e/d (consistent-state class-loaded?) (isClassTerm)))))
