(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")
(include-book "../../M6-DJVM-shared/jvm-bytecode")


(local (include-book "base-loader-preserve-consistent-state")) 


;;    (MAKE-STATE
;;         (PC S)
;;         (CURRENT-THREAD S)
;;         (HEAP (RESOLVECLASSREFERENCE (FIELDCP-CLASSNAME (ARG INST))
;;                                      S))
;;         (THREAD-TABLE S)
;;         (CLASS-TABLE (RESOLVECLASSREFERENCE (FIELDCP-CLASSNAME (ARG INST))
;;                                             S))
;;         (ENV S)
;;         (ERROR-FLAG (RESOLVECLASSREFERENCE (FIELDCP-CLASSNAME (ARG INST))
;;                                            S))
;;         (ACL2::S 'PENDING-EXCEPTION
;;                  "java.lang.NullPointerException"
;;                  (AUX (RESOLVECLASSREFERENCE (FIELDCP-CLASSNAME (ARG INST))


(defthm make-state-build-a-java-instance-data-guard-general
  (implies (and (wff-state s)
                (integerp pc))
           (equal (build-a-java-visible-instance-data-guard any 
                                                       (make-state pc 
                                                                   anycid 
                                                                   anyhp
                                                                   anytt
                                                                   (class-table s)
                                                                   anyenv
                                                                   anyefflag
                                                                   anyaux))
                  (build-a-java-visible-instance-data-guard any s))))

;; it can still be made more general. 

;; (defthm make-state-build-a-java-instance-data-guard
;;   (implies (and (wff-state s)
;;                 (integerp pc))
;;            (equal (build-a-java-visible-instance-data-guard any 
;;                                                        (make-state pc 
;;                                                                    cid 
;;                                                                    (heap s)
;;                                                                    (thread-table s)
;;                                                                    (class-table s)
;;                                                                    (env s)
;;                                                                    (error-flag s)
;;                                                                    aux))
;;                   (build-a-java-visible-instance-data-guard any s))))
;;
;;

(defthm make-state-build-a-java-instance-guard-general
  (implies (and (wff-state s)
                (equal (env s) env)
                (integerp pc))
           (equal (build-a-java-visible-instance-guard any 
                                                       (make-state pc 
                                                                   anycid 
                                                                   anyhp
                                                                   anytt
                                                                   (class-table s)
                                                                   env
                                                                   anyerr
                                                                   aux))
                  (build-a-java-visible-instance-guard any s)))
  :hints (("Goal" :in-theory (enable build-a-java-visible-instance-guard))))





(defthm loader-inv-make-state-general
  (implies (and (wff-state s)
                (or err
                    (equal (error-flag s) err))
                (equal (env s) env)
                (integerp pc)
                (jvm::loader-inv s))
           (jvm::loader-inv (make-state pc 
                                        anycid 
                                        anyhp
                                        anytt
                                        (class-table s)
                                        env
                                        err
                                        aux)))
  :hints (("Goal" :in-theory (enable jvm::loader-inv no-fatal-error?))))




(defthm class-loaded?-make-state-general
  (equal (class-loaded? any (make-state anypc 
                                        anycid 
                                        anyhp
                                        anytt
                                        (class-table s)
                                        anytt
                                        anyerr
                                        aux))
         (class-loaded? any s))
  :hints (("Goal" :in-theory (enable class-loaded?))))



(defthm make-state-heap-array-class-correctly-loaded?-general
  (equal (jvm::array-class-correctly-loaded? l 
                                             (make-state pc 
                                                         anycid 
                                                         anyhp
                                                         anytt
                                                         (class-table s)
                                                         anyenv
                                                         anyerr
                                                         aux))
                  (jvm::array-class-correctly-loaded? l s))
  :hints (("Goal" :in-theory (e/d (array-base-type)))))
                                  
  
(defthm make-state-array-class-table-inv-helper-general
  (equal (jvm::array-class-table-inv-helper l (make-state anypc 
                                                          anycid 
                                                          anyhp
                                                          anytt
                                                          (class-table s)
                                                          anyenv
                                                          anyerr
                                                          aux))
         (jvm::array-class-table-inv-helper l s)))





(defthm consistent-state-correctly-loaded
  (implies (consistent-state s)
           (correctly-loaded? "java.lang.Object"
                              (instance-class-table s)
                              (env-class-table (env s))))
  :hints (("Goal" :in-theory (enable consistent-state
                                     boot-strap-class-okp))))

(defthm consistent-state-correctly-loaded-java-lang-Class
  (implies (consistent-state s)
           (correctly-loaded? "java.lang.Class"
                              (instance-class-table s)
                              (env-class-table (env s))))
  :hints (("Goal" :in-theory (enable consistent-state
                                     boot-strap-class-okp))))

(defthm consistent-state-correctly-loaded-java-lang-String
  (implies (consistent-state s)
           (correctly-loaded? "java.lang.String"
                              (instance-class-table s)
                              (env-class-table (env s))))
  :hints (("Goal" :in-theory (enable consistent-state
                                     boot-strap-class-okp))))


(defthm correctly-loaded-implies-loaded-x
  (implies (correctly-loaded? any (instance-class-table s) 
                              (env-class-table (env s)))
           (class-loaded? any s))
  :hints (("Goal" :in-theory (enable class-loaded?))))



(defthm consistent-state-can-build-java-lang-Object
  (IMPLIES (CONSISTENT-STATE S)
           (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD "java.lang.Object" S))
  :hints (("Goal" :in-theory (e/d (consistent-state boot-strap-class-okp)
                                  (build-a-java-visible-instance-guard)))))



(defthm consistent-state-can-build-java-lang-String
  (IMPLIES (CONSISTENT-STATE S)
           (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD "java.lang.String" S))
  :hints (("Goal" :in-theory (e/d (consistent-state boot-strap-class-okp)
                                  (build-a-java-visible-instance-guard)))))



(defthm consistent-state-can-build-java-lang-Class
  (IMPLIES (CONSISTENT-STATE S)
           (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD "java.lang.Class" S))
  :hints (("Goal" :in-theory (e/d (consistent-state boot-strap-class-okp)
                                  (build-a-java-visible-instance-guard)))))


;;(i-am-here)  ;; Sun Jun 12 13:02:14 2005


;; (skip-proofs 
;;  (defthm consistent-state-make-state-x-x
;;    (implies (and (consistent-state s)
;;                  (equal (pc s) pc)
;;                  (equal (thread-table s) tt)
;;                  (equal (env s) env)
;;                  (equal (heap-init-map (aux s)) (heap-init-map aux))
;;                  (equal (current-thread s) cid))
;;             (consistent-state (make-state pc 
;;                                           cid 
;;                                           (heap s)
;;                                           tt 
;;                                           (class-table s)
;;                                           env
;;                                           any
;;                                           aux)))))


;;(i-am-here) ;; Fri Jul 15 22:13:38 2005


;; (defthm consistent-state-bootstrap-class-ok
;;   (implies (consistent-state 
;;          (CLASS-LOADED? "java.lang.Object"
;;                         (MAKE-STATE (PC S)
;;                                     (CURRENT-THREAD S)
;;                                     (HEAP S)
;;                                     (THREAD-TABLE S)
;;                                     (CLASS-TABLE S)
;;                                     (ENV S)
;;                                     ERR AUX))).

;; (i-am-here) ;; Fri Jul 15 22:23:16 2005

(local 
  (defthm consistent-state-good-scl
   (IMPLIES (CONSISTENT-STATE S)
            (bcv::good-scl (bcv::scl-jvm2bcv (env-class-table (env s)))))
   :hints (("Goal" :in-theory (e/d (consistent-state) (bcv::good-scl))))
   :rule-classes :forward-chaining))

(local 
 (defthm consistent-scl-implies-not-super-java-lang-Object-bounded
   (implies (bcv::good-scl scl)
            (NOT
             (BCV::ISCLASSTERM
              (BCV::CLASS-BY-NAME
               (BCV::CLASSSUPERCLASSNAME
                (BCV::CLASS-BY-NAME "java.lang.Object" scl))
               scl))))
   :rule-classes :forward-chaining))


(local 
 (defthm consistent-scl-implies-not-nil-bounded
   (implies (bcv::good-scl scl)
            (NOT
             (BCV::ISCLASSTERM
              (BCV::CLASS-BY-NAME  nil  scl))))
   :rule-classes :forward-chaining))



(local (in-theory (disable bcv::good-scl)))

(local 
 (defthm consistent-state-make-state-general
   (implies (and (consistent-state s)
                 (equal (pc s) pc)
                 (equal (heap-init-map (aux s)) (heap-init-map aux))
                 (equal (heap s) hp)
                 (equal (thread-table s) tt)
                 (equal (env s) env)
                 (or err
                     (equal (error-flag s) err))
                 (equal (current-thread s) cid))
            (consistent-state-step (make-state pc 
                                         cid 
                                         hp
                                         tt
                                         (class-table s)
                                         env
                                         err
                                         aux)))
  :hints (("Goal" :in-theory (e/d (consistent-state-step
                                   instance-class-table-inv
                                   boot-strap-class-okp
                                   array-class-table-inv)
                                  (class-loaded?
                                   isClassTerm))))))



(defthm consistent-state-make-state-x-general
  (implies (and (consistent-state s)
                 (equal (pc s) pc)
                 (equal (heap-init-map (aux s)) (heap-init-map aux))
                 (equal (heap s) hp)
                 (equal (thread-table s) tt)
                 (equal (env s) env)
                 (or err
                     (equal (error-flag s) err))
                 (equal (current-thread s) cid))
           (consistent-state (make-state pc 
                                         cid 
                                         hp 
                                         tt
                                         (class-table s)
                                         env
                                         err
                                         aux)))
  :hints (("Goal" :use ((:instance consistent-state-make-state-general)
                        (:instance
                         consistent-state-step-implies-consistent-state 
                         ;; from base-loader-preserve-consistent-state.lisp
                         (s (make-state pc 
                                         cid 
                                         hp
                                         tt
                                         (class-table s)
                                         env
                                         err
                                         aux))))
           :in-theory (disable consistent-state 
                               consistent-state-step))))
  






;----------------------------------------------------------------------


(defthm build-a-java-visible-instance-data-guard-make-state-general
  (implies (build-a-java-visible-instance-data-guard any s)
           (build-a-java-visible-instance-data-guard any
                                                     (MAKE-STATE (pc s)
                                                                 anytid
                                                                 anyhp
                                                                 anytt
                                                                 (class-table s)
                                                                 (ENV S)
                                                                 anyerror
                                                                 anyaux))))


(defthm array-class-table-make-state-is
  (equal (array-class-table (MAKE-STATE anypc
                                        anytid
                                        anyhp
                                        anytt
                                        (CLASS-TABLE S)
                                        anyenv
                                        anyerror
                                        anyaux))
         (array-class-table s)))



(defthm instance-class-table-make-state-is
  (equal (instance-class-table (MAKE-STATE anypc
                                        anytid
                                        anyhp
                                        anytt
                                        (CLASS-TABLE S)
                                        anyenv
                                        anyerror
                                        anyaux))
         (instance-class-table s)))


(defthm array-class-correctly-loaded-make-state-general
  (implies (jvm::array-class-correctly-loaded? l s)
           (jvm::array-class-correctly-loaded? l (MAKE-STATE anypc
                                                             anytid
                                                             anyhp
                                                             anytt
                                                             (CLASS-TABLE S)
                                                             anyenv
                                                             anyerror
                                                             anyaux)))
  :hints (("Goal" :in-theory (enable array-base-type 
                                     JVM::ARRAY-CLASS-CORRECTLY-LOADED?)
           :do-not '(generalize))))


(defthm array-class-table-inv-helper-make-state-general           
  (implies (JVM::ARRAY-CLASS-TABLE-INV-HELPER l s)
           (JVM::ARRAY-CLASS-TABLE-INV-HELPER l (MAKE-STATE anypc
                                                            anytid
                                                            anyhp
                                                            anytt
                                                            (CLASS-TABLE S)
                                                            anyenv
                                                            anyerror
                                                            anyaux))))

(defthm build-a-java-visible-instance-guard-make-state-general
  (implies (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD x s)
           (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD x (MAKE-STATE (pc s)
                                                            anytid
                                                            anyhp
                                                            anytt
                                                            (CLASS-TABLE S)
                                                            (env s)
                                                            anyerror
                                                            anyaux)))
  :hints (("Goal" :in-theory (enable build-a-java-visible-instance-guard))))

