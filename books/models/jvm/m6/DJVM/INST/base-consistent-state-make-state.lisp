(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")
(include-book "../../M6-DJVM-shared/jvm-bytecode")


(local (include-book "base-loader-preserve-consistent-state")) 


(defthm make-state-build-a-java-instance-data-guard
  (implies (and (wff-state s)
                (integerp pc))
           (equal (build-a-java-visible-instance-data-guard any 
                                                       (make-state pc 
                                                                   cid 
                                                                   (heap s)
                                                                   (thread-table s)
                                                                   (class-table s)
                                                                   (env s)
                                                                   (error-flag s)
                                                                   aux))
                  (build-a-java-visible-instance-data-guard any s))))



(defthm make-state-build-a-java-instance-guard
  (implies (and (wff-state s)
                (integerp pc))
           (equal (build-a-java-visible-instance-guard any 
                                                       (make-state pc 
                                                                   cid 
                                                                   (heap s)
                                                                   (thread-table s)
                                                                   (class-table s)
                                                                   (env s)
                                                                   (error-flag s)
                                                                   aux))
                  (build-a-java-visible-instance-guard any s)))
  :hints (("Goal" :in-theory (enable build-a-java-visible-instance-guard))))





(defthm loader-inv-make-state
  (implies (and (wff-state s)
                (integerp pc))
           (equal (jvm::loader-inv (make-state pc 
                                               cid 
                                               (heap s)
                                               (thread-table s)
                                               (class-table s)
                                               (env s)
                                               (error-flag s)
                                               aux))
                  (jvm::loader-inv s)))
  :hints (("Goal" :in-theory (enable jvm::loader-inv no-fatal-error?))))




(defthm class-loaded?-make-state
  (equal (class-loaded? any (make-state pc 
                                        cid 
                                        (heap s)
                                        (thread-table s)
                                        (class-table s)
                                        (env s)
                                        (error-flag s)
                                        aux))
         (class-loaded? any s))
  :hints (("Goal" :in-theory (enable class-loaded?))))



(defthm make-state-heap-array-class-correctly-loaded?
  (implies (and (wff-state s)
                (integerp pc))
           (equal (jvm::array-class-correctly-loaded? l 
                                                      (make-state pc 
                                                                  cid 
                                                                  (heap s)
                                                                  (thread-table s)
                                                                  (class-table s)
                                                                  (env s)
                                                                  (error-flag s)
                                                                  aux))
                  (jvm::array-class-correctly-loaded? l s)))
  :hints (("Goal" :in-theory (e/d (array-base-type)))))
                                  
  


(defthm make-state-array-class-table-inv-helper
  (implies (and (wff-state s)
                (integerp pc))
           (equal (jvm::array-class-table-inv-helper l (make-state pc 
                                                                   cid 
                                                                   (heap s)
                                                                   (thread-table s)
                                                                   (class-table s)
                                                                   (env s)
                                                                   (error-flag s)
                                                                   aux))
                  (jvm::array-class-table-inv-helper l s))))





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


(local 
 (defthm consistent-state-make-state
   (implies (and (consistent-state s)
                 (equal (pc s) pc)
                 (equal (heap-init-map (aux s)) (heap-init-map aux))
                 (equal (current-thread s) cid))
            (consistent-state-step (make-state pc 
                                         cid 
                                         (heap s)
                                         (thread-table s)
                                         (class-table s)
                                         (env s)
                                         (error-flag s)
                                         aux)))
  :hints (("Goal" :in-theory (e/d (consistent-state-step
                                  instance-class-table-inv
                                  array-class-table-inv
                                  boot-strap-class-okp) ())))))



(defthm consistent-state-make-state-x
  (implies (and (consistent-state s)
                (equal (pc s) pc)
                (wff-aux aux)
                (equal (heap-init-map (aux s)) (heap-init-map aux))
                (equal (current-thread s) cid))
           (consistent-state (make-state pc 
                                         cid 
                                         (heap s)
                                         (thread-table s)
                                         (class-table s)
                                         (env s)
                                         (error-flag s)
                                         aux)))
  :hints (("Goal" :use ((:instance consistent-state-make-state)
                        (:instance
                         consistent-state-step-implies-consistent-state 
                         ;; from base-loader-preserve-consistent-state.lisp
                         (s (make-state pc 
                                         cid 
                                         (heap s)
                                         (thread-table s)
                                         (class-table s)
                                         (env s)
                                         (error-flag s)
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

           

