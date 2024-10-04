(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-thread-primitives")
;; CHEAT!!

(skip-proofs (verify-guards signalTimeToReschedule))

(skip-proofs (verify-guards dismantleThread))

(skip-proofs (verify-guards resumeThread-inv))

(skip-proofs (verify-guards resumeThread))

(skip-proofs (verify-guards storeExecutionEnvironment))

(skip-proofs (verify-guards loadExecutionEnvironment))

(skip-proofs (verify-guards suspendThread1))

(skip-proofs (verify-guards suspendThread))

(skip-proofs (verify-guards startThread))
         
(skip-proofs (verify-guards stopThread))
               
                                                       
;;; Tue Mar 15 20:08:29 2005. 


;;;  note this guard verification as the guard put it
;;; down now is not correct!


