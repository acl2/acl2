(in-package "ACL2")
(include-book "jvm-model")
(include-book "bcv-simple-model")

;; (defun pc-in-range (frame method-table)
;;  (let* ((method-name (g 'method-name frame))
;;         (method (binding method-name method-table))
;;         (pc (g 'pc frame))
;;         (code (g 'code method)))
;;    (and (integerp pc)
;;         (<= 0 pc)
;;         (< pc (len code))))) 


                
(local (in-theory (disable bcv-simple-method bcv-simple-inst                                      
                           BCV-CHECK-STEP-PRE
                           ALL-NEXT-STATE-SAFE
                           bcv-simple-execute-step)))

(local (include-book "arithmetic/top-with-meta" :dir :system))


(local 
 (defthm bcv-simple-method1-implies-inst-verified
   (implies (and (bcv-simple-method1 i code sig-vector)
                 (integerp i)
                 (integerp pc)
                 (<= 0 (- pc i))
                 (< (- pc i) (len code)))
           (bcv-simple-inst pc
                     (nth (- pc i) code)
                     sig-vector))
   :hints (("Goal" :in-theory (enable bcv-simple-inst bcv-simple-method1)
            :do-not '(generalize)))))


(defthm bcv-simple-method-implies-next-inst-verified
  (implies (and (bcv-simple-method method method-table)
                (integerp pc)
                (<= 0 pc)
                (< pc (len (g 'code method))))
           (bcv-simple-inst pc 
                     (nth pc (g 'code method))
                     (g 'sig-vector method)))
  :hints (("Goal" :in-theory (e/d (bcv-simple-method)
                                  (bcv-simple-method1))
           :do-not '(generalize)
           :use ((:instance bcv-simple-method1-implies-inst-verified
                            (code (g 'code method))
                            (i 0)
                            (sig-vector (g 'sig-vector method)))))))
  

;; (defthm bcv-simple-method-implies-next-inst-verified-version-2
;;   (implies (and (bcv-simple-method 
;;                  (s 'sig-vector (collect-witness-bcv-method
;;                                  method 

;; method method-table)
;;                 (integerp pc)
;;                 (<= 0 pc)
;;                 (< pc (len (g 'code method))))
;;            (bcv-simple-inst pc 
;;                      (nth pc (g 'code method))
;;                      (g 'sig-vector method)))
;;   :hints (("Goal" :in-theory (e/d (bcv-simple-method)
;;                                   (bcv-simple-method1))
;;            :do-not '(generalize)
;;            :use ((:instance bcv-simple-method1-implies-inst-verified
;;                             (code (g 'code method))
;;                             (i 0)
;;                             (sig-vector (g 'sig-vector method)))))))
  


;----------------------------------------------------------------------

;; bcv-simple-inst implies 
;;         (bcv-simple-check-step-pre inst sframe))
;; and 
;;      (all-next-state-safe (bcv-simple-execute-step inst sframe))

;----------------------------------------------------------------------

;; (i-am-here) ;;  Fri Nov 11 14:55:12 2005

(defthm bcv-simple-check-step-pre-if-sig-frame-compatible
  (implies (and (sig-frame-compatible sframe gframe)
                (bcv-simple-check-step-pre inst gframe))
           (bcv-simple-check-step-pre inst sframe))
  :hints (("Goal" :in-theory (enable bcv-simple-check-step-pre))))


(local 
 (defthm pc-no-change-pop-n
   (equal (g 'pc (sig-frame-pop-n n sig-frame))
          (g 'pc sig-frame))))


(local 
 (defthm equal-opstack-pop-n-still-equal
    (implies (and (syntaxp (and (symbolp sframe)
                                (equal sframe 'sframe)))
                  (equal (g 'op-stack sframe)
                         (g 'op-stack gframe)))
             (equal (g 'op-stack (sig-frame-pop-n n sframe))
                    (g 'op-stack
                       (sig-frame-pop-n n gframe))))))


(local 
 (defthm equal-max-stack-pop-n-still-equal
  (equal (g 'max-stack (sig-frame-pop-n n sframe))
         (g 'max-stack sframe))))



(local 
 (defthm equal-method-table-pop-n-still-equal
  (equal (g 'method-table (sig-frame-pop-n n sframe))
         (g 'method-table sframe))))

(local 
 (defthm equal-method-name-pop-n-still-equal
  (equal (g 'method-name (sig-frame-pop-n n sframe))
         (g 'method-name sframe))))


(defthm bcv-check-step-post-if-sig-frame-compatible
  (implies (and (sig-frame-compatible sframe gframe)
                (all-next-state-safe (bcv-simple-execute-step inst gframe) vector))
           (all-next-state-safe (bcv-simple-execute-step inst sframe) vector))
  :hints (("Goal" :in-theory (enable bcv-simple-execute-step all-next-state-safe))))


;----------------------------------------------------------------------

;; (defthm bcv-simple-method-implies-next-inst-verified-specific
;;   (implies (and (bcv-simple-method method)
;;                 (integerp pc)
;;                 (<= 0 pc)
;;                 (< pc (len (g 'code method))))
;;            (bcv-simple-inst pc 
;;                      (nth pc (g 'code method))
;;                      (g 'sig-vector method)))
;;   :hints (("Goal" :in-theory (e/d (bcv-simple-method)
;;                                   (bcv-simple-method1))
;;            :do-not '(generalize)
;;            :use ((:instance bcv-simple-method1-implies-inst-verified
;;                             (code (g 'code method))
;;                             (i 0)
;;                             (sig-vector (g 'sig-vector method)))))))
  


