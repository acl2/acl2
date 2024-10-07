(in-package "ACL2")

(include-book "bcv-model")


(local (encapsulate ()
;;; wrap around in local encapsulate!! 

;----------------------------------------------------------------------

(defthm collect-witness-merged-code-safe-pc-not-out-of-bound
  (implies (not (member pc (collect-pc-merged-code merged-code)))
           (not (assoc-equal pc (collect-witness-merged-code-safe 
                                 merged-code
                                 sig-frame))))
  :hints (("Goal" :do-not '(generalize fertilize))))

;----------------------------------------------------------------------


(defun last-but-one (merged-code)
  (if (endp merged-code) nil
    (if (endp (cdr merged-code)) nil
      (if (equal (cadr merged-code) 'END_OF_CODE)
          (car merged-code)
        (last-but-one (cdr merged-code))))))
  
;----------------------------------------------------------------------

(defthm last-merged-code-is-inst
  (implies (and (merged-code-safe merged-code sig-frame)
                (consp (cdr merged-code)))
           (inst? (last-but-one merged-code))))

;; above is slow!! 


(defthm inst-implies-pc-properly-bounded
  (implies (and (wff-code1 code1 pc)
                (member inst code1))
           (< (g 'pc inst)
              (+ pc (len code1)))))

;----------------------------------------------------------------------

(defthm last-pc-equal
  (implies (and (merged-code-safe merged-code sig-frame)
                (consp (cdr merged-code)))
           (equal (car (last (collect-pc-merged-code merged-code)))
                  (g 'pc (last-but-one merged-code))))
  :hints (("Goal" :do-not '(generalize))))

;;; this is slow!!! not disable any thing.

(encapsulate () 
  (local (include-book "bcv-if-verified-then-pc-ordered"))
  (defthm merged-code-is-safe-implies-ordered
    (implies (and (merged-code-safe merged-code init-frame)
                  (wff-code1 (extract-code merged-code)
                             (g 'pc (car merged-code))))
             (ordered (collect-pc-merged-code merged-code)))))


(defthm ordered-implies-last-biggest
  (implies (and (ordered l)
                (member pc l))
           (<= pc (car (last l))))
  :rule-classes :linear)

(defthm member-collect-pc-implies-consp-cdr
  (implies (member pc (collect-pc-merged-code merged-code))
           (consp (cdr merged-code)))
  :rule-classes :forward-chaining)

(defthm last-but-one-is-biggest
  (implies (and (merged-code-safe merged-code init-frame)
                (wff-code1 (extract-code merged-code)
                           (g 'pc (car merged-code)))
                (member pc (collect-pc-merged-code merged-code)))
           (<=  pc (g 'pc (last-but-one merged-code))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable merged-code-safe
                               extract-code
                               last-pc-equal
                               collect-pc-merged-code)
           :use ((:instance last-pc-equal
                            (sig-frame init-frame)))))
  :rule-classes :linear)

;----------------------------------------------------------------------

(defthm inst-implies-member-extract-code
  (implies (and (inst? inst)
                (equal (car (last merged-code)) 'END_OF_CODE)
                (member inst merged-code))
           (member inst (extract-code merged-code))))

;; now it is time to prove 
(defthm last-but-one-is-a-member
  (implies (and (consp (cdr merged-code))
                (equal (car (last merged-code)) 'END_OF_CODE))
           (member (last-but-one merged-code) merged-code)))


(defthm merged-code-safe-last-merge-code-is-end-of-code
  (implies (merged-code-safe merged-code init-frame)
           (equal (car (last merged-code)) 'END_OF_CODE))
  :rule-classes :forward-chaining)

(defthm member-in-merged-code-implies-pc-less-lemma
  (implies (and (merged-code-safe merged-code init-frame)
                (wff-code1 (extract-code merged-code) 
                           (g 'pc (car merged-code)))
                (consp (cdr merged-code)))
           (< (g 'pc (last-but-one merged-code))
              (+ (g 'pc (car merged-code))
                 (len (extract-code merged-code)))))
  :hints (("Goal" :in-theory (disable merged-code-safe
                                      wff-code1
                                      extract-code
                                      last-but-one)))
  :rule-classes :linear)


(defthm member-in-merged-code-implies-pc-less
  (implies (and (merged-code-safe merged-code init-frame)
                (wff-code1 (extract-code merged-code) 
                           (g 'pc (car merged-code)))
                (member pc (collect-pc-merged-code merged-code)))
           (< pc 
              (+ (g 'pc (car merged-code))
                 (len (extract-code merged-code)))))
  :hints (("Goal" :in-theory (disable merged-code-safe
                                      wff-code1
                                      extract-code
                                      last-but-one)))
  :rule-classes :linear)

;----------------------------------------------------------------------


(encapsulate () 
  (local (include-book "bcv-succeed-implies-bcv-simple-succeed"))
  (defthm extract-code-mergeStackMapAndCode
    (implies (and (equal (car (last (mergeStackMapAndCode maps code method-name method-table)))
                         'END_OF_CODE)
                  (wff-code1 code pc))
             (equal (extract-code (mergeStackMapAndCode maps code method-name method-table))
                    code))
    :hints (("Goal" :in-theory (enable inst?)))))


(encapsulate () 
  (local (include-book "bcv-succeed-implies-bcv-simple-succeed"))
  (defthm merged-code-car-pc-same-as-code-specific
    (implies (merged-code-safe (mergeStackMapAndCode maps code method-name method-table)
                               (SIG-METHOD-INIT-FRAME METHOD METHOD-TABLE))
             (equal (g 'pc (car (mergeStackMapAndCode maps code method-name method-table)))
                    (g 'pc (car code))))))


(defthm g-pc-is-zero-from-parsecode1
  (implies (CONSP (PARSECODE1 pc code))
           (equal (g 'pc (car (parsecode1 pc code)))
                  pc)))


(defthm parsecode1-len-equal
  (equal (len (parsecode1 any code))
         (len code)))



;; (defthm collect-witness-merged-code-safe-pc-not-out-of-bound
;;   (implies (not (member pc (collect-pc-merged-code merged-code)))
;;            (not (assoc-equal pc (collect-witness-merged-code-safe 
;;                                  merged-code
;;                                  sig-frame))))
;;   :hints (("Goal" :do-not '(generalize fertilize))))

(defun wff-merged-code (merged-code)
  (if (endp merged-code) t
    (if (endp (cdr merged-code)) t
      (and (or (inst? (car merged-code))
               (stack-map? (car merged-code)))
           (wff-merged-code (cdr merged-code))))))


(defthm member-pc-implies-integerp
  (implies (and (member pc (collect-pc-merged-code merged-code))
                (wff-merged-code merged-code))
           (integerp pc))
  :hints (("Goal" :do-not '(generalize)))
  :rule-classes :forward-chaining)


(defthm make-inst-inst
  (implies (inst? inst)
           (inst? (make-inst inst)))
  :hints (("Goal" :in-theory (enable make-inst inst?))))



(defthm stack-map-make-stack-map
  (IMPLIES (STACK-MAP? MAPS1)
           (STACK-MAP? (MAKESTACKMAP MAPS1 method-name METHOD-TABLE)))
  :hints (("Goal" :in-theory (enable stack-map?))))

(defthm wff-code1-implies-wff-merge-code
  (implies (wff-code1 code pc)
           (wff-merged-code (append code (list any)))))


(defthm mergeStackMapAndCode-produce-wff-merged-code
  (implies (and (wff-code1 code pc)
                (wff-maps maps))
           (wff-merged-code (mergeStackMapAndCode maps code method-name
                                                  method-table)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable inst? make-inst
                               stack-map? makestackmap))))


(defthm member-pc-collect-pc-then-integerp-specific
  (implies (and (member pc (collect-pc-merged-code 
                            (mergeStackMapAndCode maps code method-name
                                                  method-table)))
                (wff-maps maps)
                (wff-code1 code pcx))
           (integerp pc))
  :hints (("Goal" :do-not '(generalize)
           :use ((:instance member-pc-implies-integerp
                            (merged-code
                             (mergeStackMapAndCode maps code method-name
                                                   method-table))))))
  :rule-classes :forward-chaining)


(encapsulate () 
  (local (include-book "bcv-if-pc-small-then-not-bound-in-witness"))
  (defthm merged-code-is-safe-implies-not-bound-smaller
    (implies (and (merged-code-safe merged-code init-frame)
                  (WFF-CODE1 (EXTRACT-CODE MERGED-CODE)
                             (g 'pc (car merged-code)))
                  (< pc1 (g 'pc (car merged-code))))
             (not (assoc-equal pc1 (collect-witness-merged-code-safe 
                                    merged-code init-frame))))))

))

;;(i-am-here) 

(defthm bcv-method-implies-integerp-if-bound
  (implies (and (bcv-method method method-table)
                (assoc-equal pc (collect-witness-bcv-method method method-table)))
           (integerp pc))
  :hints (("Goal" :in-theory (disable merged-code-safe
                                      ;;collect-witness-bcv-method
                                      extract-code
                                      sig-method-init-frame
                                      wff-code1)
           :cases ((member pc (collect-pc-merged-code 
                               (MERGESTACKMAPANDCODE (G 'STACKMAPS METHOD)
                                                     (PARSECODE1 0 (G 'CODE METHOD))
                                                     (G 'METHOD-NAME METHOD)
                                                     METHOD-TABLE))))))
  :rule-classes :forward-chaining)







(defthm bcv-method-implies-not-bound-if-out-of-bound
  (implies (and (bcv-method method method-table)
                (assoc-equal pc (collect-witness-bcv-method method method-table)))
           (< pc (len (g 'code method))))
  :hints (("Goal" :in-theory (disable merged-code-safe
                                      ;;collect-witness-bcv-method
                                      extract-code
                                      member-in-merged-code-implies-pc-less
                                      sig-method-init-frame
                                      wff-code1)
           :use ((:instance          
                  member-in-merged-code-implies-pc-less
                  (merged-code
                   (MERGESTACKMAPANDCODE (G 'STACKMAPS METHOD)
                                              (PARSECODE1 0 (G 'CODE METHOD))
                                              (G 'METHOD-NAME METHOD)
                                              METHOD-TABLE))
                  (init-frame 
                   (SIG-METHOD-INIT-FRAME METHOD METHOD-TABLE)))))))
                        


(defthm bcv-method-implies-not-bound-if-out-of-bound-specific
  (implies (and (bcv-method (current-method st) (g 'method-table st))
                (assoc-equal pc (collect-witness-bcv-method 
                                 (current-method st)
                                 (g 'method-table st))))
           (< pc (len (g 'code (current-method st)))))
  :hints (("Goal" :in-theory (disable current-method
                                      bcv-method
                                      collect-witness-bcv-method)))
  :rule-classes :linear)






(defthm bcv-method-implies-not-bound-if-out-of-bound-2
  (implies (and (bcv-method method method-table)
                (assoc-equal pc (collect-witness-bcv-method method method-table)))
           (<= 0  pc))
  :hints (("Goal" :in-theory (disable merged-code-safe
                                      ;;collect-witness-bcv-method
                                      extract-code
                                      member-in-merged-code-implies-pc-less
                                      sig-method-init-frame
                                      wff-code1)
           :use ((:instance          
                  merged-code-is-safe-implies-not-bound-smaller
                  (merged-code
                   (MERGESTACKMAPANDCODE (G 'STACKMAPS METHOD)
                                              (PARSECODE1 0 (G 'CODE METHOD))
                                              (G 'METHOD-NAME METHOD)
                                              METHOD-TABLE))
                  (init-frame 
                   (SIG-METHOD-INIT-FRAME METHOD METHOD-TABLE)))))))
                        


(defthm bcv-method-implies-not-bound-if-out-of-bound-specific-2
  (implies (and (bcv-method (current-method st) (g 'method-table st))
                (assoc-equal pc (collect-witness-bcv-method 
                                 (current-method st)
                                 (g 'method-table st))))
           (<= 0  pc))
  :hints (("Goal" :in-theory (disable current-method
                                      bcv-method
                                      collect-witness-bcv-method)))
  :rule-classes :forward-chaining)


