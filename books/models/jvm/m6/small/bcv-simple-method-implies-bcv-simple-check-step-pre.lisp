(in-package "ACL2")
(include-book "bcv-simple-model")

;;; Mon Nov 21 15:10:31 2005


(encapsulate () 
  (local (include-book "bcv-simple-method-properties"))
  (defthm bcv-simple-method-implies-next-inst-verified
    (implies (and (bcv-simple-method method method-table)
                  (integerp pc)
                  (<= 0 pc)
                  (< pc (len (g 'code method))))
             (bcv-simple-inst pc 
                              (nth pc (g 'code method))
                              (g 'sig-vector method)))))
  

(defthm method-verified-implies-bcv-simple-check-step-pre-on-recorded-signature-lemma                 
  (implies (and (bcv-simple-method method method-table)
                 (integerp pc)
                 (<= 0 pc)
                 (< pc (len (g 'code method)))
                (equal inst (nth pc (g 'code method)))
                (member inst (g 'code method)))
            (bcv-simple-check-step-pre inst 
                                       (cdr (assoc-equal pc (g 'sig-vector
                                                               method)))))
  :hints (("Goal" :in-theory (e/d (bcv-simple-method)
                                  (bcv-simple-check-step-pre
                                   all-next-state-safe))
           :do-not-induct t
           :use ((:instance bcv-simple-method-implies-next-inst-verified)))))
                            

