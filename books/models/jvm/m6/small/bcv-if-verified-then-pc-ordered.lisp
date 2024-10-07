(in-package "ACL2")
(include-book "bcv-model")
(include-book "bcv-simple-model")
(include-book "generic")

(local (encapsulate () 

   (local (include-book "bcv-find-correct-witness-bcv-check-pre"))

   (defthm collect-pc-merged-code-merged-code-1
     (implies (and (merged-code-safe merged-code init-frame)
                   (case-split (not (equal init-frame 'aftergoto))))
              (equal (car (collect-pc-merged-code merged-code))
                     (g 'pc init-frame)))
     :rule-classes :linear)


   ;; (defthm collect-pc-merged-code-merged-code-2
   ;;    (implies (and (merged-code-safe merged-code init-frame)
   ;;                  (wff-code1 (extract-code merged-code) 
   ;;                             (g 'pc (car merged-code))))
   ;;             (equal (car (collect-pc-merged-code merged-code))
   ;;                    (g 'pc (car merged-code))))
   ;;    :rule-classes :linear)

   ;; (defthm wff-code1-uniqueness
   ;;   (IMPLIES
   ;;    (AND (WFF-CODE1 (EXTRACT-CODE MERGED-CODE4) any)
   ;;         (MERGED-CODE-SAFE MERGED-CODE4 MERGED-CODE3))
   ;;     (wff-code1 (extract-code merged-code4)
   ;;                (g 'pc (car merged-code4))))
   ;;   :rule-classes :forward-chaining)

   (encapsulate () 
    (local (include-book "bcv-find-correct-witness-bcv-check-pre"))
    (defthm merged-code-safe-implies-extract-code-pc-is-same-strong-linear
      (implies (merged-code-safe merged-code sig-frame)
               (equal (g 'pc (car (extract-code merged-code)))
                      (g 'pc (car merged-code))))
      :rule-classes :linear))


   (defthm wff-code1-implies-pc-less
     (implies (and (wff-code1 code (+ 1 pc))
                   (consp code))
              (< pc (g 'pc (car code))))
     :rule-classes :forward-chaining)


   (defthm merged-code-safe-implies-pc-less-than
     (implies (and (WFF-CODE1 (EXTRACT-CODE MERGED-CODE)
                              (+ 1 pc))
                   (consp (extract-code merged-code))
                   (merged-code-safe merged-code sig-frame))
              (< pc 
                 (g 'pc (car merged-code))))
     :hints (("Goal" :do-not-induct t
              :in-theory (disable wff-code1
                                  extract-code
                                  merged-code-safe)
              :use ((:instance wff-code1-implies-pc-less
                               (code (extract-code merged-code))))))
     :rule-classes :linear)
              
   ;;
   ;; not necessary! 

   (defthm merged-code-safe-stack-map-implies-consp-extract-code
     (implies (and (merged-code-safe merged-code init-frame)
                   (stack-map? init-frame))
              (consp (extract-code merged-code)))
     :rule-classes :forward-chaining)


   (encapsulate () 
     (local       
      (defthm get-is-stack-map-sig-frame-pop-n
        (equal (g 'is-stack-map (sig-frame-pop-n n sig-frame))
               (g 'is-stack-map sig-frame))))
     (local 
      (defthm get-is-inst-sig-frame-pop-n
        (equal (g 'is-inst (sig-frame-pop-n n sig-frame))
               (g 'is-inst sig-frame))))

      (local 
       (defthm get-pc-sig-frame-pop-n
         (equal (g 'pc (sig-frame-pop-n n sig-frame))
                (g 'pc sig-frame))))

      (defthm bcv-execute-step-produce-stack-map-or-aftergoto
        (implies (and (stack-map? stack-map)
                      (bcv-check-step-pre inst stack-map)
                      (not (stack-map? (bcv-execute-step inst stack-map))))
                 (equal (bcv-execute-step inst stack-map) 'aftergoto))))


   (defthm merged-code-is-safe-implies-ordered-lemma
      (implies (and (merged-code-safe merged-code init-frame)
                    (consp (extract-code merged-code))
                    (wff-code1 (extract-code merged-code)
                               (g 'pc (car merged-code))))
               (ordered (collect-pc-merged-code merged-code)))
      :hints (("Goal" :in-theory (disable sig-frame-compatible
                                          bcv-check-step-pre
                                          bcv-execute-step
                                          inst? stack-map?)
               :do-not '(generalize fertilize))))

   ;----------------------------------------------------------------------


   (defthm collect-pc-merged-code-merged-code-3
       (implies (and (merged-code-safe merged-code init-frame)
                     (not (consp (extract-code merged-code))))
                (equal (car (collect-pc-merged-code merged-code))
                       (g 'pc init-frame)))
       :rule-classes :linear)



   (defthm collect-pc-merged-code-merged-code-4
       (implies (and (merged-code-safe merged-code init-frame)
                     (not (consp (extract-code merged-code))))
                (ordered (collect-pc-merged-code merged-code))))

   ;----------------------------------------------------------------------

   (defthm merged-code-is-safe-implies-ordered
      (implies (and (merged-code-safe merged-code init-frame)
                    (wff-code1 (extract-code merged-code)
                               (g 'pc (car merged-code))))
               (ordered (collect-pc-merged-code merged-code)))
      :hints (("Goal" :in-theory (disable sig-frame-compatible
                                          bcv-check-step-pre
                                          bcv-execute-step
                                          inst? stack-map?)
               :do-not '(generalize fertilize)
               :cases ((consp (extract-code merged-code))))))

))
;----------------------------------------------------------------------

(defthm merged-code-is-safe-implies-ordered
   (implies (and (merged-code-safe merged-code init-frame)
                 (wff-code1 (extract-code merged-code)
                            (g 'pc (car merged-code))))
            (ordered (collect-pc-merged-code merged-code)))
   :hints (("Goal" :in-theory (disable sig-frame-compatible
                                       bcv-check-step-pre
                                       bcv-execute-step
                                       inst? stack-map?)
            :do-not '(generalize fertilize)
            :cases ((consp (extract-code merged-code))))))

;----------------------------------------------------------------------

(defthm merged-code-safe-implies-pc-less-than
  (implies (and (WFF-CODE1 (EXTRACT-CODE MERGED-CODE)
                           (+ 1 pc))
                (consp (extract-code merged-code))
                (merged-code-safe merged-code sig-frame))
           (< pc 
              (g 'pc (car merged-code))))
  :rule-classes :linear)
           
(defthm merged-code-safe-stack-map-implies-consp-extract-code
  (implies (and (merged-code-safe merged-code init-frame)
                (stack-map? init-frame))
           (consp (extract-code merged-code)))
  :rule-classes :forward-chaining)
