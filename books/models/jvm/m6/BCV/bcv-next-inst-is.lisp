(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")


(local 
 (defthm is-suffix-facts
   (implies (IS-SUFFIX (LIST* MERGEDCODE1 any) mergedcode)
            (is-suffix any mergedcode))
   :rule-classes :forward-chaining))
 

(local 
 (defthm is-suffix-facts-member
   (implies (IS-SUFFIX (LIST* MERGEDCODE1 any) mergedcode)
            (member mergedcode1 mergedcode))
   :rule-classes :forward-chaining))




(defthm member-suffix-member
  (implies (MEMBER mergedcode1
                   (SUFFIX mergedcode1 MERGEDCODE2))
           (member mergedcode1 mergedcode2)))


           

(defthm member-implies-member-extract-pc
  (implies (and (member inst mergedcode)
                (wff-merged-code-weak mergedcode)
                (isInstruction inst))
           (member (instroffset inst)
                   (extract-pc (extract-code mergedcode)))))

(defthm member-instroffset-implies-not-all-strictly-less-than
  (implies (member x l)
           (not (all-strictly-less-than x l))))

(defthm is-suffix-member
  (implies (and (is-suffix mergedcode1 mergedcode3)
                (MEMBER MERGEDCODE2 MERGEDCODE1))
           (member mergedcode2 mergedcode3)))


(defthm is-suffix-suffix-equal
  (implies (and (is-suffix mergedcode1 mergedcode)
                (member inst mergedcode)
                (equal (car mergedcode1) inst)
                (isInstruction inst)
                (strictly-ordered (extract-pc (extract-code mergedcode)))
                (wff-merged-code-weak mergedcode))
           (equal (suffix inst mergedcode)
                  mergedcode1))
   :hints (("Goal" :do-not '(generalize fertilize)
            :in-theory (disable isInstruction
                                isstackmap
                                jvm::inst-size
                                mapOffset
                                getMap
                                instroffset
                                isEnd)
            :induct (is-suffix mergedcode1 mergedcode))))


(defthm next-inst-is-car-suffix
  (implies (and (consp mergedcode)
                (consp (cdr mergedcode)))
           (equal  (next-inst inst mergedcode)
                   (cadr (suffix inst mergedcode)))))


(defthm is-suffix-consp
  (implies (is-suffix (list* inst1 rest) mergedcode)
           (consp mergedcode))
  :rule-classes :forward-chaining)

(defthm is-suffix-consp-2
  (implies (is-suffix (list* inst1 inst2 rest) mergedcode)
           (consp (cdr mergedcode)))
  :rule-classes :forward-chaining)


(defthm is-suffix-implies-next-inst
  (implies  (and (IS-SUFFIX (LIST* inst1 inst2 rest) mergedcode)
                 (wff-merged-code-weak mergedcode)
                 (strictly-ordered (extract-pc (extract-code mergedcode)))
                 (wff-stack-map-offset-2 mergedcode)
                 (isInstruction inst1))
            (equal (next-inst inst1 mergedcode)
                   inst2))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isInstruction
                               isStackMap
                               isEnd)
           :do-not-induct t)))
                              
        
(encapsulate () 
  (local (include-book "bcv-collected-frames-are-strictly-ordered"))
  (defthm pc-wff-mergedcode1-isInstruction-then-next-pc-is-greater
   (implies (and (pc-wff-mergedcode1 pc mergedcode)
                 (consp mergedcode)
                 (isInstruction (car mergedcode)))
           (all-strictly-less-than (instroffset (car mergedcode))
                                   (extract-pc (extract-code (cdr mergedcode)))))))


(local
 (defthm pc-wff-mergedcode1-strictly-ordered-extract-pc-extract-code
   (implies (pc-wff-mergedcode1 pc mergedcode)
            (strictly-ordered (extract-pc (extract-code mergedcode))))
   :hints (("Goal" :in-theory (disable isInstruction
                                       isstackmap
                                       jvm::inst-size
                                       mapOffset getMap
                                       instroffset
                                       isEnd)))))


(defthm is-suffix-implies-next-inst-specific
  (implies  (and (IS-SUFFIX mergedcode (allinstructions env))
                 (pc-wff-mergedcode1 0 (allinstructions env))
                 (consp mergedcode)
                 (consp (cdr mergedcode))
                 (isInstruction (car mergedcode)))
            (equal (next-inst (car mergedcode) (allinstructions env))
                   (cadr mergedcode)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isInstruction
                               isStackMap
                               isEnd)
           :do-not-induct t)))