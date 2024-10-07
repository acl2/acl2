(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")

;;(i-am-here) ;; Sat Dec 31 02:24:36 2005

(defthm is-suffix-facts
  (implies (IS-SUFFIX (LIST* MERGEDCODE1 any) mergedcode)
           (is-suffix any mergedcode))
  :rule-classes :forward-chaining)


(defthm is-suffix-facts-member
  (implies (IS-SUFFIX (LIST* MERGEDCODE1 any) mergedcode)
           (member mergedcode1 mergedcode))
  :rule-classes :forward-chaining)



;; (defthm is-suffix-implies-next-inst
;;    (implies  (IS-SUFFIX (LIST* frame inst rest) mergedcode)
;;              (equal (next-inst frame mergedcode)
;;                     inst))
;;    :hints (("Goal" :do-not '(generalize)
;;             :expand (IS-SUFFIX (LIST* frame inst rest) mergedcode))))
;; ;; this is not true!!! 

;----------------------------------------------------------------------

(local 
 (defthm next-inst-append
   (implies (not (member inst prefix))
            (equal (next-inst inst (append prefix suffix))
                   (next-inst inst suffix)))))

;;;
;;; list with duplicates!! 
;;;


;----------------------------------------------------------------------

;; (i-am-here) ;; Sun Jan  1 19:21:02 2006

(defthm pc-wff-mergedcode1-equal-pc
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (consp mergedcode)
                (not (isEnd (car mergedcode))))
           (equal (instrOffset (car (extract-code mergedcode))) pc))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               sig-do-inst
                               allinstructions
                               isEnd
                               mapFrame
                               jvm::inst-size
                               getMap mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))


(defthm is-suffix-pc-equal
  (implies (and (IS-SUFFIX (LIST* MERGEDCODE1 mergedcode4) mergedcode)
                (isStackMap mergedcode1)
                (pc-wff-mergedcode1 pc  mergedcode))
           (equal (instrOffset (car (extract-code mergedcode4)))
                  (mapOffset (getMap mergedcode1))))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               sig-do-inst
                               allinstructions
                               isEnd
                               mapFrame
                               jvm::inst-size
                               getMap mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))




                  
(defthm pc-wff-mergedcode1-implies-wff-merged-code-instr
  (implies (pc-wff-mergedcode1 pc mergedcode)
           (wff-mergedcode-instr mergedcode))
  :hints (("Goal" :in-theory (disable isInstruction isStackMap
                                      isEnd
                                      jvm::inst-size)))
  :rule-classes :forward-chaining)


(defthm is-suffix-extract-code-is-consp-lemma
  (implies (and (wff-mergedcode-instr mergedcode)
                (IS-SUFFIX (LIST* MERGEDCODE1 mergedcode4) mergedcode)
                (isStackMap mergedcode1))
           (consp (extract-code mergedcode4)))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               sig-do-inst
                               allinstructions
                               isEnd
                               mapFrame
                               jvm::inst-size
                               getMap mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap)))
    :rule-classes :forward-chaining)


(defthm is-suffix-not-end
  (implies (and (IS-SUFFIX (LIST* MERGEDCODE1 mergedcode4) mergedcode)
                (wff-merged-code-weak mergedcode)
                (isStackMap mergedcode1))
           (not (isEnd (car mergedcode))))
  :hints (("Goal" :in-theory (disable isInstruction isStackMap
                                      isEnd
                                      jvm::inst-size)))
  :rule-classes :forward-chaining)



(defthm isInstruction-car-extract-code-x
  (implies (consp (extract-code mergedcode))
           (isInstruction (car (extract-code mergedcode))))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               sig-do-inst
                               allinstructions
                               isEnd
                               mapFrame
                               jvm::inst-size
                               getMap mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap)))
  :rule-classes :forward-chaining)


                          
(defthm is-suffix-extract-code-is-code
  (implies (and (IS-SUFFIX (LIST* MERGEDCODE1 mergedcode4) mergedcode)
                (isStackMap mergedcode1)
                (pc-wff-mergedcode1 pc mergedcode))
           (isInstruction (car (extract-code mergedcode4))))
  :rule-classes :forward-chaining)


(defthm is-suffix-extract-code-is-consp
  (implies (and (IS-SUFFIX (LIST* MERGEDCODE1 mergedcode4) mergedcode)
                (isStackMap mergedcode1)
                (pc-wff-mergedcode1 pc mergedcode))
           (consp (extract-code mergedcode4)))
  :rule-classes :forward-chaining)


;----------------------------------------------------------------------
