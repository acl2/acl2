(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")

;;(local (include-book "bcv-collect-sig-frame-vector-never-aftergoto"))


(defthm mergedcodeistypesafe-implies-not-end-consp
  (implies (and (mergedcodeistypesafe env mergedcode init-frame)
                (consp mergedcode)
                (pc-wff-mergedcode1 pc mergedcode)
                (not (isEnd (car mergedcode))))
           (consp (collect-sig-frame-vector env mergedcode init-frame)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               sig-do-inst
                               allinstructions
                               isEnd
                               jvm::inst-size
                               mapFrame
                               getMap mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))

  

(defthm mergedcodeistypesafe-mergedcodeistype-safe
  (implies (and (mergedcodeistypesafe env mergedcode init-frame)
                (consp mergedcode1)
                (is-suffix mergedcode1 mergedcode))
           (mergedcodeistypesafe env mergedcode1 
                                 (collect-sig-frame-at-mergecode1 
                                  env mergedcode1 mergedcode init-frame)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               sig-do-inst
                               allinstructions
                               isEnd
                               jvm::inst-size
                               mapFrame
                               getMap mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))

(defthm mapOffset-is-next-pc
  (implies (and (mergedcodeistypesafe env mergedcode init-frame)
                (pc-wff-mergedcode1 (next-pc mergedcode) mergedcode))
           (equal (mapOffset (car (collect-sig-frame-vector env mergedcode
                                                            init-frame)))
                  (next-pc mergedcode)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               sig-do-inst
                               allinstructions
                               isEnd
                               jvm::inst-size
                               mapFrame
                               getMap mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))

(defthm pc-wff-mergedcode1-pc-wff-mergedcode-pc-suffix
  (implies (and (pc-wff-mergedcode1 (next-pc mergedcode) mergedcode)
                (is-suffix mergedcode1 mergedcode)
                (consp mergedcode1)
                (not (isEnd (car mergedcode1))))
           (pc-wff-mergedcode1 (next-pc mergedcode1) mergedcode1))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               sig-do-inst
                               allinstructions
                               isEnd
                               jvm::inst-size
                               mapFrame
                               getMap mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap)))
  :rule-classes :forward-chaining)

