(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")

;----------------------------------------------------------------------

(defthm is-suffix-pc-wff-mergecode1
  (implies (and (is-suffix mergedcode1 mergedcode)
                (consp mergedcode1)
                (not (isEnd (car mergedcode1)))
                (pc-wff-mergedcode1 pc mergedcode))
           (pc-wff-mergedcode1 (next-pc mergedcode1)
                               mergedcode1))
  :hints (("Goal" :in-theory (disable isStackMap
                                      isInstruction
                                      isEnd
                                      getMap
                                      mapOffset
                                      jvm::inst-size
                                      instrOffset)
           :do-not '(generalize)))
   :rule-classes :forward-chaining)



(defthm pc-wff-mergedcode1-isStackMap-consp-remaining
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (isStackMap (car mergedcode)))
           (consp (cdr mergedcode)))
  :rule-classes :forward-chaining)


;----------------------------------------------------------------------


