(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "../M6-DJVM-shared/jvm-bytecode")


(include-book "bcv-base")



(local 
 (encapsulate () 
   (local (include-book "bcv-wff-code"))           
   (defthm pc-wff-mergedcode1-offset-specific
     (implies (and (IS-SUFFIX (CONS instr1 mergedcode1)
                              mergedcode)
                   (isInstruction instr1)
                   (pc-wff-mergedcode1 0 mergedcode)
                   (member instr2 (extract-code mergedcode1)))
              (not (equal  (instrOffset instr1)
                           (instrOffset instr2)))))))


(defthm mergedcodeIsTypesafe-implies-instructionIsTypeSafe
  (implies (and (mergedcodeIsTypesafe env mergedcode stackframe)
                (pc-wff-mergedcode1 0 (allinstructions env))
                (is-suffix mergedcode (allinstructions env))
                (member inst (extract-code mergedcode)))
           (instructionIsTypeSafe 
            inst 
            env
            (searchStackFrame (instrOffset inst)
                              (stack-map-wrap 
                               (collect-sig-frame-vector env
                                                         mergedcode
                                                         stackframe)))))
  :hints (("Goal" 
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               sig-do-inst
                               frameIsAssignable
                               isEnd
                               allinstructions
                               isInstruction
                               isStackMap)
           :do-not '(generalize))))
