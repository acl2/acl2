(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")


;----------------------------------------------------------------------



(defthm mergedcodeIsTypesafe-implies-all-good-frames
  (implies (and (mergedcodeIsTypesafe env mergedcode init-frame)
                (all-good-frames (extract-frames mergedcode) env)
                (good-frame init-frame env)
                (good-env env))
           (all-good-frames (stack-map-wrap 
                             (collect-sig-frame-vector env mergedcode
                                                       init-frame))
                            env))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                                      instructionSatisfiesHandlers
                                      instrOffset
                                      sig-do-inst
                                      allinstructions
                                      isEnd
                                      good-frame
                                      mapFrame
                                      getMap mapOffset
                                      frameIsAssignable
                                      isInstruction
                                      isStackMap))))




(defun offset-found (pc l)
  (if (endp l) nil
    (or (equal (mapOffset (getMap (car l))) pc)
        (offset-found pc (cdr l)))))

(defun all-stack-frames (l)
  (if (endp l) t
    (and (isstackmapframe (car l))
         (all-stack-frames (cdr l)))))


(defthm all-stack-frame-stack-map-wrap
  (all-stack-frames (stack-map-wrap l)))


(defthm all-good-frames-found-then-good
  (implies (and (all-good-frames l env)
                (all-stack-frames l)
                (offset-found pc l))
           (good-frame (searchstackframe pc l) env))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable good-frame 
                               isStackMap
                               mapOffset
                               mapFrame
                               getMap))))


(defthm mergedcodeIsTypesafe-offset-found
  (implies (and (mergedcodeIsTypesafe env mergedcode init-frame)
                (member inst mergedcode)
                (isInstruction inst))
           (offset-found (instrOffset inst)
                         (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV mergedcode
                                                                   INIT-FRAME))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               sig-do-inst
                               allinstructions
                               isEnd
                               good-frame
                               mapFrame
                               getMap mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))










(defthm good-frame-searchStackMap
   (implies (and (mergedcodeIsTypesafe env mergedcode init-frame)
                 (member inst mergedcode)
                 (isInstruction inst)
                 (all-good-frames (extract-frames mergedcode) env)
                 (good-frame init-frame env)
                 (good-env env))
            (good-frame (searchstackframe (instrOffset inst)
                                          (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV mergedcode
                                                                                    INIT-FRAME)))
                        env))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               sig-do-inst
                               allinstructions
                               isEnd
                               good-frame
                               mapFrame
                               getMap mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))


(local 
 (defthm is-suffix-wff-merged-code-instr-2
   (implies (and (wff-mergedcode-instr mergedcode)
                 (isStackMap (car mergedcode)))
            (isInstruction (car (forward-to-next-inst mergedcode))))))
           

(local 
 (defthm is-suffix-wff-merged-code-instr-wff-merged-code-instr
   (implies (and (is-suffix mergedcode1 mergedcode2)
                 (wff-mergedcode-instr mergedcode2))
            (wff-mergedcode-instr mergedcode1))
   :rule-classes :forward-chaining))


(local 
 (defthm is-suffix-suffix
   (implies (member frame mergedcode)
            (is-suffix (suffix frame mergedcode) mergedcode))))

(local 
 (defthm equal-car-suffix-is-frame
   (implies (member frame mergedcode)
            (equal (car (suffix frame mergedcode))
                   frame))))


(defthm frame-pc-is-equal-some-pc
  (implies (and (wff-mergedcode-instr mergedcode)
                (member frame mergedcode)
                (isStackMap frame))
           (isInstruction 
            (car (forward-to-next-inst (suffix frame mergedcode)))))
  :hints (("Goal" :in-theory (disable suffix
                                      isInstruction
                                      wff-mergedcode-instr isStackMap)
           :use ((:instance
                  is-suffix-wff-merged-code-instr-wff-merged-code-instr
                  (mergedcode1 (suffix frame mergedcode))
                  (mergedcode2 mergedcode))))))


(local 
 (defthm is-suffix-wff-stack-map-offset
   (implies (and (wff-stack-map-offset mergedcode)
                 (wff-mergedcode-instr mergedcode)
                 (isStackMap (car mergedcode)))
            (equal (mapOffset (getMap (car mergedcode)))
                   (instrOffset (car (forward-to-next-inst mergedcode)))))))


(local 
 (defthm is-suffix-wff-stack-map-offset-wff-stack-map-offset
   (implies (and (is-suffix mergedcode1 mergedcode2)
                 (wff-stack-map-offset mergedcode2))
            (wff-stack-map-offset mergedcode1))
   :rule-classes :forward-chaining))

(defthm frame-pc-is-equal-some-pc-2
  (implies (and (wff-stack-map-offset mergedcode)
                (wff-mergedcode-instr mergedcode)
                (member frame mergedcode)
                (isStackMap frame))
           (equal (mapOffset (getMap frame))
                  (instrOffset (car (forward-to-next-inst (suffix frame mergedcode))))))
  :hints (("Goal" :in-theory (disable suffix
                                      isEnd
                                      forward-to-next-inst
                                      wff-mergedcode-instr
                                      is-suffix-wff-stack-map-offset
                                      wff-stack-map-offset
                                      isStackMap
                                      isInstruction
                                      mapOffset
                                      getMap)
           :use ((:instance
                  is-suffix-wff-merged-code-instr-wff-merged-code-instr
                  (mergedcode1 (suffix frame mergedcode))
                  (mergedcode2 mergedcode))
                 (:instance 
                  is-suffix-wff-stack-map-offset-wff-stack-map-offset
                  (mergedcode1 (suffix frame mergedcode))
                  (mergedcode2 mergedcode))
                 (:instance 
                  is-suffix-wff-stack-map-offset
                  (mergedcode (suffix frame mergedcode)))))))


(local 
 (defthm is-suffix-wff-merged-code-instr-3
   (implies (and (wff-mergedcode-instr mergedcode)
                 (isStackMap (car mergedcode)))
            (member (car (forward-to-next-inst mergedcode))
                    mergedcode))))

(local 
 (defthm member-suffix-member-all
   (implies (member inst (suffix x mergedcode))
            (member inst mergedcode))))



(defthm frame-pc-is-equal-some-pc-3
  (implies (and (wff-mergedcode-instr mergedcode)
                (member frame mergedcode)
                (isStackMap frame))
           (member (car (forward-to-next-inst (suffix frame mergedcode)))
                   mergedcode))
  :hints (("Goal" :in-theory (disable suffix
                                      isEnd
                                      forward-to-next-inst
                                      wff-mergedcode-instr
                                      is-suffix-wff-stack-map-offset
                                      wff-stack-map-offset
                                      isStackMap
                                      isInstruction
                                      mapOffset
                                      getMap)
           :use ((:instance
                  is-suffix-wff-merged-code-instr-wff-merged-code-instr
                  (mergedcode1 (suffix frame mergedcode))
                  (mergedcode2 mergedcode))
                 (:instance 
                  member-suffix-member-all
                  (inst (car (forward-to-next-inst (suffix frame mergedcode))))
                  (x frame))))))


(defthm mergedcodeIsTypesafe-offset-found-2
  (implies (and (mergedcodeIsTypesafe env mergedcode init-frame)
                (wff-mergedcode-instr mergedcode)
                (wff-stack-map-offset mergedcode)
                (member frame mergedcode)
                (isStackMap frame))
           (offset-found (mapOffset (getMap frame))
                         (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV mergedcode
                                                                   INIT-FRAME))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               sig-do-inst
                               allinstructions
                               isEnd
                               jvm::inst-size
                               good-frame
                               mapFrame
                               getMap mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))




(defthm good-frame-searchStackMap-2
  (implies (and (mergedcodeIsTypesafe env mergedcode init-frame)
                (all-good-frames (extract-frames mergedcode) env)
                (member frame mergedcode)
                (isStackMap frame)
                (wff-mergedcode-instr mergedcode)
                (wff-stack-map-offset mergedcode)
                (good-frame init-frame env)
                (good-env env))
           (good-frame (searchstackframe (mapOffset (getMap frame))
                                         (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV mergedcode
                                                                                   INIT-FRAME)))
                       env))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               sig-do-inst
                               allinstructions
                               isEnd
                               jvm::inst-size
                               good-frame
                               mapFrame
                               getMap mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap)
           :do-not-induct t
           :use ((:instance good-frame-searchStackMap
                            (inst (car (forward-to-next-inst (suffix frame
                                                                     mergedcode)))))))))
                            
