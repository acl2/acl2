(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")


;----------------------------------------------------------------------


 


(local 
 (defthm mergedcodeistypesafe-implies-mergedcodeIsTypeSafe-lemma
   (implies (and (MERGEDCODEISTYPESAFE ENV mergedcode anyframe)
                 (never-after-goto (extract-frames mergedcode))
                 (isStackMap (car mergedcode))
                (wff-merged-code-weak mergedcode))
            (MERGEDCODEISTYPESAFE
             ENV
             (FORWARD-TO-NEXT-INST mergedcode)
             (NEXT-STACKFRAME mergedcode)))
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
                                isStackMap)))))



;; (local 
;;  (defthm mergedcodeistypesafe-implies-mergedcodeIsTypeSafe-lemma-2
;;    (implies (and (MERGEDCODEISTYPESAFE ENV (cdr mergedcode) 
;;                  (never-after-goto (extract-frames mergedcode))
;;                  (isStackMap (car mergedcode))
;;                 (wff-merged-code-weak mergedcode))
;;             (MERGEDCODEISTYPESAFE
;;              ENV
;;              (FORWARD-TO-NEXT-INST mergedcode)
;;              (NEXT-STACKFRAME mergedcode)))
;;    :hints (("Goal" :do-not '(generalize)
;;             :in-theory (disable instructionIsTypeSafe
;;                                 instructionSatisfiesHandlers
;;                                 instrOffset
;;                                 sig-do-inst
;;                                 allinstructions
;;                                 isEnd
;;                                 good-frame
;;                                 mapFrame
;;                                 getMap mapOffset
;;                                 frameIsAssignable
;;                                 isInstruction
;;                                 isStackMap)))))


(defthm mergedcodeistypesafe-implies-mergedcodeIsTypeSafe
  (implies (and (MERGEDCODEISTYPESAFE ENV x 
                                      (mapFrame (getMap (car mergedcode))))
                (never-after-goto (extract-frames mergedcode))
                (isStackMap (car mergedcode))
                (equal (cdr mergedcode) x)
                (wff-merged-code-weak mergedcode))
           (MERGEDCODEISTYPESAFE
            ENV
            (FORWARD-TO-NEXT-INST x)
            (NEXT-STACKFRAME mergedcode)))
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
                                isStackMap)
            :cases ((isStackMap (cadr mergedcode))))))


;----------------------------------------------------------------------

(defthm mergedcodeistypesafe-implies-mergedcodeIsTypeSafe-2
   (implies (and (MERGEDCODEISTYPESAFE ENV (cdr mergedcode)
                                       (car (sig-do-inst (car mergedcode)
                                                         env 
                                                         (SEARCHSTACKFRAME
                                                          (NEXT-PC MERGEDCODE)
                                                          (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV (ALLINSTRUCTIONS ENV)
                                                                                                    INIT-FRAME))))))
                 (never-after-goto (extract-frames mergedcode))
                 (isStackMap (cadr mergedcode))
                 (wff-merged-code-weak mergedcode))
            (MERGEDCODEISTYPESAFE
             ENV
             (FORWARD-TO-NEXT-INST (cdr mergedcode))
             (NEXT-STACKFRAME (cdr mergedcode))))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable instructionIsTypeSafe
                                       instructionSatisfiesHandlers
                                       instrOffset
                                       sig-do-inst
                                       allinstructions
                                       isEnd
                                       good-frame
                                       mapFrame
                                       next-stackframe
                                       forward-to-next-inst
                                       getMap mapOffset
                                       frameIsAssignable
                                       isInstruction
                                       isStackMap))))

(local 
 (defthm typelist-assignable-reflexive
   (TYPELISTASSIGNABLE x x  ENV)))

(local 
 (defthm frameisassignable-reflexive
   (FRAMEISASSIGNABLE frame frame env)))



(defthm mergedcodeistypesafe-expand-if-instruction-2
  (implies (and (isInstruction (car mergedcode))
                (consp (cdr mergedcode))
                (not (isEnd (cadr mergedcode)))
                (mergedcodeistypesafe env mergedcode init-frame)
                (equal (car (sig-do-inst (car mergedcode) env 
                                         init-frame))
                       'aftergoto))
           (MERGEDCODEISTYPESAFE ENV (CDR MERGEDCODE)
                                 (mapFrame (getMap (cadr mergedcode)))))
   :hints (("Goal" :in-theory (disable instructionIsTypeSafe
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
                                       isStackMap)
           :do-not-induct t
           :do-not '(generalize)))
   :rule-classes :forward-chaining)


;----------------------------------------------------------------------
;----------------------------------------------------------------------



(defthm mergedcodeistypesafe-expand-if-instruction
  (implies (and (isInstruction (car mergedcode))
                (mergedcodeistypesafe env mergedcode init-frame)
                (case-split (not (equal (car (sig-do-inst (car mergedcode) env 
                                                          init-frame))
                                        'aftergoto)))
                (case-split (NOT (EQUAL INIT-FRAME 'AFTERGOTO))))
           (MERGEDCODEISTYPESAFE ENV (CDR MERGEDCODE)
                                 (car (sig-do-inst (car mergedcode) env 
                                                   init-frame))))
  :hints (("Goal" :in-theory (disable instructionIsTypeSafe
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
                                       isStackMap)
           :do-not-induct t
           :do-not '(generalize )))
  :rule-classes :forward-chaining)

;----------------------------------------------------------------------
;----------------------------------------------------------------------

;; (i-am-here) ;; Mon Jan  2 20:10:13 2006

(local 
 (encapsulate ()
  (local (include-book "bcv-searchStackFrame-reduce"))
  (defthm searchStackFrame-is-if-stack-map
  (implies (and (isStackMap (car mergedcode))
                (equal (forward-to-next-inst mergedcode) 
                       (forward-to-next-inst x))
                (is-suffix mergedcode all-merged-code)
                (PC-WFF-MERGEDCODE1 PC ALL-MERGED-CODE)
                (mergedcodeistypesafe env all-merged-code init-frame))
           (EQUAL
            (SEARCHSTACKFRAME
             (INSTROFFSET (CAR (FORWARD-TO-NEXT-INST x)))
             (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV all-merged-code
                                                       INIT-FRAME)))
            (NEXT-STACKFRAME mergedcode))))))



(local 
 (defthm is-suffix-wff-stack-map-offset
   (implies (and (wff-stack-map-offset mergedcode)
                 (wff-mergedcode-instr mergedcode)
                 (isStackMap (car mergedcode)))
            (equal (mapOffset (getMap (car mergedcode)))
                   (instrOffset (car (forward-to-next-inst mergedcode)))))))



(defthm mergedcodeistypesafe-implies-mergedcodeIsTypeSafe-specific
  (implies (and (MERGEDCODEISTYPESAFE ENV mergedcode anyframe)
                (never-after-goto (extract-frames mergedcode))
                (isStackMap (car mergedcode))
                (wff-merged-code-weak mergedcode))
           (MERGEDCODEISTYPESAFE
            ENV
            (FORWARD-TO-NEXT-INST mergedcode)
            (NEXT-STACKFRAME mergedcode)))
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
 (defthm if-car-inst-searchStackframe-is-init
   (implies (and (mergedcodeistypesafe env mergedcode init-frame)
                 (wff-merged-code-weak mergedcode)
                 (isInstruction (car mergedcode)))
            (equal (searchstackframe (instrOffset (car mergedcode))
                                     (stack-map-wrap 
                                      (collect-sig-frame-vector 
                                       env
                                       mergedcode init-frame)))
                   init-frame))
  :hints (("Goal" :in-theory (disable instructionIsTypeSafe
                                      instructionSatisfiesHandlers
                                      instrOffset
                                      sig-do-inst
                                      allinstructions
                                      isEnd
                                      good-frame
                                      mapFrame
                                      mergedcodeistypesafe-implies-mergedcodeIsTypeSafe-lemma
                                      getMap mapOffset
                                      frameIsAssignable
                                      isInstruction
                                      isStackMap)
           :do-not-induct t))))
             
;;(i-am-here) ;; Mon Jan  2 20:46:28 2006                 


;; (local 
;;  (defthm is-suffix-wff-stack-map-offset
;;    (implies (and (wff-stack-map-offset mergedcode)
;;                  (wff-mergedcode-instr mergedcode)
;;                  (isStackMap (car mergedcode)))
;;             (equal (mapOffset (getMap (car mergedcode)))
;;                    (instrOffset (car (forward-to-next-inst mergedcode)))))))


(local 
 (defthm is-suffix-wff-merged-code-instr-2
   (implies (and (wff-mergedcode-instr mergedcode)
                 (isStackMap (car mergedcode)))
            (isInstruction (car (forward-to-next-inst mergedcode))))))
           
(local 
 (defthm forward-to-next-inst-id
   (implies (and (wff-merged-code-weak mergedcode)
                 (not (isStackMap (car mergedcode)))
                 (not (isEnd (car mergedcode))))
            (equal (forward-to-next-inst mergedcode)
                   mergedcode))))


(defthm mergedcodeistypesafe-mergedcodeIsType
  (implies (and (mergedcodeistypesafe env mergedcode init-frame)
                (case-split (not (isEnd (car mergedcode))))
                (never-after-goto (extract-frames mergedcode))
                (pc-wff-mergedcode1 pc mergedcode)
                (wff-mergedcode-instr mergedcode)
                (wff-merged-code-weak mergedcode))
           (MERGEDCODEISTYPESAFE ENV (forward-to-next-inst mergedcode)
                                 (searchstackframe 
                                  (next-pc (forward-to-next-inst mergedcode))
                                  (stack-map-wrap 
                                   (collect-sig-frame-vector 
                                    env
                                    mergedcode init-frame)))))
  :hints (("Goal" :in-theory (disable instructionIsTypeSafe
                                      instructionSatisfiesHandlers
                                      instrOffset
                                      sig-do-inst
                                      allinstructions
                                      isEnd
                                      jvm::inst-size
                                      good-frame
                                      mapFrame
                                      mergedcodeistypesafe
                                      mergedcodeistypesafe-implies-mergedcodeIsTypeSafe-lemma
                                      getMap mapOffset
                                      frameIsAssignable
                                      isInstruction
                                      isStackMap)
           :do-not-induct t
           :do-not '(generalize)
           :cases ((not (isStackMap (car mergedcode)))))
          ("Subgoal 2" :use ((:instance
                              mergedcodeistypesafe-implies-mergedcodeIsTypeSafe-lemma
                              (anyframe init-frame))))))
                              


