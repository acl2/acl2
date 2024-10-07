(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")

;----------------------------------------------------------------------

(encapsulate ()
  (local (include-book "bcv-instructionIsTypeSafe-if-verified"))
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
                                                           stackframe)))))))
  


;----------------------------------------------------------------------



(defun mergedcodeIsTypeSafe-induct (env init-frame mergedcode stackmap)
  (if (endp mergedcode)
      (list env init-frame mergedcode stackmap)
    (if (endp (cdr mergedcode))
        (list (list env init-frame mergedcode stackmap))
      (cond ((isinstruction (car mergedcode))
             (cond ((isStackMap (cadr mergedcode))
                    (mergedcodeIsTypeSafe-induct env init-frame
                                                 (forward-to-next-inst (cdr mergedcode))
                                                 (next-stackframe (cdr mergedcode))))
                   ((isInstruction (cadr mergedcode))
                    (mv-let (next-stack-frame exception-frame)
                            (sig-do-inst (car mergedcode) env stackmap)
                            (declare (ignore exception-frame))
                            (mergedcodeIsTypeSafe-induct env init-frame 
                                                         (cdr mergedcode)
                                                         next-stack-frame)))))
            ((isStackMap (car mergedcode))
             (mergedcodeIsTypeSafe-induct env init-frame
                                          (forward-to-next-inst mergedcode)
                                          (next-stackframe mergedcode)))))))
             
;----------------------------------------------------------------------


(defthm is-suffix-forward-to-next-is-suffix
  (implies (is-suffix mergedcode1 mergedcode)
           (IS-SUFFIX (FORWARD-TO-NEXT-INST mergedcode1) mergedcode))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isInstruction)
           :induct (forward-to-next-inst mergedcode1))))


;----------------------------------------------------------------------

(defthm pc-wff-mergedcode1-never-end-on-a-stackmap
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (isStackMap stackmap)
                (isEnd end))
           (not (is-suffix (list* stackmap end any)
                           mergedcode)))
  :hints (("Goal" :in-theory (disable isStackMap isEnd 
                                      jvm::inst-size
                                      isInstruction))))
;----------------------------------------------------------------------

;;;
;;; it is critical for sun's bcv, we could not have aftergoto as part of the
;;; marking.  Wed Dec 28 14:26:13 2005
;;;

(defthm pc-wff-mergedcode1-never-aftergoto
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (isStackMap stackmap)
                (member stackmap mergedcode))
           (not (equal (mapFrame (getMap stackmap))
                       'aftergoto)))
  :hints (("Goal" :in-theory (disable isStackMap isEnd 
                                      jvm::inst-size
                                      isInstruction))))               




(encapsulate ()
 (local (include-book "bcv-wff-code"))
 (defthm is-suffix-member-f
   (implies (IS-SUFFIX (cons instr mergedcode1)
                       MERGEDCODE)
            (member instr mergedcode))
   :rule-classes :forward-chaining))



;----------------------------------------------------------------------

(defthm pc-wff-mergedcode1-f
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (not (isEnd (car mergedcode))))
           (pc-wff-mergedcode1 (next-pc mergedcode) mergedcode))
  :hints (("Goal" :in-theory (disable jvm::inst-size 
                                      isInstruction
                                      isStackMap
                                      isEnd)
           :do-not '(generalize)))
  :rule-classes :forward-chaining)


(defthm mergedcodeIsTypesafe-forward-to-next-inst
  (implies (and (mergedcodeIsTypesafe env mergedcode stackframe)
                (not (isInstruction (car mergedcode)))
                (pc-wff-mergedcode1 (next-pc mergedcode) mergedcode))
           (mergedcodeIsTypesafe env 
                                 (forward-to-next-inst mergedcode)
                                 (next-stackframe mergedcode)))
  :hints (("Goal" :in-theory (disable instructionIsTypeSafe
                                      instructionSatisfiesHandlers
                                      instrOffset
                                      sig-do-inst
                                      allinstructions
                                      isEnd
                                      mapFrame
                                      getMap mapOffset
                                      frameIsAssignable
                                      isInstruction
                                      isStackMap)
           :do-not '(generalize)))
  :rule-classes :forward-chaining)

(defthm mergedcodeIsTypesafe-forward-to-next-inst-b
  (implies (and (mergedcodeIsTypesafe env mergedcode (mapFrame (getMap mergedcode1)))
                (isStackMap mergedcode1)
                (pc-wff-mergedcode1 (next-pc mergedcode) mergedcode))
           (mergedcodeIsTypesafe env 
                                 (forward-to-next-inst (cons mergedcode1 mergedcode))
                                 (next-stackframe (cons mergedcode1 mergedcode))))
  :hints (("Goal" :in-theory (disable instructionIsTypeSafe
                                      instructionSatisfiesHandlers
                                      instrOffset
                                      sig-do-inst
                                      allinstructions
                                      isEnd
                                      mapFrame
                                      getMap mapOffset
                                      frameIsAssignable
                                      isInstruction
                                      isStackMap)
           :do-not '(generalize))))



(defthm forward-to-next-inst-get-inst-if-pc-wff-merged-code
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (consp mergedcode)
                (isStackMap (car mergedcode)))
           (isinstruction (car (forward-to-next-inst mergedcode))))
  :hints (("Goal" :in-theory (disable instructionIsTypeSafe
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



(local (in-theory (disable next-stackframe forward-to-next-inst)))


(encapsulate () 
 (local (include-book "bcv-pc-wff-mergedcode1"))


 (defthm is-suffix-pc-wff-mergecode1
   (implies (and (is-suffix mergedcode1 mergedcode)
                (consp mergedcode1)
                (not (isEnd (car mergedcode1)))
                (pc-wff-mergedcode1 pc mergedcode))
           (pc-wff-mergedcode1 (next-pc mergedcode1)
                               mergedcode1))
   :rule-classes :forward-chaining)



 (defthm pc-wff-mergedcode1-isStackMap-consp-remaining
   (implies (and (pc-wff-mergedcode1 pc mergedcode)
                 (isStackMap (car mergedcode)))
            (consp (cdr mergedcode)))
   :rule-classes :forward-chaining))



;----------------------------------------------------------------------

;;; 

;;(i-am-here) ;; Sat Dec 31 02:22:06 2005


(encapsulate () 
 (local (include-book "bcv-is-suffix-facts"))

 (defthm is-suffix-facts
   (implies (IS-SUFFIX (LIST* MERGEDCODE1 any) mergedcode)
            (is-suffix any mergedcode))
   :rule-classes :forward-chaining)


 (defthm is-suffix-facts-member
   (implies (IS-SUFFIX (LIST* MERGEDCODE1 any) mergedcode)
            (member mergedcode1 mergedcode))
   :rule-classes :forward-chaining))



(defthm forward-to-next-inst-get-inst-if-pc-wff-merged-code-specific
  (implies (and (is-suffix (list* mergedcode1 mergedcode) (allinstructions env))
                (pc-wff-mergedcode1 0 (allinstructions env))
                (isStackMap mergedcode1))
           (isinstruction (car (forward-to-next-inst (cons mergedcode1 mergedcode)))))
  :hints (("Goal" :in-theory (disable instructionIsTypeSafe
                                      instructionSatisfiesHandlers
                                      instrOffset
                                      sig-do-inst
                                      allinstructions
                                      isEnd
                                      ;;next-pc
                                      mapFrame
                                      jvm::inst-size
                                      getMap mapOffset
                                      frameIsAssignable
                                      isInstruction
                                      isStackMap)
           :use ((:instance forward-to-next-inst-get-inst-if-pc-wff-merged-code
                            (mergedcode (list* mergedcode1 mergedcode))
                            (pc (next-pc mergedcode)))
                 (:instance is-suffix-pc-wff-mergecode1
                            (mergedcode1 (list* mergedcode1 mergedcode))
                            (mergedcode (allinstructions env))
                            (pc 0)))))
  :rule-classes :forward-chaining)



;----------------------------------------------------------------------

(encapsulate () 
 (local (include-book "bcv-collect-sig-frame-vector-never-aftergoto"))
 (defthm collect-sig-frame-vector-never-aftergoto
   (not (equal (searchstackframe 
                any 
                (stack-map-wrap (collect-sig-frame-vector any-env any-code
                                                          any-init-frame)))
               'aftergoto))))

;----------------------------------------------------------------------
;----------------------------------------------------------------------


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
            (NEXT-STACKFRAME mergedcode)))))



;;; Sat Dec 31 02:19:30 2005

;----------------------------------------------------------------------

;; Subgoal *1/5'
;; (IMPLIES
;;  (AND
;;   (CONSP MERGEDCODE)
;;   (CONSP (CDR MERGEDCODE))
;;   (ISINSTRUCTION (CAR MERGEDCODE))
;;   (NOT (ISSTACKMAP (CADR MERGEDCODE)))
;;   (NOT (ISINSTRUCTION (CADR MERGEDCODE)))
;;   (MERGEDCODEISTYPESAFE ENV (ALLINSTRUCTIONS ENV)
;;                         INIT-FRAME)
;;   (EQUAL
;;      STACKFRAME
;;      (SEARCHSTACKFRAME
;;           (NEXT-PC MERGEDCODE)
;;           (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV (ALLINSTRUCTIONS ENV)
;;                                                     INIT-FRAME))))
;;   (MERGEDCODEISTYPESAFE ENV MERGEDCODE STACKFRAME)
;;   (PC-WFF-MERGEDCODE1 0 (ALLINSTRUCTIONS ENV))
;;   (IS-SUFFIX MERGEDCODE (ALLINSTRUCTIONS ENV)))
;;  (BCV-SIMPLE-METHOD1 (EXTRACT-CODE MERGEDCODE)
;;                      (COLLECT-SIG-FRAME-VECTOR ENV (ALLINSTRUCTIONS ENV)
;;                                                INIT-FRAME)
;;                      ENV)).

(defthm extract-code-forward-next-inst-reduce
  (implies (wff-merged-code-weak mergedcode)
           (equal (EXTRACT-CODE (FORWARD-TO-NEXT-INST MERGEDCODE))
                  (extract-code mergedcode)))
  :hints (("Goal" :in-theory (enable forward-to-next-inst))))

;; (i-am-here) ;; Sun Jan  1 15:50:54 2006
;----------------------------------------------------------------------


(encapsulate () 
  (local (include-book "bcv-searchStackFrame-reduce"))
   (defthm mergecodeIsTypeSafe-implies-collect-sig-vector-compatible-1
    (implies (and (mergedcodeIsTypeSafe env mergecode stackframe)
                  (member inst mergecode)
                  (isInstruction inst)
                  (isInstruction (next-inst inst mergecode))
                  (pc-wff-mergedcode1 (next-pc mergecode) mergecode))
             (equal (car (sig-do-inst inst
                                      env
                                      (searchStackFrame (instroffset inst)
                                                        (stack-map-wrap
                                                         (collect-sig-frame-vector
                                                          env mergecode
                                                          stackframe)))))
                    (searchStackFrame (instroffset (next-inst inst mergecode))
                                      (stack-map-wrap (collect-sig-frame-vector
                                                       env mergecode
                                                       stackframe)))))))

;----------------------------------------------------------------------
;;(i-am-here) ;; Sun Jan  1 23:22:11 2006

;;(i-am-here)

(defthm typelist-assignable-reflexive
  (TYPELISTASSIGNABLE x x  ENV))


(defthm frameisassignable-reflexive
   (FRAMEISASSIGNABLE frame frame env))

;;(i-am-here) ;; Sun Jan  1 18:22:32 2006

(encapsulate () 
   (local (include-book "bcv-sig-do-produce-compatible-next-state"))
   (defthm frameIsAssignable-transitive-specific
     (implies  (and (FRAMEISASSIGNABLE
                  (CAR
                   (SIG-DO-INST
                      MERGEDCODE1 ENV
                      (SEARCHSTACKFRAME
                       (INSTROFFSET MERGEDCODE1)
                       (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV (ALLINSTRUCTIONS ENV)
                                                                 INIT-FRAME)))))
                  (MAPFRAME (GETMAP MERGEDCODE3))
                  ENV)
                 (isStackMap mergedcode3)
                 (equal (mapOffset (getMap mergedcode3)) npc)
                 (member mergedcode3 (allinstructions env))
                 (pc-wff-mergedcode1 0 (allinstructions env))
                 (mergedcodeIsTypesafe env (allinstructions env) init-frame)
                 (GOOD-FRAME
                  (SEARCHSTACKFRAME
                   (MAPOFFSET (GETMAP MERGEDCODE3))
                   (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV (ALLINSTRUCTIONS ENV)
                                                             INIT-FRAME)))
                  ENV)
                  (good-frame  (SEARCHSTACKFRAME
                                (INSTROFFSET MERGEDCODE1)
                                (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV (ALLINSTRUCTIONS ENV)
                                                                          INIT-FRAME)))
                               env)
                 (all-good-frames (extract-frames (allinstructions env)) env)
                 (good-env env))
             (FRAMEISASSIGNABLE
              (CAR
               (SIG-DO-INST
                MERGEDCODE1 ENV
                (SEARCHSTACKFRAME
                 (INSTROFFSET MERGEDCODE1)
                 (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV (ALLINSTRUCTIONS ENV)
                                                           INIT-FRAME)))))
              (SEARCHSTACKFRAME
                npc
               (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV (ALLINSTRUCTIONS ENV)
                                                         INIT-FRAME)))
              env))))

;----------------------------------------------------------------------
;----------------------------------------------------------------------



(encapsulate () 
  (local (include-book "bcv-is-suffix-facts"))

  (defthm is-suffix-pc-equal
   (implies (and (IS-SUFFIX (LIST* MERGEDCODE1 mergedcode4) mergedcode)
                 (isStackMap mergedcode1)
                 (pc-wff-mergedcode1 pc mergedcode))
            (equal (instrOffset (car (extract-code mergedcode4)))
                   (mapOffset (getMap mergedcode1)))))


                          
 (defthm is-suffix-extract-code-is-code
   (implies (and (IS-SUFFIX (LIST* MERGEDCODE1 mergedcode4) mergedcode)
                 (isStackMap mergedcode1)
                 (pc-wff-mergedcode1 pc mergedcode))
            (isInstruction (car (extract-code mergedcode4))))
   :rule-classes :forward-chaining))


;----------------------------------------------------------------------

;; (i-am-here) ;; Mon Jan  2 19:49:18 2006

(encapsulate ()  
  (local (include-book "bcv-collected-frames-are-good-frames"))
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
                        env)))

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
                         env))))

;----------------------------------------------------------------------

(defthm is-suffix-implies-member-code
  (implies (and (is-suffix mergedcode1 mergedcode)
                (member x mergedcode1))
           (member x mergedcode))
  :hints (("Goal" :in-theory (disable isInstruction
                                      isStackMap
                                      isEnd))))
                                    
(defthm member-extract-code-member
  (implies (member x (extract-code mergedcode))
           (member x mergedcode))
  :rule-classes :forward-chaining)

  

(defthm forward-to-next-inst-reduce 
   (implies (isStackMap mergedcode1)
            (equal (FORWARD-TO-NEXT-INST (CONS MERGEDCODE1 MERGEDCODE2))
                   (forward-to-next-inst mergedcode2)))
   :hints (("Goal" :in-theory (disable isInstruction 
                                       isStackMap)
            :expand (FORWARD-TO-NEXT-INST (CONS MERGEDCODE1 MERGEDCODE2)))))



(defthm extract-code-forward-to-next
  (implies (wff-merged-code-weak mergedcode)
           (equal (EXTRACT-CODE (FORWARD-TO-NEXT-INST MERGEDCODE))
                  (extract-code mergedcode)))
  :hints (("Goal" :in-theory (e/d (forward-to-next-inst)
                                  (isInstruction 
                                   isStackMap
                                   isEnd)))))



(encapsulate ()
  (local (include-book "bcv-next-inst-is"))
  (defthm is-suffix-implies-next-inst-specific
    (implies  (and (IS-SUFFIX mergedcode (allinstructions env))
                   (pc-wff-mergedcode1 0 (allinstructions env))
                   (consp mergedcode)
                   (consp (cdr mergedcode))
                   (isInstruction (car mergedcode)))
              (equal (next-inst (car mergedcode) (allinstructions env))
                     (cadr mergedcode)))
    :hints (("Goal" :do-not '(generalize)))))

;----------------------------------------------------------------------


(defthm pc-wff-mergedcode1-pc-wff-mergedcode-pc-specific
  (implies (and (pc-wff-mergedcode1 0 (allinstructions env))
                (consp (allinstructions env))
                (not (isEnd (car (allinstructions env)))))
           (pc-wff-mergedcode1 (next-pc (allinstructions env))
                               (allinstructions env)))
  :hints (("Goal" :in-theory (disable isInstruction
                                      isStackMap
                                      isEnd))))
                                      



(defthm is-suffix-consp-consp
  (implies (and (is-suffix mergedcode1 mergedcode)
                (consp mergedcode1))
           (consp mergedcode))
  :rule-classes :forward-chaining)



(defthm is-suffix-not-end-not-end
  (implies (and (is-suffix mergedcode1 mergedcode)
                (wff-merged-code-weak mergedcode)
                (consp mergedcode1)
                (not (isEnd (car mergedcode1))))
           (not (isEnd (car mergedcode))))
  :rule-classes :forward-chaining)

;;(in-theory (disable forward-to-next-inst-reduce ))


(defthm is-suffix-wff-mergecode-weak
  (implies (and (is-suffix mergedcode1 mergedcode)
                (consp mergedcode1)
                (wff-merged-code-weak mergedcode))
           (wff-merged-code-weak mergedcode1))
  :rule-classes :forward-chaining)


;; (defthm pc-wff-mergedcode1-implies-wff-merged-code-instr
;;   (implies (pc-wff-mergedcode1 pc mergedcode)
;;            (wff-mergedcode-instr mergedcode))
;;   :hints (("Goal" :in-theory (disable isInstruction isStackMap
;;                                       isEnd
;;                                       jvm::inst-size)))
;;   :rule-classes :forward-chaining)



(defthm is-suffix-wff-merged-code-instr
  (implies (and (is-suffix (list* map mergedcode) all-mergedcode)
                (isStackMap map)
                (wff-mergedcode-instr all-mergedcode)
                (wff-merged-code-weak all-mergedcode))
           (consp (extract-code mergedcode)))
  :rule-classes :forward-chaining)



(in-theory (enable forward-to-next-inst))


(defthm is-suffix-wff-merged-code-instr-wff-merged-code-instr
  (implies (and (is-suffix mergedcode1 mergedcode2)
                (wff-mergedcode-instr mergedcode2))
           (wff-mergedcode-instr mergedcode1))
  :rule-classes :forward-chaining)

(defthm is-suffix-wff-merged-code-instr-2
  (implies (and (wff-mergedcode-instr mergedcode)
                (isStackMap (car mergedcode)))
           (isInstruction (car (forward-to-next-inst mergedcode)))))
  

(include-book "bcv-mergedcodeIsTypesafe")

;;(i-am-here) ;; Mon Jan  2 20:41:32 2006


(defthm mergedcodeIsTypeSafe-implies-bcv-simple-method1-lemma
  (implies (and (mergedcodeIsTypesafe env (allinstructions env) init-frame)
                (good-frame init-frame env)
                (equal (searchStackFrame (next-pc mergedcode)
                                         (stack-map-wrap (collect-sig-frame-vector env 
                                                                                   (allinstructions env)
                                                                                   init-frame)))
                       stackframe)
                (mergedcodeIsTypesafe env mergedcode stackframe)
                (pc-wff-mergedcode1 0 (allinstructions env))
                (is-suffix mergedcode (allinstructions env))
                (all-good-frames (extract-frames (allinstructions env)) env)
                (good-env env))
           (bcv-simple-method1 (extract-code mergedcode)
                               (collect-sig-frame-vector env 
                                                         (allinstructions env)
                                                         init-frame)
                               env))
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
           :induct (mergedcodeistypesafe-induct env init-frame
                                                mergedcode stackframe)
           :do-not '(generalize))))

;----------------------------------------------------------------------
;----------------------------------------------------------------------
;----------------------------------------------------------------------


;; (local 
;;  (defthm extract-code-no-change
;;    (implies (wff-merged-code-weak mergedcode)
;;             (equal (EXTRACT-CODE (FORWARD-TO-NEXT-INST mergedcode))
;;                    (extract-code mergedcode)))))

;; (local 
;;  (defthm is-suffix-forward-to-next-inst
;;    (IS-SUFFIX (FORWARD-TO-NEXT-INST mergedcode)
;;               mergedcode)))

(defthm mergedcodeIsTypeSafe-implies-bcv-simple-method1
  (implies (and (mergedcodeIsTypesafe env (allinstructions env) init-frame)
                (good-frame init-frame env)
                (pc-wff-mergedcode1 0 (allinstructions env))
                (all-good-frames (extract-frames (allinstructions env)) env)
                (good-env env))
           (bcv-simple-method1 (extract-code (allinstructions env))
                               (collect-sig-frame-vector env 
                                                         (allinstructions env)
                                                         init-frame)
                               env))
  :hints (("Goal" :in-theory (disable instructionIsTypeSafe
                                      instructionSatisfiesHandlers
                                      instrOffset
                                      sig-do-inst
                                      allinstructions
                                      isEnd
                                      next-pc
                                      good-frame
                                      mapFrame
                                      mergedcodeIsTypesafe
                                      getMap mapOffset
                                      frameIsAssignable
                                      isInstruction
                                      isStackMap)
           :do-not-induct t
           :use ((:instance
                  mergedcodeIsTypeSafe-implies-bcv-simple-method1-lemma
                  (mergedcode (forward-to-next-inst (allinstructions env)))
                  (stackframe (searchstackframe 
                               (next-pc (forward-to-next-inst (allinstructions env)))
                               (stack-map-wrap 
                                (collect-sig-frame-vector 
                                 env
                                 (allinstructions env)
                                 init-frame))))))
           :do-not '(generalize))))
