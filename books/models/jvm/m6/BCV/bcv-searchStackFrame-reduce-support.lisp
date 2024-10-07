(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")

;----------------------------------------------------------------------


(defthm collect-sig-frame-vector-is-suffix
  (implies (and (is-suffix mergedcode1 mergedcode)
                (mergedcodeistypesafe env mergedcode init-frame))
           (is-suffix (collect-sig-frame-vector env mergedcode1 
                                                (collect-sig-frame-at-mergecode1
                                                 env
                                                 mergedcode1
                                                 mergedcode
                                                 init-frame))
                      (collect-sig-frame-vector env mergedcode init-frame)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               jvm::inst-size
                               next-pc
                               sig-do-inst
                               isstackmap
                               makestackmap
                               allinstructions
                               isEnd
                               mapFrame
                               getMap 
                               mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))

;----------------------------------------------------------------------



;;;
;;; Thu Dec 29 22:29:44 2005
;;;
                                            


(encapsulate () 
 (local (include-book "bcv-collected-frames-are-strictly-ordered"))
 (defthm collect-sig-frame-vector-return-ordered-list
   (implies (pc-wff-mergedcode1 (next-pc mergedcode) mergedcode)
            (strictly-ordered (extract-frame-pc 
                               (collect-sig-frame-vector env
                                                         mergedcode init-frame))))))




;----------------------------------------------------------------------
;----------------------------------------------------------------------


(defthm sig-do-inst-reduce-to-collect-sig-frame-at-mergecode1
  (implies (and (mergedcodeistypesafe env mergedcode init-frame)
                (isInstruction (car mergedcode)))
           (equal (car (sig-do-inst (car mergedcode) env init-frame))
                  (collect-sig-frame-at-mergecode1 env (cdr mergedcode)
                                                   mergedcode
                                                   init-frame)))
    :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               jvm::inst-size
                               next-pc
                               sig-do-inst
                               isstackmap
                               makestackmap
                               allinstructions
                               isEnd
                               mapFrame
                               getMap 
                               mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))

(local (in-theory (disable collect-sig-frame-at-mergecode1)))

;----------------------------------------------------------------------

(encapsulate () 
  (local (include-book "bcv-searchStackFrame-only-suffix-matters"))
  (defthm searchStackFrame-reduce
  (implies (and (is-suffix stack-maps1 stack-maps)
                (consp stack-maps1)
                (strictly-ordered (extract-frame-pc stack-maps))
                (<= (mapOffset (car stack-maps1)) pc))
           (equal (searchStackFrame pc (stack-map-wrap stack-maps1))
                  (searchStackFrame pc (stack-map-wrap stack-maps))))))
                              
                            
;----------------------------------------------------------------------

;; (i-am-here)

(encapsulate () 
  (local (include-book "bcv-collect-sig-frame-vector-misc"))

  (defthm mergedcodeistypesafe-implies-not-end-consp
    (implies (and (mergedcodeistypesafe env mergedcode init-frame)
                  (consp mergedcode)
                  (pc-wff-mergedcode1 pc mergedcode)
                  (not (isEnd (car mergedcode))))
             (consp (collect-sig-frame-vector env mergedcode init-frame))))
  
  (defthm mergedcodeistypesafe-mergedcodeistype-safe
    (implies (and (mergedcodeistypesafe env mergedcode init-frame)
                  (consp mergedcode1)
                  (is-suffix mergedcode1 mergedcode))
             (mergedcodeistypesafe env mergedcode1 
                                   (collect-sig-frame-at-mergecode1 
                                    env mergedcode1 mergedcode init-frame))))

  (defthm mapOffset-is-next-pc
    (implies (and (mergedcodeistypesafe env mergedcode init-frame)
                  (pc-wff-mergedcode1 (next-pc mergedcode) mergedcode))
             (equal (mapOffset (car (collect-sig-frame-vector env mergedcode
                                                              init-frame)))
                    (next-pc mergedcode))))

  (defthm pc-wff-mergedcode1-pc-wff-mergedcode-pc-suffix
    (implies (and (pc-wff-mergedcode1 (next-pc mergedcode) mergedcode)
                  (is-suffix mergedcode1 mergedcode)
                  (consp mergedcode1)
                  (not (isEnd (car mergedcode1))))
             (pc-wff-mergedcode1 (next-pc mergedcode1) mergedcode1))
    :rule-classes :forward-chaining))


(defthm searchStackFrame-reduce-specific
  (implies (and (is-suffix mergedcode1 mergedcode)
                (consp mergedcode1)
                (pc-wff-mergedcode1 (next-pc mergedcode) mergedcode)
                (not (isEnd (car mergedcode1)))
                (mergedcodeistypesafe env mergedcode init-frame)
                (<= (next-pc mergedcode1) pc))
           (equal (searchStackFrame pc (stack-map-wrap 
                                        (collect-sig-frame-vector 
                                         env mergedcode1 
                                         (collect-sig-frame-at-mergecode1 
                                          env mergedcode1 mergedcode init-frame))))
                  (searchStackFrame pc (stack-map-wrap 
                                        (collect-sig-frame-vector
                                         env mergedcode init-frame)))))
  :hints (("Goal" :in-theory (disable collect-sig-frame-vector
                                      mapOffset instrOffset next-pc
                                      mergedcodeistypesafe
                                      searchStackFrame-reduce
                                      isstackmapframe isstackmap isInstruction isEnd
                                      collect-sig-frame-at-mergecode1
                                      InstructionIsTypeSafe
                                      sig-do-inst
                                      jvm::inst-size
                                      is-suffix)
           :do-not-induct t
           :use ((:instance searchStackFrame-reduce
                            (stack-maps (collect-sig-frame-vector
                                         env mergedcode init-frame))
                            (stack-maps1 (collect-sig-frame-vector 
                                          env mergedcode1 
                                          (collect-sig-frame-at-mergecode1 
                                           env mergedcode1 mergedcode
                                           init-frame))))))))
                            

;----------------------------------------------------------------------
;; (i-am-here) ;;Sat Dec 31 02:02:14 2005

(defthm member-frame-ordered
  (implies (and (ordered (extract-pc mergedcode))
                (wff-merged-code-weak mergedcode)
                (isStackMap frame)
                (member frame (cdr mergedcode)))
           (<= (next-pc mergedcode)
               (mapOffset (getMap frame))))
    :hints (("Goal" :do-not '(generalize)
             :in-theory (disable 
                         mapOffset instrOffset
                         isstackmapframe isstackmap isInstruction isEnd
                         jvm::inst-size))))

;;;; Fri Dec 30 15:00:58 2005
;;;;; Fri Dec 30 17:54:07 2005


;; (defun wff-stack-map-offset (mergecode)
;;   (if (endp mergecode) t
;;     (if (isStackMap (car mergecode))
;;         (and (not (endp (cdr mergecode)))
;;              (equal (next-pc (cdr mergecode))
;;                     (mapoffset (getMap (car mergecode))))
;;              (wff-stack-map-offset (cdr mergecode)))
;;       (wff-stack-map-offset (cdr mergecode)))))



(defthm collect-sig-frame-vector-reduce
  (implies (and (isInstruction (car mergedcode4))
                (mergedcodeIsTypeSafe env mergedcode4 frame))
           (equal 
            (car (COLLECT-SIG-FRAME-VECTOR ENV MERGEDCODE4 frame))
            (list (instrOffset (car mergedcode4))
                  frame)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               jvm::inst-size
                               next-pc
                               sig-do-inst
                               isstackmap
                               makestackmap
                               allinstructions
                               isEnd
                               mapFrame
                               getMap 
                               mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))



(defthm searchstackframe-reduce-2
  (implies (and (isInstruction (car mergedcode4))
                (mergedcodeIsTypeSafe env mergedcode4 frame)
                (equal (next-pc mergedcode4) pc))
           (equal 
            (searchstackframe pc 
                              (stack-map-wrap (COLLECT-SIG-FRAME-VECTOR ENV MERGEDCODE4 frame)))
            frame))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               jvm::inst-size
                               next-pc
                               sig-do-inst
                               isstackmap
                               makestackmap
                               allinstructions
                               isEnd
                               mapFrame
                               getMap 
                               mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))




(defthm collect-sig-frame-vector-reduce-2
  (implies (and (isStackMap (car mergedcode4))
                (wff-mergedcode-instr mergedcode4)
                (wff-stack-map-offset mergedcode4)
                (mergedcodeIsTypeSafe env mergedcode4 frame))
           (equal 
            (car (COLLECT-SIG-FRAME-VECTOR ENV MERGEDCODE4 frame))
            (list (mapOffset (getMap (car mergedcode4)))
                  (next-stackframe mergedcode4))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               jvm::inst-size
                               next-pc
                               sig-do-inst
                               isstackmap
                               makestackmap
                               allinstructions
                               isEnd
                               mapFrame
                               getMap 
                               mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))


(defthm searchstackframe-reduce-3
  (implies (and (isStackMap (car mergedcode4))
                (wff-mergedcode-instr mergedcode4)
                (wff-stack-map-offset mergedcode4)
                (mergedcodeIsTypeSafe env mergedcode4 frame)
                (equal (next-pc mergedcode4) pc))
           (equal 
            (searchstackframe pc 
                              (stack-map-wrap (COLLECT-SIG-FRAME-VECTOR ENV MERGEDCODE4 frame)))
            (next-stackframe mergedcode4)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               jvm::inst-size
                               next-pc
                               sig-do-inst
                               isstackmap
                               makestackmap
                               allinstructions
                               isEnd
                               mapFrame
                               getMap 
                               mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))


(defthm searchstackframe-reduce-4
  (implies (and (not (isInstruction (car mergedcode4)))
                (wff-mergedcode-instr mergedcode4)
                (extract-code mergedcode4)
                (wff-stack-map-offset mergedcode4)
                (wff-merged-code-weak mergedcode4)
                (mergedcodeIsTypeSafe env mergedcode4 frame)
                (equal (next-pc mergedcode4) pc))
           (equal 
            (searchstackframe pc 
                              (stack-map-wrap (COLLECT-SIG-FRAME-VECTOR ENV MERGEDCODE4 frame)))
            (next-stackframe mergedcode4)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               jvm::inst-size
                               next-pc
                               sig-do-inst
                               isstackmap
                               makestackmap
                               allinstructions
                               isEnd
                               mapFrame
                               getMap 
                               mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))


(defthm wff-mergedcode-offset-tr-implies-consp-extract-pc
  (implies (and (MEMBER FRAME MERGEDCODE2)
                (wff-stack-map-offset mergedcode2)
                (wff-merged-code-weak mergedcode2)
                (ISSTACKMAP FRAME))
           (CONSP (EXTRACT-PC MERGEDCODE2)))
  :hints (("Goal" :in-theory (disable isstackmap
                                      isInstruction
                                      mapOffset
                                      instrOffset
                                      isEnd))))
                


;; (skip-proofs 
;;  (defthm wff-stack-map-offset-2-implies-not-equal-frame
;;    (implies (and (wff-stack-map-offset-2 mergedcode)
;;                  (member frame (cdr mergedcode))                
;;                  (isInstruction (car mergedcode))
;;                  (ordered (extract-pc mergedcode))
;;                  (consp mergedcode)
;;                  (consp (cdr mergedcode))
;;                  (not (isEnd (cadr mergedcode))))
;;             (not (equal (instrOffset (car mergedcode))
;;                         (mapOffset frame))))
;;    :rule-classes :forward-chaining))
                
            
(defthm ordered-implies-less-not-equal
  (implies (and (< pc (car (extract-pc mergedcode)))
                (ordered (extract-pc mergedcode))
                (isstackmap frame)
                (wff-merged-code-weak mergedcode)
                (member frame mergedcode)
                (< pc (car (extract-pc mergedcode))))
           (< pc (mapOffset (getMap frame))))
  :hints (("Goal" :in-theory (disable mapOffset 
                                      getMap
                                      isEnd
                                      instrOffset
                                      isInstruction
                                      isstackmap)))
  :rule-classes :forward-chaining)

;; (skip-proofs 
;;  (defthm member-frame-ordered
;;    (implies (and (ordered (extract-pc mergedcode))
;;                  (isStackMap frame)
;;                  (member frame (cdr mergedcode)))
;;             (<= (next-pc mergedcode)
;;                 (mapOffset (getMap frame))))))

(defthm collect-sig-frame-vector-collect-last-frame-lemma
  (implies (and (isStackMap frame)
                (member frame mergedcode)
                (ordered (extract-pc mergedcode))
                (wff-stack-map-offset mergedcode)
                (wff-stack-map-offset-2 mergedcode)
                (wff-merged-code-weak mergedcode)
                (wff-mergedcode-instr mergedcode)
                (mergedcodeistypesafe env mergedcode init-frame))
           (equal (searchStackFrame (mapOffset (getMap frame))
                                    (stack-map-wrap (collect-sig-frame-vector
                                                     env mergedcode
                                                     init-frame)))
                  (next-stackframe (suffix frame mergedcode))))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               jvm::inst-size
                               next-pc
                               sig-do-inst
                               isstackmap
                               makestackmap
                               allinstructions
                               isEnd
                               mapFrame
                               getMap 
                               mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))

;;;
;;; if we query the collected vector, we get the next stackframe right before
;;; the next instruction
;;;

                  
                  
(defthm pc-wff-mergedcode1-implies-wff-stack-map-offset
  (implies (pc-wff-mergedcode1 pc mergedcode)
           (wff-stack-map-offset mergedcode))
  :hints (("Goal" :in-theory (disable isInstruction isStackMap
                                      isEnd
                                      jvm::inst-size)))
  :rule-classes :forward-chaining)


                  
(defthm pc-wff-mergedcode1-implies-wff-merged-code-instr
  (implies (pc-wff-mergedcode1 pc mergedcode)
           (wff-mergedcode-instr mergedcode))
  :hints (("Goal" :in-theory (disable isInstruction isStackMap
                                      isEnd
                                      jvm::inst-size)))
  :rule-classes :forward-chaining)

           

(defthm pc-wff-mergedcode1-implies-ordered-extract-pc
  (implies (pc-wff-mergedcode1 pc mergedcode)
           (ordered (extract-pc mergedcode)))
  :hints (("Goal" :in-theory (disable isInstruction isStackMap
                                      isEnd
                                      jvm::inst-size)
           :do-not '(generalize)))
  :rule-classes :forward-chaining)


(defthm pc-wff-mergedcode1-implies-wff-stack-map-offset-2
  (implies (pc-wff-mergedcode1 pc mergedcode)
           (wff-stack-map-offset-2 mergedcode))
  :hints (("Goal" :in-theory (disable isInstruction isStackMap
                                      isEnd
                                      jvm::inst-size)
           :do-not '(generalize)))
  :rule-classes :forward-chaining)


(defthm collect-sig-frame-vector-collect-last-frame
  (implies (and (isStackMap frame)
                (member frame mergedcode)
                (pc-wff-mergedcode1 pc mergedcode)
                (mergedcodeistypesafe env mergedcode init-frame))
           (equal (searchStackFrame (mapOffset (getMap frame))
                                    (stack-map-wrap (collect-sig-frame-vector
                                                     env mergedcode
                                                     init-frame)))
                  (next-stackframe (suffix frame mergedcode))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               jvm::inst-size
                               next-pc
                               sig-do-inst
                               isstackmap
                               makestackmap
                               allinstructions
                               isEnd
                               mapFrame
                               getMap 
                               mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))

;----------------------------------------------------------------------
;----------------------------------------------------------------------

(encapsulate () 
  (local (include-book "bcv-next-stackframe-equal-suffix-suffix"))
  (defthm is-suffix-then-suffix-is
    (implies (and (is-suffix mergedcode all-merged-code)
                  (ordered (extract-pc all-merged-code))
                  (wff-stack-map-offset-2 all-merged-code)
                  (wff-merged-code-weak all-merged-code)
                  (member (car mergedcode) all-merged-code)
                  (isStackMap (car mergedcode)))
             (equal (next-stackframe (suffix (car mergedcode) all-merged-code))
                    (next-stackframe mergedcode)))))


;; Thu Dec 29 17:57:49 2005
;;
;; complication if there is duplicated entries in mergedcode
;;

(defthm is-suffix-not-nil-member
  (implies (and (is-suffix mergedcode all-merged-code)
                (consp mergedcode))
           (member (CAR MERGEDCODE)
                   ALL-MERGED-CODE))
  :rule-classes :forward-chaining)

(defthm isStackMap-car-consp
  (implies (isStackMap (car mergedcode))
           (consp mergedcode))
  :rule-classes :forward-chaining)



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

;; (i-am-here) ;; Sun Jan  1 20:22:02 2006

(defthm pc-wff-mergedcode1-isStackMap-consp-remaining-specific
  (implies 
   (AND (ISSTACKMAP MERGEDCODE1)
        (IS-SUFFIX (CONS MERGEDCODE1 MERGEDCODE2)
                   ALL-MERGED-CODE)
        (PC-WFF-MERGEDCODE1 PC ALL-MERGED-CODE))
   (consp mergedcode2))
  :hints (("Goal" :use ((:instance
                         pc-wff-mergedcode1-isStackMap-consp-remaining
                         (mergedcode (cons mergedcode1 mergedcode2))
                         (pc (next-pc (cons mergedcode1 mergedcode2))))
                        (:instance 
                         is-suffix-pc-wff-mergecode1
                         (mergedcode1 (cons mergedcode1 mergedcode2))
                         (mergedcode all-merged-code)))
           :in-theory (disable isstackmap pc-wff-mergedcode1
                               isEnd isInstruction
                               is-suffix-pc-wff-mergecode1
                               pc-wff-mergedcode1-isStackMap-consp-remaining
                               is-suffix)))
  :rule-classes :forward-chaining)


(defthm pc-wff-mergedcode1-mapOffset-equal-forward-to-next-inst
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (isstackmap (car mergedcode)))
           (equal (instrOffset (car (forward-to-next-inst mergedcode)))
                  (mapOffset (getMap (car mergedcode)))))
  :hints (("Goal" :in-theory (disable isInstruction instrOffset mapOffset
                                      isstackmap isend))))


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
            (NEXT-STACKFRAME mergedcode)))
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
                               isStackMap)
           :use ((:instance collect-sig-frame-vector-collect-last-frame
                            (frame (car mergedcode))
                            (mergedcode  all-merged-code))))))

 
