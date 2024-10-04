(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")


;----------------------------------------------------------------------


(encapsulate () 
  (local (include-book "bcv-isAssignable-transitive"))
  (defthm isAssignable-Transitive
    (implies (and (good-bcv-type t1 icl)
                  (good-bcv-type t2 icl)
                  (good-bcv-type t3 icl)
                  (equal (classtableEnvironment env) scl)
                  (good-icl icl)
                  (good-scl scl)
                  (icl-scl-compatible icl scl)
                  (isAssignable t1 t2 env)
                  (isAssignable t2 t3 env))
             (isAssignable t1 t3 env))
    :hints (("Goal" :in-theory (e/d () (isjavaassignable good-scl jvm::primitive-type?))
             :do-not '(generalize fertilize)))))

;; ;;;
;; ;;; transitive!!! ;;; problem with domain!! 
;; ;;;

;;(include-book "bcv-good-env-encapsulate")

; Matt K. mod: Avoid raw Lisp error in tau; see similar disable in
; BCV/bcv-isAssignable-transitive.lisp.
(local (in-theory (disable (:e tau-system))))

(defthm typelist-assignable-transitive
  (implies (and (good-env env)
                (good-typelist l1 env)
                (good-typelist l2 env)
                (good-typelist l3 env)
                (typelistassignable l1 l2 env)
                (typelistassignable l2 l3 env))
           (TYPELISTASSIGNABLE l1 l3  ENV))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isAssignable
                               good-bcv-type
                               classtableEnvironment
                               icl-scl-compatible
                               good-icl good-scl))
          ("Subgoal *1/9" :use ((:instance isAssignable-Transitive
                                           (icl (icl-witness env))
                                           (scl (classtableEnvironment env))
                                           (t1 (car l1))
                                           (t2 (car l2))
                                           (t3 (car l3)))))))




(defthm frameIsAssignable-transitive
  (implies (and (frameIsAssignable frame1 frame2 env)
                (frameIsAssignable frame2 frame3 env)
                (good-env env)
                (good-frame frame1 env)
                (good-frame frame2 env)
                (good-frame frame3 env))
           (frameIsAssignable frame1 frame3 env)))


(encapsulate () 
   (local (include-book "bcv-searchStackFrame-reduce-support"))
   (defthm collect-sig-frame-vector-collect-last-frame
     (implies (and (isStackMap frame)
                   (member frame mergedcode)
                   (pc-wff-mergedcode1 pc mergedcode)
                   (mergedcodeistypesafe env mergedcode init-frame))
              (equal (searchStackFrame (mapOffset (getMap frame))
                                       (stack-map-wrap (collect-sig-frame-vector
                                                        env mergedcode
                                                        init-frame)))
                     (next-stackframe (suffix frame mergedcode))))))


(defthm typelist-assignable-reflexive
  (TYPELISTASSIGNABLE x x  ENV))


(defthm frameisassignable-reflexive
   (FRAMEISASSIGNABLE frame frame env))


(defun never-after-goto (frames)
  (if (endp frames) t
    (and (not (equal (mapFrame (getMap (car frames))) 'aftergoto))
         (never-after-goto (cdr frames)))))


(defthm all-good-frames-extract-frames
  (implies (and (all-good-frames (extract-frames mergedcode) env)
                (consp mergedcode)
                (wff-mergedcode-instr mergedcode)
                (wff-merged-code-weak mergedcode)
                (isStackMap (car mergedcode)))
           (good-frame (next-stackframe mergedcode) env))
  :hints (("Goal" :in-theory (disable isEnd isInstruction
                                      mapFrame getMap
                                      isStackMap 
                                      good-frame))))


(defthm frameIsAssignable-Transitive-specific-x
  (implies (and (FRAMEISASSIGNABLE (MAPFRAME (GETMAP MERGEDCODE3))
                                   (NEXT-STACKFRAME MERGEDCODE4)
                                   ENV)
                (FRAMEISASSIGNABLE (MAPFRAME (GETMAP MERGEDCODE1))
                                   (MAPFRAME (GETMAP MERGEDCODE3))
                                   ENV)
              (GOOD-FRAME (MAPFRAME (GETMAP MERGEDCODE1))
                          ENV)
              (GOOD-FRAME (MAPFRAME (GETMAP MERGEDCODE3))
                          ENV)
              (consp mergedcode4)
              (wff-merged-code-weak mergedcode4)
              (wff-mergedcode-instr mergedcode4)
              (ALL-GOOD-FRAMES (EXTRACT-FRAMES MERGEDCODE4)
                               ENV)
              (good-env env)
              (isStackMap (car mergedcode4)))
         (FRAMEISASSIGNABLE (MAPFRAME (GETMAP MERGEDCODE1))
                            (NEXT-STACKFRAME MERGEDCODE4)
                            ENV))
  :hints (("Goal" :in-theory (disable frameisassignable
                                      good-frame
                                      mapframe
                                      getmap
                                      isStackMap)
           :do-not-induct t
           :use ((:instance frameisassignable-transitive
                            (frame1 (MAPFRAME (GETMAP MERGEDCODE1)))
                            (frame2 (MAPFRAME (GETMAP MERGEDCODE3)))
                            (frame3 (next-stackframe mergedcode4)))))))
                                      



(defthm mergedcodeIsTypeSafe-implies-stackmap-assignable-lemma
  (implies (and (mergedcodeIsTypeSafe env mergedcode init-frame)
                (isStackMap (car mergedcode))
                (never-after-goto (extract-frames mergedcode))
                (wff-merged-code-weak mergedcode)
                (wff-mergedcode-instr mergedcode)
                (all-good-frames (extract-frames mergedcode) env)
                (good-env env))
           (frameisassignable (mapFrame (getMap (car mergedcode)))
                              (next-stackframe mergedcode) env))
 :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               jvm::inst-size
                               ;;next-pc
                               sig-do-inst
                               isstackmap
                               makestackmap
                               allinstructions
                               isEnd
                               mapFrame
                               getMap 
                               mapOffset
                               good-frame
                               frameIsAssignable
                               isInstruction
                               isStackMap))))



(defthm pc-wff-mergedcode1-never-aftergoto-x
  (implies (pc-wff-mergedcode1 pc mergedcode)
           (never-after-goto (extract-frames mergedcode)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (disable isInstruction isEnd isStackMap
                                      jvm::inst-size))))


(defthm pc-wff-mergedcode1-pc-implies-pc-next-pc
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (not (isEnd (car mergedcode))))
           (pc-wff-mergedcode1 (next-pc mergedcode) 
                               mergedcode))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (disable isInstruction isEnd isStackMap
                                      jvm::inst-size))))


(defthm pc-wff-mergedcode1-pc-implies-pc-next-pc-specific
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (member stackmap mergedcode)
                (isStackMap stackmap))
           (pc-wff-mergedcode1 (next-pc mergedcode) 
                               mergedcode))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (disable isInstruction isEnd isStackMap
                                      jvm::inst-size))))






(defthm mergedcodeIsTypesafe-implies-stackmap-more-specific
  (implies (and (mergedcodeIsTypesafe env mergedcode init-frame)
                (pc-wff-mergedcode1 (next-pc mergedcode) mergedcode)
                (member stackmap mergedcode)
                (isStackmap stackmap)
                (all-good-frames (extract-frames mergedcode) env)
                (good-env env))
           (frameisassignable (mapFrame (getMap stackmap))
                              (next-stackframe (suffix stackmap mergedcode))
                              env))
 :hints (("Goal" :do-not '(generalize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               jvm::inst-size
                               good-frame
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
;;; appears that lemma are not necessary!! once we manage to prove 
;;;
;;; mergedcodeIsTypeSafe-implies-stackmap-assignable-lemma
;;;
;;;


;; (encapsulate () 
;;   (local (include-book "bcv-searchStackFrame-reduce-support"))
;;   (defthm collect-sig-frame-vector-collect-last-frame
;;     (implies (and (isStackMap frame)
;;                 (member frame mergedcode)
;;                 (pc-wff-mergedcode1 pc mergedcode)
;;                 (mergedcodeistypesafe env mergedcode init-frame))
;;            (equal (searchStackFrame (mapOffset (getMap frame))
;;                                     (stack-map-wrap (collect-sig-frame-vector
;;                                                      env mergedcode
;;                                                      init-frame)))
;;                   (next-stackframe (suffix frame mergedcode))))))



(defthm mergedcodeIsTypesafe-implies-stackmap-searchStackFrame
  (implies (and (mergedcodeIsTypesafe env mergedcode init-frame)
                (member stackmap mergedcode)
                (pc-wff-mergedcode1 pc mergedcode)
                (member stackmap mergedcode)
                (isStackmap stackmap)
                (all-good-frames (extract-frames mergedcode) env)
                (good-env env))
           (frameisassignable (mapFrame (getMap stackmap))
                              (searchStackFrame 
                                (mapOffset (getMap stackmap))
                                (stack-map-wrap 
                                 (collect-sig-frame-vector env mergedcode
                                                           init-frame)))
                              env))
  :hints (("Goal" :in-theory (disable searchStackFrame 
                                      mapOffset getMap
                                      mapFrame
                                      next-pc
                                      mergedcodeIsTypesafe
                                      pc-wff-mergedcode1
                                      collect-sig-frame-vector
                                      jvm::inst-size
                                      isStackmap good-frame
                                      frameisassignable)
           :restrict ((collect-sig-frame-vector-collect-last-frame
                       ((pc pc)))
                      (mergedcodeIsTypesafe-implies-stackmap-more-specific
                       ((init-frame init-frame))))
           :do-not-induct t)))



(defthm member-good-frames
  (implies (and (member x frames)
                (all-good-frames frames env))
           (good-frame (mapFrame (getMap x)) env))
  :hints (("Goal" :in-theory (disable good-frame)))
  :rule-classes :forward-chaining)


(defthm member-good-frames-b
  (implies (and (member x frames)
                (all-good-frames frames env))
           (good-frame (mapFrame (getMap x)) env))
  :hints (("Goal" :in-theory (disable good-frame))))

(defthm isStackmap-member-extract-frames
  (implies (and (isStackmap frame)
                (member frame mergedcode)
                (wff-merged-code-weak mergedcode))
           (member frame (extract-frames mergedcode))))



(defthm isStackmap-good-frame-specific
  (implies (and (member x (allinstructions env))
                (pc-wff-mergedcode1 0 (allinstructions env))
                (isStackmap x)
                (all-good-frames (extract-frames (allinstructions env)) env))
           (good-frame (mapFrame (getMap x)) env))
  :hints (("Goal" :in-theory (disable good-frame mapFrame getMap
                                      isStackmap allinstructions)
           :restrict ((member-good-frames-b
                       ((frames (extract-frames (allinstructions env)))))))))



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
              env))
  :hints (("Goal" :restrict ((frameisassignable-transitive
                              ((frame2 (MAPFRAME (GETMAP MERGEDCODE3)))
                               (frame1 (CAR
                                        (SIG-DO-INST
                                         MERGEDCODE1 ENV
                                         (SEARCHSTACKFRAME
                                          (INSTROFFSET MERGEDCODE1)
                                          (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV (ALLINSTRUCTIONS ENV)
                                                                                    INIT-FRAME))))))))
                             (mergedcodeIsTypesafe-implies-stackmap-searchStackFrame
                              ((init-frame init-frame)
                               (pc 0))))
           :do-not-induct t
           :in-theory (disable instructionIsTypeSafe
                               collect-sig-frame-vector-collect-last-frame
                               instructionSatisfiesHandlers
                               pc-wff-mergedcode1
                               good-frame
                               mergedcodeIsTypesafe
                               mergedcodeIsTypesafe-implies-stackmap-more-specific
                               instrOffset
                               sig-do-inst
                               allinstructions
                               isEnd
                               mapFrame
                               getMap mapOffset
                               frameIsAssignable
                               isInstruction
                               isStackMap))))



