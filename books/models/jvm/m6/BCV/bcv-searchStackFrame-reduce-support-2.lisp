(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")


;----------------------------------------------------------------------

(encapsulate () 
  (local (include-book "bcv-collected-frames-are-strictly-ordered"))
  (defthm pc-wff-mergedcode1-isInstruction-then-next-pc-is-greater
   (implies (and (pc-wff-mergedcode1 pc mergedcode)
                 (consp mergedcode)
                 (isInstruction (car mergedcode)))
           (all-strictly-less-than (instroffset (car mergedcode))
                                   (extract-pc (extract-code (cdr mergedcode)))))))


(defthm pc-wff-mergedcode1-strictly-ordered-extract-pc-extract-code
  (implies (pc-wff-mergedcode1 pc mergedcode)
           (strictly-ordered (extract-pc (extract-code mergedcode))))
  :hints (("Goal" :in-theory (disable isInstruction
                                      isstackmap
                                      jvm::inst-size
                                      mapOffset getMap
                                      instroffset
                                      isEnd))))

;----------------------------------------------------------------------

;----------------------------------------------------------------------

(defthm strictly-ordered-next-inst
  (implies (and (strictly-ordered (extract-pc (extract-code mergedcode)))
                (wff-merged-code-weak mergedcode)
                (member inst mergedcode)
                (isInstruction inst)
                (isInstruction (next-inst inst mergedcode)))
           (< (instroffset inst)
              (instroffset (next-inst inst mergedcode))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isInstruction
                               isstackmap
                               jvm::inst-size
                               mapOffset
                               getMap
                               instroffset
                               isEnd))))
;;;
;;; well this is proved by induction!!! 
;;;
;;; although we usually don't want to prove such things using induction
;;; directly!!
;;;

;;            :use ((:instance member-suffix-then-strictly-greater
;;                             (x (instroffset inst))
;;                             (y (instroffset (next-inst inst mergedcode)))
;;                             (l (extract-pc (extract-code mergedcode))))
;;                  (:instance
;;                   member-code-isInstruction-implies-member-extract-pc-general
;;                   (inst (next-inst inst mergedcode))
;;                   (pc-list (cdr (suffix (instroffset inst)
;;                                         (extract-pc (extract-code
;;                                                      mergedcode)))))
;;                   (mergedcode (cdr (suffix inst mergedcode))))
;;                  (:instance member-inst-implies-consp
;;                             (inst (next-inst inst mergedcode))
;;                             (mergedcode (cdr (suffix inst mergedcode)))))
;;            :do-not-induct t)))

;----------------------------------------------------------------------

;; (defthm pc-wff-mergedcode1-implies-wff-merged-code-weak
;;   (implies (pc-wff-mergedcode1 pc mergedcode)
;;           (wff-merged-code-weak mergedcode))
;;   :rule-classes :forward-chaining
;;   :hints (("Goal" :do-not '(generalize)
;;            :in-theory (disable isInstruction
;;                                isstackmap
;;                                jvm::inst-size
;;                                mapOffset
;;                                getMap
;;                                instroffset
;;                                isEnd))))
;;; in bcv-base.lisp
;;

(defthm next-inst-never-occur-before
  (implies (and (member inst mergedcode)
                (pc-wff-mergedcode1 pc mergedcode)
                (isInstruction (next-inst inst mergedcode))
                (isInstruction inst))
           (< (instroffset inst)
              (instroffset (next-inst inst mergedcode))))
  :rule-classes :linear
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isInstruction
                               isstackmap
                               jvm::inst-size
                               mapOffset
                               getMap
                               instroffset
                               isEnd))))


(defthm member-inst-pc-no-less-than
  (implies (and (member inst mergedcode)
                (pc-wff-mergedcode1 pc mergedcode)
                (isInstruction inst))
           (<= pc (instroffset inst)))
  :rule-classes :linear
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isInstruction
                               isstackmap
                               jvm::inst-size
                               mapOffset
                               getMap
                               instroffset
                               isEnd))))




(defthm member-inst-pc-no-less-than-specific
   (implies (and (member inst mergedcode)
                 (pc-wff-mergedcode1 pc mergedcode)
                 (isInstruction inst)
                 (isInstruction (next-inst inst mergedcode)))
            (< pc (instroffset (next-inst inst mergedcode))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable instroffset isInstruction
                                       pc-wff-mergedcode1
                                       next-inst member))))
           

;----------------------------------------------------------------------

;; (defthm member-del-x-member
;;   (implies (and (member x l)
;;                 (member y l)
;;                 (not (equal x y)))
;;            (member x (del y l))))


;; (defthm strictly-ordered-list-del-member
;;   (implies (strictly-ordered l)
;;            (not (member x (del x l)))))


;; (defthm member-member-pc
;;   (implies (and (member inst mergedcode)
;;                 (wff-merged-code-weak mergedcode)
;;                 (isInstruction inst))
;;            (member (instroffset inst) 
;;                    (extract-pc (extract-code mergedcode)))))

;; (defthm extract-pc-del-is-del-extract-pc
;;   (implies (and ;; (strictly-ordered (extract-pc (extract-code mergedcode)))
;;                 (unique 
;;                 (member inst mergedcode)
;;                 (isInstruction inst))
;;            (equal (extract-pc (extract-code (del inst mergedcode)))
;;                   (del (instroffset inst) (extract-pc (extract-code
;;                                                        mergedcode)))))
;;     :hints (("Goal" :do-not '(generalize)
;;            :in-theory (disable isInstruction
;;                                isstackmap
;;                                jvm::inst-size
;;                                mapOffset
;;                                getMap
;;                                instroffset
;;                                isEnd))))


           

(defthm strictly-ordered-next-inst-specific
  (implies (and (equal (instroffset inst2)
                       (instroffset inst1))
                (member inst1 mergedcode)
                (member inst2 mergedcode)
                (strictly-ordered (extract-pc (extract-code mergedcode)))
                (wff-merged-code-weak mergedcode)
                (isInstruction inst1)
                (isInstruction inst2))
           (equal inst2 inst1))
   :rule-classes :forward-chaining
   :hints (("Goal" :do-not '(generalize fertilize)
            :in-theory (disable isInstruction
                                isstackmap
                                jvm::inst-size
                                mapOffset
                                getMap
                                instroffset
                                isEnd))))


(defthm pc-wff-mergedcode1-all-greater-than
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (member inst mergedcode)
                (isInstruction inst))
           (<= pc (instroffset inst)))
  :rule-classes :linear
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (disable isInstruction
                               isstackmap
                               jvm::inst-size
                               mapOffset
                               getMap
                               instroffset
                               isEnd))))


                 
(defthm not-pc-wff-mergecode1-if-member
  (implies (and (< 0 x)
                (member inst mergedcode2)
                (isInstruction inst))
           (not (PC-WFF-MERGEDCODE1 (+ x
                                       (INSTROFFSET INST))
                                    MERGEDCODE2)))
     :hints (("Goal" :do-not '(generalize fertilize)
              :do-not-induct t
              :use ((:instance pc-wff-mergedcode1-all-greater-than
                               (pc (+ x (instroffset inst)))
                               (mergedcode mergedcode2)))
              :in-theory (disable isInstruction
                                  isstackmap
                                  jvm::inst-size
                                  mapOffset
                                  getMap
                                  instroffset
                                  isEnd))))


;----------------------------------------------------------------------
;----------------------------------------------------------------------

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
                                                     stackframe)))))
  :hints (("Goal" :do-not '(generalize fertilize)
           :in-theory (disable instructionIsTypeSafe
                               instructionSatisfiesHandlers
                               instrOffset
                               jvm::inst-size
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






