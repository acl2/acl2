(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")



(defthm extract-frame-pc-subset-extract-pc
  (implies (member pc (extract-frame-pc 
                       (collect-sig-frame-vector env mergedcode stackmap)))
           (member pc (extract-pc (extract-code mergedcode))))
  :hints (("Goal" :in-theory (disable instructionIsTypeSafe
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
;;; need a good library of is-suffix and is-subsequence 
;;;

;; (defthm ordered-implies-ordered2 
;;   (iff  (ordered l)
;;         (ordered2 l)))

(defthm subsetp-extract-code-l
  (subsetp (extract-code l) l))


(defthm member-x-member-extract-pc
  (implies (and (member x (extract-pc l1))
                (subsetp l1 l2)
                (wff-merged-code-weak l2))
           (member x (extract-pc l2))))


(defthm subsetp-cdr-subsetp
  (implies (subsetp l1 l2)
           (subsetp (cdr l1) l2)))

(defthm member-x-mermber-extract-pc
  (implies (and (member x l)
                (isInstruction x)
                (wff-merged-code-weak l))
           (member (instrOffset x) (extract-pc l)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isInstruction isStackMap
                               isEnd instrOffset
                               mapOffset))))


(defthm member-x-mermber-extract-pc-2
  (implies (and (member x l)
                (isStackMap x)
                (wff-merged-code-weak l))
           (member (mapOffset (getMap x)) (extract-pc l)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isInstruction isStackMap
                               isEnd instrOffset
                               getMap
                               mapOffset))))

(defthm subsetp-subsetp-extract-pc
  (implies (and (subsetp l1 l2)
                (wff-merged-code-weak l2))
           (subsetp (extract-pc l1) (extract-pc l2)))
  :hints (("Goal" :in-theory (disable isInstruction isStackMap
                                      isEnd instrOffset getMap
                                      mapOffset)
           :do-not '(generalize))))


(defthm all-no-less-than-subsetp
  (implies (and (all-no-less-than x s2)
                (subsetp s1 s2))
           (all-no-less-than x s1)))

(defthm all-no-less-than-all-no-less-than
  (implies (and (all-no-less-than y l)
                (< x y))
           (all-no-less-than x l)))


(defthm pc-wff-mergedcode1-all-no-less
  (implies (pc-wff-mergedcode1 pc mergedcode)
           (all-no-less-than pc (extract-pc mergedcode)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isInstruction isStackMap
                               isEnd getMap instrOffset
                               mapOffset
                               jvm::inst-size))))
;; above not necessary!! 

(defthm pc-wff-mergedcode1-ordered-pc
  (implies (pc-wff-mergedcode1 pc mergedcode)
           (ordered (extract-pc mergedcode)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isInstruction isStackMap
                                      isEnd getMap instrOffset
                                      mapOffset
                                      jvm::inst-size))))


;; (skip-proofs 
;;  (defthm pc-wff-mergedcode1-ordered-pc-2
;;    (implies (pc-wff-mergedcode1 pc mergedcode)
;;             (ordered2 (extract-pc mergedcode)))
;;    :hints (("Goal" :in-theory (disable isInstruction isStackMap
;;                                        isEnd
;;                                        jvm::inst-size)))
;;    :rule-classes :forward-chaining))

                 
                 



;; (defthm ordered-ordered-extract-code
;;   (implies (ordered2 (extract-pc l))
;;            (ordered2 (extract-pc (extract-code l))))
;;   :hints (("Goal" :in-theory (disable isInstruction isStackMap 
;;                                       instrOffset)
;;            :do-not '(generalize))))
                                      

(defthm all-strictly-less-if-less-than-first-orderred
  (implies (and (ordered l)
                (< pc (car l)))
           (all-strictly-less-than pc l)))


(defthm pc-wff-mergedcode1-isInstruction-then-next-pc-is-greater-lemma
   (implies (and (pc-wff-mergedcode1 pc mergedcode)
                 (consp mergedcode)
                (isInstruction (car mergedcode)))
           (all-strictly-less-than pc (extract-pc (cdr mergedcode))))
    :hints (("Goal" :do-not '(generalize)
             :do-not-induct t
             :use ((:instance all-strictly-less-if-less-than-first-orderred
                              (l (extract-pc (cdr mergedcode)))))
             :in-theory (disable instructionIsTypeSafe
                                 instructionSatisfiesHandlers
                                 instrOffset
                                 ;;ordered-implies-ordered2 
                                 all-strictly-less-if-less-than-first-orderred
                                 pc-wff-mergedcode1-ordered-pc
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
                                 isStackMap))
            ("Subgoal 2" :use ((:instance pc-wff-mergedcode1-ordered-pc
                                          (pc (+ (JVM::INST-SIZE (car MERGEDCODE))
                                                 (INSTROFFSET (car MERGEDCODE))))
                                          (mergedcode (cdr mergedcode)))))
            ("Subgoal 1" :expand (PC-WFF-MERGEDCODE1 (+ (JVM::INST-SIZE MERGEDCODE1)
                                                        (INSTROFFSET MERGEDCODE1))
                                                     MERGEDCODE2))))
        


(defthm all-strictly-less-than-subsetp
  (implies (and (all-strictly-less-than x s2)
                (subsetp s1 s2))
           (all-strictly-less-than x s1)))



(defthm pc-wff-mergedcode1-isInstruction-then-next-pc-is-greater
   (implies (and (pc-wff-mergedcode1 pc mergedcode)
                 (consp mergedcode)
                 (isInstruction (car mergedcode)))
           (all-strictly-less-than (instroffset (car mergedcode))
                                   (extract-pc (extract-code (cdr mergedcode)))))
    :hints (("Goal" :do-not '(generalize)
             :do-not-induct t
             :in-theory (disable instructionIsTypeSafe
                                 instructionSatisfiesHandlers
                                 instrOffset
                                 ;;ordered-implies-ordered2 
                                 all-strictly-less-if-less-than-first-orderred
                                 pc-wff-mergedcode1-ordered-pc
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
                                 isStackMap)
             :use ((:instance all-strictly-less-than-subsetp
                              (s2 (extract-pc (cdr mergedcode)))
                              (s1 (extract-pc (extract-code (cdr mergedcode))))
                              (x pc))))))


(defthm pc-wff-mergedcode1-isInstruction-then-next-pc-is-greater-specific
   (implies (and (PC-WFF-MERGEDCODE1 (+ (JVM::INST-SIZE MERGEDCODE1)
                                        (INSTROFFSET MERGEDCODE1))
                                     MERGEDCODE2)
                 (<= 1  (JVM::INST-SIZE MERGEDCODE1))
                 (isInstruction mergedcode1))
           (all-strictly-less-than (instroffset mergedcode1)
                                   (extract-pc (extract-code mergedcode2))))
    :hints (("Goal" :do-not '(generalize)
             :do-not-induct t
             :in-theory (disable instructionIsTypeSafe
                                 instructionSatisfiesHandlers
                                 instrOffset
                                 ;;ordered-implies-ordered2 
                                 all-strictly-less-if-less-than-first-orderred
                                 pc-wff-mergedcode1-ordered-pc
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
                                 isStackMap)
             :use ((:instance
                    pc-wff-mergedcode1-isInstruction-then-next-pc-is-greater
                    (pc (instrOffset mergedcode1))
                    (mergedcode (cons mergedcode1
                                      mergedcode2)))))))


(defthm subset-cons
  (implies (subsetp x l)
           (subsetp x (cons y l))))


(defthm subsetp-extract-frame-pc-subset-pc
  (subsetp (extract-frame-pc (collect-sig-frame-vector env mergedcode frame))
           (extract-pc (extract-code mergedcode)))
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


;;; no need to go through these troubles!!! 

(defthm all-strictly-less-than-subsetp-specific
  (implies (all-strictly-less-than x (extract-pc (extract-code mergedcode)))
           (all-strictly-less-than x (extract-frame-pc
                                      (collect-sig-frame-vector env mergedcode
                                                                init-frame))))
  :hints (("Goal" :in-theory (disable extract-frame-pc extract-pc extract-code
                                      all-strictly-less-than collect-sig-frame-vector))))
        

(defthm pc-wff-mergedcode1-pc-wff-merged-code1
  (implies (and (PC-WFF-MERGEDCODE1 pc MERGEDCODE2)
                (case-split (not (isEnd (car mergedcode2)))))
           (pc-wff-mergedcode1 (next-pc mergedcode2) mergedcode2))
  :hints (("Goal" :in-theory (disable isInstruction instrOffset
                                      isStackMap mapOffset
                                      jvm::inst-size
                                      isEnd)
           :do-not '(generalize))))


(defthm collect-sig-frame-vector-return-ordered-list
  (implies (pc-wff-mergedcode1 (next-pc mergedcode) mergedcode)
           (strictly-ordered (extract-frame-pc 
                              (collect-sig-frame-vector env
                                                        mergedcode init-frame))))
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
                               isStackMap)
           :induct (collect-sig-frame-vector env mergedcode init-frame))))


