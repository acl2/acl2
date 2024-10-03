(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "../M6-DJVM-shared/jvm-bytecode")


(include-book "bcv-base")

;; we prove a few result. 
;;
;; 1. ordered pc! 
;;

;;
;; 2. if instruction are strictly increasing 
;;     as a lemma it is not equal
;;

;----------------------------------------------------------------------

(local (in-theory (disable jvm::inst-size 
                           isStackMap
                           isEnd
                           instrOffset
                           mapOffset
                           getMap
                           isInstruction)))


;----------------------------------------------------------------------


;----------------------------------------------------------------------


;----------------------------------------------------------------------

(local 
(encapsulate () 

(defthm is-suffix-member-extract-code
   (implies (and (is-suffix mergedcode1 mergedcode)
                 (wff-merged-code-weak mergedcode)
                 (member inst (extract-code mergedcode1)))
            (member inst (extract-code mergedcode))))



(defthm pc-wff-mergedcode1-offset-lemma-2
   (implies (and (pc-wff-mergedcode1 pc mergedcode)
                 (member x (extract-pc mergedcode)))
            (<= pc x)))



(defthm pc-wff-mergedcode1-any
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (consp mergedcode)
                (not (isEnd (car mergedcode)))
                (<= 0 pc))
           (PC-WFF-MERGEDCODE1 (next-pc MERGEDCODE)
                               MERGEDCODE))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (enable getMap mapOffset))))


(defthm pc-wff-mergedcode1-is-suffix
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (wff-merged-code-weak mergedcode1)
                (is-suffix mergedcode1 mergedcode)
                (consp mergedcode1)
                (not (isEnd (car mergedcode1))))
           (pc-wff-mergedcode1 (next-pc mergedcode1)
                               mergedcode1))
  :hints (("Goal" :do-not '(generalize))))


(defthm pc-wff-mergedcode1-is-suffix-specific
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (wff-merged-code-weak mergedcode1)
                (is-suffix (cons instr mergedcode1) mergedcode)
                (isInstruction instr))
           (pc-wff-mergedcode1 (+ (instrOffset instr)
                                  (jvm::inst-size instr))
                               mergedcode1))
  :hints (("Goal" :do-not '(generalize)
           :use ((:instance pc-wff-mergedcode1-is-suffix
                            (mergedcode1 (cons instr mergedcode1)))))))
           

(defthm pc-wff-mergedcode1-jvm-size-greater
  (implies (and (member instr  mergedcode)
                (isInstruction instr)
                (pc-wff-mergedcode1 pc mergedcode))
           (<= 1 (jvm::inst-size instr))))

           

(defthm is-suffix-member
  (implies (IS-SUFFIX (cons instr mergedcode1)
                      MERGEDCODE)
           (member instr mergedcode)))



(defthm member-extract-inst-member-extract-pc
  (implies (member inst (extract-code mergedcode))
           (member (instrOffset inst)
                   (extract-pc mergedcode))))

))


;----------------------------------------------------------------------


(defthm wff-merged-code-weak-is-suffix
  (implies (and (is-suffix mergedcode1 mergedcode)
                (consp mergedcode1)
                (wff-merged-code-weak mergedcode))
           (wff-merged-code-weak mergedcode1))
  :rule-classes :forward-chaining)



(defthm pc-wff-mergedcode1-is-suffix
  (implies (and (pc-wff-mergedcode1 pc mergedcode)
                (wff-merged-code-weak mergedcode1)
                (is-suffix mergedcode1 mergedcode)
                (consp mergedcode1)
                (not (isEnd (car mergedcode1))))
           (pc-wff-mergedcode1 (next-pc mergedcode1)
                               mergedcode1))
  :hints (("Goal" :do-not '(generalize))))
           

;----------------------------------------------------------------------


(defthm pc-wff-mergedcode1-offset-greater
  (implies (and (IS-SUFFIX (CONS instr1 mergedcode1)
                           mergedcode)
                (isInstruction instr1)
                (pc-wff-mergedcode1 0 mergedcode)
                (member instr2 (extract-code mergedcode1)))
           (< (instrOffset instr1)
              (instrOffset instr2)))
  :hints (("Goal" 
           :in-theory (disable pc-wff-mergedcode1-offset-lemma-2
                               pc-wff-mergedcode1-is-suffix-specific
                               wff-merged-code-weak-is-suffix
                               pc-wff-mergedcode1-jvm-size-greater)
           :use ((:instance pc-wff-mergedcode1-offset-lemma-2
                                   (pc (+ (instrOffset instr1)
                                          (jvm::inst-size instr1)))
                                   (x (instrOffset instr2))
                                   (mergedcode mergedcode1))
                        (:instance pc-wff-mergedcode1-is-suffix-specific
                                   (pc 0)
                                   (instr instr1))
                        (:instance wff-merged-code-weak-is-suffix
                                   (mergedcode1 (cons instr1 mergedcode1)))
                        (:instance pc-wff-mergedcode1-jvm-size-greater
                                   (instr instr1)
                                   (pc 0))
                        (:instance is-suffix-member
                                   (instr instr1)))
           :do-not-induct t)))

;----------------------------------------------------------------------


(defthm pc-wff-mergedcode1-offset-specific
  (implies (and (IS-SUFFIX (CONS instr1 mergedcode1)
                           mergedcode)
                (isInstruction instr1)
                (pc-wff-mergedcode1 0 mergedcode)
                (member instr2 (extract-code mergedcode1)))
           (not (equal  (instrOffset instr1)
                        (instrOffset instr2))))
  :hints (("Goal" :use ((:instance pc-wff-mergedcode1-offset-greater)))))

;----------------------------------------------------------------------

(defthm is-suffix-member-f
  (implies (IS-SUFFIX (cons instr mergedcode1)
                      MERGEDCODE)
           (member instr mergedcode))
  :rule-classes :forward-chaining)


