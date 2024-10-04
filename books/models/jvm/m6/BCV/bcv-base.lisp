(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "../M6-DJVM-shared/jvm-bytecode")
(include-book "bcv-functions")
(include-book "bcv-good-env-encapsulate")

(defun extract-code (mergedcode)
  (if (endp mergedcode) nil
    (cond  ((isEnd (car mergedcode)) nil)
           ((isStackMap (car mergedcode))
            (extract-code (cdr mergedcode)))
           ((isInstruction (car mergedcode))
            (cons (car mergedcode) (extract-code (cdr mergedcode))))
           (t nil))))

(defun is-suffix (mergedcode1 mergedcode)
  (if (endp mergedcode) 
      (equal mergedcode1 mergedcode)
    (or (equal mergedcode1 mergedcode)
        (is-suffix mergedcode1 (cdr mergedcode)))))


(defun pc-wff-mergedcode1 (pc mergecode)
  (if (endp mergecode) nil
    (cond ((isEnd (car mergecode)) 
           (and (integerp pc) 
                (< 0 pc)
                (equal (nth 1 (car mergecode)) pc)
                (endp (cdr mergecode))))
          ((isStackMap (car mergecode))
           (and (equal (mapOffset (getMap (car mergecode))) pc)
                (consp (cdr mergecode))
                (not (equal (mapFrame (getMap (car mergecode))) 'aftergoto))
                (not (isEnd (cadr mergecode)))
                (pc-wff-mergedcode1 pc (cdr mergecode))))
          ((isInstruction (car mergecode))
           (and (equal (instrOffset (car mergecode)) pc)
                (<= 1 (jvm::inst-size (car mergecode)))
                (pc-wff-mergedcode1 (+ (JVM::inst-size (car mergecode)) pc)
                                    (cdr mergecode))))
          (t nil))))
                    


(defun wff-merged-code-weak (mergedcode)
  (if (endp mergedcode) nil
    (if (endp (cdr mergedcode))
        (isEnd (car mergedcode))
      (and (or (isStackMap (car mergedcode))
               (isInstruction (car mergedcode)))
           (wff-merged-code-weak (cdr mergedcode))))))

(defun extract-pc (mergedcode)
  (if (endp mergedcode) nil
    (cond ((isEnd (car mergedcode)) nil)
          ((isStackMap (car mergedcode))
           (cons (mapOffset (getMap (car mergedcode)))
                 (extract-pc (cdr mergedcode))))
          ((isInstruction (car mergedcode))
           (cons (instrOffset (car mergedcode))
                 (extract-pc (cdr mergedcode))))
          (t nil))))
  





(defun all-no-less-than (x l)
  (if (endp l) t
    (and (<= x (car l))
         (all-no-less-than x (cdr l)))))

(defun ordered2 (l)
  (if (endp l) t
    (and (all-no-less-than (car l) (cdr l))
         (ordered2 (cdr l)))))
  




(defun next-pc (mergedcode)
  (cond ((isInstruction (car mergedcode)) (instrOffset (car mergedcode)))
        ((isStackMap (car mergedcode))
         (mapOffset (getMap (car mergedcode))))
        (t nil)))

;----------------------------------------------------------------------

;----------------------------------------------------------------------


(defthm is-suffix-cdr 
  (implies (and (is-suffix mergedcode1 mergedcode)
                (consp mergedcode1))
           (is-suffix (cdr mergedcode1) mergedcode)))


(defthm is-suffix-membership
  (implies (is-suffix (list* x mergedcode1) mergedcode)
           (member x mergedcode))
  :rule-classes :forward-chaining)



(defthm is-suffix-is-suffix-x
  (implies (is-suffix (list* x mergedcode1) mergedcode)
           (is-suffix mergedcode1  mergedcode))
  :rule-classes :forward-chaining)



(defthm isEnd-implies-not-isStackMap
  (implies (isStackmap frame)
           (not (isEnd frame)))
  :hints (("Goal" :in-theory (enable isEnd isStackmap)))
  :rule-classes :forward-chaining)

(defthm isEnd-implies-not-isInstruction
  (implies (isInstruction frame)
           (not (isEnd frame)))
  :hints (("Goal" :in-theory (enable isEnd instrOffset 
                                     isInstruction)))
  :rule-classes :forward-chaining)



(defthm isEnd-implies-not-isInstruction-2
  (implies (isEnd frame)
           (not (isInstruction frame)))
  :hints (("Goal" :in-theory (enable isEnd instrOffset 
                                     isInstruction)))
  :rule-classes :forward-chaining)


(defthm isStackMap-implies-not-isInstruction
  (implies (isInstruction frame)
           (not (isStackMap frame)))
  :hints (("Goal" :in-theory (enable isStackMap instrOffset 
                                     isInstruction)))
  :rule-classes :forward-chaining)


(defthm isEnd-implies-not-isStackMap-2
  (implies (isEnd frame)
           (not (isStackMap frame)))
  :hints (("Goal" :in-theory (enable isEnd instrOffset 
                                     isStackMap)))
  :rule-classes :forward-chaining)


(defthm isInstruction-implies-not-isStackMap
  (implies (isStackMap frame)
           (not (isInstruction frame)))
  :hints (("Goal" :in-theory (enable isStackMap
                                     instrOffset
                                     isInstruction)))
  :rule-classes :forward-chaining)

;----------------------------------------------------------------------


(defthm pc-wff-mergedcode1-implies-wff-merged-code-weak
  (implies (pc-wff-mergedcode1 pc mergedcode)
           (wff-merged-code-weak mergedcode))
  :rule-classes :forward-chaining)


;----------------------------------------------------------------------

;; concept needed to prove ... 

(defun forward-to-next-inst (mergedcode)
  (if (endp mergedcode) mergedcode
    (if (isInstruction (car mergedcode))
        mergedcode
      (forward-to-next-inst (cdr mergedcode)))))


(defun next-stackframe (mergedcode)
  (if (endp mergedcode) "impossible"
    (if (endp (cdr mergedcode)) "impossible"
        (if (isInstruction (cadr mergedcode))
            (mapFrame (getMap (car mergedcode)))
          (next-stackframe (cdr mergedcode))))))
            
;----------------------------------------------------------------------




(defun next-inst (inst mergecode)
  (if (endp mergecode) nil
    (if (endp (cdr mergecode)) nil
      (if (equal (car mergecode) inst)
          (cadr mergecode)
        (next-inst inst (cdr mergecode))))))



(defun next-insts (inst mergecode)
  (if (endp mergecode) nil
    (if (endp (cdr mergecode)) nil
      (if (equal (car mergecode) inst)
          (cdr mergecode)
        (next-insts inst (cdr mergecode))))))
        

;----------------------------------------------------------------------


(defun suffix (frame mergedcode)
  (if (endp mergedcode) nil
    (if (equal (car mergedcode) frame)
        mergedcode
      (suffix frame (cdr mergedcode)))))




(defun collect-sig-frame-at-mergecode1 (env mergedcode1 mergedcode stackmap)
  (if (equal mergedcode1 mergedcode) 
      stackmap
    (if (endp mergedcode) nil
      (if (endp (cdr mergedcode)) nil
        (if (equal stackmap 'afterGoto)
            (if (isStackMap (car Mergedcode))
                (collect-sig-frame-at-mergecode1
                 env mergedcode1 (cdr mergedcode)
                 (mapFrame (getMap (car mergedcode))))
              nil)
          (cond ((isStackMap (car mergedcode))
                 (and (frameIsAssignable stackmap 
                                         (mapFrame (getMap (car mergedcode)))
                                         env)
                      (collect-sig-frame-at-mergecode1
                       env mergedcode1 
                       (cdr mergedcode) 
                       (mapFrame (getMap (car mergedcode))))))
                ((isInstruction (car mergedcode))
                 (let ((offset     (instrOffset (car MergedCode)))
                       (instr      (car MergedCode)))
                   (and (instructionIsTypeSafe instr env stackmap)
                        (mv-let (NextStackFrame ExceptionStackFrame)
                                (sig-do-inst instr env stackmap)
                                (and (instructionSatisfiesHandlers env offset
                                                                   ExceptionStackFrame)
                                     (mergedCodeIsTypeSafe env (cdr MergedCode)
                                                           NextStackFrame)
                                     (collect-sig-frame-at-mergecode1
                                      env 
                                      mergedcode1
                                      (cdr mergedcode) 
                                      NextStackFrame))))))
                (t nil)))))))

;----------------------------------------------------------------------



(defun extract-frame-pc (frames)
  (if (endp frames) nil
    (cons (mapOffset (car frames))
          (extract-frame-pc (cdr frames)))))

(defun all-strictly-less-than (v l)
  (if (endp l) t
    (and (< v (car l))
         (all-strictly-less-than v (cdr l)))))


(defun strictly-ordered (l)
  (if (endp l) t
    (and (all-strictly-less-than (car l) (cdr l))
         (strictly-ordered (cdr l)))))

;----------------------------------------------------------------------



(defthm car-makeStackMap-stack_map
  (equal (car (makestackmap frame)) 'stack_map))

(defthm mapFrame-list-reduce 
  (equal (MAPFRAME (LIST pc frame))
         frame))

(defthm mapoffset-reduce 
  (equal (MAPOFFSET (LIST pc frame))
         pc))


(defthm getMap-makestackmap
  (equal (getMap (makestackmap frame))
         frame))


;----------------------------------------------------------------------


(defun wff-stack-map-offset (mergecode)
  (if (endp mergecode) t
    (if (isStackMap (car mergecode))
        (and (not (endp (cdr mergecode)))
             (equal (next-pc (cdr mergecode))
                    (mapoffset (getMap (car mergecode))))
             (wff-stack-map-offset (cdr mergecode)))
      (wff-stack-map-offset (cdr mergecode)))))


(defthm next-pc-expand
  (implies (isInstruction mergedcode3)
           (equal (NEXT-PC (CONS MERGEDCODE3 MERGEDCODE4))
                  (instrOffset mergedcode3)))
  :hints (("Goal" :in-theory (e/d (next-pc)
                                  (isInstruction 
                                   isEnd 
                                   isStackMap)))))


(defthm next-pc-expand-2
  (implies (isStackMap mergedcode3)
           (equal (NEXT-PC (CONS MERGEDCODE3 MERGEDCODE4))
                  (mapOffset (getMap mergedcode3))))
  :hints (("Goal" :in-theory (e/d (next-pc)
                                  (isInstruction 
                                   isEnd 
                                   isStackMap)))))

(defthm getmap-reduce
  (equal (GETMAP (LIST* MERGEDCODE1 MERGEDCODE3 MERGEDCODE4))
         mergedcode3))

;----------------------------------------------------------------------



(defun wff-mergedcode-instr (mergedcode)
  (if (endp mergedcode) t
    (if (isStackMap (car mergedcode))
        (and (consp (extract-code mergedcode))
             (wff-mergedcode-instr (cdr mergedcode)))
      (wff-mergedcode-instr (cdr mergedcode)))))


;----------------------------------------------------------------------



(defun wff-stack-map-offset-2 (mergedcode)
  (if (endp mergedcode) t
      (if (isInstruction (car mergedcode))
          (and (or (not (consp (cdr mergedcode)))
                   (isEnd (cadr mergedcode))
                   (< (instrOffset (car mergedcode))
                      (car (extract-pc (cdr mergedcode)))))
               (wff-stack-map-offset-2 (cdr mergedcode)))
        (wff-stack-map-offset-2 (cdr mergedcode)))))
              

;----------------------------------------------------------------------

(defun all-good-frames (frames env)
  (if (endp frames) t
    (and (good-frame (mapframe (getmap (car frames))) env)
         (all-good-frames (cdr frames) env))))

(defun extract-frames (mergedcode)
  (if (endp mergedcode) nil
    (cond  ((isEnd (car mergedcode)) nil)
           ((isStackMap (car mergedcode))
            (cons (car mergedcode) (extract-frames (cdr mergedcode))))
           ((isInstruction (car mergedcode))
            (extract-frames (cdr mergedcode)))
           (t nil))))

;----------------------------------------------------------------------


                  
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

;----------------------------------------------------------------------


(defun prefix (mergedcode1 mergedcode)
  (if (equal mergedcode mergedcode1) nil
    (if (endp mergedcode) "impossible"
      (cons (car mergedcode)
            (prefix mergedcode1 (cdr mergedcode))))))




(defthm suffix-is-append-prefix
  (implies (is-suffix mergedcode1 mergedcode)
           (equal (append (prefix mergedcode1  mergedcode)
                          mergedcode1)
                  mergedcode)))
                  
;----------------------------------------------------------------------


(defun never-after-goto (frames)
  (if (endp frames) t
    (and (not (equal (mapFrame (getMap (car frames))) 'aftergoto))
         (never-after-goto (cdr frames)))))


(defthm pc-wff-mergedcode1-implies-never-after-goto-x
  (implies (pc-wff-mergedcode1 pc mergedcode)
           (never-after-goto (extract-frames mergedcode)))
  :hints (("Goal" :in-theory (disable isStackMap
                                      isInstruction
                                      isEnd
                                      jvm::inst-size)))
  :rule-classes :forward-chaining)




(defthm is-suffix-never-after-goto-x
  (implies (and  (is-suffix mergedcode1 mergedcode2)
                 (wff-merged-code-weak mergedcode2)
                 (never-after-goto (extract-frames mergedcode2)))
           (never-after-goto (extract-frames mergedcode1)))
  :hints (("Goal" :in-theory (disable isStackMap
                                      isInstruction
                                      isEnd
                                      jvm::inst-size)))
  :rule-classes :forward-chaining)

