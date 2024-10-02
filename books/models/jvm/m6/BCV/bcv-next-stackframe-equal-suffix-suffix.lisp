(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")



(defthm is-suffix-then-is-suffix-suffix
  (implies (and (is-suffix mergedcode all-merged-code)
                (consp mergedcode))
           (is-suffix mergedcode (suffix (car mergedcode) all-merged-code))))


;; (defun prefix (mergedcode1 mergedcode)
;;   (if (equal mergedcode mergedcode1) nil
;;     (if (endp mergedcode) "impossible"
;;       (cons (car mergedcode)
;;             (prefix mergedcode1 (cdr mergedcode))))))



(defun all-stack-frame (frames)
  (if (endp frames) t
    (and (isStackMap (car frames))
         (all-stack-frame (cdr frames)))))

(defthm next-stackframe-append-stack-frames-in-front
  (implies (and (isStackMap frame)
                (isStackMap (car any)))
           (equal (next-stackframe (cons frame any))
                  (next-stackframe any)))
  :hints (("Goal" :in-theory (disable isInstruction
                                      isStackMap
                                      isEnd))))


(defun induct-append (frames any)
  (if (endp frames) (list frames any)
    (induct-append (cdr frames)
                   (cons (car frames) any))))

(defthm next-stackframe-append-stack-frames-in-front-2
  (implies (and (all-stack-frame frames)
                (isStackMap (car any)))
           (equal (next-stackframe (append frames any))
                  (next-stackframe any)))
  :hints (("Goal" :in-theory (disable isInstruction
                                      isStackMap
                                      next-stackframe
                                      isEnd)
           :do-not '(generalize fertilize)
           :induct (induct-append frames any))))


(defthm suffix-is-append-prefix
  (implies (is-suffix mergedcode1 mergedcode)
           (equal (append (prefix mergedcode1  mergedcode)
                          mergedcode1)
                  mergedcode)))
                  
;----------------------------------------------------------------------

;; (defthm member-instruction
;;   (implies (and (member instr prefix)
;;                 (wff-stack-map-offset-2 (append prefix mergedcode))
;;                 (wff-merged-code-weak (append prefix mergedcode))
;;                 (ordered (extract-pc (append prefix mergedcode))))
;;            (< (next-pc (car prefix))
;;               (next-pc mergedcode)))
;;   :hints (("Goal" :in-theory (disable isInstruction isStackMap
;;                                       isEnd mapOffset instrOffset))))


(defun all-less-than (x l)
  (if (endp l) t
    (and (<= (car l) x)
         (all-less-than x (car l)))))


(defun wff-merged-code-weak-2 (l)
  (if (endp l) t
    (and (or (isStackMap (car l))
             (isInstruction (car l)))
         (wff-merged-code-weak-2 (cdr l)))))


(defthm wff-stack-map-offset-2-implies-strictly-less-than
  (implies (and (wff-stack-map-offset-2 mergedcode)
                (wff-merged-code-weak-2 mergedcode)
                (member inst mergedcode)
                (isInstruction inst)
                (consp (cdr (suffix inst mergedcode))))
           (< (instrOffset inst)
              (next-pc (cdr (suffix inst mergedcode))))))


(defthm wff-stack-map-offset-2-wff-stack-map-offset
  (implies (wff-stack-map-offset-2 (append prefix (cons x any)))
           (wff-stack-map-offset-2 (append prefix (list x))))
  :hints (("Goal" :in-theory (disable isEnd isInstruction isStackMap
                                      instrOffset
                                      mapOffset next-pc)
           :do-not '(generalize))))

(defthm wff-merged-code-weak-implies-wff-merged-code-weak-2
  (implies (and (wff-merged-code-weak (append prefix (cons x any)))
                (isStackMap x))
           (wff-merged-code-weak-2 (append prefix (list x))))
  :hints (("Goal" :in-theory (disable isEnd isInstruction isStackMap
                                      instrOffset
                                      mapOffset next-pc)
           :do-not '(generalize))))

(defthm ordered-implies-no-less-than
  (implies (and (member x l)
                (ordered l))
           (<= x (car (last l)))))

(defthm extract-pc-apppend
  (implies (wff-merged-code-weak-2 (append prefix mergedcode))
           (equal (extract-pc (append prefix mergedcode))
                  (append (extract-pc prefix) (extract-pc mergedcode)))))

(defthm car-last-append
  (equal (car (last (append l (list x))))
         x))


(defthm member-inst-member
  (implies (and (member inst prefix)
                (consp mergedcode))
           (member (car (cdr (suffix inst (append prefix mergedcode))))
                   (append prefix mergedcode))))


(defthm member-pc-member
  (implies (and (member inst mergedcode)
                (wff-merged-code-weak-2 mergedcode)
                (isInstruction inst))
           (member (instrOffset inst) (extract-pc mergedcode)))
  :hints (("Goal" :in-theory (disable isInstruction isStackMap
                                      mapOffset
                                      isEnd instrOffset))))


(defthm member-next-pc-member
  (implies (and (member (car l) (append l1 l2))
                (wff-merged-code-weak-2 (append l1 l2)))
           (member (next-pc l) 
                   (append (extract-pc l1) 
                           (extract-pc l2)))))

(defthm ordered-append-nil
  (equal (ordered (append l nil))
         (ordered l)))

(defthm isStackMap-consp
  (implies (ISSTACKMAP MERGEDCODE1)
           (consp mergedcode1))
  :rule-classes :forward-chaining)

(defthm ordered-append-1
  (implies (ORDERED (append l1 l2))
           (ordered l1))
  :rule-classes :forward-chaining)


(defthm ordered-append-1-specific
  (implies (ordered (extract-pc (append prefix (cons x l))))
           (ordered (extract-pc (append prefix (list x)))))
  :hints (("Goal" :in-theory (disable isEnd isInstruction isStackMap
                                      instrOffset
                                      mapOffset next-pc)
           :do-not '(generalize)))
  :rule-classes :forward-chaining)


(defthm ordered-append-1-specific-further
  (implies (and (wff-merged-code-weak-2 (append prefix (list x)))
                (isStackMap x))
           (equal (extract-pc (append prefix (list x)))
                  (append (extract-pc prefix) (list (mapOffset (getMap x)))))))
  

(defthm member-inst-prefix
  (implies (member inst prefix)
           (CONSP (CDR (SUFFIX INST
                               (APPEND PREFIX (LIST MERGEDCODE1)))))))


(defthm member-inst-member-append
  (implies (member inst prefix)
           (MEMBER INST
                   (APPEND PREFIX (LIST MERGEDCODE1)))))


(defthm wff-stack-map-offset-member-then-last-pc-larger
  (implies (and (ordered (extract-pc (append prefix mergedcode)))
                (wff-stack-map-offset-2 (append prefix mergedcode))
                (wff-merged-code-weak (append prefix mergedcode))
                (isInstruction inst)
                (consp mergedcode)
                (isStackMap (car mergedcode))
                (member inst prefix))
           (< (instrOffset inst)
              (mapOffset (getMap (car mergedcode)))))
  :hints (("Goal" :in-theory (disable isEnd isInstruction isStackMap
                                      instrOffset getMap
                                      mapOffset next-pc)
            :use ((:instance wff-stack-map-offset-2-implies-strictly-less-than
                             (mergedcode (append prefix (list (car
                                                               mergedcode)))))
                  (:instance ordered-implies-no-less-than
                             (x (NEXT-PC (CDR (SUFFIX INST
                                                      (APPEND PREFIX (LIST (car MERGEDCODE)))))))
                             (l (extract-pc (append prefix (list (car
                                                                  mergedcode))))))
                  (:instance member-inst-member
                             (mergedcode (append prefix (list (car
                                                               mergedcode)))))
                  (:instance member-next-pc-member
                             (l (cdr (suffix inst (append prefix (list (car
                                                                        mergedcode))))))
                             (l1 prefix)
                             (l2 (list (car mergedcode))))
                  (:instance wff-merged-code-weak-implies-wff-merged-code-weak-2
                             (x (car mergedcode))
                             (any (cdr mergedcode)))
                  (:instance ordered-append-1-specific
                             (x (car mergedcode))
                             (l (cdr mergedcode))))
           :do-not-induct t))
  :rule-classes :linear)
                                      
  
;; stupid!! Fri Dec 30 20:56:18 2005

;----------------------------------------------------------------------




(defthm extract-pc-is-consp
  (implies (and (WFF-MERGED-CODE-WEAK (APPEND PREFIX MERGEDCODE))
                (isStackMap (car mergedcode)))
           (CONSP (EXTRACT-PC (APPEND PREFIX MERGEDCODE)))))


(defthm extract-pc-ordered-fact
  (implies (and (ORDERED (EXTRACT-PC (APPEND PREFIX mergedcode)))
                (wff-merged-code-weak (append prefix mergedcode))
                (isStackMap (car mergedcode)))
           (<= (car (extract-pc (append prefix mergedcode)))
               (mapOffset (getMap (car mergedcode)))))
  :hints (("Goal" :in-theory (disable isEnd isInstruction isStackMap
                                      instrOffset getMap
                                      mapOffset)))
  :rule-classes :forward-chaining)

(defthm wff-merged-code-weak-never-end
  (implies (and (wff-merged-code-weak (append prefix mergedcode))
                (isStackMap (car mergedcode)))
           (not (isEnd (car (append prefix mergedcode)))))
  :hints (("Goal" :in-theory (disable isEnd isInstruction isStackMap
                                      instrOffset getMap
                                      mapOffset))))

;----------------------------------------------------------------------


(defthm wff-stack-map-offset-2-implies-all-frames-lemma
  (implies (and (wff-stack-map-offset-2 (append prefix mergedcode))
                (wff-merged-code-weak (append prefix mergedcode))
                (isStackMap (car mergedcode))
                (ordered (extract-pc (append prefix mergedcode)))
                (equal (next-pc prefix)
                       (mapOffset (getMap (car mergedcode)))))
           (all-stack-frame prefix))
  :hints (("Goal" :in-theory (disable isEnd isInstruction isStackMap
                                      instrOffset getMap
                                      mapOffset)
           :do-not '(generalize fertilize))))


;----------------------------------------------------------------------


(defthm car-prefix-is-car
   (implies (and (is-suffix mergedcode1 mergedcode)
                 (not (equal mergedcode1 mergedcode))
                 (consp mergedcode))
            (equal (car (prefix mergedcode1 mergedcode))
                   (car mergedcode))))

;; (NEXT-PC (PREFIX MERGEDCODE1 MERGEDCODE))



(defthm wff-stack-map-offset-2-implies-all-frames
  (implies (and (wff-stack-map-offset-2 mergedcode)
                (wff-merged-code-weak mergedcode)
                (ordered (extract-pc mergedcode))
                (is-suffix mergedcode1 mergedcode)
                (isStackMap (car mergedcode1))
                (isStackMap (car mergedcode))
                (equal (mapOffset (getMap (car mergedcode)))
                       (mapOffset (getMap (car mergedcode1)))))
           (all-stack-frame (prefix mergedcode1 mergedcode)))
  :hints (("Goal" :in-theory (disable isEnd isInstruction isStackMap
                                      instrOffset getMap
                                      mapOffset)
           :do-not-induct t
           :cases ((equal mergedcode1 mergedcode)))
          ("Subgoal 2"   :use ((:instance wff-stack-map-offset-2-implies-all-frames-lemma
                                          (prefix (prefix mergedcode1 mergedcode))
                                          (mergedcode mergedcode1))))))
          

;----------------------------------------------------------------------

;; (defthm next-stackframe-append-stack-frames-in-front-2
;;   (implies (and (all-stack-frame frames)
;;                 (isStackMap (car any)))
;;            (equal (next-stackframe (append frames any))
;;                   (next-stackframe any)))
;;   :hints (("Goal" :in-theory (disable isInstruction
;;                                       isStackMap
;;                                       next-stackframe
;;                                       isEnd)
;;            :do-not '(generalize fertilize)
;;            :induct (induct-append frames any))))


(defthm is-suffix-suffix
  (implies (member x l)
           (IS-SUFFIX (SUFFIX x l) l)))


(defthm car-suffix-is-car
  (implies (member x all-merged-code)
           (equal (car (SUFFIX x ALL-MERGED-CODE))
                  x)))

(defthm wff-stack-map-offset-2-suffix
  (implies (and (wff-stack-map-offset-2 all-merged-code)
                (member x all-merged-code))
           (WFF-STACK-MAP-OFFSET-2 (SUFFIX x  ALL-MERGED-CODE))))

(defthm wff-merged-code-weak-suffix
  (implies (and (wff-merged-code-weak all-merged-code)
                (member x all-merged-code)
                (not (isEnd x)))
           (WFF-MERGED-CODE-WEAK (SUFFIX x ALL-MERGED-CODE))))


(defthm ordered-suffix
  (implies (and (ordered (extract-pc all-merged-code))
                (member x all-merged-code)
                (wff-merged-code-weak all-merged-code))
           (ORDERED (EXTRACT-PC (SUFFIX x ALL-MERGED-CODE))))
  :hints (("Goal" :in-theory (disable isEnd isInstruction isStackMap
                                      instrOffset getMap
                                      mapOffset))))


(defthm is-suffix-suffix-2
  (implies (and (is-suffix mergedcode all-merged-code)
                (consp mergedcode))
           (IS-SUFFIX MERGEDCODE (SUFFIX (CAR MERGEDCODE) ALL-MERGED-CODE))))

(defthm isStackMap-consp-x
  (implies (isStackMap (car mergedcode))
           (consp mergedcode))
  :rule-classes :forward-chaining)

(defthm is-suffix-then-suffix-is
  (implies (and (is-suffix mergedcode all-merged-code)
                (ordered (extract-pc all-merged-code))
                (wff-stack-map-offset-2 all-merged-code)
                (wff-merged-code-weak all-merged-code)
                (member (car mergedcode) all-merged-code)
                (isStackMap (car mergedcode)))
           (equal (next-stackframe (suffix (car mergedcode) all-merged-code))
                  (next-stackframe mergedcode)))
  :hints (("Goal" :in-theory (disable isInstruction
                                      isStackMap
                                      isEnd
                                      next-stackframe
                                      mapOffset
                                      mapFrame
                                      instrOffset
                                      getMap)
           :do-not-induct t
           :do-not '(generalize fertilize)
           :use ((:instance next-stackframe-append-stack-frames-in-front-2
                            (frames (prefix mergedcode
                                            (suffix (car mergedcode)
                                                    all-merged-code)))
                            (any mergedcode))))))
                                 


;----------------------------------------------------------------------


