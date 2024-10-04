(in-package "DJVM")
(include-book "base")
(include-book "../../M6/m6-bytecode")
(include-book "../../DJVM/consistent-state-to-untag-state")


(in-theory (disable state-equiv thread-table-equiv 
                    thread-entry-equiv
                    call-stack-equiv
                    frame-equiv locals-equiv))

(include-book "base-bind-free")


(defun m6-symbol (s)
  (declare (xargs :guard (acl2::symbolp s)))
  (equal (acl2::symbol-package-name s) "M6"))


(defthm wff-state-alt-if-state-set-pc
  (wff-state-alt (state-set-pc pc s))
  :hints (("Goal" :in-theory (enable wff-state-alt
                                     state-set-pc))))

(defthm wff-state-alt-if-state-set-thread-table
  (wff-state-alt (state-set-thread-table tt s)))


(defthm wff-state-alt-if-state-set-heap
  (wff-state-alt (state-set-heap hp s)))



(in-theory (disable wff-state-alt))


(defthm state-equiv-implied-by
  (implies (and (wff-state-alt m6-s)
                (thread-table-equiv (thread-table m6-s) (thread-table djvm-s))
                (equal (pc m6-s) (pc djvm-s))
                (equal (current-thread m6-s)
                       (current-thread djvm-s))
                (equal (heap m6-s)
                       (heap djvm-s))
                (equal (class-table m6-s) (class-table djvm-s))
                (equal (env m6-s) (env djvm-s))
                (equal (error-flag m6-s) (error-flag djvm-s))
                (equal (aux m6-s) (aux djvm-s)))
           (state-equiv m6-s djvm-s))
  :hints (("Goal" :in-theory (enable state-equiv wff-state-alt))))



(defthm state-equiv-implies
  (implies (and (syntaxp (and (symbolp m6-s)
                              (m6-symbol m6-s)))
                (bind-free (acl2::default-bind-free 'djvm-s 'djvm-s
                                                    (acl2::pkg-witness "DJVM"))
                           (djvm-s))
                (state-equiv m6-s djvm-s))
           (and  (equal (pc m6-s) (pc djvm-s))
                 (equal (current-thread m6-s)
                        (current-thread djvm-s))
                 (equal (heap m6-s)
                        (heap djvm-s))
                 (equal (class-table m6-s) (class-table djvm-s))
                 (equal (env m6-s) (env djvm-s))
                 (equal (error-flag m6-s) (error-flag djvm-s))
                 (equal (aux m6-s) (aux djvm-s))))
  :hints (("Goal" :in-theory (enable state-equiv))))




(defthm state-equiv-implies-2
  (implies (and (syntaxp (and (symbolp m6-s)
                              (m6-symbol m6-s)))
                (state-equiv m6-s djvm-s))
           (thread-table-equiv (thread-table m6-s) (thread-table djvm-s)))
  :hints (("Goal" :in-theory (enable state-equiv))))


;----------------------------------------------------------------------


;;; 
;;; the replace-thread-table-entry is badly defined!!! 
;;;


(local 
 (defthm collect-thread-id-mem-id
   (implies (and (<= 0 i)
                 (integerp i)
                 (< i (len tt)))
            (MEM (THREAD-ID (NTH I tt))
                 (COLLECT-THREAD-ID TT)))))




(local 
 (defthm unique-id-thread-table-ever-equal
   (implies (and (unique-id-thread-table tt)
                 (integerp i)
                 (<= 0 i)
                 (< i (len (cdr tt))))
            (not (EQUAL (car tt)
                        (nth i (cdr tt)))))
   :hints (("Goal" :do-not '(generalize)))))


(local 
 (defthm unique-id-thread-table-implies-cdr-unique-id
   (implies (unique-id-thread-table tt)
            (unique-id-thread-table (cdr tt)))))


(defthm thread-table-equiv-implies-replace-i-th
   (implies (and (thread-table-equiv m6-tt djvm-tt)
                 (unique-id-thread-table m6-tt)
                 (unique-id-thread-table djvm-tt)
                 (integerp i)
                 (<= 0 i)
                 (< i (len m6-tt))
                 (< i (len djvm-tt))
                 (thread-entry-equiv m6-th djvm-th))                
            (thread-table-equiv (replace-thread-table-entry
                                 (nth i m6-tt)
                                 m6-th
                                 m6-tt)
                                (replace-thread-table-entry
                                 (nth i djvm-tt)
                                 djvm-th
                                 djvm-tt)))
   :hints (("Goal" :in-theory (e/d (thread-table-equiv)
                                   (unique-id-thread-table))
            :do-not '(generalize fertilize))))




(defun find-index-i-for-id (id tt)
  (if (endp tt) 0
    (if (equal (thread-id (car tt)) id) 0
      (+ 1 (find-index-i-for-id id (cdr tt))))))
    

(defthm thread-by-id-reduce-to-nth-i
  (implies (thread-by-id id tt)
           (equal (thread-by-id id tt)
                  (nth (find-index-i-for-id id tt) tt)))
  :hints (("Goal" :in-theory (enable thread-by-id))))
  

(defthm thread-table-equiv-implies-find-index-by-id-same
  (implies (and (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
                                                             'djvm::djvm-s m6-tt
                                                             'djvm-tt)
                           (djvm-tt))
                (thread-table-equiv m6-tt djvm-tt))
           (equal (find-index-i-for-id id m6-tt)
                  (find-index-i-for-id id djvm-tt)))
  :hints (("Goal" :in-theory (enable thread-table-equiv thread-entry-equiv))))


;----------------------------------------------------------------------




;----------------------------------------------------------------------
; allow quote some skip proofs! 

(local 
 (defthm thread-by-id-thread-table-equiv
  (implies (and (syntaxp (and (acl2::found-symbol2 'm6::m6-s m6-tt)))
                (bind-free (acl2::replace-occurance-binding2 
                            'm6::m6-s 'djvm::djvm-s m6-tt 'djvm-tt)
                           (djvm-tt))
                (thread-table-equiv m6-tt djvm-tt)
                (thread-by-id id djvm-tt))
           (thread-by-id id m6-tt))
  :hints (("Goal" :in-theory (e/d (thread-by-id 
                                   thread-entry-equiv
                                   thread-table-equiv)
                                  (thread-by-id-reduce-to-nth-i))))))
           
(local 
 (defthm consistent-state-thread-by-id-exists-lemma
   (implies (consistent-state s)
            (thread-by-id (current-thread s) (thread-table s)))))


(defthm consistent-state-thread-by-id-exists-alt
  (implies (consistent-state s)
           (nth (find-index-i-for-id (current-thread s) (thread-table s))
                (thread-table s)))
  :hints (("Goal" :use ((:instance consistent-state-thread-by-id-exists-lemma)
                        (:instance thread-by-id-reduce-to-nth-i
                                   (tt (thread-table s))
                                   (id (current-thread s)))))))



(defthm thread-by-id-thread-table-equiv-alt
  (implies (and (syntaxp (and (acl2::found-symbol2 'm6::m6-s m6-tt)))
                (bind-free (acl2::replace-occurance-binding2 
                            'm6::m6-s 'djvm::djvm-s m6-tt 'djvm-tt)
                           (djvm-tt))
                (thread-table-equiv m6-tt djvm-tt)
                (nth (find-index-i-for-id id djvm-tt) djvm-tt))
           (nth (find-index-i-for-id id m6-tt) m6-tt))
  :hints (("Goal" :in-theory (e/d (thread-entry-equiv
                                   thread-table-equiv) ()))))

;; (local 
;;  (defthm thread-by-id-thread-reduce-2
;;    (implies (and (syntaxp (and (acl2::found-symbol2 'm6::m6-s m6-tt)))
;;                  (bind-free (acl2::replace-occurance-binding2 
;;                             'm6::m6-s 'djvm::djvm-s m6-tt 'djvm-tt)
;;                            (djvm-tt))
;;                 (thread-table-equiv m6-tt djvm-tt))
            



;; (defthm thread-by-id-thread-table-equiv-alt-2
;;   (implies (and (syntaxp (and (acl2::found-symbol2 'm6::m6-s m6-tt)))
;;                 (bind-free (acl2::replace-occurance-binding2 
;;                             'm6::m6-s 'djvm::djvm-s m6-tt 'djvm-tt)
;;                            (djvm-tt))
;;                 (thread-table-equiv m6-tt djvm-tt)
;;                 (nth (find-index-i-for-id id djvm-tt) djvm-tt))

;;   :hints (("Goal" :in-theory (e/d (thread-entry-equiv
;;                                    thread-table-equiv) ()))))


(defthm collect-thread-id-if-thread-equiv
  (implies (and (syntaxp (and (acl2::found-symbol2 'm6::m6-s m6-tt)))
                (bind-free (acl2::replace-occurance-binding2 
                             'm6::m6-s 'djvm::djvm-s m6-tt 'djvm-tt)
                            (djvm-tt))
                (thread-table-equiv m6-tt djvm-tt))
           (equal (collect-thread-id m6-tt)
                  (collect-thread-id djvm-tt)))
  :hints (("Goal" :in-theory (enable thread-table-equiv thread-entry-equiv))))



(defthm consistent-state-unique-thread-table
  (implies (consistent-state s)
           (nodup-set (collect-thread-id (thread-table s))))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm thread-table-equiv-len-equal
  (implies (and (syntaxp (and (acl2::found-symbol2 'm6::m6-s m6-tt)))
                (bind-free (acl2::replace-occurance-binding2 
                            'm6::m6-s 'djvm::djvm-s m6-tt 'djvm-tt)
                           (djvm-tt))
                (thread-table-equiv m6-tt djvm-tt))
           (equal (len m6-tt)
                  (len djvm-tt)))
  :hints (("Goal" :in-theory (enable thread-table-equiv))))



(defthm find-index-i-for-id-in-range
  (implies (thread-by-id id tt)
           (< (find-index-i-for-id id tt)
              (len tt)))
  :hints (("Goal" :in-theory (enable thread-by-id)))
  :rule-classes :linear)




;----------------------------------------------------------------------

;; >V d          (DEFUN MAKE-THREAD
;;                      (ID PC JVM::CALL-STACK JVM::S
;;                          JVM::M-REF JVM::MDEPTH THREAD-REF)
;;                      (LIST 'JVM::THREAD
;;                            ID (CONS 'JVM::SAVED-PC PC)
;;                            (CONS 'JVM::CALL-STACK JVM::CALL-STACK)
;;                            (CONS 'JVM::STATUS JVM::S)
;;                            (CONS 'MONITOR JVM::M-REF)
;;                            (CONS 'JVM::MDEPTH JVM::MDEPTH)
;;                            (CONS 'JVM::THREAD-OBJ THREAD-REF)))


(defun wff-thread-alt (th)
  (equal (make-thread (thread-id th)
                      (thread-saved-pc th)
                      (thread-call-stack th)
                      (thread-state th)
                      (thread-mref th)
                      (thread-mdepth th)
                      (thread-ref th))
         th))


(defthm thread-entry-equiv-implied-by
  (implies (and (wff-thread-alt m6-th)
                (call-stack-equiv (thread-call-stack m6-th) (thread-call-stack djvm-th))
                (equal (thread-id m6-th) (thread-id djvm-th))
                (equal (thread-saved-pc m6-th) (thread-saved-pc djvm-th))
                (equal (thread-state m6-th) (thread-state djvm-th))
                (equal (thread-mref m6-th) (thread-mref djvm-th))
                (equal (thread-mdepth m6-th) (thread-mdepth djvm-th))
                (equal (thread-ref m6-th) (thread-ref djvm-th)))
           (thread-entry-equiv m6-th djvm-th))
  :hints (("Goal" :in-theory (enable thread-entry-equiv 
                                     thread-set-call-stack
                                     wff-thread-alt))))

(in-theory (disable wff-thread-alt))


(local 
 (defthm thread-entry-equiv-implies
   (implies (and (syntaxp (and (symbolp m6-th)
                               (m6-symbol m6-th)))
                 (bind-free (acl2::default-bind-free 'djvm-th 'djvm-th
                                                     (acl2::pkg-witness "DJVM"))
                            (djvm-th))
                (thread-entry-equiv m6-th djvm-th))
            (and  (equal (thread-id m6-th) (thread-id djvm-th))
                  (equal (thread-saved-pc m6-th) (thread-saved-pc djvm-th))
                  (equal (thread-state m6-th) (thread-state djvm-th))
                  (equal (thread-mref m6-th) (thread-mref djvm-th))
                  (equal (thread-mdepth m6-th) (thread-mdepth djvm-th))
                  (equal (thread-ref m6-th) (thread-ref djvm-th))))
  :hints (("Goal" :in-theory (e/d (thread-entry-equiv
                                   thread-set-call-stack)
                                  (THREAD-MDEPTH
                                   THREAD-MREF
                                   THREAD-REF
                                   THREAD-SAVED-PC
                                   THREAD-STATE))))))

           
(in-theory  (disable THREAD-MDEPTH
                     THREAD-MREF
                     THREAD-REF
                     THREAD-SAVED-PC
                     THREAD-STATE))



(defthm thread-entry-equiv-implies-2
  (implies (and (syntaxp (and (symbolp m6-th)
                              (m6-symbol m6-th)))
                (thread-entry-equiv m6-th djvm-th))
           (call-stack-equiv (thread-call-stack m6-th) (thread-call-stack djvm-th)))
  :hints (("Goal" :in-theory (enable thread-entry-equiv))))


(local 
 (defthm wff-thread-alt-thread-set-call-stack
   (wff-thread-alt (thread-set-call-stack any th))
   :hints (("Goal" :in-theory (enable thread-set-call-stack
                                      wff-thread-alt)))))


(in-theory (disable push pop top))



(defthm call-stack-equiv-push-same
  (implies (and (frame-equiv m6-frame djvm-frame)
                (call-stack-equiv m6-cs djvm-cs))
           (call-stack-equiv (push m6-frame m6-cs)
                             (push djvm-frame djvm-cs)))
  :hints (("Goal" :in-theory (enable call-stack-equiv push pop))))


(defthm call-stack-equiv-pop-same
  (implies (call-stack-equiv m6-cs djvm-cs)
           (call-stack-equiv (pop m6-cs)
                             (pop djvm-cs)))
  :hints (("Goal" :in-theory (enable call-stack-equiv push pop))))



;; >V d          (DEFUN MAKE-FRAME
;;                      (RETURN-PC JVM::OPERANT-STACK LOCALS
;;                                 METHOD-PTR SYNC-OBJ-REF RESUME-PC AUX)
;;                      (LIST 'FRAME
;;                            (CONS 'RETURN_PC RETURN-PC)
;;                            (CONS 'OPERAND-STACK JVM::OPERANT-STACK)
;;                            (CONS 'LOCALS LOCALS)
;;                            METHOD-PTR
;;                            (CONS 'SYNC-OBJ-REF SYNC-OBJ-REF)
;;                            (CONS 'RESUME-PC RESUME-PC)
;;                            (CONS 'AUX AUX)))


(defun wff-frame-alt (frame)
  (equal (make-frame (return-pc frame)
                     (operand-stack frame)
                     (locals frame)
                     (method-ptr frame)
                     (sync-obj-ref frame)
                     (resume-pc frame)
                     (frame-aux frame))
         frame))

  
(defthm frame-equiv-implied-by
  (implies (and (wff-frame-alt m6-frame)
                (locals-equiv (locals m6-frame) (locals djvm-frame))
                (equal (return-pc m6-frame) (return-pc djvm-frame))
                (equal (operand-stack m6-frame) (untag-opstack (operand-stack
                                                                djvm-frame)))
                (equal (method-ptr m6-frame) (method-ptr djvm-frame))
                (equal (sync-obj-ref m6-frame) (sync-obj-ref djvm-frame))
                (equal (resume-pc m6-frame) (resume-pc djvm-frame)))
           (frame-equiv m6-frame djvm-frame))
  :hints (("Goal" :in-theory (e/d (frame-equiv frame-set-locals
                                               frame-set-operand-stack
                                               frame-set-aux
                                   wff-frame-alt) 
                                  (frame-aux)))))





(defthm frame-equiv-implies
  (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-th m6-frame))
                (bind-free (acl2::replace-occurance-binding2 'm6::m6-th
                                                             'djvm::djvm-th
                                                             m6-frame
                                                             'djvm-frame)
                           (djvm-frame))
                (frame-equiv m6-frame djvm-frame))
           (and (equal (return-pc m6-frame) (return-pc djvm-frame))
                (equal (operand-stack m6-frame) (untag-opstack (operand-stack djvm-frame)))
                (equal (method-ptr m6-frame) (method-ptr djvm-frame))
                (equal (sync-obj-ref m6-frame) (sync-obj-ref djvm-frame))
                (equal (resume-pc m6-frame) (resume-pc djvm-frame))))
  :hints (("Goal" :in-theory (e/d (frame-equiv frame-set-operand-stack
                                               frame-set-locals) ()))))


(in-theory (disable frame-equiv))

(defthm frame-equiv-frame-equiv-set-operand-stack
  (implies (and (equal m6-opstack (untag-opstack djvm-opstack))
                (frame-equiv m6-frame djvm-frame))
           (frame-equiv (frame-set-operand-stack m6-opstack m6-frame)
                        (frame-set-operand-stack djvm-opstack djvm-frame)))
  :hints (("Goal" :in-theory (enable frame-set-operand-stack frame-equiv))))

;;
;; (defthm call-stack-equiv-top-frame-frame-equiv
;;   (implies (and (call-stack-equiv m6-cs djvm-cs)
;;                 (consp djvm-cs))
;;            (frame-equiv (top m6-cs) (top djvm-cs)))
;;   :hints (("Goal" :in-theory (enable call-stack-equiv push pop top))))
;;

(local 
 (defthm not-consp-top-is-nil
   (implies (not (consp x))
            (equal (top x) nil))
   :hints (("Goal" :in-theory (enable top)))))

(local 
 (defthm not-consp-pop-is-nil
   (implies (not (consp x))
            (equal (pop x) nil))
   :hints (("Goal" :in-theory (enable pop)))))

(defthm call-stack-equiv-consp-not-consp
   (implies (and (call-stack-equiv m6-cs djvm-cs)
                 (not (consp djvm-cs)))
            (not (consp m6-cs)))
   :hints (("Goal" :in-theory (enable call-stack-equiv push pop top))))


(local 
 (defthm thread-entry-equiv-implies-2-general
   (implies (and (syntaxp (and (symbolp m6-th)
                               (m6-symbol m6-th)))
                 (thread-entry-equiv m6-th djvm-th))
            (call-stack-equiv (thread-call-stack m6-th) (thread-call-stack djvm-th)))
   :hints (("Goal" :in-theory (enable thread-entry-equiv)))))

(defthm wff-thread-alt-make-threadk
  (WFF-THREAD-ALT (MAKE-THREAD id saved-pc cs status mref mdepth ref))
  :hints (("Goal" :in-theory (Enable wff-thread-alt))))


;; (local 
;;  (defthm untag-stack-pop-equal-pop-untag-stack
;;    (implies (and (bind-free (acl2::replace-occurance-binding2 'djvm::djvm-th
;;                                                               'm6::m6-th 
;;                                                               stack2
;;                                                               'stack1)
;;                             (stack1))
;;                  (equal (untag-opstack stack2) stack1))
;;             (equal (untag-opstack (pop stack2))
;;                    (pop stack1)))
;;    :hints (("Goal" :in-theory (enable untag-opstack pop push)))))





;; (local 
;;  (defthm untag-stack-pop-equal-pop-untag-stack
;;    (implies (and (bind-free (acl2::replace-occurance-binding2 'm6::m6-th 
;;                                                               'djvm::djvm-th
;;                                                               stack1
;;                                                               'stack2)
;;                             (stack2))
;;                  (equal stack1 (untag-opstack stack2)))
;;             (equal (pop stack1)
;;                    (untag-opstack (pop stack2))))
;;    :hints (("Goal" :in-theory (enable untag-opstack pop push)))))





(local 
 (defthm untag-stack-pop-equal-pop-untag-stack-specific
   (equal (pop (untag-opstack stack2))
          (untag-opstack (pop stack2)))
   :hints (("Goal" :in-theory (enable untag-opstack pop push)))))





(local 
 (encapsulate () 

    (defthm thread-saved-pc-thread-set-call-stack
      (equal (thread-saved-pc (thread-set-call-stack any th))
             (thread-saved-pc th))
      :hints (("Goal" :in-theory (enable thread-set-call-stack))))

   (defthm thread-state-thread-set-call-stack
     (equal (thread-state (thread-set-call-stack any th))
            (thread-state th))
     :hints (("Goal" :in-theory (enable thread-set-call-stack))))

   (defthm thread-mref-thread-set-call-stack
     (equal (thread-mref (thread-set-call-stack any th))
            (thread-mref th))
     :hints (("Goal" :in-theory (enable thread-set-call-stack))))


   (defthm thread-mdepth-thread-set-call-stack
     (equal (thread-mdepth (thread-set-call-stack any th))
            (thread-mdepth th))
     :hints (("Goal" :in-theory (enable thread-set-call-stack))))

   (defthm thread-ref-thread-set-call-stack
     (equal (thread-ref (thread-set-call-stack any th))
            (thread-ref th))
     :hints (("Goal" :in-theory (enable thread-set-call-stack))))

   (defthm call-stack-equiv-top-frame-equiv
      (implies (and (call-stack-equiv m6-cs djvm-cs)
                    (consp djvm-cs))
               (frame-equiv (top m6-cs) (top djvm-cs)))
      :hints (("Goal" :in-theory (enable call-stack-equiv push pop top))))))


(defthm thread-entry-equiv-popStack-of-thread
  (implies (thread-entry-equiv m6::m6-th djvm::djvm-th)
           (THREAD-ENTRY-EQUIV (popstack-of-thread m6::m6-th)
                               (popstack-of-thread djvm::djvm-th)))
  :hints (("Goal" :in-theory (e/d (popstack-of-thread)
                                  (untag-opstack 
                                   frame-equiv))
           :cases ((consp (thread-call-stack djvm::djvm-th))))
          ("Subgoal 2" :in-theory (e/d (popstack-of-thread 
                                        thread-set-call-stack
                                        frame-set-operand-stack)
                                       (untag-opstack frame-equiv
                                        call-stack-equiv-consp-not-consp))
           :use ((:instance call-stack-equiv-consp-not-consp
                            (m6-cs (thread-call-stack m6::m6-th))
                            (djvm-cs (thread-call-stack djvm::djvm-th)))))))


;; (i-am-here) ;; Tue Aug  2 00:47:35 2005

;----------------------------------------------------------------------


(defthm thread-table-equiv-implies-nth-entry-equiv
  (implies (and (thread-table-equiv m6-tt djvm-tt)
                (< i (len djvm-tt))
                (<= 0 i))
           (thread-entry-equiv (nth i m6-tt)
                               (nth i djvm-tt)))
  :hints (("Goal" :in-theory (enable thread-table-equiv))))


(local 
 (defthm thread-by-id-thread-by-id-replace-thread-entry
   (implies (and (thread-by-id id tt)
                 (wff-thread new)
                 (equal (thread-id new) (thread-id old)))
            (THREAD-BY-id id (replace-thread-table-entry old new tt)))
   :hints (("Goal" :in-theory (e/d (thread-by-id)
                                   (thread-by-id-reduce-to-nth-i))
            :do-not '(generalize)))))

(local 
 (defthm wff-thread-popstack-of-thread
   (wff-thread (popstack-of-thread thread))
   :hints (("Goal" :in-theory (enable popstack-of-thread 
                                      make-thread
                                      thread-set-call-stack
                                      wff-thread)))))

(defthm thread-by-id-thread-by-id-popStack
  (implies (thread-by-id id (thread-table djvm-s))
           (THREAD-BY-id id (THREAD-TABLE (POPSTACK djvm-s))))
  :hints (("Goal" :in-theory (enable popstack thread-by-id))))


(encapsulate () 
 (local (include-book "base-locals"))
 (defun invalidate-category2-value (index s)
  (declare (xargs :guard (and (integerp index)
                              (current-frame-guard s)
                              (wff-call-frame (current-frame s))
                              (<= -1 index)
                              (< index (- (len (locals (current-frame s))) 1))
                              (or (< index 0)
                                  (wff-tagged-value (local-at index s))))))
  (if (< index 0) s
    (if (equal (type-size (tag-of (local-at index s))) 1) s
      (state-set-local-at index '(topx . topx) s)))))


(local 
 (defthm wff-thread-set-local-at-of-thread
   (wff-thread (set-local-at-of-thread index any thread))
   :hints (("Goal" :in-theory (enable set-local-at-of-thread
                                      make-thread
                                      thread-set-call-stack
                                      wff-thread)))))


(defthm thread-by-id-thread-by-id-invalidate-category2-value
  (implies (thread-by-id id (thread-table djvm-s))
           (THREAD-BY-id id (THREAD-TABLE (invalidate-category2-value any djvm-s))))
  :hints (("Goal" :in-theory (enable invalidate-category2-value thread-by-id))))




;;(defthm thread-by-id-reduce-to-nth-i
;;   (implies (thread-by-id id tt)
;;            (equal (thread-by-id id tt)
;;                   (nth (find-index-i-for-id id tt) tt)))
;;   :hints (("Goal" :in-theory (enable thread-by-id))))



(defthm thread-by-id-reduce-to-nth-i-alt
   (implies (and (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6-tt))
                      (bind-free (acl2::replace-occurance-binding2 
                                  'm6::m6-s 'djvm::djvm-s m6-tt 'djvm-tt)
                                 (djvm-tt)))
                 (thread-table-equiv m6-tt djvm-tt)
                 (thread-by-id id djvm-tt))
            (equal (thread-by-id id m6-tt)
                   (nth (find-index-i-for-id id djvm-tt) m6-tt)))
   :hints (("Goal" :use ((:instance  thread-by-id-reduce-to-nth-i
                                     (tt m6-tt))
                         (:instance
                          thread-table-equiv-implies-find-index-by-id-same)
                         (:instance thread-by-id-thread-table-equiv)))))






(defthm thread-table-thread-table-equiv
  (implies (and (syntaxp (and (acl2::found-symbol2 'm6::m6-s m6::m6-s)
                              (equal (acl2::substitue-symbol2 'm6::m6-s
                                                              'djvm::djvm-s
                                                              m6::m6-s)
                                     djvm::djvm-s)))
                (consistent-state djvm::djvm-s)
                (equal (current-thread m6::m6-s)
                       (current-thread djvm::djvm-s))
                (thread-table-equiv (thread-table m6::m6-s)
                                    (thread-table djvm::djvm-s)))
           (thread-table-equiv (thread-table (popStack m6::m6-s))
                               (thread-table (popStack djvm::djvm-s))))
  :hints (("Goal" :in-theory (enable state-equiv popStack))))

;----------------------------------------------------------------------

(local 
 (defthm find-index-for-id-replace-thread-entry
   (implies (and (thread-by-id id tt)
                 (wff-thread new)
                 (equal (thread-id new) (thread-id old)))
            (equal (find-index-i-for-id id (replace-thread-table-entry old new
                                                                       tt))
                   (find-index-i-for-id id tt)))
   :hints (("Goal" :in-theory (e/d (thread-by-id)
                                   (thread-by-id-reduce-to-nth-i))
            :do-not '(generalize)))))



(defthm find-index-i-for-id-no-change-invalidate-value
  (implies (thread-by-id id (thread-table s))
           (equal (FIND-INDEX-I-FOR-ID id (THREAD-TABLE (INVALIDATE-CATEGORY2-VALUE any s)))
                  (find-index-i-for-id id (thread-table s))))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))





;----------------------------------------------------------------------


(defthm collect-thread-id-popStack-no-change
  (equal (COLLECT-THREAD-ID (THREAD-TABLE (POPSTACK DJVM-S)))
         (collect-thread-id (thread-table djvm-s)))
  :hints (("Goal" :in-theory (enable popstack))))



(defthm collect-thread-id-invalidate-value-no-change
  (equal (COLLECT-THREAD-ID (THREAD-TABLE (invalidate-category2-value any djvm-s)))
         (collect-thread-id (thread-table djvm-s)))
  :hints (("Goal" :in-theory (enable popstack))))



(local 
 (defthm len-replace-thread-entry
   (equal (len (replace-thread-table-entry old new tt))
          (len tt))))



(defthm len-thread-table-invalidate-category2-value
  (equal (LEN (THREAD-TABLE (invalidate-category2-value any s)))
         (len (thread-table s)))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))



(defthm len-thread-table-popStack
  (equal (LEN (THREAD-TABLE (popStack s)))
         (len (thread-table s)))
  :hints (("Goal" :in-theory (enable popStack))))

;----------------------------------------------------------------------


(defthm wff-thread-alt-set-local-at-of-thread
  (WFF-THREAD-ALT (SET-LOCAL-AT-OF-THREAD I any th))
  :hints (("Goal" :in-theory (enable set-local-at-of-thread wff-thread-alt))))



(defthm locals-equiv-locals-equiv-update-nth-i
  (implies (locals-equiv m6-locals djvm-locals)
           (locals-equiv (update-nth i (value-of v) m6-locals)
                         (update-nth i v djvm-locals)))
  :hints (("Goal" :in-theory (enable locals-equiv))))


(defthm frame-equiv-frame-equiv-set-locals
  (implies (and (frame-equiv m6-frame djvm-frame)
                (locals-equiv m6-locals djvm-locals))
           (frame-equiv (frame-set-locals (update-nth i (value-of v) m6-locals) m6-frame)
                        (frame-set-locals (update-nth i v djvm-locals) djvm-frame)))
  :hints (("Goal" :in-theory (enable frame-set-operand-stack frame-equiv))))


;; (local 
;;  (skip-proofs 
;;   (defthm frame-equiv-frame-set-locals
;;   (FRAME-EQUIV (FRAME-SET-LOCALS (UPDATE-NTH I (VALUE-OF TAGGED-VALUE)
;;                                              'NIL)
;;                                  'NIL)
;;                (FRAME-SET-LOCALS (UPDATE-NTH I TAGGED-VALUE 'NIL)
;;                                  'NIL)))))

(in-theory (disable wff-frame-alt frame-set-locals))


(defthm locals-frame-set-locals-reduce
  (equal (LOCALS (FRAME-SET-LOCALS locals frame))
         locals)
  :hints (("Goal" :in-theory (enable frame-set-locals))))


(defthm wff-frame-alt-frame-set-locals
  (wff-frame-alt (frame-set-locals locals frame))
  :hints (("Goal" :in-theory (enable wff-frame-alt frame-set-locals))))

;;    (defthm call-stack-equiv-top-frame-equiv
;;       (implies (and (call-stack-equiv m6-cs djvm-cs)
;;                     (consp djvm-cs))
;;                (frame-equiv (top m6-cs) (top djvm-cs)))
;;       :hints (("Goal" :in-theory (enable call-stack-equiv push pop top))))))



(defthm frame-equiv-implies-2
  (implies (frame-equiv m6-frame djvm-frame)
           (locals-equiv (locals m6-frame)
                         (locals djvm-frame)))
  :hints (("Goal" :in-theory (e/d (frame-equiv) ()))))


(defthm thread-entry-equiv-set-local-at-of-thread
  (implies (and (thread-entry-equiv m6::m6-th djvm::djvm-th)
                (equal (value-of tagged-value) value))
           (THREAD-ENTRY-EQUIV (set-local-at-of-thread i value m6::m6-th)
                               (set-local-at-of-thread i tagged-value
                                                       djvm::djvm-th)))
  :hints (("Goal" :in-theory (e/d (set-local-at-of-thread)
                                  (frame-set-locals frame-equiv))
           :cases ((consp (thread-call-stack djvm::djvm-th))))
          ("Subgoal 2" :in-theory (e/d (set-local-at-of-thread
                                        frame-set-locals
                                        wff-frame-alt
                                        frame-equiv)
                                       (call-stack-equiv-consp-not-consp))
           :use ((:instance call-stack-equiv-consp-not-consp
                            (m6-cs (thread-call-stack m6::m6-th))
                            (djvm-cs (thread-call-stack djvm::djvm-th)))))))



;----------------------------------------------------------------------


(local 
 (defthm thread-entry-equiv-implies-2-general-more
   (implies (and (syntaxp (and (acl2::found-symbol2 'm6::m6-s m6-th)
                               (equal (acl2::substitue-symbol2 'm6::m6-s
                                                               'djvm::djvm-s
                                                               m6-th)
                                      djvm-th)))
                 (thread-entry-equiv m6-th djvm-th))
            (call-stack-equiv (thread-call-stack m6-th) (thread-call-stack djvm-th)))
   :hints (("Goal" :in-theory (enable thread-entry-equiv)))))


;; (local 
;;  (defthm thread-call-stack-equiv-implies-top-frame-equiv
;;    (implies (and (call-stack-equiv m6-cs djvm-cs)
;;                  (consp djvm-cs))
;;             (frame-equiv (top m6-cs) (top djvm-cs)))))

(local 
 (defthm untag-opstack-implies-top-stack-equal-value-lemma
   (implies (equal (untag-opstack opstack2) opstack1)
            (equal (value-of (top opstack2)) (top opstack1)))
   :hints (("Goal" :in-theory (enable value-of top untag-value)))))

(local 
 (defthm operand-stack-frame-set-locals
   (equal (operand-stack (frame-set-locals locals frame))
          (operand-stack frame))
   :hints (("Goal" :in-theory (enable frame-set-locals)))))


(local 
 (defthm untag-opstack-implies-top-stack-equal-value
   (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6-frame))
                 (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
                                                              'djvm::djvm-s
                                                              m6-frame
                                                              'djvm-frame)
                            (djvm-frame))
                 (frame-equiv  m6-frame djvm-frame))
            (equal (top (operand-stack m6-frame)) (value-of (top (operand-stack djvm-frame)))))
   :hints (("Goal" :in-theory (e/d (frame-equiv) (untag-opstack))
            :use ((:instance untag-opstack-implies-top-stack-equal-value-lemma
                             (opstack2 (operand-stack djvm-frame))
                             (opstack1 (operand-stack m6-frame))))))))

(local (in-theory (disable untag-opstack-implies-top-stack-equal-value-lemma)))


(defthm state-equiv-implies-topStack
  (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6::m6-s))
                (bind-free (acl2::replace-occurance-binding2 
                            'm6::m6-s 'djvm::djvm-s
                            m6::m6-s 'djvm-s))
                (state-equiv m6::m6-s djvm::djvm-s)
                (consistent-state djvm::djvm-s))
           (equal (topStack m6::m6-s)
                  (value-of (topStack djvm::djvm-s))))
  :hints (("Goal" :in-theory (e/d (topStack current-frame)
                                  (topframe-normalization))
           :cases ((consp (thread-call-stack (NTH (FIND-INDEX-I-FOR-ID (CURRENT-THREAD DJVM-S)
                                                      (THREAD-TABLE DJVM-S))
                                                           (THREAD-TABLE djvm::djvm-S))))))
          ("Subgoal 2" :in-theory (e/d (wff-frame-alt
                                        current-frame
                                        frame-equiv)
                                       (topframe-normalization 
                                        call-stack-equiv-consp-not-consp))
           :use ((:instance call-stack-equiv-consp-not-consp
                            (m6-cs (thread-call-stack (NTH (FIND-INDEX-I-FOR-ID (CURRENT-THREAD DJVM-S)
                                                      (THREAD-TABLE DJVM-S))
                                                           (THREAD-TABLE m6::m6-S))))
                            (djvm-cs (thread-call-stack (NTH (FIND-INDEX-I-FOR-ID (CURRENT-THREAD DJVM-S)
                                                      (THREAD-TABLE DJVM-S))
                                                           (THREAD-TABLE djvm::djvm-S)))))))))
                   


;----------------------------------------------------------------------





;;  (THREAD-ENTRY-EQUIV
;;   M6::M6-TH
;;   (THREAD-SET-CALL-STACK
;;    (PUSH
;;     (FRAME-SET-LOCALS (UPDATE-NTH I '(TOPX . TOPX)
;;                                   (LOCALS (TOP (THREAD-CALL-STACK DJVM-TH))))
;;                       (TOP (THREAD-CALL-STACK DJVM-TH)))
;;     (POP (THREAD-CALL-STACK DJVM-TH)))

(local 
 (defthm wff-thread-alt-and-consp-reduce
   (implies (and (wff-thread-alt m6::m6-th)
                 (consp (thread-call-stack m6::m6-th)))
            (EQUAL (THREAD-SET-CALL-STACK (PUSH (TOP (THREAD-CALL-STACK M6::M6-TH))
                                                (POP (THREAD-CALL-STACK M6::M6-TH)))
                                          M6::M6-TH)
                   M6::M6-TH))
   :hints (("Goal" :in-theory (enable push wff-thread-alt thread-set-call-stack top pop)))))
            

(defthm call-stack-equiv-consp-consp
   (implies (and (call-stack-equiv m6-cs djvm-cs)
                 (consp djvm-cs))
            (consp m6-cs))
   :hints (("Goal" :in-theory (enable call-stack-equiv push pop top))))


(local 
 (defthm thread-entry-equiv-implies-wff-thread-alt
   (implies (thread-entry-equiv m6-th djvm-th)
            (wff-thread-alt m6-th))
   :hints (("Goal" :in-theory (enable thread-set-call-stack 
                                      wff-thread-alt thread-entry-equiv)))
   :rule-classes :forward-chaining))
   

(local 
 (defthm thread-entry-equiv-implies-wff-thread-alt-back
   (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-th m6-th))
                 (bind-free (acl2::replace-occurance-binding2 'm6::m6-th
                                                              'djvm::djvm-th
                                                              m6-th
                                                              'djvm-th)
                            (djvm-th))
                 (thread-entry-equiv m6-th djvm-th))
            (wff-thread-alt m6-th))
   :hints (("Goal" :in-theory (enable thread-set-call-stack 
                                      wff-thread-alt thread-entry-equiv)))))


;; (local 
;;  (defthm wff-thread-alt-thead-set-call-stack
;;    (wff-thread-alt (thread-set-call-stack cs th))
;;    :hints (("Goal" :in-theory (enable thread-set-call-stack)))))
 
(local (in-theory (disable frame-aux)))

(defthm frame-equiv-implies-wff-frame-alt
  (implies (frame-equiv m6-frame djvm-frame)
           (wff-frame-alt m6-frame))
  :hints (("Goal" :in-theory (enable frame-equiv 
                                     frame-set-operand-stack
                                     frame-set-locals wff-frame-alt)))
  :rule-classes :forward-chaining)


(defthm thread-entry-equiv-call-stack-equiv-f
  (implies (thread-entry-equiv m6-th djvm-th)
           (call-stack-equiv (thread-call-stack m6-th) (thread-call-stack djvm-th)))
  :hints (("Goal" :in-theory (enable thread-entry-equiv)))
  :rule-classes :forward-chaining)



(defthm call-stack-equiv-frame-equiv-f
  (implies (and (call-stack-equiv m6-cs djvm-cs)
                (consp djvm-cs))
           (frame-equiv (top m6-cs) (top djvm-cs)))
  :hints (("Goal" :in-theory (enable call-stack-equiv top)))
  :rule-classes :forward-chaining)



(defthm locals-equiv-locals-equiv-update-nth-i-specific
  (implies (and (locals-equiv m6-locals djvm-locals)
                (integerp i)
                (<= 0 i)
                (< i (len djvm-locals)))
           (locals-equiv m6-locals 
                         (update-nth i '(topx . topx) djvm-locals)))
  :hints (("Goal" :in-theory (enable locals-equiv))))


(defthm sync-obj-rec-frame-set-locals
  (equal (SYNC-OBJ-REF
          (FRAME-SET-LOCALS locals frame))
         (sync-obj-ref frame))
  :hints (("Goal" :in-theory (enable frame-set-locals))))

(defthm resume-pc-frame-set-locals
  (equal (resume-pc
          (FRAME-SET-LOCALS locals frame))
         (resume-pc frame))
  :hints (("Goal" :in-theory (enable frame-set-locals))))


(local 
 (defthm expanding-m6-th
  (IMPLIES
   (AND   (CONSP (THREAD-CALL-STACK DJVM-TH))
          (THREAD-ENTRY-EQUIV M6::M6-TH DJVM-TH)
          (<= 0 I)
          (< I
             (LEN (LOCALS (TOP (THREAD-CALL-STACK DJVM-TH)))))
          (INTEGERP I))
   (THREAD-ENTRY-EQUIV 
    (THREAD-SET-CALL-STACK (PUSH (TOP (THREAD-CALL-STACK M6::M6-TH))
                                 (POP (THREAD-CALL-STACK M6::M6-TH)))
                           M6::M6-TH)
    (SET-LOCAL-AT-OF-THREAD I '(TOPX . TOPX)
                            DJVM-TH)))
  :hints (("Goal" :in-theory (e/d (set-local-at-of-thread)
                                  (wff-thread-alt-and-consp-reduce))))))


(local 
 (defthm thread-entry-equiv-set-local-at-of-thread-topx-topx
   (implies (and (thread-entry-equiv m6::m6-th djvm::djvm-th)
                (<= 0 i)
                (< i (len (locals (top (thread-call-stack djvm::djvm-th)))))
                (integerp i))
           (THREAD-ENTRY-EQUIV m6::m6-th 
                               (set-local-at-of-thread i '(topx . topx)
                                                       djvm::djvm-th)))
  :hints (("Goal" :in-theory (e/d (set-local-at-of-thread)
                                  (frame-set-locals frame-equiv))
           :cases ((consp (thread-call-stack djvm::djvm-th))))
          ("Subgoal 2" :in-theory (e/d (set-local-at-of-thread
                                        frame-set-locals
                                        wff-frame-alt
                                        frame-equiv)
                                       (wff-thread-alt-and-consp-reduce
                                        call-stack-equiv-consp-not-consp))
           :use ((:instance call-stack-equiv-consp-not-consp
                            (m6-cs (thread-call-stack m6::m6-th))
                            (djvm-cs (thread-call-stack djvm::djvm-th)))))
          ("Subgoal 1" :cases ((equal m6::m6-th
                                      (thread-set-call-stack 
                                       (push (top (thread-call-stack m6::m6-th))
                                             (pop (thread-call-stack
                                                   m6::m6-th)))
                                       m6::m6-th))))
          ("Subgoal 1.2" :use ((:instance wff-thread-alt-and-consp-reduce)
                               (:instance call-stack-equiv-consp-consp 
                                          (m6-cs (thread-call-stack m6::m6-th))
                                          (djvm-cs (thread-call-stack
                                                    djvm::djvm-th)))))
          ("Subgoal 1.1" :use ((:instance wff-thread-alt-and-consp-reduce)
                               (:instance expanding-m6-th))))))

(local 
 (defthm equal-replace-thread-table-entry
   (equal (REPLACE-THREAD-TABLE-ENTRY same same M6-TT)
          m6-tt)))

(local 
 (defthm thread-table-equiv-implies-replace-i-th-specific
   (implies (and (thread-table-equiv m6-tt djvm-tt)
                 (unique-id-thread-table m6-tt)
                 (unique-id-thread-table djvm-tt)
                 (integerp i)
                 (<= 0 i)
                 (< i (len m6-tt))
                 (< i (len djvm-tt))
                 (thread-entry-equiv (nth i m6-tt) djvm-th))                
            (thread-table-equiv m6-tt 
                                (replace-thread-table-entry
                                 (nth i djvm-tt)
                                 djvm-th
                                 djvm-tt)))
   :hints (("Goal" :use ((:instance thread-table-equiv-implies-replace-i-th
                                    (m6-th (nth i m6-tt))))))))


(defthm thread-table-equiv-invalidate-category2-value
  (implies (and (thread-table-equiv (thread-table m6::m6-s) (thread-table
                                                             djvm::djvm-s))
                (equal (current-thread m6::m6-s) (current-thread djvm::djvm-s))
                (consistent-state djvm::djvm-s)
                (integerp i)
                (<= -1 i)
                (< i (- (len (locals (current-frame djvm::djvm-s))) 1)))
           (THREAD-TABLE-EQUIV (THREAD-TABLE m6::m6-s)
                               (THREAD-TABLE (INVALIDATE-CATEGORY2-VALUE i
                                                                         djvm::djvm-s))))
  :hints (("Goal" :in-theory (e/d (invalidate-category2-value
                                   current-frame)
                                  (topframe-normalization)))))

 

;----------------------------------------------------------------------


(defthm class-table-popStack-reduce
  (EQUAL (CLASS-TABLE (POPSTACK s))
         (class-table s))
  :hints (("Goal" :in-theory (enable popstack))))


(defthm error-flag-state-set-local-at
   (equal (ERROR-FLAG (STATE-SET-LOCAL-AT i v s))
          (error-flag s))
   :hints (("Goal" :in-theory (enable state-set-local-at))))

(defthm error-flag-PopStack
   (equal (ERROR-FLAG (popStack s))
          (error-flag s))
   :hints (("Goal" :in-theory (enable popStack))))

(defthm error-flag-invalidate-category2-value
   (equal (ERROR-FLAG (invalidate-category2-value any s))
          (error-flag s))
   :hints (("Goal" :in-theory (enable invalidate-category2-value))))


;----------------------------------------------------------------------

;;
;; Tue Aug  2 13:56:42 2005
;;
;; Similiar theorems for pushStack!! 
;;

;; 


;; ;;             (frame-equiv (top m6-cs) (top djvm-cs)))))

(local 
 (defthm locals-equiv-nth-i-value-is-value-of
   (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6-locals))
                 (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
                                                              'djvm::djvm-s
                                                              m6-locals
                                                              'djvm-locals)
                            (djvm-locals))
                 (locals-equiv m6-locals djvm-locals)
                 (not (equal (tag-of (nth i djvm-locals)) 'topx)))
            (equal (nth i m6-locals) (value-of (nth i djvm-locals))))
   :hints (("Goal" :in-theory (enable value-of top locals-equiv)))))




(local 
 (defthm consistent-thread-entry-implies-if-found-then-consistent-entry
   (implies (and (consistent-thread-entries tt cl hp)
                 (thread-by-id id tt))
            (consistent-thread-entry (thread-by-id id tt) cl hp))
   :hints (("Goal" :in-theory (e/d (thread-by-id)
                                   (consistent-thread-entry))))))

(local 
 (defthm consistent-thread-entry-implies-if-found-then-consistent-entry-specific
   (implies (and (consistent-thread-entries tt cl hp)
                 (thread-by-id id tt))
            (consistent-thread-entry (nth (find-index-i-for-id id tt)
                                          tt)
                                     cl hp))
   :hints (("Goal" :in-theory (e/d (thread-by-id) (consistent-thread-entry))))))



(local 
 (defthm consistent-state-implies-consistent-thread-entry-f
   (implies (consistent-state s)
            (consistent-thread-entry 
             (nth (find-index-i-for-id (current-thread s)
                                       (thread-table s))
                  (thread-table s))
             (instance-class-table s)
             (heap s)))
   :hints (("Goal" :in-theory (e/d (consistent-state)
                                   (consistent-thread-entry-implies-if-found-then-consistent-entry-specific
                                    consistent-thread-entry))
            :use ((:instance
                   consistent-thread-entry-implies-if-found-then-consistent-entry-specific
                   (tt (thread-table s))
                   (cl (instance-class-table s))
                   (hp (heap s))
                   (id (current-thread s))))))
   :rule-classes :forward-chaining))


(local 
 (defthm consistent-state-implies-consp-djvm-cs-f
   (implies (consistent-state s)
            (consp (thread-call-stack (nth (find-index-i-for-id 
                                            (current-thread s)
                                            (thread-table s))
                                           (thread-table s)))))
   :hints (("Goal" :in-theory (enable consistent-state)))
   :rule-classes :forward-chaining))

                 



(local 
 (defthm state-equiv-implies-frame-equiv-current-frame
   (implies (and (state-equiv m6::m6-s djvm::djvm-s)
                 (consistent-state djvm::djvm-s))
            (frame-equiv (current-frame m6::m6-s)
                         (current-frame djvm::djvm-s)))
   :hints (("Goal" :in-theory (e/d (current-frame)
                                   (topframe-normalization))))))


(defthm state-equiv-implies-equal-local-equal
  (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6::m6-s))
                (bind-free (acl2::replace-occurance-binding2 'm6::m6-s 
                                                             'djvm::djvm-s
                                                             m6::m6-s 
                                                             'djvm-s)
                           (djvm::djvm-s))
                (not (equal (tag-of (NTH i (LOCALS (CURRENT-FRAME
                                                    djvm::djvm-s)))) 'topx))
                (consistent-state djvm::djvm-s)
                (state-equiv m6::m6-s djvm::djvm-s))
           (EQUAL (NTH i (LOCALS (CURRENT-FRAME m6::m6-s)))
                  (VALUE-OF (NTH i (LOCALS (CURRENT-FRAME djvm::djvm-s)))))))


;; >L            (DEFUN UNTAG-OPSTACK (OPSTACK)
;;                      (IF (NOT (CONSP OPSTACK))
;;                          NIL
;;                          (CONS (UNTAG-VALUE (CAR OPSTACK))
;;                                (UNTAG-OPSTACK (CDR OPSTACK)))))

;;
;; this definition make untag-opstack not equal!! 
;; 
;; Tue Aug  2 15:28:08 2005
;;

(local 
 (defthm untag-opstack-push-reduce
  (implies (equal opstack (untag-opstack tagged-opstack))
           (equal (UNTAG-OPSTACK (PUSH tv tagged-opstack))
                  (push (value-of tv) opstack)))
  :hints (("Goal" :in-theory (enable untag-opstack value-of
                                     push untag-value)))))

;; (local 
;;  (defthm untag-opstack-push-reduce
;;   (implies (and (syntaxp (acl2::found-symbol2 'djvm::djvm-th tagged-opstack))
;;                 (bind-free (acl2::replace-occurance-binding2 'djvm::djvm-th
;;                                                              'm6::m6-th
;;                                                              tagged-opstack
;;                                                              'opstack)
;;                            (opstack))
;;                 (equal opstack (untag-opstack tagged-opstack)))
;;            (equal (UNTAG-OPSTACK (PUSH tv tagged-opstack))
;;                   (push (value-of tv) opstack)))
;;   :hints (("Goal" :in-theory (enable untag-opstack value-of
;;                                      push untag-value))))))

(local 
 (defthm untag-opstack-push-reduce-specific
   (equal (UNTAG-OPSTACK (PUSH tv nil))
          (push (value-of tv) nil))
   :hints (("Goal" :in-theory (enable untag-opstack value-of
                                      push untag-value)))))




(local 
 (defthm frame-equiv-implies-operand-stack-is-untag-opstack
   (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-th m6-frame))
                 (bind-free (acl2::replace-occurance-binding2 'm6::m6-th
                                                              'djvm::djvm-th
                                                              m6-frame
                                                              'djvm-frame)
                            (djvm-frame))
                 (frame-equiv  m6-frame djvm-frame))
            (equal (operand-stack m6-frame) (untag-opstack (operand-stack djvm-frame))))
   :hints (("Goal" :in-theory (e/d (frame-equiv) (untag-opstack))))))


(local 
 (defthm wff-frame-alt-frame-set-opstack
   (WFF-FRAME-ALT
    (FRAME-SET-OPERAND-STACK any frame))
   :hints (("Goal" :in-theory (enable frame-set-operand-stack
                                      wff-frame-alt)))))


(local 
 (defthm frame-equiv-implies-specific
  (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-frame m6-frame))
                (bind-free (acl2::replace-occurance-binding2 'm6::m6-frame
                                                             'djvm::djvm-frame
                                                             m6-frame
                                                             'djvm-frame)
                           (djvm-frame))
                (frame-equiv m6-frame djvm-frame))
           (and (equal (return-pc m6-frame) (return-pc djvm-frame))
                (equal (operand-stack m6-frame) (untag-opstack (operand-stack djvm-frame)))
                (equal (method-ptr m6-frame) (method-ptr djvm-frame))
                (equal (sync-obj-ref m6-frame) (sync-obj-ref djvm-frame))
                (equal (resume-pc m6-frame) (resume-pc djvm-frame))))
  :hints (("Goal" :in-theory (e/d (frame-equiv frame-set-operand-stack
                                               frame-set-locals) ())))))



;; (defthm frame-equiv-implies-2
;;   (implies (frame-equiv m6-frame djvm-frame)
;;            (locals-equiv (locals m6-frame)
;;                          (locals djvm-frame)))
;;   :hints (("Goal" :in-theory (e/d (frame-equiv) ()))))

(local 
 (defthm frame-equiv-frame-equiv-push
   (implies (and (frame-equiv m6::m6-frame djvm::djvm-frame)
                (equal (value-of tv) v))
           (FRAME-EQUIV
            (FRAME-SET-OPERAND-STACK (push v (OPERAND-STACK
                                              m6::m6-frame)) m6::m6-frame)
            (FRAME-SET-OPERAND-STACK (PUSH tv (operand-stack djvm::djvm-frame))
                                     djvm::djvm-frame)))))


(local 
 (defthm thread-entry-equiv-push-stack-of-thread
  (implies (and (thread-entry-equiv m6::m6-th djvm::djvm-th)
                (equal value (value-of tagged-value)))
           (THREAD-ENTRY-EQUIV (push-stack-of-thread value m6::m6-th)
                               (push-stack-of-thread tagged-value djvm::djvm-th)))
  :hints (("Goal" :in-theory (e/d (push-stack-of-thread)
                                  (untag-opstack frame-equiv))
           :cases ((consp (thread-call-stack djvm::djvm-th))))
          ("Subgoal 2" :in-theory (e/d (push-stack-of-thread
                                        frame-equiv
                                        frame-set-locals
                                        frame-set-operand-stack
                                        thread-set-call-stack)
                                       (untag-opstack
                                        call-stack-equiv-consp-not-consp))
           :use ((:instance call-stack-equiv-consp-not-consp
                            (m6-cs (thread-call-stack m6::m6-th))
                            (djvm-cs (thread-call-stack djvm::djvm-th))))))))


(defthm thread-table-thread-table-equiv-pushStack
  (implies (and (syntaxp (and (acl2::found-symbol2 'm6::m6-s m6::m6-s)
                              (equal (acl2::substitue-symbol2 'm6::m6-s
                                                              'djvm::djvm-s
                                                              m6::m6-s)
                                     djvm::djvm-s)))
                (consistent-state djvm::djvm-s)
                (equal (current-thread m6::m6-s)
                       (current-thread djvm::djvm-s))
                (equal value (value-of tagged-value))
                (thread-table-equiv (thread-table m6::m6-s)
                                    (thread-table djvm::djvm-s)))
           (thread-table-equiv (thread-table (pushStack value m6::m6-s))
                               (thread-table (pushStack tagged-value djvm::djvm-s))))
  :hints (("Goal" :in-theory (enable state-equiv popStack))))





(defthm class-table-pushStack-no-change
  (equal (class-table (pushStack any s))
         (class-table s))
  :hints (("Goal" :in-theory (enable state-set-thread-table pushStack))))


(defthm env-pushStack-no-change
  (equal (env (pushStack any s))
         (env  s))
  :hints (("Goal" :in-theory (enable state-set-thread-table pushStack))))

(defthm error-flag-pushStack-no-change
  (equal (error-flag (pushStack any s))
         (error-flag s))
  :hints (("Goal" :in-theory (enable state-set-thread-table pushStack))))


(defthm aux-pushStack-no-change
  (equal (aux (pushStack any s))
         (aux s))
  :hints (("Goal" :in-theory (enable state-set-thread-table pushStack))))

;----------------------------------------------------------------------

(local (include-book "base-load-class-normalize"))


;; (local 
;;  (defthm wff-state-alt-load_class_x
;;    (implies (wff-state-alt s)
;;             (wff-state-alt (load_class_x any s seen mode)))
;;    :hints (("Goal" :in-theory (enable resolveclassreference wff-state-alt)))))

;; (local 
;;  (defthm wff-state-alt-resolveClassReference
;;    (implies (wff-state-alt s)
;;             (wff-state-alt (resolveclassreference any s)))
;;    :hints (("Goal" :in-theory (enable load_class resolveclassreference wff-state-alt)))))


(skip-proofs 
 (defthm state-equiv-implies-state-equiv-resolveClassReference
   (implies (state-equiv m6::m6-s djvm::djvm-s)
            (STATE-EQUIV
             (RESOLVECLASSREFERENCE any M6::M6-S)
             (RESOLVECLASSREFERENCE any djvm::DJVM-S)))))


;----------------------------------------------------------------------

(defthm state-equiv-implies-no-fatal-error
  (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6::m6-s))
                (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
                                                             'djvm::djvm-s m6::m6-s
                                                             'djvm-s)
                           (djvm::djvm-s))
                (state-equiv m6::m6-s djvm::djvm-s))
           (equal (no-fatal-error? m6::m6-s)
                  (no-fatal-error? djvm::djvm-s)))
  :hints (("Goal" :in-theory (enable no-fatal-error?))))

;----------------------------------------------------------------------

(defthm state-equiv-implies-pending-exceptions
  (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6::m6-s))
                (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
                                                             'djvm::djvm-s m6::m6-s
                                                             'djvm-s)
                           (djvm::djvm-s))
                (state-equiv m6::m6-s djvm::djvm-s))
           (equal (pending-exception m6::m6-s)
                  (pending-exception djvm::djvm-s)))
  :hints (("Goal" :in-theory (enable pending-exception))))



(skip-proofs 
 (defthm state-equiv-implies-state-equiv-raise-exception
   (implies (state-equiv m6::m6-s djvm::djvm-s)
            (STATE-EQUIV
             (jvm::raise-exception any m6::m6-s)
             (raise-exception any djvm::djvm-s)))))



(skip-proofs 
 (defthm state-equiv-implies-state-equiv-get-array-class
   (implies (state-equiv m6::m6-s djvm::djvm-s)
            (STATE-EQUIV
             (getArrayClass any m6::m6-s)
             (getArrayClass any djvm::djvm-s)))))



(skip-proofs 
 (defthm state-equiv-implies-state-equiv-update-trace
   (implies (state-equiv m6::m6-s djvm::djvm-s)
            (STATE-EQUIV
             (update-trace any m6::m6-s)
             (update-trace any djvm::djvm-s)))))



(skip-proofs 
 (defthm state-equiv-implies-state-equiv-set-heap
   (implies (state-equiv m6::m6-s djvm::djvm-s)
            (STATE-EQUIV
             (state-set-heap any m6::m6-s)
             (state-set-heap any djvm::djvm-s)))))




(defthm state-equiv-implies-heap-equal
  (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6::m6-s))
                (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
                                                             'djvm::djvm-s m6::m6-s
                                                             'djvm-s)
                           (djvm::djvm-s))
                (state-equiv m6::m6-s djvm::djvm-s))
           (equal (heap m6::m6-s)
                  (heap djvm::djvm-s)))
  :hints (("Goal" :in-theory (enable pending-exception))))


(skip-proofs 
 (defthm state-equiv-implies-build-an-array-instance
   (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6::m6-s))
                (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
                                                             'djvm::djvm-s m6::m6-s
                                                             'djvm-s)
                           (djvm::djvm-s))
                (state-equiv m6::m6-s djvm::djvm-s))
           (equal (car (build-an-array-instance basetype value m6::m6-s))
                  (car (build-an-array-instance basetype value djvm::djvm-s))))
  :hints (("Goal" :in-theory (enable pending-exception)))))



(skip-proofs 
 (defthm state-equiv-implies-state-equiv-set-pc
   (implies (state-equiv m6::m6-s djvm::djvm-s)
            (STATE-EQUIV
             (state-set-pc any m6::m6-s)
             (state-set-pc any djvm::djvm-s)))))



(skip-proofs 
 (defthm state-equiv-implies-state-popStack
   (implies (state-equiv m6::m6-s djvm::djvm-s)
            (STATE-EQUIV
             (popStack  m6::m6-s)
             (popStack djvm::djvm-s)))))


(defthm value-of-tag-REF-is-same
  (equal (value-of (tag-REF v))
         v)
  :hints (("Goal" :in-theory (enable tag-REF tag value-of))))


(skip-proofs 
 (defthm state-equiv-implies-state-pushStack
   (implies (and (state-equiv m6::m6-s djvm::djvm-s)
                 (equal (value-of v2) v1))
            (STATE-EQUIV
             (pushStack v1   m6::m6-s)
             (pushStack v2 djvm::djvm-s)))))

;----------------------------------------------------------------------


(include-book "base-consistent-state")

(in-theory (disable m6::check-array))

(skip-proofs 
 (defthm m6-check-array-normalize-to-djvm-check-array
   (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6::m6-s))
                 (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
                                                              'djvm::djvm-s m6::m6-s
                                                              'djvm::djvm-s)
                            (djvm::djvm-s))
                 (state-equiv m6::m6-s djvm::djvm-s))
            (equal (m6::check-array aref index m6::m6-s)
                   (djvm::check-array aref index djvm::djvm-s)))))


(skip-proofs 
 (defthm REF-reduce-to-value-of
   (equal (rREF v)
          (value-of v))))


(in-theory (disable m6::element-at-array))

(skip-proofs 
 (defthm m6-element-at-array-normalize-to-djvm-element-at-array
   (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6::m6-s))
                 (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
                                                              'djvm::djvm-s m6::m6-s
                                                              'djvm::djvm-s)
                            (djvm::djvm-s))
                 (state-equiv m6::m6-s djvm::djvm-s))
            (equal (m6::element-at-array index aref  m6::m6-s)
                   (djvm::element-at-array index aref djvm::djvm-s)))))

(skip-proofs 
 (defthm value-of-tag-is-v
   (equal (value-of (tag v type)) v)))



(skip-proofs 
 (defthm state-equiv-implies-state-isAssignableTo-test
   (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6::m6-s))
                 (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
                                                              'djvm::djvm-s m6::m6-s
                                                              'djvm::djvm-s)
                            (djvm::djvm-s)) 
                 (state-equiv m6::m6-s djvm::djvm-s))
            (equal (CAR (ISASSIGNABLETO typ1 typ2 m6::m6-s))
                   (CAR (ISASSIGNABLETO typ1 typ2 djvm::djvm-s))))))


(in-theory (disable set-element-at-array))


(skip-proofs  
 (defthm state-equiv-state-equiv-set-element-at-array
   (implies (state-equiv m6::m6-s djvm::djvm-s)
            (state-equiv (set-element-at-array index value aref m6::m6-s)
                         (set-element-at-array index value aref djvm::djvm-s)))))
                         


(skip-proofs 
 (defthm binding-value-of-deref2-normalize
   (equal (binding (value-of v) hp)
          (deref2 v hp))))



(skip-proofs 
 (defthm state-equiv-implies-state-lookupfield
   (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6::m6-s))
                 (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
                                                              'djvm::djvm-s m6::m6-s
                                                              'djvm::djvm-s)
                            (djvm::djvm-s)) 
                 (state-equiv m6::m6-s djvm::djvm-s))
            (equal (LOOKUPFIELD fieldptr m6::m6-s)
                   (lookupfield fieldptr djvm::djvm-s)))))



(skip-proofs 
 (defthm state-equiv-implies-state-class-table
   (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6::m6-s))
                 (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
                                                              'djvm::djvm-s m6::m6-s
                                                              'djvm::djvm-s)
                            (djvm::djvm-s))
                 (state-equiv m6::m6-s djvm::djvm-s))
            (equal (CLASS-TABLE M6::M6-S)
                   (class-table djvm::djvm-s)))))


(in-theory (disable fatalSlotError))



(skip-proofs 
 (defthm state-equiv-implies-state-fatalSlotError
   (implies (state-equiv m6::m6-s djvm::djvm-s)
            (state-equiv (fatalSlotError err m6::m6-s)
                         (fatalSlotError err djvm::djvm-s)))))





(skip-proofs 
 (defthm state-equiv-implies-state-pushStack-specific
   (implies (state-equiv m6::m6-s djvm::djvm-s)
            (STATE-EQUIV
             (pushStack 'topx   m6::m6-s)
             (pushStack '(topx . topx) djvm::djvm-s)))))



(skip-proofs 
 (defthm state-equiv-implies-m6-get-field-equal
   (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6::m6-s))
                 (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
                                                              'djvm::djvm-s m6::m6-s
                                                              'djvm::djvm-s)
                            (djvm::djvm-s))
                 (state-equiv m6::m6-s djvm::djvm-s))
            (equal (m6-getfield classname fieldname aref M6::M6-S)
                   (m6-getfield classname fieldname aref djvm::djvm-s)))))


(in-theory (disable STATE-SET-PENDING-EXCEPTION-SAFE))


(skip-proofs 
 (defthm state-equiv-implies-state-set-pending-execption-safe
   (implies (state-equiv m6::m6-s djvm::djvm-s)
            (state-equiv (state-set-pending-exception-safe ex m6::m6-s)
                         (state-set-pending-exception-safe ex djvm::djvm-s)))))



(skip-proofs
 (defthm pending-exception-state-set-pending-exception
   (equal (pending-exception (state-set-pending-exception-safe ex s))
          ex)))

;;; Sat Aug  6 01:16:23 2005  export this!! 


;; (defthm locals-equiv-nth-i-value-is-value-of-specific
;;   (implies (and (syntaxp (acl2::found-symbol2 'm6::m6-s m6-frame))
;;                 (bind-free (acl2::replace-occurance-binding2 'm6::m6-s
;;                                                              'djvm::djvm-s
;;                                                              m6-frame
;;                                                              'djvm-frame)
;;                            (djvm-frame))
;;                 (frame-equiv m6-frame djvm-frame)
;;                 (not (equal (tag-of (nth i (locals djvm-frame))) 'topx)))
;;            (equal (nth i (locals m6-frame)) (value-of (nth i (locals djvm-frame)))))
;;   :hints (("Goal" :in-theory (enable value-of top frame-equiv))))


;;; Tue Aug  2 17:47:50 2005
