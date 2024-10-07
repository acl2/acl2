(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")
(include-book "base-locals")



(defthm wff-call-frame-preserved
  (implies (and (wff-call-frame frame)
                (equal (locals frame) locals))
           (wff-call-frame (frame-set-locals (update-nth i v locals) frame)))
  :hints (("Goal" :in-theory (enable wff-call-frame make-frame
                                     return-pc operand-stack locals
                                     method-ptr sync-obj-ref resume-pc
                                     ))))


(defthm wff-state-state-set-local-at
  (implies (wff-state s)
           (WFF-STATE (STATE-SET-LOCAL-AT i v s)))
  :hints (("Goal" :in-theory (enable state-set-local-at))))


(defthm current-thread-state-set-local-at
  (equal (current-thread (state-set-local-at i v s))
         (current-thread s))
  :hints (("Goal" :in-theory (enable state-set-local-at))))


(defthm pc-state-set-local-at
  (equal  (pc (state-set-local-at i v s))
          (pc  s))
  :hints (("Goal" :in-theory (enable state-set-local-at))))


(defthm consistent-state-pc-integerp-f
  (implies (consistent-state s)
           (integerp (pc s)))
  :hints (("Goal" :in-theory (enable wff-state consistent-state)))
  :rule-classes :forward-chaining)


(defthm thread-table-state-set-local-at-is
  (equal (THREAD-TABLE (STATE-SET-LOCAL-AT i v s))
         (replace-thread-table-entry (thread-by-id (current-thread s) 
                                                   (thread-table s))
                                     (SET-LOCAL-AT-OF-THREAD
                                      i v (thread-by-id (current-thread s) 
                                                   (thread-table s)))
                                     (thread-table s)))
  :hints (("Goal" :in-theory (enable state-set-local-at))))


(defthm wff-thread-set-local-at-of-thread
  (implies (wff-thread thread)
           (WFF-THREAD (SET-LOCAL-AT-OF-THREAD i v thread))))


(defthm thread-call-stack-set-local-at-of-thread
  (equal (THREAD-CALL-STACK
          (SET-LOCAL-AT-OF-THREAD i v thread))
         (push (frame-set-locals (update-nth i v (locals (top (thread-call-stack
                                                              thread))))
                                 (top (thread-call-stack thread)))
               (pop (thread-call-stack thread))))
  :hints (("Goal" :in-theory (e/d (set-local-at-of-thread)
                                  ()))))


(defthm current-frame-after-set-local-is
  (implies (consistent-state s)
           (equal (current-frame (state-set-local-at i v s))
                  (frame-set-locals (UPDATE-NTH i v (locals (current-frame s)))
                                    (current-frame s))))
  :hints (("Goal" :in-theory (enable current-frame))))


(defthm operand-stack-frame-set-locals
  (equal (OPERAND-STACK (FRAME-SET-LOCALS locals frame))
         (operand-stack frame))
  :hints (("Goal" :in-theory (enable frame-set-locals))))



(in-theory (disable state-set-local-at frame-set-locals))


;; (defun invalidate-category2-value (index s)
;;   (declare (xargs :guard (and (integerp index)
;;                               (current-frame-guard s)
;;                               (wff-call-frame (current-frame s))
;;                               (<= -1 index)
;;                               (< index (- (len (locals (current-frame s))) 1)))))
;;   (if (< index 0) s
;;     (if (equal (type-size (local-at index s)) 1) s
;;       (state-set-local-at index '(topx . topx) s))))

;; moved to base-locals.lisp!! 

(local (include-book "base-consistent-state-step-definition"))        
(local (include-book "base-consistent-state-step-properties"))

(defthm env-state-set-local-at-no-change
  (equal (ENV (STATE-SET-LOCAL-AT INDEX any s))
         (env s))
  :hints (("Goal" :in-theory (enable state-set-local-at))))

(defthm aux-state-set-local-at-no-change
  (equal (aux (STATE-SET-LOCAL-AT INDEX any s))
         (aux s))
  :hints (("Goal" :in-theory (enable state-set-local-at))))


(defthm class-table-state-set-local-at-no-change
  (equal (class-table (STATE-SET-LOCAL-AT INDEX any s))
         (class-table s))
  :hints (("Goal" :in-theory (enable state-set-local-at))))


(defthm instance-class-table-state-set-local-at-no-change
  (equal (instance-class-table (STATE-SET-LOCAL-AT INDEX any s))
         (instance-class-table s))
  :hints (("Goal" :in-theory (enable state-set-local-at))))

(defthm array-class-table-state-set-local-at-no-change
  (equal (array-class-table (STATE-SET-LOCAL-AT INDEX any s))
         (array-class-table s))
  :hints (("Goal" :in-theory (enable state-set-local-at))))


(defthm heap-state-set-local-at-no-change
  (equal (heap (STATE-SET-LOCAL-AT INDEX any s))
         (heap s))
  :hints (("Goal" :in-theory (enable state-set-local-at))))

(defthm thread-REF-reduce
  (equal (THREAD-REF
          (THREAD-SET-CALL-STACK cs th))
         (thread-ref th))
  :hints (("Goal" :in-theory (enable thread-set-call-stack make-thread))))


(defthm locals-frame-set-locals
  (equal (LOCALS (FRAME-SET-LOCALS locals frame))
         locals)
  :hints (("Goal" :in-theory (enable frame-set-locals))))

(local 
 (defthm update-nth-expand
   (implies (and (syntaxp (quotep (car i)))
                 (< 0 i)
                 (integerp i))
            (equal (update-nth i any l)
                   (cons (car l)
                         (update-nth (- i 1) any (cdr l)))))))


(local 
 (defthm m-1-m-1-m-2
   (equal (+ -1 -1 i)
          (+ -2 i))))

(defthm update-nth-i-segment
  (implies (and (<= 2 i)
                (integerp i))
           (equal (update-nth i any l)
                  (cons (car l)
                        (cons (cadr l)
                              (update-nth (- i 2) any (cddr l)))))))


(defthm not-primitive-type-not-REF-not-consistent-value-x
  (implies (and (NOT (PRIMITIVE-TYPE? (TAG-OF ACL2::LOCALS1)))
                (NOT (EQUAL (TAG-OF ACL2::LOCALS1) 'REF)))
           (not (CONSISTENT-VALUE-X ACL2::LOCALS1 CL HP)))
  :hints (("Goal" :in-theory (enable consistent-value-x consistent-value))))



(defthm consistent-locals-set-topx-still-consistent
  (implies (and (consistent-locals locals cl hp)
                (integerp index)
                (< index (len locals))
                (<= 0 index))
           (CONSISTENT-LOCALS (UPDATE-NTH INDEX '(TOPX . TOPX) locals)
                                          cl hp))
  :hints (("Goal" :in-theory (enable category1)
           :do-not '(generalize)
           :induct (valid-local-index index locals))
          ("Subgoal *1/6" :cases ((< index 2)))))



(defthm sync-obj-rREF-set-locals
  (equal (SYNC-OBJ-REF
          (FRAME-SET-LOCALS locals frame))
         (sync-obj-ref frame))
  :hints (("Goal" :in-theory (enable frame-set-locals))))



(defthm thread-mREF-thread-set-call-stack
  (equal (thread-mREF (thread-set-call-stack cs th))
         (thread-mREF th))
  :hints (("Goal" :in-theory (enable thread-set-call-stack make-thread))))

(in-theory (disable wff-call-frame 
                    METHOD-CODE
                    METHOD-EXISTS?
                    METHOD-MAXLOCALS
                    METHOD-MAXSTACK 
                    METHOD-PTR 
                    SYNC-OBJ-REF
                    VALID-METHOD-PTR VALID-SYNC-OBJ 
                    WFF-CODE                    
                    wff-method-decl abstract-method))

(defthm consistent-thread-entry-implies
  (implies (and (consistent-thread-entry th cl hp)
                (<= 0 index)
                (integerp index)
                (< index (len (locals (top (thread-call-stack th))))))
           (consistent-thread-entry 
            (SET-LOCAL-AT-OF-THREAD INDEX '(TOPX . TOPX) th)
            cl hp))
  :hints (("Goal" :in-theory (e/d (set-local-at-of-thread
                                   wff-invocation-frame)
                                  (THREAD-MREF 
                                   locals
                                   wff-method-decl
                                   wff-call-frame
                                   thread-REF)))))


(defthm out-of-bound-is-nil
  (implies (and (nth i l)
                (integerp i))
           (< i (len l))))


(defthm load-inv-state-set-local-at-no-change
  (implies (loader-inv s)
           (loader-inv (state-set-local-at index any s)))
  :hints (("Goal" :in-theory (enable loader-inv 
                                     no-fatal-error?
                                     state-set-local-at))))



(defthm class-loaded?-inv-state-set-local-at-no-change
  (equal (class-loaded? any (state-set-local-at index any s))
         (class-loaded? any s))
  :hints (("Goal" :in-theory (enable class-loaded?
                                     state-set-local-at))))


(defthm class-loaded?-inv-state-set-local-at-no-change-2
  (implies (class-loaded? any s)
           (class-loaded? any (state-set-local-at index any s)))
  :hints (("Goal" :in-theory (enable class-loaded?
                                     state-set-local-at))))



(defthm consistent-thread-entries-replace-replace
  (implies (and (consistent-thread-entries tt cl hp)
                (consistent-thread-entry new cl hp))
           (consistent-thread-entries 
            (replace-thread-table-entry old 
                                        new tt) cl hp))
  :hints (("Goal" :in-theory (disable consistent-thread-entry))))



(defthm build-immediate-data-guard-state-set-local-at-no-change
  (implies (build-immediate-instance-data-guard c s)
           (build-immediate-instance-data-guard c (STATE-SET-LOCAL-AT INDEX any s)))
  :hints (("Goal" :in-theory (e/d (state-set-local-at) ()))))




(defthm build-a-java-visible-instance-data-guard-state-set-local-at-no-change
  (implies (BUILD-A-JAVA-VISIBLE-INSTANCE-data-GUARD l s)
           (BUILD-A-JAVA-VISIBLE-INSTANCE-data-GUARD l (STATE-SET-LOCAL-AT INDEX any s)))
  :hints (("Goal" :in-theory (e/d (BUILD-A-JAVA-VISIBLE-INSTANCE-DATA-GUARD)
                                  (build-immediate-instance-data-guard)))))


(defthm build-a-java-visible-instance-guard-state-set-local-at-no-change
  (implies (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD
            c s)
           (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD
            c
            (STATE-SET-LOCAL-AT INDEX any s)))
  :hints (("Goal" :in-theory (e/d (build-a-java-visible-instance-guard)
                                  (build-a-java-visible-instance-data-guard)))))


(defthm array-class-table-inv-helper
  (implies (JVM::ARRAY-CLASS-TABLE-INV-HELPER l s)
           (JVM::ARRAY-CLASS-TABLE-INV-HELPER 
            l 
            (STATE-SET-LOCAL-AT INDEX any s)))
  :hints (("Goal" :in-theory (e/d (state-set-local-at class-loaded?) (isClassTerm)))))


(local 
 (defthm invalidate-category2-value-preserve-consistent-state-lemma
   (implies (and (consistent-state s)
                 (integerp index)
                 (< index (len (locals (current-frame s)))))
            (consistent-state-step (invalidate-category2-value index s)))
   :hints (("Goal" :in-theory (e/d (class-loaded?)
                                   (isClassTerm 
                                    consistent-thread-entry))))))



(local 
 (defthm consistent-state-step-implies-consistent-state
   (implies (consistent-state-step s)
            (consistent-state s))
   :hints (("Goal" :in-theory (enable consistent-state)))
   :rule-classes nil))

;; (local 
;;  (defthm invalidate-category2-value-not-integer
;;    (equal (invalidate-category2-value index s)
;;           (invalidate-category2-value (acl2::nfix index) s))
;;    :hints (("Goal" :in-theory (enable state-set-local-at)))))

(defthm invalidate-category2-value-preserve-consistent-state
  (implies (and (consistent-state s)
                (integerp index)
                (< index (len (locals (current-frame s)))))
           (consistent-state (invalidate-category2-value index s)))
  :hints (("Goal" :in-theory (disable consistent-state-step
                                      invalidate-category2-value)
           :use ((:instance consistent-state-step-implies-consistent-state
                            (s (invalidate-category2-value index s)))))))
           

(in-theory (disable invalidate-category2-value wff-inst))






;----------------------------------------------------------------------



(local 
 (defthm thread-by-id-cons-x
   (EQUAL (THREAD-BY-ID (THREAD-ID NEW-THREAD)
                        (CONS NEW-THREAD TT2))
          NEW-THREAD)
   :hints (("Goal" :in-theory (enable thread-by-id)))))

(local 
 (defthm replace-thread-table-entry-not-mem-equal
   (implies (not (mem oldthread tt))
            (equal (thread-by-id any (replace-thread-table-entry oldthread
                                                                 newthread tt))
                   (thread-by-id any tt)))
   :hints (("Goal" :do-not '(generalize)
            :in-theory (enable thread-by-id)))))


(local 
 (defthm thread-by-id-replace-thread-table-entry-any-any
   (implies (equal (thread-id new-thread) id)
            (equal (thread-by-id id 
                                 (replace-thread-table-entry 
                                  (thread-by-id id tt)
                                  new-thread
                                  tt))
                   (if (mem  (thread-by-id id tt) tt)
                       new-thread
                     (thread-by-id id tt))))
   :hints (("Goal" :do-not '(generalize)
            :in-theory (enable thread-by-id)))))


(local 
 (defthm thread-id-make-thread
   (equal (thread-id (make-thread ID PC CALL-STACK S
                         M-REF MDEPTH THREAD-REF))
          id)
   :hints (("Goal" :in-theory (enable thread-id)))))

(local 
 (defthm mem-thread-thread-id
   (implies (and (mem (thread-by-id id tt) tt)
                 (thread-by-id id tt))
            (equal (thread-id (thread-by-id id tt)) id))
   :hints (("Goal" :in-theory (enable thread-by-id thread-id)
            :do-not '(generalize)))))

(local 
 (defthm not-thread-by-id-replace-thread-entry
   (implies (and (not (thread-by-id id tt))
                 (mem nil tt)
                 new-thread
                 (equal  (thread-id new-thread) id))
            (equal (thread-by-id id
                                 (replace-thread-table-entry 
                                  nil
                                  new-thread tt))
                   new-thread))
   :hints (("Goal" :in-theory (enable thread-by-id)))))


(local
 (defthm not-id-nil-then-thread-by-id-nil
   (implies (and (not (equal id nil))
                 (not (thread-by-id id tt)))
            (not (THREAD-BY-ID id 
                               (REPLACE-THREAD-TABLE-ENTRY
                                NIL
                                (MAKE-THREAD NIL NIL
                                             (LIST (FRAME-SET-OPERAND-STACK (LIST V) NIL))
                                             NIL NIL NIL NIL)
                                tt))))
   :hints (("Goal" :in-theory (e/d (thread-by-id) (make-thread))))))


                            

(defthm thread-by-id-implies-mem
  (implies (THREAD-BY-ID id tt)
           (MEM (THREAD-BY-ID id tt) tt))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (enable thread-by-id))))




(defthm state-set-local-at-local-effect
  (implies (and (<= 0 i)
                (< i (len (locals (current-frame s)))))
           (equal (LOCALS (CURRENT-FRAME (state-set-local-at i any s)))
                  (update-nth i any (locals (current-frame s)))))
  :hints (("Goal" :in-theory (e/d (current-frame set-local-at-of-thread)
                                  (update-nth 
                                   TOPFRAME-NORMALIZATION
                                   CAR-THREAD-CALL-NORMALIZATION))
           :cases ((thread-by-id (current-thread s)
                                 (thread-table s))))))
  


(defthm state-set-local-at-operand-stack-effect
  (equal (operand-stack (CURRENT-FRAME (state-set-local-at i any s)))
         (operand-stack (current-frame s)))
  :hints (("Goal" :in-theory (e/d (current-frame) ())
           :cases ((mem (thread-by-id (current-thread s)
                                      (thread-table s))
                        (thread-table s))))
          ("Subgoal 1" :cases ((thread-by-id (current-thread s)
                                             (thread-table s))))
          ("Subgoal 1.2" :cases ((equal (current-thread s) nil)))))



(defthm state-set-local-at-method-ptr-effect
  (equal (method-ptr (current-frame (state-set-local-at i any s)))
         (method-ptr (current-frame s)))
  :hints (("Goal" :in-theory (e/d (current-frame
                                   thread-set-call-stack
                                   popstack-of-thread)
                                  (topframe-normalization
                                   make-thread
                                   method-ptr))
           :cases ((mem (thread-by-id (current-thread s)
                                      (thread-table s))
                        (thread-table s))))
          ("Subgoal 1" :cases ((thread-by-id (current-thread s)
                                             (thread-table s))))
          ("Subgoal 1.2" :cases ((equal (current-thread s) nil)))))

;;(i-am-here) ;;

(defthm update-nth-len
  (implies (and (< i (len l))
                (<= 0 i))
           (equal (len (update-nth i any l))
                  (len l))))


;;(in-theory (enable invalidate-category2-value))

(defthm invalidate-category2-value-no-change
  (implies (< i (len (locals (current-frame s))))
           (equal (LEN (LOCALS (CURRENT-FRAME (INVALIDATE-CATEGORY2-VALUE i s))))
                  (len (locals (current-frame s)))))
  :hints (("Goal" :in-theory (e/d (invalidate-category2-value) (state-set-local-at)))))


(defthm true-listp-original-locals-true-listp
   (implies (and (true-listp (locals (current-frame s)))
                 (<= 0 i)
                 (< i (len (locals (current-frame s)))))
            (true-listp (LOCALS (CURRENT-FRAME (INVALIDATE-CATEGORY2-VALUE  i s)))))
   :hints (("Goal" :in-theory (enable invalidate-category2-value))))



(defthm operand-stack-invalidate-category2-value-no-change
  (equal (operand-stack (current-frame (invalidate-category2-value i s)))
         (operand-stack (current-frame s)))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))


(defthm locals-invalidate-category2-value-effect-expander
  (implies (< i (len (locals (current-frame s))))
           (equal (locals (current-frame (invalidate-category2-value i s)))
                  (if (< i 0) (locals (current-frame s))
                    (IF (EQUAL (TYPE-SIZE (tag-of (LOCAL-AT i S))) 1)
                        (locals (current-frame S))
                        (update-nth i '(topx . topx) (locals (current-frame s)))))))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))


;----------------------------------------------------------------------



(defthm pc-invalidate-category-value
  (equal (pc (invalidate-category2-value i s))
         (pc s))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))

;----------------------------------------------------------------------

(defthm topStack-guard-strong-preserved-by-state-set-local-at
  (implies (topStack-guard-strong s)
           (TOPSTACK-GUARD-STRONG
            (STATE-SET-LOCAL-AT i v s)))
  :hints (("Goal" :in-theory (enable topstack-guard-strong))))


(defthm topStack-guard-strong-preserved-by-invalidate-type-size-2
  (implies (topStack-guard-strong s)
           (topStack-guard-strong (invalidate-category2-value i s)))
    :hints (("Goal" :in-theory (enable topstack-guard-strong invalidate-category2-value))))

;----------------------------------------------------------------------




;; (skip-proofs 
;;  (defthm consistent-state-state-set-local-size-1-value
;;    (implies (and (consistent-state s)
;;                  (consistent-value-x v (instance-class-table s)
;;                                      (heap s))
;;                  (not (equal (type-size (tag-of v)) 2))
;;                  (<= 0 i)
;;                  (< i (len (locals (current-frame s)))))
;;             (consistent-state
;;              (STATE-SET-LOCAL-AT i v
;;                                  (INVALIDATE-CATEGORY2-VALUE (+ -1 i)
;;                                                             S))))))

(local 
 (defthm wff-call-frame-frame-set-locals
   (implies (wff-call-frame frame)
            (WFF-CALL-FRAME
             (FRAME-SET-LOCALS (CONS V (CDR (LOCALS frame))) frame)))
   :hints (("Goal" :in-theory (enable frame-set-locals 
                                      operand-stack
                                      locals
                                      wff-call-frame make-frame)))))

(defthm consistent-value-x-category1-if-tag-not-size-2
  (implies (and (consistent-value-x v cl hp)
                (not (equal (type-size (tag-of v)) 2)))
           (category1 v))
  :hints (("Goal" :in-theory (enable wff-REFp category1 consistent-value-x)))
  :rule-classes :forward-chaining)
           

(defthm consistent-locals-implies-consistent-locals-cdr
  (implies (consistent-locals locals cl hp)
           (consistent-locals (cdr locals) cl hp))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable category1loc category2loc)
           :cases ((not (consp locals))))
          ("Subgoal 2" :cases ((not (category1loc locals))))
          ("Subgoal 2.1" :cases ((not (category2loc locals))))
          ("Subgoal 2.1.2" :expand (consistent-locals locals cl hp)
           :in-theory (enable category2loc category1))))


(defthm consistent-thread-entry-implies-set-position-0
  (implies (and (consistent-thread-entry th cl hp)
                (consistent-value-x v cl hp)
                (not (equal (type-size (tag-of v)) 2))
                (< 0 (len (locals (top (thread-call-stack th))))))
           (consistent-thread-entry 
            (SET-LOCAL-AT-OF-THREAD 0 v th)
            cl hp))
  :hints (("Goal" :in-theory (e/d (set-local-at-of-thread
                                   wff-invocation-frame)
                                  (THREAD-MREF type-size thread-REF)))))


(local 
 (defthm state-set-local-at-invalidate-category2-value-preserve-consistent-state-lemma-1
  (implies (and (consistent-state s)
                 (consistent-value-x v (instance-class-table s)
                                      (heap s))
                 (not (equal (type-size (tag-of v)) 2))
                 (< 0 (len (locals (current-frame s)))))
            (consistent-state-step
             (state-set-local-at  0 v s)))
   :hints (("Goal" :in-theory (e/d (class-loaded?)
                                   (isClassTerm type-size))))))
 


;;(i-am-here) ;; Wed Jun 14 21:49:29 2006
(local 
 (defthm car-update-nth
   (implies (and (integerp i)
                 (< 0 i))
            (equal (car (update-nth i v l))
                   (car l)))))

(defthm consistent-locals-implies-consistent-locals-update-nth-1
  (implies (and (consistent-locals locals cl hp)
                (consistent-value-x v cl hp)
                (< 0  i)
                (< i (len locals))
                (not (equal (type-size (tag-of v)) 2))
                (not (equal (type-size (tag-of (nth (- i 1) locals))) 2)))
           (consistent-locals (update-nth i v locals) cl hp))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable type-size))
          ("Subgoal *1/6.5" :cases ((equal i 1)))
          ("Subgoal *1/6.3" :cases ((equal i 1)))))


(defthm consistent-thread-entry-implies-set-position-i-if-previous-not-category2
  (implies (and (consistent-thread-entry th cl hp)
                (consistent-value-x v cl hp)
                (not (equal (type-size (tag-of v)) 2))
                (< i (len (locals (top (thread-call-stack th)))))
                (< 0 i)
                (not (equal (type-size (tag-of (nth (- i 1) 
                                                    (locals (top (thread-call-stack
                                                                  th))))))
                            2)))
           (consistent-thread-entry 
            (SET-LOCAL-AT-OF-THREAD i v th)                                                                
            cl hp))
  :hints (("Goal" :in-theory (e/d (set-local-at-of-thread
                                   wff-invocation-frame)
                                  (THREAD-MREF type-size thread-REF)))))




(defthm consistent-locals-implies-consistent-locals-update-nth-2
  (implies (and (consistent-locals locals cl hp)
                (consistent-value-x v cl hp)
                (integerp i)
                (< 0  i)
                (< i (len locals))
                (not (equal (type-size (tag-of v)) 2))
                (equal (type-size (tag-of (nth (- i 1) locals))) 2))
           (consistent-locals (update-nth 
                               i v 
                               (update-nth (- i 1) '(topx . topx) locals)) cl hp))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable type-size)
           :induct (valid-local-index i locals))))


(local (in-theory (disable wff-call-frame-frame-set-locals)))
(local (in-theory (disable UPDATE-NTH-I-SEGMENT update-nth-expand)))

(defthm consistent-thread-entry-implies-set-position-i-set-topx-if-previous-category2
  (implies (and (consistent-thread-entry th cl hp)
                (consistent-value-x v cl hp)
                (not (equal (type-size (tag-of v)) 2))
                (integerp i)
                (< i (len (locals (top (thread-call-stack th)))))
                (< 0 i)
                (equal (type-size (tag-of (nth (- i 1) 
                                               (locals (top (thread-call-stack
                                                             th))))))
                       2))
           (consistent-thread-entry 
            (SET-LOCAL-AT-OF-THREAD i v 
                                    (set-local-at-of-thread (- i 1)
                                                            '(topx . topx)
                                                            th))
            cl hp))
  :hints (("Goal" :in-theory (e/d (set-local-at-of-thread
                                   wff-invocation-frame)
                                  (THREAD-MREF type-size thread-REF)))))




;; (defthm consistent-thread-entries-replace-replace
;;   (implies (and (consistent-thread-entries tt cl hp)
;;                 (consistent-thread-entry new cl hp))
;;            (consistent-thread-entries 
;;             (replace-thread-table-entry old 
;;                                         new tt) cl hp))
;;   :hints (("Goal" :in-theory (disable consistent-thread-entry))))

(local 
 (defthm greater-equal-zero-not-equal-greater-than
   (implies (and (<= 0 i)
                 (integerp i)
                 (not (equal i 0)))
            (< 0 i))))


;; (local 
;;  (defthm |Subgoal 1.1|
;;   (IMPLIES (AND (NOT (EQUAL I 0))
;;               (CONSISTENT-STATE S)
;;               (INTEGERP I)
;;               (CONSISTENT-VALUE-X V (INSTANCE-CLASS-TABLE S)
;;                                   (HEAP S))
;;               (NOT (EQUAL (TYPE-SIZE (TAG-OF V)) 2))
;;               (<= 0 I)
;;               (< I (LEN (LOCALS (CURRENT-FRAME S))))
;;               (EQUAL (TYPE-SIZE ((NTH (+ -1 I)
;;                                      (LOCALS (CURRENT-FRAME S))))
;;                      1))
;;          (CONSISTENT-THREAD-ENTRIES
;;               (REPLACE-THREAD-TABLE-ENTRY
;;                    (THREAD-BY-ID (CURRENT-THREAD S)
;;                                  (THREAD-TABLE S))
;;                    (SET-LOCAL-AT-OF-THREAD I V
;;                                            (THREAD-BY-ID (CURRENT-THREAD S)
;;                                                          (THREAD-TABLE S)))
;;                    (THREAD-TABLE S))
;;               (INSTANCE-CLASS-TABLE S)
;;               (HEAP S)))
;;   :hints (("Goal" :in-theory (disable consistent-thread-entry type-size)))))

(local 
 (defthm state-set-local-at-invalidate-category2-value-preserve-consistent-state-lemma
   (implies (and (consistent-state s)
                 (integerp i)
                 (consistent-value-x v (instance-class-table s)
                                      (heap s))
                 (not (equal (type-size (tag-of v)) 2))
                 (<= 0 i)
                 (< i (len (locals (current-frame s)))))
            (consistent-state-step
             (state-set-local-at 
              i v 
              (invalidate-category2-value (- i 1) s))))
   :hints (("Goal" :in-theory (e/d (invalidate-category2-value class-loaded?)
                                   (isClassTerm consistent-thread-entry
                                                type-size)))
           ("Subgoal 1" :cases ((not (equal i 0)))))))
 




(defthm state-set-local-at-invalidate-category2-value-preserve-consistent-state
   (implies (and (consistent-state s)
                 (integerp i)
                 (consistent-value-x v (instance-class-table s)
                                      (heap s))
                 (not (equal (type-size (tag-of v)) 2))
                 (<= 0 i)
                 (< i (len (locals (current-frame s)))))
            (consistent-state
             (state-set-local-at 
              i v 
              (invalidate-category2-value (- i 1) s))))
  :hints (("Goal" :in-theory (disable consistent-state-step
                                      invalidate-category2-value)
           :use ((:instance consistent-state-step-implies-consistent-state
                            (s (state-set-local-at 
                                i v 
                                (invalidate-category2-value (- i 1) s))))))))


 
;----------------------------------------------------------------------
;; (i-am-here) ;; Sat Jul 30 14:39:57 2005

(defthm instance-class-table-after-invalidate-category2-value
  (equal (INSTANCE-CLASS-TABLE (INVALIDATE-CATEGORY2-VALUE any s))
         (instance-class-table s))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))

(defthm heap-after-invalidate-category2-value
  (equal (HEAP (INVALIDATE-CATEGORY2-VALUE any s))
         (heap s))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))

(defthm aux-after-invalidate-category2-value
  (equal (aux (INVALIDATE-CATEGORY2-VALUE any s))
         (aux s))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))


(defthm current-thread-after-invalidate-category2-value
  (equal (current-thread  (INVALIDATE-CATEGORY2-VALUE any s))
         (current-thread s))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))

;----------------------------------------------------------------------

(defthm consistent-state-thread-by-id
  (implies (and (consistent-state s)
                (equal (current-thread s) id))
           (wff-thread (thread-by-id id 
                                     (thread-table s)))))


(defthm consistent-state-thread-by-id-consistent-thread
  (implies (and (consistent-state s)
                (equal (current-thread s) id)
                (equal (instance-class-table s) cl)
                (equal (heap s) hp))
           (consistent-thread-entry
            (thread-by-id id 
                          (thread-table s))
            cl hp)))


;----------------------------------------------------------------------


(defthm current-frame-invalidate-category2-value-reduce
  (implies (< i 0) 
           (equal (INVALIDATE-CATEGORY2-VALUE i s)
                  s))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))

;----------------------------------------------------------------------

(defthm method-ptr-invalidate-category2-value
  (equal (METHOD-PTR
          (CURRENT-FRAME (INVALIDATE-CATEGORY2-VALUE any s)))
         (method-ptr (current-frame s)))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))

;----------------------------------------------------------------------

(defthm frame-aux-frame-set-locals
  (equal (frame-aux (frame-set-locals locals frame))
         (frame-aux frame))
  :hints (("Goal" :in-theory (e/d (frame-set-locals) (frame-aux)))))

(in-theory (disable frame-aux))

(defthm frame-aux-state-set-locals-at
  (equal (frame-aux 
            (CURRENT-FRAME (state-set-local-at i any s)))
         (frame-aux (current-frame s)))
  :hints (("Goal" :in-theory (e/d (current-frame
                                   thread-set-call-stack
                                   popstack-of-thread)
                                  (topframe-normalization
                                   make-thread
                                   frame-aux
                                   method-ptr))
           :cases ((mem (thread-by-id (current-thread s)
                                      (thread-table s))
                        (thread-table s))))
          ("Subgoal 1" :cases ((thread-by-id (current-thread s)
                                             (thread-table s))))
          ("Subgoal 1.2" :cases ((equal (current-thread s) nil)))))



(defthm frame-aux-invalidate-category2-value
  (equal (frame-aux 
            (CURRENT-FRAME (INVALIDATE-CATEGORY2-VALUE any s)))
         (frame-aux (current-frame s)))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))




(defthm gen-frame-flags-state-set-local-at
  (equal (gen-frame-flags 
            (CURRENT-FRAME (state-set-local-at i any s)) hp-init)
         (gen-frame-flags (current-frame s) hp-init))
  :hints (("Goal" :in-theory (enable gen-frame-flags))))


(defthm gen-frame-flags-invalidate-category2-value
  (equal (gen-frame-flags 
            (CURRENT-FRAME (invalidate-category2-value any s)) hp-init)
         (gen-frame-flags (current-frame s) hp-init))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))

(in-theory (disable gen-frame-flags))            

;----------------------------------------------------------------------

(defthm pc-invalidate-category2-value
  (equal (pc (invalidate-category2-value any s))
         (pc s))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))



(defthm class-table-invalidate-category2-value
  (equal (class-table (invalidate-category2-value any s))
         (class-table s))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))




(defthm env-invalidate-category2-value
  (equal (env (invalidate-category2-value any s))
         (env s))
  :hints (("Goal" :in-theory (enable invalidate-category2-value))))

;----------------------------------------------------------------------

