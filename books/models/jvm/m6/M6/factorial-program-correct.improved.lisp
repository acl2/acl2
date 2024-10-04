;; This is really a continuation of the proof of the ADD1 program proof.

(in-package "M6")
(include-book "../M6/m6-start-jvm")

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)


(include-book "ADD1-program-correct.improved")

;-- Initial State -----------------------------------------------------

;; (acl2::set-guard-checking nil)
;; (defconst *s2* (setup-initial-state "Second" '() *s*))

;; (thread-table (round-robin-run *s2* 101))

;; (defun init-state2 ()
;;   (round-robin-run *s2* 10))
;; (acl2::set-guard-checking t)

(include-book "factorial-program-init-state")

;
; Properties of init-state
;

(defthm no-pending-exception-init-state2
  (not (acl2::g 'pending-exception (aux (init-state2))))
  :hints (("Goal" :in-theory (enable init-state2))))

(defthm no-fatal-error?-init-state2
  (no-fatal-error? (init-state2))
  :hints (("Goal" :in-theory (enable init-state2))))

;----------------------------------------------------------------------



;----------------------------------------------------------------------

(defun inst-equiv (i2 i1)
  (equal (inst-inst i2) (inst-inst i1)))


(defequiv inst-equiv)
(defcong inst-equiv equal (inst-opcode inst) 1
  :hints (("Goal" :in-theory (enable inst-opcode))))

(defcong inst-equiv equal (inst-inst inst) 1)

(defcong inst-equiv equal (execute-invokestatic inst s) 1
  :hints (("Goal" :in-theory (disable CALL_STATIC_METHOD
                                      RESOLVEMETHODREFERENCE))))

; need to simplify the execute-invokestatic 
;
;;; (defun execute-invokestatic (inst s)
;;;     (let* ((methodCP (arg inst))
;;;            (method-ptr (methodCP-to-method-ptr methodCP)))
;;;     (mv-let (method-rep new-s)
;;;             (resolveMethodReference method-ptr t s) ;; we know class is loaded
;;;             (if (pending-exception s)
;;;                 (raise-exception (pending-exception s) s)
;;;               (if method-rep
;;;                   (let* ((class-rep  (static-method-class-rep method-rep new-s))
;;;                          (mclassname (classname class-rep))
;;;                          (class-ref  (class-ref class-rep)))
;;;                     (if (class-rep-in-error-state? class-rep)
;;;                         (fatalError "expected initialized class" new-s)
;;;                       (if (not (class-initialized? mclassname  new-s))
;;;                           (prog2$ (acl2::debug-print "hereXXX")
;;;                                   (reschedule (initializeClass mclassname new-s))) 
;;;                         ;; re-execute the same instruction. 
;;;                         (call_static_method class-ref method-rep new-s))))
;;;                 (fatalSlotError methodCP new-s))))))
;
;
;----------------------------------------------------------------------


;----------------------------------------------------------------------
;
; Sun Jan 11 21:57:30 2004

(defun state-equiv-class-table-equal (s2 s1)
  (and (equal (class-table s2) (class-table s1))
       (equal (env s2) (env s1))
       (equal (heap s2) (heap s1))
       (equal (error-flag s2) (error-flag s1))
       (equal (acl2::g 'pending-exception (aux s2))
              (acl2::g 'pending-exception (aux s1)))))


;; properties of state-equiv-class-table-equal


(defequiv state-equiv-class-table-equal)


(defcong state-equiv-class-table-equal equal (class-table s) 1)
(defcong state-equiv-class-table-equal equal (heap s) 1)
(defcong state-equiv-class-table-equal equal (env s) 1)
(defcong state-equiv-class-table-equal equal (error-flag s) 1)

(defcong state-equiv-class-table-equal equal (instance-class-table s) 1
  :hints (("Goal" :in-theory (enable instance-class-table))))

(defcong state-equiv-class-table-equal equal (array-class-table s) 1
  :hints (("Goal" :in-theory (enable array-class-table))))

(defcong state-equiv-class-table-equal equal (class-loaded? cn s) 2
  :hints (("Goal" :in-theory (cons 'class-loaded? (disable state-equiv-class-table-equal)))))

(defcong state-equiv-class-table-equal equal (no-fatal-error? s) 1
  :hints (("Goal" :in-theory (enable no-fatal-error?))))

(defthm state-equiv-class-table-equal-make-state
  (state-equiv-class-table-equal (make-state (pc s)
                                             (current-thread s)
                                             (heap s)
                                             (thread-table s)
                                             (class-table s)
                                             (env s)
                                             (error-flag s)
                                             (aux s))
                                 s))

(defthm implies-state-equiv-class-table-equal
  (implies (and (equal (heap s2) (heap s1))
                (equal (class-table s2) (class-table s1))
                (equal (env s2) (env s1))
                (equal (error-flag s2) (error-flag s1))
                (equal (acl2::g 'pending-exception (aux s2))
                       (acl2::g 'pending-exception (aux s1))))
           (equal (state-equiv-class-table-equal s2 s1) t)))


;; should disable this soon.

(in-theory (disable state-equiv-class-table-equal))

;----------------------------------------------------------------------

;----------------------------------------------------------------------
;
; init-state property again


(defconst *second-method*
  '(METHOD
   "Second" "fact" (PARAMETERS INT)
   (RETURNTYPE . INT)
   (ACCESSFLAGS *CLASS* *PUBLIC* *STATIC*)
   (CODE (MAX_STACK . 3)
         (MAX_LOCAL . 1)
         (CODE_LENGTH . 15)
         (PARSEDCODE (0 (ILOAD_0))
                     (1 (IFGT 6))
                     (4 (ICONST_1))
                     (5 (IRETURN))
                     (6 (ILOAD_0))
                     (7 (ILOAD_0))
                     (8 (ICONST_1))
                     (9 (ISUB))
                     (10 (INVOKESTATIC (METHODCP "fact" "Second" (INT) INT)))
                     (13 (IMUL))
                     (14 (IRETURN))
                     (ENDOFCODE 15))
         (EXCEPTIONS)
         (STACKMAP))))

(defconst *fact-ptr*
   '(METHOD-PTR "Second" "fact" (INT) INT))  



(defthm second-method-code
  (equal (code-instrs (METHOD-CODE *second-method*))
         '((0 (ILOAD_0))
           (1 (IFGT 6))
           (4 (ICONST_1))
           (5 (IRETURN))
           (6 (ILOAD_0))
           (7 (ILOAD_0))
           (8 (ICONST_1))
           (9 (ISUB))
           (10 (INVOKESTATIC (METHODCP "fact" "Second" (INT) INT)))
           (13 (IMUL))
           (14 (IRETURN))
           (ENDOFCODE 15))))


(defthm deref-method-fact-ptr 
  (equal (DEREF-METHOD *FACT-PTR*
                       (INSTANCE-CLASS-TABLE (INIT-STATE2)))
         *second-method*))

(in-theory (disable init-state2 (init-state2)))

(in-theory (disable code-instrs))

(defthm inst-is
    (implies (state-equiv-class-table-equal s (init-state2))
             (equal  (INST-BY-OFFSET1
                      ip
                      (CODE-INSTRS
                       (METHOD-CODE
                        (DEREF-METHOD *fact-ptr*
                                      (INSTANCE-CLASS-TABLE S)))))
                     (inst-by-offset1 
                      ip
                      (code-instrs (method-code *second-method*))))))

;----------------------------------------------------------------------


;----------------------------------------------------------------------
; 
; definition of poised for execution!
;

;; don't care about heap
(defun poised-for-execute-fact (s)
  (and (inst-equiv (next-inst s)
         '(any (invokestatic (METHODCP "fact" "Second" (INT) INT))))
       (current-thread-exists? s)
       ;; (wff-state-regular s)
       ;; (wff-thread-table-regular (thread-table s))
       (unique-id-thread-table (thread-table s))
       (state-equiv-class-table-equal s (init-state2))))


;----------------------------------------------------------------------


;----------------------------------------------------------------------
;
; Call opener: deal with the method invocation
;

;; Start dealing with dynamic class loading primitives that in term incurs that
;; we need to talk about creating object in the heap

;; (defthm state-equiv-class-table-equal-mv-state-equiv-class-table-equal-1
;;   (implies (state-equiv-class-table-equal s2 s1))
;;            (equal (car (build-a-java-visible-instance-data  classnames s2))
;;                   (car (build-a-java-visible-instance-data  classnames s1)))))
;;;
;;; this cause loops in v28
;;;

(defthm state-equiv-class-table-equal-mv-state-equiv-class-table-equal-1
  (implies (and (state-equiv-class-table-equal s2 s1)
                (not (equal s2 s1)))
           (equal (car (build-a-java-visible-instance-data  classnames s2))
                  (car (build-a-java-visible-instance-data  classnames s1)))))



(defthm state-equiv-class-table-equal-mv-state-equiv-class-table-equal-2
  (implies (and (state-equiv-class-table-equal s2 s1)
                (not (equal s2 s1)))
           (state-equiv-class-table-equal 
            (mv-nth 1 (build-a-java-visible-instance-data  classnames s2))
            (mv-nth 1 (build-a-java-visible-instance-data  classnames s1)))))
                
(in-theory (disable build-a-java-visible-instance-data))


;; (i-am-here) ;; Tue Jul  4 22:24:07 2006

(defthm state-equiv-class-table-equal-build-an-instance-1
  (implies (and (state-equiv-class-table-equal s2 s1)
                (not (equal s2 s1)))
           (equal (car (build-an-instance  classnames s2))
                  (car (build-an-instance  classnames s1))))
  :hints (("Goal" :restrict 
           ((STATE-EQUIV-CLASS-TABLE-EQUAL-MV-STATE-EQUIV-CLASS-TABLE-EQUAL-1
             ((s1 s1) (s2 s2)))))))
            



;;   :hints (("Goal" :use ((:instance 
;;                          state-equiv-class-table-equal-mv-state-equiv-class-table-equal-1
;;                          (s2 s1) (s1 s1)
;;                          (classnames (collect-superclass-list1 classnames
;;                                                               (instance-class-table s1) ni))))
;;            :in-theory (disable
;;                        state-equiv-class-table-equal-mv-state-equiv-class-table-equal-1))))




(defthm state-equiv-class-table-equal-build-an-instance-2
  (implies (state-equiv-class-table-equal s2 s1)
           (state-equiv-class-table-equal 
            (mv-nth 1 (build-an-instance  classnames s2))
            (mv-nth 1 (build-an-instance  classnames s1)))))

;;; I know those rules are bad!! Thu Apr  1 09:41:26 2004


(defthm state-equiv-class-table-equal-build-an-instanceClass-1
  (implies (state-equiv-class-table-equal s2 s1)
           (equal (car (build-an-instanceClass  classnames s2))
                  (car (build-an-instanceClass  classnames s1)))))

(defthm state-equiv-class-table-equal-build-an-instanceClass-2
  (implies (state-equiv-class-table-equal s2 s1)
           (state-equiv-class-table-equal 
            (mv-nth 1 (build-an-instanceClass  classnames s2))
            (mv-nth 1 (build-an-instanceClass  classnames s1)))))

(defthm state-equiv-class-table-equal-set-trace
  (state-equiv-class-table-equal  
   (state-set-aux (aux-set-trace any (aux s)) s) s)
  :hints (("Goal" :in-theory (enable aux-set-trace
                                     state-equiv-class-table-equal))))

(defthm get-exception-aux-set-trace
  (equal (acl2::g 'pending-exception (aux-set-trace any aux))
         (acl2::g 'pending-exception aux))
  :hints (("Goal" :in-theory (enable aux-set-trace))))


(in-theory (disable aux-set-trace ))
(in-theory (disable add-obj-th-count))

(defthm state-equiv-class-table-equal-load_cp_entry-1
  (implies (state-equiv-class-table-equal s2 s1)
           (state-equiv-class-table-equal 
            (mv-nth 1 (load_cp_entry  cp s2))
            (mv-nth 1 (load_cp_entry  cp s1))))
  :hints (("Goal" :in-theory (e/d (load_cp_entry state-equiv-class-table-equal)
                                  (build-an-instance)))))


(defthm state-equiv-class-table-equal-load_cp_entry-2
  (implies (state-equiv-class-table-equal s2 s1)
           (equal
            (car (load_cp_entry  cp s2))
            (car (load_cp_entry  cp s1))))
  :hints (("Goal" :in-theory (enable load_cp_entry))))

(in-theory (disable load_cp_entry))

(defthm state-equiv-class-table-equal-load_cp_entries
  (and (implies (state-equiv-class-table-equal s2 s1)
                (state-equiv-class-table-equal 
                 (mv-nth 1 (load_cp_entries  cps s2))
                 (mv-nth 1 (load_cp_entries  cps s1))))
       (implies (state-equiv-class-table-equal s2 s1)
                (equal  (car (load_cp_entries  cps s2))
                        (car (load_cp_entries  cps s1)))))
  :hints (("Goal" :restrict ((STATE-EQUIV-CLASS-TABLE-EQUAL-LOAD_CP_ENTRY-2
                              ((s1 s1) (s2 s2)))
                             (state-equiv-class-table-equal-load_cp_entry-1
                              ((s1 s1) (s2 s2)))))))


(defthm state-equiv-class-table-equal-implies-get-pending-equal
  (implies (state-equiv-class-table-equal s2 s1)         
           (equal (acl2::g 'pending-exception (aux s2))
                  (acl2::g 'pending-exception (aux s1))))
  :hints (("Goal" :in-theory (enable state-equiv-class-table-equal))))

(defthm state-equiv-class-table-equal-implies-get-pending-equal-specific
  (implies (state-equiv-class-table-equal s2 s1)         
           (equal (acl2::g 'pending-exception (aux (mv-nth 1 (load_cp_entries
                                                              cps s2))))
                  (acl2::g 'pending-exception (aux (mv-nth 1 (load_cp_entries
                                                              cps s1))))))
  :hints (("Goal" :restrict ((STATE-EQUIV-CLASS-TABLE-EQUAL-LOAD_CP_ENTRY-2
                              ((s1 s1) (s2 s2)))
                             (state-equiv-class-table-equal-load_cp_entry-1
                              ((s1 s1) (s2 s2)))
                             (STATE-EQUIV-CLASS-TABLE-EQUAL-IMPLIES-GET-PENDING-EQUAL
                              ((s1 s1) (s2 s2)))))))



  
(defcong state-equiv-class-table-equal state-equiv-class-table-equal 
  (load_class2 classname s) 2
  :hints (("Goal" :in-theory (e/d (load_class2) ())
           :restrict ((STATE-EQUIV-CLASS-TABLE-EQUAL-LOAD_CP_ENTRY-2
                       ((s1 s) (s2 s-equiv)))
                      (state-equiv-class-table-equal-load_cp_entry-1
                       ((s1 s) (s2 s-equiv)))
                      (state-equiv-class-table-equal-load_cp_entries
                       ((s1 s) (s2 s-equiv)))
                   (STATE-EQUIV-CLASS-TABLE-EQUAL-IMPLIES-GET-PENDING-EQUAL-SPECIFIC
                    ((s1 s) (s2 s-equiv)))
                      (STATE-EQUIV-CLASS-TABLE-EQUAL-IMPLIES-GET-PENDING-EQUAL
                       ((s1 s) (s2 s-equiv)))))))
           

(in-theory (disable state-equiv-class-table-equal-implies-get-pending-equal-specific))

(defun load_class_x_induct (p s seen mode s-equiv)
  (declare (xargs :measure (induct-measure p s seen mode)))
  (let ((classname p)
        (interfaces p))
    (cond ((and (equal mode 3)
                (or (class-loaded? classname s)
                    (mem classname seen)
                    (mv-let (def-found class-desc)
                            (class-by-name-s classname 
                                             (external-class-table s))
                            (declare (ignore class-desc))
                            (not def-found))))
                (list p s seen mode))
          ((and (equal mode 3)
                (or (not (trivial-inv-env-do-not-change 
                          (load_class_x classname s seen 2) s))
                    (not (no-fatal-error? (load_class_x classname s seen 2)))))
           (load_class_x_induct classname s seen 2 s-equiv))
          ((equal mode 3)
           (list (load_class_x_induct classname s seen 2 s-equiv)
                 (load_class_x_induct classname 
                                      (load_class_x classname s seen 2) seen 1 
                                      (load_class_x classname s-equiv seen 2))))
                                      
          ((and (equal mode 2)
                (not (load_class_1-inv classname s seen))
                (list p seen mode)))
          ((equal mode 2)
           (mv-let (def-found class-desc)
                   (class-by-name-s classname (external-class-table s))
                   (declare (ignore def-found))
                   (let* ((supername (super-s class-desc)))
                     (load_class_x_induct supername s (cons classname seen)
                                          3 s-equiv))))
          ((and (equal mode 1)
                (not (load_class_2-inv classname s seen)))
                (list p seen mode))
          ((equal mode 1)
           (mv-let (def-found class-desc)
                   (class-by-name-s classname (external-class-table s))
                   (declare (ignore def-found))
                   (let* ((interfaces (interfaces-s class-desc)))
                     (load_class_x_induct interfaces s (cons classname seen) 0 s-equiv))))
          ((and (equal mode 0)
                (or (endp interfaces)
                    (not (no-fatal-error? s))
                    (mem (car interfaces) seen))
                (list p seen s mode)))
          ((and (equal mode 0)
                (class-loaded? (car interfaces) s)
                 (let ((class-rep (class-by-name (car interfaces)
                                                          (instance-class-table s))))
                   (not (isInterface class-rep))))
           (list p seen s mode))
          ((and (equal mode 0)
                (class-loaded? (car interfaces) s))
           (load_class_x_induct (cdr interfaces) s seen 0 s-equiv))
          ((and (equal mode 0)
                (let* ((new-s (load_class_x (car interfaces) s seen 3))
                       (class-rep (class-by-name (car interfaces)
                                                 (instance-class-table
                                                  new-s))))
                  (or (not (trivial-inv-env-do-not-change new-s s))
                      (not (no-fatal-error? new-s))
                      (not (isInterface class-rep)))))
                (load_class_x_induct (car interfaces) s seen 3 s-equiv))
          ((equal mode 0)
           (let* ((new-s (load_class_x (car interfaces) s seen 3)))
             (list (load_class_x_induct (car interfaces) s seen 3 s-equiv)
                   (load_class_x_induct (cdr interfaces) new-s seen 0
                                        (load_class_x (car interfaces) s-equiv seen 3)))))
          (t (list p s seen mode s-equiv)))))
           
(in-theory (disable load_class2))

(defcong state-equiv-class-table-equal state-equiv-class-table-equal 
  (fatalerror any s) 2
  :hints (("Goal" :in-theory (enable fatalerror
                                     state-equiv-class-table-equal))))


(in-theory (disable   fatalError 
            STATE-EQUIV-CLASS-TABLE-EQUAL-IMPLIES-GET-PENDING-EQUAL))



(defcong state-equiv-class-table-equal state-equiv-class-table-equal 
  (load_class_x classname s anySeen anyMode) 2
  :hints (("Goal" :do-not '(generalize)
           :induct (load_class_x_induct classname s anySeen anyMode
                                        s-equiv))))


(defcong state-equiv-class-table-equal state-equiv-class-table-equal 
  (load_array_class2 basetype s) 2
  :hints (("Goal" :in-theory (enable load_array_class2
                                     array-class-table
                                     state-equiv-class-table-equal 
                                     instance-class-table))))


(in-theory (disable load_array_class2 load_class_x state-equiv-class-table-equal))



(defcong state-equiv-class-table-equal state-equiv-class-table-equal
  (state-set-current-thread cid s) 2
  :hints (("Goal" :in-theory (enable state-set-current-thread 
                                     state-equiv-class-table-equal))))


(defthm state-equiv-class-table-equal-set-cid
  (state-equiv-class-table-equal 
        (state-set-current-thread cid s)
        s)
  :hints (("Goal" :in-theory (enable state-set-current-thread 
                                     state-equiv-class-table-equal))))


(in-theory (disable state-set-current-thread))

(defcong state-equiv-class-table-equal state-equiv-class-table-equal 
  (load_class classname s) 2
  :hints (("Goal" :in-theory (enable load_class))))


(defcong state-equiv-class-table-equal state-equiv-class-table-equal 
  (load_array_class basetype s) 2
  :hints (("Goal" :in-theory (enable load_array_class load_class))))


(defcong state-equiv-class-table-equal state-equiv-class-table-equal 
  (resolveClassReference classname s) 2
  :hints (("Goal" :in-theory (enable resolveClassReference))))

;
;  Finally, we proved the needed congruence rule. 
; 
;----------------------------------------------------------------------


;----------------------------------------------------------------------
;  
;  To prove the following, we do not need above proof at all!!
;


(defthm resolveClassReference-loaded-class-no-change 
  (implies (and (class-loaded? classname s)
                (not (array-type? classname)))
           (equal (resolveClassReference classname s)
                  s))
  :hints (("Goal" :in-theory (enable resolveClassReference))))


(defthm poised-execute-next-inst-is
  (implies (and (inst-equiv (next-inst s) '(any (invokestatic (METHODCP "fact"
                                                                        "Second" (INT) INT))))
                (no-fatal-error? s))
           (equal (m6step s) (execute-invokestatic (next-inst s) s)))
  :hints (("Goal" :in-theory (e/d (m6step) (execute-invokestatic next-inst inst-equiv)))))



(defthm call-opener-execute-invokestatic-Fact-equal-call-static
  (implies (and (poised-for-execute-fact s)
                (inst-equiv inst '(any (invokestatic (METHODCP "fact" "Second" (INT) INT)))))
           (equal (execute-invokestatic inst s)
                  (call_static_method 55 *second-method* s)))
  :hints (("Goal" :in-theory (e/d ((init-state2)
                                   STATE-EQUIV-CLASS-TABLE-EQUAL-IMPLIES-GET-PENDING-EQUAL)
                                  (call_static_method)))))


(defthm call-opener-execute-invoke
   (implies (poised-for-execute-fact s)
            (equal (m6step s)
                   (call_static_method 55 *second-method* s))))
 


(in-theory (disable call-opener-execute-invokestatic-Fact-equal-call-static poised-execute-next-inst-is))

;
;  We know how to do invoke from a state equiv to initial-state!!
; 
;----------------------------------------------------------------------

;;
;; just use executable counterpart.
;;

;
;----------------------------------------------------------------------
;
;  Regular opener for doing recusive funcation call and  looping 
;

;; (defun natp (x)
;;   (and (integerp x)
;;        (<= 0 x)))

(defun c+ (i j)
  (if (zp i)
      (nfix j)
    (+ 1 (c+ (- i 1) j))))


(defun fact-clock (n)
    (if (zp n)
        5
      (c+ 7 (c+ (fact-clock (- n 1)) 2))))


(defun fact (n)
  (if (zp n)
      1
    (* n (fact (- n 1)))))

(defun fact-induct (n s)
  (if (zp n)
      (list n s)
     (fact-induct (- n 1) (simple-run s 7))))

#|
(defthm c+-revealed
  (equal (c+ i j) (+ (nfix i) (nfix j))))

(in-theory (disable c+-revealed))
|#


(defthm simple-run-+
  (implies (and (natp i) (natp j))
           (equal (simple-run s (+ i j))
                  (simple-run (simple-run s i) j))))


(defthm simple-run-c+
  (implies (and (natp i) (natp j))
           (equal (simple-run s (c+ i j))
                  (simple-run (simple-run s i) j))))


(defthm simple-run-opener-J
  (and (equal (simple-run s 0) s)
       (implies (natp i)
                (equal (simple-run s (+ 1 i))
                       (simple-run (m6step s) i)))))

(in-theory (disable simple-run-opener simple-run))


;----------------------------------------------------------------------
;
; Statement of the theorem 
;

(in-theory (disable implies-state-equiv-class-table-equal))

;; (defthm wff-state-regular-implies-equal
;;   (implies (poised-for-execute-fact s)
;;            (EQUAL (MAKE-STATE (PC S)
;;                               (CURRENT-THREAD S)
;;                               (HEAP (INIT-STATE2))
;;                               (THREAD-TABLE S)
;;                               (CLASS-TABLE (INIT-STATE2))
;;                               (ENV (INIT-STATE2))
;;                               (ERROR-FLAG (INIT-STATE2))
;;                               (AUX S))
;;                   S)))

;; (in-theory (disable pushFrame0))

;; (defthm second-is-correct-lemma
;;   (implies (and (poised-for-execute-fact s)
;;                 ;; (wff-state-regular s)
;;                 ;; (wff-thread-table-regular (thread-table s))
;; ;;                 (EQUAL (MAKE-STATE (PC S)
;; ;;                                    (CURRENT-THREAD S)
;; ;;                                    (HEAP (INIT-STATE2))
;; ;;                                    (THREAD-TABLE S)
;; ;;                                    (CLASS-TABLE (INIT-STATE2))
;; ;;                                    (ENV (INIT-STATE2))
;; ;;                                    (ERROR-FLAG (INIT-STATE2))
;; ;;                                    (AUX S))
;; ;;                     s)
;;                 (no-fatal-error? s)
;;                 (integerp n)
;;                 (<= 0 n)
;;                 (intp n)
;;                 (equal n (topStack s)))
;;            (equal (simple-run s (fact-clock n))
;;                   (state-set-pc (+ 3 (pc s))
;;                                 (pushStack (int-fix (fact n))
;;                                            (popStack s)))))
;;   :hints (("Goal" :do-not '(generalize fertilize)
;;            :induct (fact-induct n s))
;;           ("Subgoal *1/2" 
;;            :cases ((inst-equiv (next-inst s) 
;;                                '(any (invokestatic (METHODCP "fact" "Second" (INT) INT))))))))
           

                                 

;----------------------------------------------------------------------



(defun intp (n)
  (and (integerp n)
       (<= (- (expt 2 31)) n)
       (<  n (expt 2 31))))


(defthm intp-int-fix
  (implies (intp n)
           (equal (int-fix n) n))
  :hints (("Goal" :in-theory (enable int-fix))))


;; (skip-proofs 
;;  (defthm int-fix-int-fix
;;    (equal (int-fix (* x (int-fix y)))
;;           (int-fix (* x y)))))


;----------------------------------------------------------------------

(in-theory (enable next-inst))


;; (defthm second-is-correct
;;   (implies (and (poised-for-execute-fact s)
;;                 (wff-state-regular s)
;;                 (wff-thread-table-regular (thread-table s))
;;                 (no-fatal-error? s)
;;                 (integerp n)
;;                 (<= 0 n)
;;                 (intp n)
;;                 (equal n (topStack s)))
;;            (equal (simple-run s (fact-clock n))
;;                   (state-set-pc (+ 3 (pc s))
;;                                 (pushStack (int-fix (fact n))
;;                                            (popStack s)))))
;;   :hints (("Goal" :do-not '(generalize fertilize preprocess)
;;            :induct (fact-induct n s))
;;           ("Subgoal *1/2" 
;;            :cases ((inst-equiv (next-inst s) 
;;                                '(any (invokestatic (METHODCP "fact" "Second" (INT) INT))))))))
           
                                 
;----------------------------------------------------------------------

;----------------------------------------------------------------------
;
;
;  These are used for simplifying the term to get the next instruction. 
;
;

(defthm pushFrame0-current-frame
  (implies (and (wff-thread-table (thread-table s))
                (current-thread-exists? s))
           (equal (current-frame (pushFrame0 new-frame s))
                  new-frame))
  :hints (("Goal" :in-theory (enable current-frame pushFrame0
                                     current-thread-exists?))))

;; (defcong equiv-frame equal (method-ptr frame) 1)

(defthm current-method-ptr-popStackN
  (equal (current-method-ptr (popStackN n s))
         (current-method-ptr s)))

(defthm current-method-ptr-state-set-pc
  (equal (current-method-ptr (state-set-pc pc s))
         (current-method-ptr s)))


(defthm current-method-ptr-popStack
  (equal (current-method-ptr (popStack s))
         (current-method-ptr s)))

(defthm current-method-ptr-pushStack
  (equal (current-method-ptr (pushStack v s))
         (current-method-ptr s)))

(defthm current-method-ptr-pushFrame0
   (implies (and (wff-thread-table (thread-table s))
                 (current-thread-exists? s))
            (equal (current-method-ptr 
                    (pushFrame0 new-frame s))
                   (method-ptr new-frame)))
    :hints (("Goal" :in-theory (enable current-method-ptr
                                       current-frame
                                       pushFrame0
                                       thread-exists?
                                       current-thread-exists?))))


(defthm pc-pushFrame0
  (equal (pc (pushFrame0 new-frame s)) 0)
  :hints (("Goal" :in-theory (enable pushFrame0))))

(defthm pc-popFrame
  (equal  (pc (popFrame s))
          (return-pc (current-frame s)))
  :hints (("Goal" :in-theory (enable popFrame current-frame))))


(defthm instance-class-table-pushFrame0
  (equal  (instance-class-table (pushFrame0 new-frame s))
          (instance-class-table s))
  :hints (("Goal" :in-theory (enable pushFrame0))))


(in-theory (enable wff-thread-table-regular))

(defthm current-thread-exists?-popStackN
  (implies (current-thread-exists? s)
           (current-thread-exists? (popStackN n s))))


(defthm current-thread-exists?-popStack
  (implies (current-thread-exists? s)
           (current-thread-exists? (popStack s))))

(defthm current-thread-exists?-state-set-pc
  (implies (current-thread-exists? s)
           (current-thread-exists? (state-set-pc n s))))

(defthm current-thread-exists?-pushFrame
  (implies (current-thread-exists? s)
           (current-thread-exists? (pushFrame0 frame s)))
  :hints (("Goal" :in-theory (enable current-thread-exists? pushFrame0 thread-exists?))))


(defthm instance-class-table-popStack
  (equal (instance-class-table (popStack s))
         (instance-class-table s)))


(defthm instance-class-table-popStackN
  (equal (instance-class-table (popStackN n s))
         (instance-class-table s)))


(defthm wff-thread-table-regular-popStackN
  (implies (and (wff-thread-table-regular (thread-table s))
                (current-thread-exists? s))
           (wff-thread-table-regular (thread-table (popStackN n s)))))

;----------------------------------------------------------------------
; 
; These should deal with no-fatal-error?
;

(defcong state-equiv-class-table-equal state-equiv-class-table-equal 
  (pushFrame0 frame s) 2
  :hints (("Goal" :in-theory (enable pushFrame0
                                     state-equiv-class-table-equal))))

(defthm state-equiv-class-table-equal-pushFrame
  (state-equiv-class-table-equal (pushFrame0 frame s) s)
  :hints (("Goal" :in-theory (enable pushFrame0 state-equiv-class-table-equal))))


(defcong state-equiv-class-table-equal state-equiv-class-table-equal 
  (popStack s) 1
  :hints (("Goal" :in-theory (enable popStack
                                     state-equiv-class-table-equal))))

(defthm state-equiv-class-table-equal-popStack 
    (state-equiv-class-table-equal (popStack  s) s)
  :hints (("Goal" :in-theory (enable popStack state-equiv-class-table-equal))))

(defcong state-equiv-class-table-equal state-equiv-class-table-equal 
  (pushStack v s) 2
  :hints (("Goal" :in-theory (enable pushStack
                                     state-equiv-class-table-equal))))

(defthm state-equiv-class-table-equal-pushStack 
    (state-equiv-class-table-equal (pushStack v  s) s)
  :hints (("Goal" :in-theory (enable pushStack
                                     state-equiv-class-table-equal))))

(defcong state-equiv-class-table-equal state-equiv-class-table-equal 
  (state-set-local-at i v s) 3
  :hints (("Goal" :in-theory (enable state-set-local-at
                                     state-equiv-class-table-equal))))

(defthm state-equiv-class-table-equal-state-set-local-at
    (state-equiv-class-table-equal (state-set-local-at i v s) s)
  :hints (("Goal" :in-theory (enable state-set-local-at state-equiv-class-table-equal))))

(defcong state-equiv-class-table-equal state-equiv-class-table-equal 
  (popStackN n s) 2)

(defthm state-equiv-class-table-equal-popStackN 
    (state-equiv-class-table-equal (popStackN n s) s))

(defcong state-equiv-class-table-equal state-equiv-class-table-equal 
  (state-set-pc pc s) 2
    :hints (("Goal" :in-theory (enable state-set-pc state-equiv-class-table-equal))))

(defthm state-equiv-class-table-equal-state-set-pc
    (state-equiv-class-table-equal (state-set-pc pc s) s)
    :hints (("Goal" :in-theory (enable state-set-pc state-equiv-class-table-equal))))


;; ??? WHY? those do not apply automatically?

(defthm no-fatal-error-pushFrame0
  (equal (no-fatal-error? (pushFrame0 frame s))
         (no-fatal-error? s)))


(defthm no-fatal-error-state-set-pc
   (equal (no-fatal-error? (state-set-pc pc s))
          (no-fatal-error? s)))


(defthm no-fatal-error-popStack
    (equal (no-fatal-error? (popStack s))
           (no-fatal-error? s)))


(defthm pushStack-no-change-instance-class-table
   (equal (instance-class-table (pushStack v s))
          (instance-class-table s)))

(defthm no-fatal-error-popStackN
    (equal (no-fatal-error? (popStackN n s))
           (no-fatal-error? s)))

;; (in-theory (disable pushFrame0 (init-state2) code-instrs inst-inst))

;; (in-theory (disable execute-invokestatic))

;----------------------------------------------------------------------


(in-theory (enable local-at))


(defthm car-operand-stack-current-frame-is-topStack
  (equal (car (operand-stack (current-frame s)))
         (topStack s))
  :hints (("Goal" :in-theory (enable topStack))))



;----------------------------------------------------------------------
;
;   Next deal with popStack-pushStack!!! w
;
;   we need 


(defthm wff-state-regular-pushFrame
  (implies (wff-state-regular s)
           (wff-state-regular (pushFrame0 frame s)))
  :hints (("Goal" :in-theory (enable pushFrame0 wff-state state-set-pc 
                                     make-state pc current-thread thread-table
                                     class-table env aux heap error-flag))))



(defthm wff-state-regular-popStackN
   (implies (wff-state-regular s)
            (wff-state-regular (popStackN n s))))


;; (defthm wff-state-regular-pushStack
;;    (implies (wff-state-regular s)
;;             (wff-state-regular (pushStack v s))))



(defthm wff-thread-table-regular-pushFrame0
   (implies (and (current-thread-exists? s)
                 (wff-thread-table-regular (thread-table s)))
            (wff-thread-table-regular (thread-table (pushFrame0 frame s))))
   :hints (("Goal" :in-theory (enable pushFrame0))))


;; (defthm wff-thread-table-regular-popStackN
;;    (implies (and (current-thread-exists? s)
;;                  (wff-thread-table-regular (thread-table s)))
;;             (wff-thread-table-regular (thread-table (popStackN n s)))))


(defthm wff-state-regular-integerp-pc
  (implies (wff-state-regular s)
           (integerp (pc s)))
  :hints (("Goal" :in-theory (enable wff-state-regular)))
  :rule-classes :forward-chaining)




(defthm wff-state-regular-state-set-pc
  (implies (and (wff-state-regular s)
                (integerp pc))
            (wff-state-regular (state-set-pc pc s)))
  :hints (("Goal" :in-theory (enable state-set-pc wff-state state-set-pc 
                                     make-state pc current-thread thread-table
                                     class-table env aux heap error-flag))))

(in-theory (disable wff-state-regular))




(defthm unique-id-thread-table-pushFrame0
   (implies (and (current-thread-exists? s)
                 (unique-id-thread-table (thread-table s)))
            (unique-id-thread-table (thread-table (pushFrame0 frame s))))
   :hints (("Goal" :in-theory (enable pushFrame0))))

(defthm unique-id-thread-table-popStackN
  (implies (and (current-thread-exists? s)
                (unique-id-thread-table (thread-table s)))
           (unique-id-thread-table (thread-table (popStackN n s)))))


(defthm wff-call-frame-regular-make-frame
  (implies (and (wff-method-ptr mptr)
                (true-listp locals)
                (true-listp ops))
           (wff-call-frame-regular (MAKE-FRAME rpc
                                               ops
                                               locals
                                               mptr
                                               sync
                                               resume-pc
                                               aux)))
  :hints (("Goal" :in-theory (enable wff-call-frame-regular wff-call-frame
                                     make-frame locals operand-stack return-pc
                                     method-ptr sync-obj-ref))))


(defthm wff-call-frame-regular-locals-truelistp
  (implies (wff-call-frame-regular frame)
           (true-listp (locals frame)))
  :hints (("Goal" :in-theory (enable wff-call-frame 
                                     wff-call-frame-regular locals))))


(defthm wff-call-frame-regular-opstack-truelistp
  (implies (wff-call-frame-regular frame)
           (true-listp (operand-stack frame)))
  :hints (("Goal" :in-theory (enable wff-call-frame 
                                     wff-call-frame-regular operand-stack))))

;;
;; this is not provable anymore after we updatd to wff-call-frame to assert 
;; a lot of properties about the frame. 
;; 
;; To prove the same theorem. we need add a lot of more hypthoesis 

;----------------------------------------------------------------------
; 

(defthm current-thread-pushFrame
  (equal (current-thread (pushFrame0 frame s))
         (current-thread s))
  :hints (("Goal" :in-theory (enable pushFrame0))))

(defthm current-thread-popStackN
  (equal (current-thread (popStackN n s))
         (current-thread s)))

;----------------------------------------------------------------------


;----------------------------------------------------------------------
;
; About popFrame


(defthm popFrame-opstack-primitves 
  (and (implies (and (current-thread-exists? s)
                     (wff-state-regular s)
                     (unique-id-thread-table (thread-table s))
                     (wff-thread-table-regular (thread-table s)))
                (equal (popFrame (popStack s))
                       (popFrame s)))
       (implies (and (current-thread-exists? s)
                     (unique-id-thread-table (thread-table s))
                     (wff-thread-table-regular (thread-table s))
                     (wff-state-regular s))
                (equal (popFrame (pushStack v s))
                       (popFrame s)))
       (implies (and (current-thread-exists? s)
                     (unique-id-thread-table (thread-table s))
                     (wff-thread-table-regular (thread-table s))
                     (wff-state-regular s))
                (equal (popFrame (state-set-pc pc s))
                       (popFrame s)))
       (implies (and (current-thread-exists? s)
                     (unique-id-thread-table (thread-table s))
                     (wff-thread-table-regular (thread-table s))
                     (wff-state-regular s))
                (equal (popFrame (state-set-local-at i v s))
                       (popFrame s))))
   :hints (("Goal" :in-theory (enable popFrame current-thread-exists?
                                      state-set-local-at thread-exists?
                                      popStack pushStack state-set-pc))))

;
; Interaction between popFrame and opStack
; 
;----------------------------------------------------------------------


(defthm bind-wff-thread-regular-implies
  (implies (and (thread-by-id id tt)
                (wff-thread-table-regular tt))
           (wff-thread-regular (thread-by-id id tt))))

(defthm wff-thread-regular-make-thread-equal
  (implies (wff-thread-regular (thread-by-id (current-thread s) 
                                             (thread-table s)))
           (equal (MAKE-THREAD (CURRENT-THREAD S)
                               (THREAD-SAVED-PC (THREAD-BY-ID (CURRENT-THREAD S)
                                                              (THREAD-TABLE S)))
                               (THREAD-CALL-STACK (THREAD-BY-ID (CURRENT-THREAD S)
                                                                (THREAD-TABLE S)))
                               (THREAD-STATE (THREAD-BY-ID (CURRENT-THREAD S)
                                                           (THREAD-TABLE S)))
                               (THREAD-MREF (THREAD-BY-ID (CURRENT-THREAD S)
                                                          (THREAD-TABLE S)))
                               (THREAD-MDEPTH (THREAD-BY-ID (CURRENT-THREAD S)
                                                            (THREAD-TABLE S)))
                               (THREAD-REF (THREAD-BY-ID (CURRENT-THREAD S)
                                                         (THREAD-TABLE s))))
                  (thread-by-id (current-thread s) (thread-table s)))))


(defthm state-set-pc-state-set-thread-table-normalize
  (equal (state-set-thread-table th (state-set-pc pc s))         
         (state-set-pc pc (state-set-thread-table th s)))
  :hints (("Goal" :in-theory (enable state-set-thread-table state-set-pc))))

(defthm state-set-thread-table-set-thread-table-normalize
  (equal (state-set-thread-table th1 (state-set-thread-table th2 s))
         (state-set-thread-table th1 s))
  :hints (("Goal" :in-theory (enable state-set-thread-table))))


;; (defthm thread-primitives-state-set-pc
;;   (and (equal (popStack (state-set-pc npc s))
;;               (state-set-pc npc (popStack s)))
;;        (equal (pushStack v  (state-set-pc npc s))
;;               (state-set-pc npc (pushStack v s)))
;;        (equal (state-set-local-at i v (state-set-pc npc s))
;;               (state-set-pc npc (state-set-local-at i v s))))
;;   :hints (("Goal" :in-theory (enable state-set-pc popStack pushStack
;;                                      state-set-local-at
;;                                      state-set-thread-table))))


(defthm popStackN-state-set-pc-normalize
  (equal (popStackN n (state-set-pc pc s))         
         (state-set-pc pc (popStackN n s))))



(defthm wff-state-regular-state-set-thread-table
  (implies (wff-state-regular s)
           (equal (state-set-thread-table (thread-table s) s)
                  s))
  :hints (("Goal" :in-theory (enable wff-state-regular state-set-thread-table))))

(defthm popFrame-pushFrame0-is
  (implies (and (current-thread-exists? s)
                (wff-state-regular s)
                (wff-thread-table-regular (thread-table s))
                (unique-id-thread-table (thread-table s)))
  (equal (popFrame (pushFrame0 frame s))
         (state-set-pc (return-pc frame) s)))
  :hints (("Goal" :in-theory (enable popFrame pushFrame0 current-thread-exists?
                                     thread-exists?))))


(in-theory (disable popFrame pushFrame0))

;----------------------------------------------------------------------


(defthm second-is-correct
  (implies (and (poised-for-execute-fact s)
                (wff-state-regular s)
                (wff-thread-table-regular (thread-table s))
                (no-fatal-error? s)
                (integerp n)
                (<= 0 n)
                (intp n)
                (equal n (topStack s)))
           (equal (simple-run s (fact-clock n))
                  (state-set-pc (+ 3 (pc s))
                                (pushStack (int-fix (fact n))
                                           (popStack s)))))
  :hints (("Goal" :do-not '(generalize fertilize)
           :induct (fact-induct n s))))

