#|
public class First { 
    public static void main(String[] args) {
	int i=1; // modified to i=j 
	int j=i+1;
	i=j;
	return;
    };

};

(defconst *First*
 (make-class-def
      '(class "First"
            "java.lang.Object"
            (constant_pool)
            (fields)
            (methods
                        (method "<init>"
                              (parameters )
                              (returntype void)
                              (accessflags  *class*  *public* )
                              (code
                                   (max_stack 1) (max_locals 1) (code_length 5)
                                   (parsedcode
                                      (0 (aload_0))
                                      (1 (invokespecial
					(methodCP "<init>" "java.lang.Object" () void)))
                                      (4 (return))
                                      (endofcode 5))
                                   (Exceptions )
                                   (StackMap )))
                        (method "main"
                              (parameters (array (class "java.lang.String")))
                              (returntype void)
                              (accessflags  *class*  *public*  *static* )
                              (code
                                   (max_stack 2) (max_locals 3) (code_length 9)
                                   (parsedcode
                                      (0 (iconst_1)) ;; (0 (iload_2)) 
                                      (1 (istore_1))
                                      (2 (iload_1))
                                      (3 (iconst_1))
                                      (4 (iadd))
                                      (5 (istore_2))
                                      (6 (iload_2))
                                      (7 (istore_1))
                                      (8 (return))
                                      (endofcode 9))
                                   (Exceptions )
                                   (StackMap ))))
            (interfaces)
            (accessflags  *class*  *public*  *super*  *synchronized* )
            (attributes
              (attribute "SourceFile")))))
|#

(in-package "M6")


(include-book "../M6/m6-start-jvm")

;;; After proving the following theorem, we disable the definition of m6step.
;;; In some sense to make the only fact ACL2 know about the m6step is the
;;; following. Thus ACL2 will not be side tracked into expanding the definition
;;; of m6step all the time
;;;
;;; The following theorem says: If we know (next-inst s) is a "constant"
;;; already, we know m6step can be expanded in the following ways. 
;;;  

;; (i-am-here) ;; Tue Jul  4 19:14:05 2006

(defthm do-inst-opener
  (implies (consp (next-inst s))
           (equal (m6step s)
                  (let* ((inst (next-inst s))
                         (op   (inst-opcode inst)))
                    (if (no-fatal-error? s)
                        (prog2$ (acl2::cw "thread ~p0 executing inst ~p1~%Current pc ~p2~%"
                                                   (current-thread s) inst (pc s))
                                (if (equal op 'invalid-op-code) ;; shouldn't happen if verified.
                                    (fatalError  "impossible: opcode invalid" s)
                                  (if (equal op 'JVM::INVALID-INST-OFFSET)
                                      (fatalError  "impossible: fall off the method" s)
                                    (case  op 
                                      (NOP        (execute-NOP        inst s))
                                      (ICONST_M1  (execute-ICONST_M1  inst s))
                                      (ICONST_0   (execute-ICONST_0   inst s))
                                      (ICONST_1   (execute-ICONST_1   inst s))
                                      (ICONST_2   (execute-ICONST_2   inst s))
                                      (ICONST_3   (execute-ICONST_3   inst s))
                                      (ICONST_4   (execute-ICONST_4   inst s))
                                      (ICONST_5   (execute-ICONST_5   inst s))
                                      (LCONST_0   (execute-LCONST_0   inst s))
                                      (LCONST_1   (execute-LCONST_1   inst s))
                                    
                                      (ACONST_NULL (execute-ACONST_NULL inst s))
                                      (BIPUSH     (execute-BIPUSH     inst s))
                                      (SIPUSH     (execute-SIPUSH     inst s))
                                      (LDC        (execute-LDC        inst s))             
                                      (ILOAD      (execute-ILOAD      inst s))
                                      (LLOAD      (execute-LLOAD      inst s))
                                      (ALOAD      (execute-ALOAD      inst s))
                                      (ILOAD_0    (execute-ILOAD_0    inst s))
                                      (ILOAD_1    (execute-ILOAD_1    inst s))
                                      (ILOAD_2    (execute-ILOAD_2    inst s))             
                                      (ILOAD_3    (execute-ILOAD_3    inst s))             
                                      (ALOAD_0    (execute-ALOAD_0    inst s))
                                      (ALOAD_1    (execute-ALOAD_1    inst s))
                                      (ALOAD_2    (execute-ALOAD_2    inst s))
                                      (ALOAD_3    (execute-ALOAD_3    inst s))
                                      (IALOAD     (execute-IALOAD     inst s))
                                      (LALOAD     (execute-LALOAD     inst s))
                                      (AALOAD     (execute-AALOAD     inst s))
                                      (BALOAD     (execute-BALOAD     inst s))
                                      (ISTORE     (execute-ISTORE     inst s))
                                      (LSTORE     (execute-LSTORE     inst s))
                                      (ASTORE     (execute-ASTORE     inst s))
                                      (ISTORE_0   (execute-ISTORE_0   inst s))
                                      (ISTORE_1   (execute-ISTORE_1   inst s))
                                      (ISTORE_2   (execute-ISTORE_2   inst s))
                                      (ISTORE_3   (execute-ISTORE_3   inst s))
                                      (LSTORE_0   (execute-LSTORE_0   inst s))
                                      (LSTORE_1   (execute-LSTORE_1   inst s))
                                      (LSTORE_2   (execute-LSTORE_2   inst s))
                                      (LSTORE_3   (execute-LSTORE_3   inst s))
                                      (ASTORE_0   (execute-ASTORE_0   inst s))
                                      (ASTORE_1   (execute-ASTORE_1   inst s))
                                      (ASTORE_2   (execute-ASTORE_2   inst s))
                                      (ASTORE_3   (execute-ASTORE_3   inst s))

                                      (IASTORE    (execute-IASTORE    inst s))
                                    
                                      (LASTORE    (execute-LASTORE    inst s))
                                      (AASTORE    (execute-AASTORE    inst s))
                                      (BASTORE    (execute-BASTORE    inst s))
             
                                      (CALOAD     (execute-CALOAD     inst s))
                                      (CASTORE    (execute-CASTORE    inst s))
                                      (SASTORE    (execute-SASTORE    inst s))
                                      (POP        (execute-POP        inst s))
                                      (POP2       (execute-POP2       inst s))
                                      (DUP        (execute-DUP        inst s))             
                                      (DUP_X1     (execute-DUP_X1     inst s))             
                                      (DUP_X2     (execute-DUP_X2     inst s))
                                      (DUP2       (execute-DUP2       inst s))             
                                      (DUP2_X1    (execute-DUP2_X1    inst s))             
                                      (DUP2_X2    (execute-DUP2_X2    inst s))
                                      (SWAP       (execute-SWAP       inst s))
                                      (IADD       (execute-IADD       inst s))             
                                      (LADD       (execute-LADD       inst s))             
                                      (LCMP       (execute-LCMP       inst s))             
                                      (ISUB       (execute-ISUB       inst s))             
                                      (IMUL       (execute-IMUL       inst s))             
                                      (IDIV       (execute-IDIV       inst s))             
                                      (IREM       (execute-IREM       inst s))
                                      (INEG       (execute-INEG       inst s))             
                                      (IINC       (execute-IINC       inst s))
                                    
                                      (NEWARRAY    (execute-NEWARRAY    inst s))
                                      (ARRAYLENGTH (execute-ARRAYLENGTH inst s))
             
             
                                      (MONITORENTER (execute-MONITORENTER inst s))
                                      (MONITOREXIT  (execute-MONITOREXIT  inst s))
                                    
                                      (CHECKCAST    (execute-CHECKCAST    inst s))
                                    
                                      (CUSTOMCODE (execute-CUSTOMCODE inst s))

                                      (ISTORE_1   (execute-ISTORE_1   inst s))
                                    
                                      (ISTORE_2   (execute-ISTORE_2   inst s))

                                      (IADD       (execute-IADD       inst s))
                                      (NEW        (execute-NEW        inst s))

                                      (LDC        (execute-LDC        inst s))
                                      (INVOKESPECIAL  (execute-INVOKESPECIAL inst s))
                                      (INVOKESTATIC   (execute-INVOKESTATIC inst s))
                                      (INVOKEVIRTUAL   (execute-INVOKEVIRTUAL inst s))
                                      (INVOKEINTERFACE (execute-INVOKEINTERFACE inst s))
                                      (ASTORE_3     (execute-ASTORE_3   inst s))
                                      (ALOAD_0    (execute-ALOAD_0 inst s))

                                      (PUTFIELD   (execute-PUTFIELD inst s))
                                      (GETFIELD   (execute-GETFIELD inst s))

                                      (GETSTATIC  (execute-GETSTATIC inst s))
                                      (PUTSTATIC  (execute-PUTSTATIC inst s))

                                      (CASTORE    (execute-CASTORE   inst s))
                                      (PUTSTATIC  (execute-PUTSTATIC inst s))
                                      (IFNULL     (execute-IFNULL      inst s))
                                      (IFNONNULL  (execute-IFNONNULL   inst s))
                                      (IFEQ       (execute-IFEQ        inst s))
                                      (IFNE       (execute-IFNE        inst s))
                                      (IFLT      (execute-IFLT        inst s))
                                      (IFGE      (execute-IFGE        inst s))
                                      (IFGT      (execute-IFGT        inst s))
                                      (IFLE      (execute-IFLE        inst s))
                                      (IF_ICMPEQ  (execute-IF_ICMPEQ    inst s))
                                      (IF_ICMPNE  (execute-IF_ICMPNE    inst s))
                                      (IF_ICMPLT  (execute-IF_ICMPLT    inst s))
                                      (IF_ICMPGE  (execute-IF_ICMPGE    inst s))
                                      (IF_ICMPGT  (execute-IF_ICMPGT    inst s))
                                      (IF_ICMPLE  (execute-IF_ICMPLE    inst s))
                                      (GOTO       (execute-GOTO         inst s))
                                      (IRETURN    (execute-RETURN       inst s 1))  
                                      (RETURN     (execute-RETURN       inst s 0))
                                      (ARETURN    (execute-RETURN       inst s 1))
                                      (ATHROW     (execute-ATHROW       inst s))
                                      (JSR        (execute-JSR          inst s))
                                      (RET        (execute-RET          inst s))
                                      (t s)))))
                      s))))
                  :hints (("Goal" :in-theory (cons 'm6step (disable   
                                    execute-NOP       
                                    execute-ICONST_M1 
                                    execute-ICONST_0  
                                    execute-ICONST_1  
                                    execute-ICONST_2  
                                    execute-ICONST_3  
                                    execute-ICONST_4  
                                    execute-ICONST_5  
                                    execute-LCONST_0   
                                    execute-LCONST_1   
             			    		       
                                    execute-ACONST_NULL
				    		       
                                    execute-BIPUSH     
                                    execute-SIPUSH     
                                    execute-LDC           
                                    execute-ILOAD      
                                    execute-LLOAD      
                                    execute-ALOAD      
                                    execute-ILOAD_0    
                                    execute-ILOAD_1    
                                    execute-ILOAD_2       
                                    execute-ILOAD_3       
                                    execute-ALOAD_0    
                                    execute-ALOAD_1    
                                    execute-ALOAD_2    
                                    execute-ALOAD_3    
                                    execute-CALOAD
                                    execute-IALOAD     
                                    execute-LALOAD     
                                    execute-AALOAD     
                                    execute-BALOAD     
                                    execute-ISTORE     
                                    execute-LSTORE     
                                    execute-ASTORE     
                                    execute-ISTORE_0   
                                    execute-ISTORE_1   
                                    execute-ISTORE_2   
                                    execute-ISTORE_3   
                                    execute-LSTORE_0   
                                    execute-LSTORE_1   
                                    execute-LSTORE_2   
                                    execute-LSTORE_3   
                                    execute-ASTORE_0   
                                    execute-ASTORE_1   
                                    execute-ASTORE_2   
                                    execute-ASTORE_3   
                                    execute-IASTORE    
                                    execute-LASTORE    
                                    execute-AASTORE    
                                    execute-BASTORE    
                                    execute-CASTORE    
                                    execute-SASTORE    
                                    execute-POP        
                                    execute-POP2       
                                    execute-DUP           
                                    execute-DUP_X1        
                                    execute-DUP_X2     
                                    execute-DUP2          
                                    execute-DUP2_X1       
                                    execute-DUP2_X2    
                                    execute-SWAP       
                                    execute-IADD          
                                    execute-LADD          
                                    execute-LCMP
                                    execute-ISUB          
                                    execute-IMUL          
                                    execute-IDIV          
                                    execute-INEG          
                                    execute-IINC       
             			    		       
                                    execute-NEWARRAY   
                                    execute-ARRAYLENGTH
             			    		       
             			    		       
                                    execute-MONITORENTER
                                    execute-MONITOREXIT
				    		       
                                    execute-CHECKCAST  
				    		       
                                    execute-CUSTOMCODE 
				    		       
                                    execute-ISTORE_1   
				    		       
                                    execute-ISTORE_2   
				    		       
                                    execute-IADD       
                                    execute-NEW        
				    		       
                                    execute-LDC        
                                    execute-INVOKESPECIAL
                                    execute-INVOKESTATIC
                                    execute-INVOKEVIRTUAL
                                    execute-INVOKEINTERFACE
                                    execute-ASTORE_3   
                                    execute-ALOAD_0 
				    		       
                                    execute-PUTFIELD 
                                    execute-GETFIELD
				    		       
                                    execute-GETSTATIC 
                                    execute-PUTSTATIC 
				    		       
                                    execute-CASTORE   
                                    execute-PUTSTATIC 
                                    execute-IFNULL     
                                    execute-IFNONNULL  
                                    execute-IFEQ       
                                    execute-IFNE       
                                    execute-IFLT       
                                    execute-IFGE       
                                    execute-IFGT       
                                    execute-IFLE       
                                    execute-IF_ICMPEQ  
                                    execute-IF_ICMPNE  
                                    execute-IF_ICMPLT  
                                    execute-IF_ICMPGE  
                                    execute-IF_ICMPGT  
                                    execute-IF_ICMPLE  
                                    execute-GOTO       
                                    execute-RETURN     
                                    execute-RETURN     
                                    execute-RETURN     
                                    execute-ATHROW     
                                    execute-JSR    
                                    execute-IREM
                                    execute-RET)))))

(in-theory (disable m6step))

;----------------------------------------------------------------------

; Now we need to effectively reduce the complicated (next-inst s) into our
; intuitive understanding of it. We need to identify under what condition the
; next-inst is simply what we tend to think it is. 


;;; Define a equivalence relation so that we could relatively easily talk about
;;; the next instruction, current-method-ptr, we could succinctly talk about the
;;;  initial condition 

; The definition starts from call frame then going upward until we can define
; an equivalence of state. Because most of our primitives works on state, we
; need such a equivalence to characterize what does NOT change.

(defun equiv-frame (f1 f0)
  (and (equal (return-pc f1) (return-pc f0))
       (equal (method-ptr f1) (method-ptr f0))
       (equal (sync-obj-ref f1) (sync-obj-ref f0))))

;;;  equal except for opstack and locals

(defequiv equiv-frame)   ;; equiv-frame is a equivalence
(defcong equiv-frame equal (return-pc f) 1)
(defcong equiv-frame equal (method-ptr f) 1)
(defcong equiv-frame equal (sync-obj-ref f) 1)

(in-theory (disable equiv-frame))

;----------------------------------------------------------------------

(defun top-frame (thread)
  (top (thread-call-stack thread)))

; We define the concept of top-frame of a thread
; It allows us to take about the concept directly as an primitive.

;;; It would be best if we write our JVM definition in terms of top-frame in
;;; the first place.
;;;
;;; Currently, we add this rewrite rule, so that we don't have to modify the
;;; defintions, else where.
;;; 
;;; ACL2 will handle the conversion "on the fly"

(defthm top-thread-call-stack-rewrite 
  (equal (top (thread-call-stack thread)) (top-frame thread)))

(in-theory (disable top-frame))


; similarly non-top-frame, which we do not care in this proof. 

(defun non-top-frames (thread)
  (pop (thread-call-stack thread)))

(defthm pop-thread-call-stack-rewrite 
  (equal (pop (thread-call-stack thread)) (non-top-frames thread)))

(in-theory (disable non-top-frames))

;----------------------------------------------------------------------

; thread equivalence. 

(defun equiv-thread-except-topframe (t1 t2)
  (and (equal (thread-saved-pc t1) (thread-saved-pc t2))
       (equal (thread-mref t1) (thread-mref t2))
       (equal (thread-mdepth t1) (thread-mdepth t2))
       (equal (thread-ref t1) (thread-ref t2))
       (equal (thread-id t1) (thread-id t2))
       (equal (thread-state t1) (thread-state t2))
       (equiv-frame (top-frame t1)
                    (top-frame t2))))

;; Note: We do not need to assert anything about non-top-frame!  We are only
;; talking about a straightline code that runs in one frame.
;;

(defequiv equiv-thread-except-topframe)

(defcong equiv-thread-except-topframe equiv-frame (top-frame t1) 1)
(defcong equiv-thread-except-topframe equal (thread-id t1) 1)
(defcong equiv-thread-except-topframe equal (thread-state t1) 1)
(defcong equiv-thread-except-topframe equal (thread-saved-pc t1) 1)
(defcong equiv-thread-except-topframe equal (thread-mref t1) 1)
(defcong equiv-thread-except-topframe equal (thread-mdepth t1) 1)
(defcong equiv-thread-except-topframe equal (thread-ref t1) 1)

(in-theory (disable equiv-thread-except-topframe thread-mref thread-state
                    thread-id thread-saved-pc))


(defun equiv-thread-table (tl1 tl2)
  (cond ((endp tl1) (endp tl2))
        ((endp tl2) nil)
        ((equiv-thread-except-topframe (car tl1) (car tl2))
         (equiv-thread-table (cdr tl1) (cdr tl2)))
        (t nil)))

(defequiv equiv-thread-table)


(defcong equiv-thread-table equiv-thread-except-topframe (thread-by-id id tt)
  2)


(defcong equiv-thread-table equal (search-active-thread-in-range s e tt) 3)
;;;  This is used for proving round-robin run return the same result on the
;;;  equiv-state


(defun equiv-state (s1 s0)
  (and (equiv-thread-table (thread-table s1) (thread-table s0))
       (equal (current-thread s1) (current-thread s0))
       (equal (error-flag s1)     (error-flag s0))
       (equal (class-table s1)    (class-table s0))
       (equal (env s1)            (env s0))
       (equal (aux s1)            (aux s0))))

(defequiv equiv-state)
(defcong equiv-state equiv-thread-table (thread-table t1) 1)
(defcong equiv-state equal (current-thread t1) 1)
(defcong equiv-state equal (error-flag t1) 1)
(defcong equiv-state equal (env t1) 1)
(defcong equiv-state equal (aux t1) 1)
(defcong equiv-state equal (instance-class-table t1) 1
  :hints (("Goal" :in-theory (enable instance-class-table))))
(defcong equiv-state equal (array-class-table t1) 1
  :hints (("Goal" :in-theory (enable array-class-table))))


(defcong equiv-state equiv-frame (current-frame s) 1
  :hints (("Goal" :in-theory (enable current-frame))))

(defcong equiv-state equal (no-fatal-error? s) 1
  :hints (("Goal" :in-theory (enable no-fatal-error?))))


(in-theory (disable equiv-state))

(defcong equiv-state equal (current-method-ptr s) 1
  :hints (("Goal" :in-theory (enable current-method-ptr))))


;----------------------------------------------------------------------

(defthm non-top-frame-make-thread
  (equal (non-top-frames (make-thread id pc (cons new-frame frames) status mref
                                      mdep th-ref))
         frames)
  :hints (("Goal" :in-theory (list* 'non-top-frames 
                                    (disable POP-THREAD-CALL-STACK-REWRITE)))))

(defthm  top-frame-make-thread
  (equal (top-frame (make-thread id pc (cons new-frame frames) status mref
                                      mdep th-ref))
         new-frame)
  :hints (("Goal" :in-theory (list* 'top-frame 
                                    (disable TOP-THREAD-CALL-STACK-REWRITE)))))

(in-theory (disable aux))


(in-theory (disable thread-mdepth thread-ref))

(defthm equiv-thread-except-topframe-thread-primitives
  (and (equiv-thread-except-topframe (push-stack-of-thread v thread)
                                     thread)
       (equiv-thread-except-topframe (popStack-of-thread thread)
                                     thread)
       (equiv-thread-except-topframe (set-local-at-of-thread i v thread)
                                     thread))
  :hints (("Goal" :in-theory (enable equiv-thread-except-topframe
                                     push-stack-of-thread
                                     popStack-of-thread
                                     set-local-at-of-thread
                                     equiv-frame))))

; We introduced the push-stack-of-thread, popStack-of-thread as an immediate
; primitives as a bridge between pushStack with push, popStack with pop.



(defthm equiv-thread-except-topframe-thread-primitives-2
  (and (equal (equiv-thread-except-topframe (push-stack-of-thread v thread)
                                            thread) t)
       (equal (equiv-thread-except-topframe (popStack-of-thread thread)
                                            thread) t)
       (equal (equiv-thread-except-topframe (set-local-at-of-thread i v thread)
                                            thread) t)))


;;;  Ideally we may define another equivalence relation to exactly capture the 
;;;  effect of push-stack-of-thread, so property as follows will be expressed
;;;  as congruence rules on that equivalence. 
;;;
;;;  This means that we need a hierachy of equivalence. 

(defthm equal-non-top-frames-frame-op-no-change
  (and (equal (non-top-frames (push-stack-of-thread v thread))
              (non-top-frames thread))
      (equal (non-top-frames (popStack-of-thread thread))
             (non-top-frames thread))
      (equal (non-top-frames (set-local-at-of-thread i v thread))
             (non-top-frames thread)))
  :hints (("Goal" :in-theory (e/d (non-top-frames push-stack-of-thread
                                   popStack-of-thread set-local-at-of-thread)               
                                  (POP-THREAD-CALL-STACK-REWRITE
                                   top-thread-call-stack-rewrite)))))

                         

(in-theory (disable push-stack-of-thread))
(in-theory (disable popStack-of-thread))
(in-theory (disable set-local-at-of-thread))

; Disable those definitions. Now to ACL2, those become primitives (just like
; those to the operator of ACL2 ---  us user)

(defthm equiv-thread-table-replace-thread-table-entry
  (implies (equiv-thread-except-topframe new-thread old-thread)
           (equiv-thread-table (replace-thread-table-entry old-thread
                                                           new-thread tt)
                               tt)))

(defthm opstack-local-primitives-preserve-equiv-state-2
  (and (equiv-state (pushStack v s) s)
       (equiv-state (popStack s) s)
       (equiv-state (state-set-local-at i v s) s)
       (equiv-state (state-set-pc npc s) s))
  :hints (("Goal" :in-theory (enable equiv-state))))



(defthm opstack-local-primitives-preserve-equiv-state-3
   (and (implies (equiv-state s1 s0)
                 (equal (equiv-state (pushStack v s1) s0) t))

        (implies (equiv-state s1 s0)
                 (equal (equiv-state (popStack s1) s0) t))

        (implies (equiv-state s1 s0)
                 (equal (equiv-state (state-set-local-at i v s1) s0) t))
        
        (implies (equiv-state s1 s0)
                 (equal (equiv-state (state-set-pc npc s1) s0) t))))

;;;;; This above is some workaround for the limitation of ACL2.


(defthm pc-state-set-pc
  (equal (pc (state-set-pc ip s))
         ip))

(defthm pc-popStack
  (equal (pc (popStack s))
         (pc s)))

(defthm pc-pushStack
  (equal (pc (pushStack v s))
         (pc s)))

(defthm pc-state-set-local-at
  (equal (pc (state-set-local-at i v s))
         (pc s)))


(defthm pc-popStackN
  (equal (pc (popStackN n s))
         (pc s)))


(defthm state-set-pc-state-set-pc
  (equal (state-set-pc pc1 (state-set-pc pc2 s))
         (state-set-pc pc1 s))
  :hints (("Goal" :in-theory (enable state-set-pc))))


(in-theory (disable pushStack popStack state-set-local-at state-set-pc))

(in-theory (disable inst-opcode)) 

(defthm no-fatal-error?-state-set
  (and (equal (no-fatal-error? (popStack s))
              (no-fatal-error? s))
       (equal (no-fatal-error? (pushStack v s))
              (no-fatal-error? s))
       (equal (no-fatal-error? (state-set-local-at i v s))
              (no-fatal-error? s))
       (equal (no-fatal-error? (state-set-pc npc s))
              (no-fatal-error? s))))

;----------------------------------------------------------------------

;; (program)
;; (acl2::set-guard-checking nil)

;; (include-book "../M6-DJVM-shared/cldc-classtable")
;; ; (acl2::set-guard-checking t)

;; (defconst *ip* 0)
;; (defconst *th* 0)
;; (defconst *h*  nil)
;; (defconst *tt* nil)
;; (defconst *dcl* nil)
;; (defconst *s* (make-state *ip* *th* *h* *tt* *dcl* (make-env
;;                                                     JVM::|*OUT/CLDC-CLASS-TABLE*|)
;;                           nil
;;                           nil))

;; (acl2::set-guard-checking nil)
;; (defconst *s1* (round-robin-run (setup-initial-state "First" '() *s*) 6))

;; (acl2::set-guard-checking t)
;; (logic)
;; (defun init-state ()
;;   *s1*)


(include-book "../M6-DJVM-shared/cldc-classtable")

(include-book "ADD1-init-state")

; define the init-state
; In fact this is not the state that we want to property on. 
; Our proof is about all states that is in some sense equivalent to this
; initial state. 
;
; Thus the init-state is only a way to specified the states that we want to
; prove properties on. 

;----------------------------------------------------------------------
;
; Start reasoning about the next-inst.  
;
; The goal to reduce the next instruction to the intuitive idea of "next"
; instruction in the code stream.
;

;;; property of initial state.
(defun first-method-ptr ()
  '(METHOD-PTR "First"
               "main" ((ARRAY "java.lang.String"))
               VOID))


(defun theMethod ()
  '(METHOD "First" "main"
           (JVM::PARAMETERS (ARRAY "java.lang.String"))
           (JVM::RETURNTYPE . VOID)
           (JVM::ACCESSFLAGS *CLASS* *PUBLIC* *STATIC*)
           (JVM::CODE (JVM::MAX_STACK . 2)
                      (JVM::MAX_LOCAL . 3)
                      (JVM::CODE_LENGTH . 9)
                      (JVM::PARSEDCODE 
                                      ;;(0 (iconst_1))
                                      (0 (iload_2))
                                      (1 (istore_1))
                                      (2 (iload_1))
                                      (3 (iconst_1))
                                      (4 (iadd))
                                      (5 (istore_2))
                                      (6 (iload_2))
                                      (7 (istore_1))
                                      (8 (return))
                                      (JVM::ENDOFCODE 9))
                      (JVM::EXCEPTIONS)
                      (JVM::STACKMAP))))

(defthm deref-method-first-method-ptr
  (equal (deref-method (first-method-ptr) (instance-class-table (init-state)))
         (theMethod)))

;----------------------------------------------------------------------

(defthm init-state-current-thread
  (equal (current-thread (init-state)) 0))

(defthm init-state-current-method-ptr
  (equal (current-method-ptr (init-state))
         (first-method-ptr))
  :hints (("Goal" :in-theory (enable (init-state)))))

(defthm init-state-no-fatal-error?
  (no-fatal-error? (init-state))
  :hints (("Goal" :in-theory (enable (init-state)))))

; property of the "initial state"

;----------------------------------------------------------------------

(in-theory (disable init-state (init-state) (first-method-ptr)
                    first-method-ptr no-fatal-error?))


;----------------------------------------------------------------------

(in-theory (disable next-inst))

;----------------------------------------------------------------------


(defthm equiv-state-init-state-next-inst
  (implies (equiv-state s (init-state))
           (equal (next-inst s)
                  (inst-by-offset (pc s) (theMethod))))
  :hints (("Goal" :in-theory (enable next-inst))))

; this is the first example theorem refered in the paper 
;        "Java Program Verification via a JVM Deep Embedding in ACL2"

;----------------------------------------------------------------------



(defthm first-is-correct-lemma
  (implies (and (equiv-state  s1 (init-state))
                (equal (pc s1) 2))
           (equiv-state (m6step (m6step (m6step s1)))
                        (init-state))))

(defthm first-is-correct
  (implies (and (equiv-state  s1 (init-state))
                (equal (pc s1) 2))
           (equiv-state (m6step s1)
                        (init-state))))

(defthm simple-run-opener
  (implies (syntaxp (quotep n))
           (equal (simple-run s n)
                  (IF (ZP N)
                      S (SIMPLE-RUN (M6STEP S) (- N 1))))))

(in-theory (disable int-fix))

(defthm first-is-correct-1
  (implies (and (equiv-state  s1 (init-state))
                (equal (pc s1) 0))
           (equiv-state (simple-run s1 7)
                        (init-state))))

;; Some show case theorems: during proof development. Those above are used to
;; guide the search for a proper set of lemma to "train" ACL2.

;; Wed Jan  7 23:33:15 2004
;; 
;; Basically says that straight line code's exeuction perserve the equiv-state
;; From equiv-state we could derive a lot of properties --- What is not changing!!
;; 
;;;;;;;;;;;;;;


;----------------------------------------------------------------------

(defthm round-robin-run-opener
  (implies (or (equal (round-robin-schedule s) 0) 
               (zp n))
           (equal (round-robin-run s n)
                  (if (zp n)
                      s
                    (let ((cid (current-thread s)))
                      (if (equal cid -1)
                          (prog2$ (acl2::cw "NO ACTIVE THREAD!~%") s)
                        (prog2$ (acl2::cw "Executing Thread ~p0 Instruction ~p1~%" cid (next-inst s))
                                (let* ((sn (m6step s))
                                       (nid  (round-robin-schedule sn))
                                       (ccid (current-thread sn)))
                                  (if (equal nid -1)
                                      (prog2$ (acl2::cw "Continue executing ~p0~%" ccid)
                                              (round-robin-run sn (- n 1)))
                                    (if (not (equal nid cid))
                                        (prog2$ (acl2::cw 
                                                 "~%~%***************~%switch from THREAD ~p0 to THREAD~p1 ~%**************~%~%" 
                                                 cid nid )
                                                (round-robin-run 
                                                 (loadExecutionEnvironment nid 
                                                                           (storeExecutionEnvironment
                                                                            (state-set-current-thread cid sn))) (- n 1)))
                                      (round-robin-run sn (- n 1)))))))))))
  :hints (("Goal" :in-theory (disable loadexecutionenvironment
                                      storeexecutionenvironment
                                      inst-opcode do-inst-opener)
           :expand (round-robin-run s n))))

(in-theory (disable round-robin-run))

; Like Do-instr-opener, Decide when should ACL2 should use the definition of
; round-robin-run

;----------------------------------------------------------------------

;; about round robin schedule.
(defthm round-robin-schedule-init-state
  (equal (round-robin-schedule (init-state)) 0)
  :hints (("Goal" :in-theory (enable (init-state)))))

(defcong equiv-thread-table equal (len s1) 1
  :hints (("Goal" :in-theory (enable equiv-thread-table))))


;----------------------------------------------------------------------

;; we need this to prove round-robin-schedule 
(defcong equiv-state equal (round-robin-schedule s) 1
  :hints (("Goal" :in-theory (enable round-robin-schedule))))

(in-theory (disable loadexecutionenvironment storeexecutionenvironment round-robin-schedule))

(in-theory (disable int-fix))

(defthm equal-round-robin-schedule-0
  (implies (equiv-state s (init-state))
           (equal (round-robin-schedule s) 0)))



(defthm first-is-correct-3
  (implies (and (equiv-state  s1 (init-state))
                (equal (pc s1) 2))
           (equiv-state (round-robin-run s1 4)
                        (init-state))))

;----------------------------------------------------------------------

;; Note (round-robin-run s1 4)
;; is expanded into 
;;            (STATE-SET-PC
;;                 6
;;                    (POPSTACK
;;                     (STATE-SET-LOCAL-AT
;;                      2
;;                      (pop (OPERAND-STACK
;;                            (CURRENT-FRAME
;;                             (STATE-SET-PC
;;                              5
;;                              (PUSHSTACK
;;                               (INT-FIX
;;                                (+
;;                                 (pop  (OPERAND-STACK
;;                                        (CURRENT-FRAME
;;                                         (STATE-SET-PC
;;                                          4
;;                                          (PUSHSTACK
;;                                           1
;;                                           (STATE-SET-PC 3
;;                                                         (PUSHSTACK (NTH 1 (LOCALS (CURRENT-FRAME S1)))
;;                                                                    S1)))))))
;;                                 (CAR
;;                                  (OPERAND-STACK
;;                                   (CURRENT-FRAME
;;                                    (POPSTACK
;;                                     (STATE-SET-PC
;;                                      4
;;                                      (PUSHSTACK
;;                                       1
;;                                       (STATE-SET-PC
;;                                        3
;;                                        (PUSHSTACK (NTH 1 (LOCALS (CURRENT-FRAME S1)))
;;                                                   S1))))))))))
;;                               (POPSTACK
;;                                (POPSTACK
;;                                 (STATE-SET-PC
;;                                  4
;;                                  (PUSHSTACK
;;                                   1
;;                                   (STATE-SET-PC 3
;;                                                 (PUSHSTACK (NTH 1 (LOCALS (CURRENT-FRAME S1)))
;;                                                            S1)))))))))))
;;                      (STATE-SET-PC
;;                       5
;;                       (PUSHSTACK
;;                        (INT-FIX
;;                         (+
;;                          (CAR
;;                           (OPERAND-STACK
;;                            (CURRENT-FRAME
;;                             (STATE-SET-PC
;;                              4
;;                              (PUSHSTACK
;;                               1
;;                               (STATE-SET-PC 3
;;                                             (PUSHSTACK (NTH 1 (LOCALS (CURRENT-FRAME S1)))
;;                                                        S1)))))))
;;                          (CAR
;;                           (OPERAND-STACK
;;                            (CURRENT-FRAME
;;                             (POPSTACK
;;                              (STATE-SET-PC
;;                               4
;;               (PUSHSTACK
;;                  1
;;                  (STATE-SET-PC 3
;;                                (PUSHSTACK (NTH 1 (LOCALS (CURRENT-FRAME S1)))
;;                                           S1))))))))))
;;        (POPSTACK
;;         (POPSTACK
;;          (STATE-SET-PC
;;             4
;;             (PUSHSTACK
;;                  1
;;                  (STATE-SET-PC 3
;;                                (PUSHSTACK (NTH 1 (LOCALS (CURRENT-FRAME S1)))
;;                                           S1)))))))))))


;----------------------------------------------------------------------

;; Fri Jan  9 00:12:15 2004
;; Why this? 
;; We need the following to prove 
;; (topStack (state-set-pc ....)) is (topStack s)

;;; Theorems about  what is not changing. The proofs are trival. 
;;; ACL2 learns the "quick" facts.

(defthm current-frame-state-set
  (and (equal (current-frame (state-set-pc npc s))
              (current-frame s))
       (equal (current-frame (state-set-heap heap s))
              (current-frame s))
       (equal (current-frame (state-set-error-flag errflg s))
              (current-frame s))
       (equal (current-frame (state-set-class-table classtable s))
              (current-frame s))
       (equal (current-frame (state-set-aux aux s))
              (current-frame s)))
  :hints (("Goal" :in-theory (enable state-set-pc))))


(defthm current-thread-exists?-state-set
  (and (equal (current-thread-exists? (state-set-pc npc s))
              (current-thread-exists? s))
       (equal (current-thread-exists? (state-set-heap heap s))
              (current-thread-exists? s))
       (equal (current-thread-exists? (state-set-error-flag errflg s))
              (current-thread-exists? s))
       (equal (current-thread-exists?(state-set-class-table classtable s))
              (current-thread-exists? s))
       (equal (current-thread-exists? (state-set-aux aux s))
              (current-thread-exists? s)))
  :hints (("Goal" :in-theory (enable state-set-pc))))


;----------------------------------------------------------------------
;;; A failed attempt in characterizing the proof efforts 

;; 
;;
;;  ...
;; Wed Jan  7 23:35:22 2004 
;; ;;; 
;; ;;; Why wff-state??

;; (defthm wff-state-state-set-pc
;;   (implies (wff-state s)
;;            (wff-state (state-set-pc npc s)))
;;   :hints (("Goal" :in-theory (enable state-set-pc))))


(defthm topStack-of-pushStack-of-thread
  (equal (car (operand-stack (top-frame (push-stack-of-thread v thread))))
         v)
  :hints (("Goal" :in-theory (enable push-stack-of-thread))))


(defthm topStack-of-thread-set-local-at
  (equal (car (operand-stack (top-frame (set-local-at-of-thread i v thread))))
         (car (operand-stack (top-frame thread))))
  :hints (("Goal" :in-theory (enable set-local-at-of-thread))))


;----------------------------------------------------------------------
;
;  Some counter intuitive cases from the our choice of implementation 
;
;
;; the following should be true!
;;; 
;;; Some counter intuitive cases from the our choice of implementation 
;;;
;; (skip-proofs
;;  (defthm topStack-state-set-local
;;    (equal (topStack (state-set-local-at i v s))
;;           (topStack s))
;;    :hints (("Goal" :in-theory (enable state-set-local-at)))))

;; 
;; But we may want to limit ourselves to only talking about 'valid cases'
;; 

;;; this is not true!! because we need unique-id-thread-table!!


;; (defthm replace-thread-table-entry-thread-by-id
;;   (implies (and (wff-thread-table tt)
;;                 (unique-id-thread-table tt)
;;                 (equal (thread-id old-thread) id)
;;                 (equal (thread-id new-thread) id)
;;                 (thread-exists? id tt))
;;            (equal (thread-by-id id (replace-thread-table-entry
;;                                      old-thread
;;                                      new-thread tt))
;;                   new-thread))
;;   :hints (("Goal" :in-theory (enable wff-thread-table wff-thread))))

;----------------------------------------------------------------------

(defcong equiv-thread-except-topframe
         equiv-thread-except-topframe (set-local-at-of-thread i v thread) 3)


(defthm thread-by-id-replace-thread-table-entry
  (let ((old-thread (thread-by-id tid tt)))
  (implies (and (equal (thread-id new-thread)  tid)
                (thread-exists? tid tt))
           (equal (thread-by-id tid
                                (replace-thread-table-entry 
                                 old-thread new-thread tt))
                  new-thread))))

(defthm thread-id-wff-thread-table
  (implies (and (wff-thread-table tt)
                (thread-exists? id tt))
           (equal (thread-id (thread-by-id id tt))
                  id)))

(defthm thread-id-is-set-local-at-of-thread
  (equal (thread-id (set-local-at-of-thread i v thread))
         (thread-id thread)))



;;; Thu Jan  8 16:23:15 2004
;;
;; problemetic that 
;; 
;; Without the explicit rewrite rule, ACL2 will not prove the following. 
;; WHY? congruence rule should rewrite ....

(defthm not-thread-exists?-thread-by-id-nil
  (implies (not (thread-exists? id tt))
           (equal (thread-by-id id tt) nil)))


(defthm wff-thread-table-replace-nil-not-changed
  (implies (wff-thread-table tt)
           (equal (thread-by-id id (replace-thread-table-entry nil any tt))
                  (thread-by-id id tt)))
  :hints (("Goal" :in-theory (enable wff-thread-table))))


(defthm topStack-state-set-local
  (implies (wff-thread-table (thread-table s))
           (equal (topStack (state-set-local-at i v s))
                  (topStack s)))
  :hints (("Goal" :in-theory (e/d (state-set-local-at current-frame current-thread-exists?)
                                  (set-local-at-of-thread thread-exists?))
           :cases ((current-thread-exists? s)))))

(defthm topStack-state-set-pc 
  (equal (topStack (state-set-pc npc s))
         (topStack s)))


;; (defthm topStack-of-pushStack 
;;   (equal (topStack (pushStack v s))
;;          v)
;;   :hints (("Goal" :in-theory (enable pushStack current-frame))))
;;
;;; Thu Jan  8 00:07:33 2004 this is not true!!
;;;
;;; because the way we wrote our replace-thread-table-entry 
;;;


(defthm topStack-of-pushStack 
   (implies (and (current-thread-exists? s)
                 (wff-thread-table (thread-table s)))
            (equal (topStack (pushStack v s))
                   v))
   :hints (("Goal" :in-theory (enable pushStack current-frame current-thread-exists?))))

;; now we need to prove other operations perserve wff-thread-table and
;; current-thread-exists?


(in-theory (disable  POP-THREAD-CALL-STACK-REWRITE
                     TOP-THREAD-CALL-STACK-REWRITE))


;; Why we need the following??

;; ;; (defthm wff-thread-implies-push-top-frame-non-top-frames
;; ;;   (implies (wff-thread thread)
;; ;;            (equal (cons  (top-frame thread)
;; ;;                          (non-top-frames thread))
;; ;;                   (thread-call-stack thread)))
;; ;;   :hints (("Goal" :in-theory (enable top-frame non-top-frames
;; ;;                                      wff-thread))))
                 

;; ;; (defthm wff-thread-implies-top-frame
;; ;;   (implies (wff-thread thread)
;; ;;            (wff-call-frame (top-frame thread)))
;; ;;   :hints (("Goal" :in-theory (list* 'topx-frame 'wff-thread 'topx
;; ;;                                    (disable top-thread-call-stack-rewrite)))))


;; ;; (defthm wff-call-frame-implies-equal
;; ;;   (implies (wff-call-frame frame)
;; ;;            (EQUAL (MAKE-FRAME (RETURN-PC FRAME)
;; ;;                               (OPERAND-STACK FRAME)
;; ;;                               (LOCALS FRAME)
;; ;;                               (METHOD-PTR FRAME)
;; ;;                               (SYNC-OBJ-REF FRAME))
;; ;;                   FRAME)))

;; ;; (in-theory (disable wff-call-frame))



;; ;; (in-theory (enable  POP-THREAD-CALL-STACK-REWRITE
;; ;;                     TOP-THREAD-CALL-STACK-REWRITE))

;; Because we want the following to be exactly equal?


;; (skip-proofs
;;  (defthm pop-stack-of-thread-push-stack-of-thread
;;    (implies (wff-thread thread)
;;             (equal (popStack-of-thread (push-stack-of-thread v thread))
;;                    thread))
;;    :hints (("Goal" :in-theory (enable popStack-of-thread 
;;                                       push-stack-of-thread
;;                                       wff-thread)))))




;; (defun th-mem (th tt)
;;   (mem th tt))

;; (defthm not-thread-id-equal-implies-not-mem
;;   (implies (and (not (mem (thread-id thread) 
;;                           (collect-thread-id tt))))
;;            (not (mem thread tt)))))

;; ;; (in-theory (disable id-mem))

;; (defthm mem-not-mem-thread
;;   (let ((id (thread-id new-thread)))
;;     (implies (and (unique-id-thread-table tt)
;;                   (thread-exists? (thread-id new-thread) tt)
;;                   (not (equal (thread-by-id id tt)
;;                               new-thread)))
;;              (not (mem new-thread tt))))
;;     :hints (("Goal" :in-theory (enable thread-exists?))))

;; (in-theory (disable not-thread-id-equal-implies-not-mem))

;; (defthm mem-not-th-mem-thread
;;   (let ((id (thread-id new-thread)))
;;     (implies (and (unique-id-thread-table tt)
;;                   (thread-exists? (thread-id new-thread) tt)
;;                   (not (equal (thread-by-id id tt)
;;                               new-thread)))
;;              (not (th-mem new-thread tt))))
;;   :hints (("Goal" :in-theory (disable unique-id-thread-table))))

;; (in-theory (disable mem-not-mem-thread th-mem))


;; (defthm thread-exists?-mem-thread-by-id
;;   (implies (thread-exists? id tt)
;;            (th-mem (thread-by-id id tt)
;;                    tt))
;;   :hints (("Goal" :in-theory (enable thread-exists? th-mem))))



;; (defthm replace-thread-table-entry-replace-thread-table-entry
;;   (implies (and (not (th-mem c tt))
;;                 (th-mem a tt)
;;                 (not (equal a c)))
;;            (equal (replace-thread-table-entry c b 
;;                                               (replace-thread-table-entry a c tt))
;;                   (replace-thread-table-entry a b tt)))
;;   :hints (("Goal" :in-theory (enable th-mem))))

;; (defthm replace-thread-table-entry-replace-thread-table-entry-2
;;   (equal (replace-thread-table-entry c c tt) 
;;          tt))

;; (defthm replace-thread-table-entry-replace-thread-table-entry-x
;;   (implies (and (equal c a)
;;                 (th-mem a tt))
;;            (equal (replace-thread-table-entry c b 
;;                                               (replace-thread-table-entry a c tt))
;;                   (replace-thread-table-entry a b tt)))
;;   :hints (("Goal" :in-theory (enable th-mem))))


;; (defthm not-equal-thread-call-stack-implies-not-equal
;;   (implies (not (equal (operand-stack (top (thread-call-stack s2)))
;;                        (operand-stack (top (thread-call-stack s1)))))
;;            (not (equal s2 s1))))


;; (defthm not-equal-pushStack-of-thread
;;   (not (equal (push-stack-of-thread v thread)
;;               thread))
;;   :hints (("Goal" :in-theory (enable push-stack-of-thread)
;;            :use ((:instance  not-equal-thread-call-stack-implies-not-equal
;;                              (s2 (push-stack-of-thread v thread))
;;                              (s1 thread))))))




;; (skip-proofs
;;  (defthm popStack-pushStack-1
;;    (implies (wff-state s)
;;             (equal (popStack (pushStack v s))
;;                    s))
;;    :hints (("Goal" :cases ((current-thread-exists? s))
;;             :in-theory (enable popStack pushStack))
;;            ("Subgoal 1''" :in-theory (enable current-thread-exists?)))))


(defthm thread-primitives-state-set-pc
  (and (equal (popStack (state-set-pc npc s))
              (state-set-pc npc (popStack s)))
       (equal (pushStack v  (state-set-pc npc s))
              (state-set-pc npc (pushStack v s)))
       (equal (state-set-local-at i v (state-set-pc npc s))
              (state-set-pc npc (state-set-local-at i v s))))
  :hints (("Goal" :in-theory (enable state-set-pc popStack pushStack
                                     state-set-local-at
                                     state-set-thread-table))))

;;; move pushStack, popStack inside ....


;; this is not true, because of the norm-state.
;; Maybe I should introduce a normal state predicate.

(defthm locals-unchanged-by
  (and (equal (locals (top-frame (push-stack-of-thread v thread)))
              (locals (top-frame thread)))
       (equal (locals (top-frame (popStack-of-thread  thread)))
              (locals (top-frame thread))))
  :hints (("Goal" :in-theory (enable push-stack-of-thread
                                     top-frame
                                     popStack-of-thread))))


(defthm locals-of-set-local-at
  (equal (locals (top-frame (set-local-at-of-thread i v thread)))
         (update-nth i v (locals (top-frame thread))))
  :hints (("Goal" :in-theory (enable set-local-at-of-thread top-frame))))


(in-theory (enable  POP-THREAD-CALL-STACK-REWRITE
                     TOP-THREAD-CALL-STACK-REWRITE))

(defthm local-at-accessor-2
  (implies (and (wff-thread-table (thread-table s))
                (current-thread-exists? s))
           (equal (local-at i (state-set-local-at j v s))
                  (if (equal (nfix i) (nfix j))
                      v
                    (local-at i s))))
  :hints (("Goal" :in-theory (enable state-set-local-at local-at current-frame 
                                     current-thread-exists?))))
          

;; (defthm local-at-accessor-2
;;   (implies (and (current-thread-exists? s)
;;                 (wff-thread-table (thread-table s)))
;;            (equal (local-at i (state-set-local-at j v s))
;;                   (if (equal (nfix i) (nfix j))
;;                       v
;;                     (local-at i s))))
;;   :hints (("Goal" :in-theory (enable state-set-local-at local-at current-frame 
;;                                      current-thread-exists?))))

(defthm local-at-accessor-1
  (and (implies (wff-thread-table (thread-table s))
                (equal (local-at i (popStack s)) 
                       (local-at i s)))
       (implies (wff-thread-table (thread-table s))
                (equal (local-at i (pushStack v s))
                       (local-at i s)))
       (implies (wff-thread-table (thread-table s))
                (equal (local-at i (state-set-pc npc s))
                       (local-at i s))))
       :hints (("Goal" :in-theory (enable popStack pushStack 
                                          current-frame current-thread-exists?)
                :cases ((current-thread-exists? s)))))


(in-theory (disable local-at topStack int-fix))

(in-theory (disable wff-state init-state m6step round-robin-run (init-state)))


; (acl2::set-match-free-error nil)

(defcong equiv-state equiv-state (pushStack v s) 2)
(defcong equiv-state equiv-state (popStack s) 1)
(defcong equiv-state equiv-state (state-set-local-at i v s) 3)

;----------------------------------------------------------------------


(include-book "../M6-DJVM-shared/wff-data-structure")

;; Identify the domain

;----------------------------------------------------------------------



(defthm wff-thread-push-stack-of-thread
  (wff-thread (push-stack-of-thread v thread))
  :hints (("Goal" :in-theory (enable push-stack-of-thread))))

(defthm wff-call-frame-top-frame-push-stack-of-thread
  (implies (wff-call-frame-regular (top-frame thread))
           (wff-call-frame-regular (top-frame (push-stack-of-thread v thread))))
  :hints (("Goal" :in-theory (enable push-stack-of-thread make-frame
                                     wff-call-frame return-pc operand-stack
                                     locals method-ptr sync-obj-ref))))


(defthm wff-thread-table-prevserved-by-pushStack
  (implies (wff-thread-table (thread-table s))
           (wff-thread-table (thread-table (pushStack v s))))
  :hints (("Goal" :in-theory (enable pushStack))))

(defthm wff-call-frame-current-frame-prevserved-by-pushStack
  (implies (and (wff-call-frame-regular (current-frame s))
                (wff-thread-table (thread-table s))
                (current-thread-exists? s))
           (wff-call-frame-regular (current-frame (pushStack v s))))
  :hints (("Goal" :in-theory (enable pushStack current-thread-exists? current-frame))))

(defthm wff-thread-pop-stack-of-thread
  (wff-thread (popStack-of-thread  thread))
  :hints (("Goal" :in-theory (enable popStack-of-thread))))


(defthm wff-call-frame-top-frame-pop-stack-of-thread
  (implies (wff-call-frame-regular (top-frame thread))
           (wff-call-frame-regular (top-frame (popStack-of-thread thread))))
  :hints (("Goal" :in-theory (enable popStack-of-thread make-frame
                                     wff-call-frame return-pc operand-stack
                                     locals method-ptr sync-obj-ref))))


(defthm wff-call-frame-current-frame-prevserved-by-popStack
  (implies (and (wff-call-frame-regular (current-frame s))
                (wff-thread-table (thread-table s))
                (current-thread-exists? s))
           (wff-call-frame-regular (current-frame (popStack s))))
  :hints (("Goal" :in-theory (enable popStack current-thread-exists? current-frame))))


(defthm wff-thread-table-prevserved-by-popStack
  (implies (wff-thread-table (thread-table s))
           (wff-thread-table (thread-table (popStack s))))
  :hints (("Goal" :in-theory (enable popStack))))


(defthm wff-thread-set-local-at-of-thread
  (wff-thread (set-local-at-of-thread i v  thread))
  :hints (("Goal" :in-theory (enable set-local-at-of-thread))))


(defthm wff-call-frame-top-frame-set-local-at-of-thread
  (implies (wff-call-frame-regular (top-frame thread))
           (wff-call-frame-regular (top-frame (set-local-at-of-thread i v  thread))))
  :hints (("Goal" :in-theory (enable set-local-at-of-thread make-frame
                                     wff-call-frame return-pc operand-stack
                                     locals method-ptr sync-obj-ref))))


(defthm wff-call-frame-current-frame-prevserved-by-state-set-local-at
  (implies (and (wff-call-frame-regular (current-frame s))
                (wff-thread-table (thread-table s))
                (current-thread-exists? s))
           (wff-call-frame-regular (current-frame (state-set-local-at i v  s))))
  :hints (("Goal" :in-theory (enable state-set-local-at current-thread-exists? current-frame))))


(defthm wff-thread-table-prevserved-by-set-local
   (implies (wff-thread-table (thread-table s))
            (wff-thread-table (thread-table (state-set-local-at i v s))))
   :hints (("Goal" :in-theory (enable state-set-local-at))))


(defthm current-thread-exists-prevserved-by-pushStack
  (implies (current-thread-exists? s)
           (current-thread-exists? (pushStack v s)))
  :hints (("Goal" :in-theory (enable current-thread-exists? 
                                     pushStack))))

(defthm current-thread-exists-prevserved-by-popStack
   (implies (current-thread-exists? s)
            (current-thread-exists? (popStack s)))
   :hints (("Goal" :in-theory (enable current-thread-exists? popStack))))

(defthm current-thread-exists-prevserved-by-set-local
   (implies (current-thread-exists? s)
            (current-thread-exists? (state-set-local-at i v s)))
   :hints (("Goal" :in-theory (enable current-thread-exists? state-set-local-at))))

;----------------------------------------------------------------------
   
;; We really want this (popStack (pushStack v s)) == s!
;; However this is not always true. Only if s is wff-state-strong in some sense.!!

;----------------------------------------------------------------------


(defthm consp-call-stack-implies-cons-top-frame-non-top-frame
  (implies (consp (thread-call-stack thread))
           (equal (cons (top-frame thread)
                        (non-top-frames thread))
                  (thread-call-stack thread)))
  :hints (("Goal" :in-theory (e/d (top-frame non-top-frames)
                                  (top-thread-call-stack-rewrite
                                   pop-thread-call-stack-rewrite)))))


(defthm wff-thread-implies-push-top-frame-non-top-frames
  (implies (wff-call-frame (top-frame thread))
           (consp (thread-call-stack thread)))
  :hints (("Goal" :in-theory (e/d (top-frame wff-call-frame)
                                  (top-thread-call-stack-rewrite)))))
                 

(defthm pop-stack-of-thread-push-stack-of-thread
  (implies (and (wff-call-frame-regular (top-frame thread))
                (wff-thread-regular thread))
           (equal (popStack-of-thread (push-stack-of-thread v thread))
                  thread))
  :hints (("Goal" :in-theory (enable popStack-of-thread 
                                     push-stack-of-thread
                                     wff-call-frame
                                     wff-thread))))


;; (defthm wff-state-regular-set-tt
;;   (implies (and (equal tt (thread-table s))
;;                 (wff-state-regular s))
;;            (equal (state-set-thread-table tt s)
;;                   s))
;;   :hints (("Goal" :in-theory (enable state-set-thread-table wff-state 
;;                                      make-state pc current-thread  heap
;;                                      thread-table class-table error-flag aux env))))

;; ;; this proof is hard because the our implementation of
;; ;; replace-thread-table-entry 

;; (defthm state-set-thread-table-set-tt
;;   (equal (state-set-thread-table tt1 (state-set-thread-table tt2 s))
;;          (state-set-thread-table tt1 s))
;;   :hints (("Goal" :in-theory (enable state-set-thread-table))))


(in-theory (disable wff-call-frame-regular thread-exists?))


(defthm thread-by-id-wff-thread-table
  (implies (and (thread-exists? id tt)
               (wff-thread-table tt))
          (wff-thread (thread-by-id id tt)))
  :hints (("Goal" :in-theory (enable wff-thread-table thread-exists?))))


(defthm thread-by-id-wff-thread-table-regular
  (implies (and (thread-exists? id tt)
               (wff-thread-table-regular tt))
           (wff-thread-regular (thread-by-id id tt)))
  :hints (("Goal" :in-theory (enable wff-thread-table-regular thread-exists?))))



;; (defthm current-thread-exists-wff-thread-table
;;   (implies (and (current-thread-exists? s)
;;                 (wff-thread-table (thread-table s)))
;;            (wff-thread (thread-by-id (current-thread s)
;;                                      (thread-table s))))
;;   :hints (("Goal" :in-theory (enable current-thread-exists?))))




(defthm collect-thread-id-replace-is-not-changed
  (implies (equal (thread-id new) (thread-id old))
           (equal (collect-thread-id (replace-thread-table-entry old new tt))
                  (collect-thread-id tt))))

(defthm unique-id-thread-table-replace-entry
  (implies (and (unique-id-thread-table tt)
                (equal (thread-id new) (thread-id old)))
           (unique-id-thread-table (replace-thread-table-entry old new tt))))

;----------------------------------------------------------------------

(defthm replace-replace-is-replace
  (implies (and (unique-id-thread-table tt)
                (equal (thread-id thread2) id)
                (equal (thread-id thread1) id)
                (thread-by-id id tt))
           (equal (replace-thread-table-entry thread1 thread2
                       (replace-thread-table-entry (thread-by-id id tt) thread1 tt))
                  (replace-thread-table-entry (thread-by-id id tt) thread2 tt))))



(defthm replace-equal-is-equal
  (equal (replace-thread-table-entry old old tt)
         tt))

;----------------------------------------------------------------------

(in-theory (disable unique-id-thread-table))

(defthm wff-thread-table-regular-implies-wff-thread-table
  (implies (wff-thread-table-regular tt)
           (wff-thread-table tt))
  :hints (("Goal" :in-theory (enable wff-thread-table))))


(defthm popStack-pushStack-is
   (implies (and (current-thread-exists? s)
                 (wff-state-regular s)
                 (unique-id-thread-table    (thread-table s))
                 (wff-call-frame-regular    (current-frame s))
                 (wff-thread-table-regular  (thread-table s)))
            (equal (popStack (pushStack v s))
                    s))
  :hints (("Goal" :in-theory (enable current-frame
                                     thread-exists?
                                     current-thread-exists? 
                                     state-set-thread-table
                                     pushStack popStack topStack))))

; finally, we have what I wanted. 
;
;----------------------------------------------------------------------

(defthm wff-state-regular-pushStack
  (implies (wff-state-regular s)
           (wff-state-regular (pushStack v s)))
  :hints (("Goal" :in-theory (enable pushStack state-set-thread-table wff-state
                                     make-state pc aux current-thread heap
                                     thread-table class-table env
                                     error-flag))))

(defthm unique-id-thread-table-pushStack
  (implies (unique-id-thread-table (thread-table s))
           (unique-id-thread-table (thread-table (pushStack v s))))
  :hints (("Goal" :in-theory (enable pushStack state-set-thread-table))))



(defthm wff-state-regular-popStack
  (implies (wff-state-regular s)
           (wff-state-regular (popStack s)))
  :hints (("Goal" :in-theory (enable popStack state-set-thread-table wff-state
                                     make-state pc aux current-thread heap
                                     thread-table class-table env error-flag))))

(defthm unique-id-thread-table-popStack
  (implies (unique-id-thread-table (thread-table s))
           (unique-id-thread-table (thread-table (popStack s))))
  :hints (("Goal" :in-theory (enable popStack state-set-thread-table))))



(defthm wff-state-regular-state-set-local
  (implies (wff-state-regular s)
           (wff-state-regular (state-set-local-at i v s)))
  :hints (("Goal" :in-theory (enable state-set-local-at state-set-thread-table wff-state
                                     make-state pc aux current-thread heap
                                     thread-table class-table env error-flag))))

(defthm unique-id-thread-table-state-set-local
  (implies (unique-id-thread-table (thread-table s))
           (unique-id-thread-table (thread-table (state-set-local-at i v s))))
  :hints (("Goal" :in-theory (enable state-set-local-at state-set-thread-table))))


(defthm wff-thread-table-regular-replace-regular
  (implies (and (wff-thread-table-regular tt)
                (wff-thread-regular new))
           (wff-thread-table-regular (replace-thread-table-entry old new tt))))


(defthm wff-thread-regular-push-stack-of-thread
  (implies (wff-thread-regular thread)
           (wff-thread-regular (push-stack-of-thread v thread)))
  :hints (("Goal" :in-theory (enable push-stack-of-thread))))

(defthm wff-thread-regular-pop-stack-of-thread
  (implies (wff-thread-regular thread)
           (wff-thread-regular (popstack-of-thread thread)))
  :hints (("Goal" :in-theory (enable popstack-of-thread))))

(defthm wff-thread-regular-state-set-local-at
  (implies (wff-thread-regular thread)
           (wff-thread-regular (set-local-at-of-thread i v thread)))
  :hints (("Goal" :in-theory (enable set-local-at-of-thread))))

(defthm wff-thread-table-regular-pushStack
  (implies (and (wff-thread-table-regular (thread-table s))
                (current-thread-exists? s))
           (wff-thread-table-regular (thread-table (pushStack v s))))
  :hints (("Goal" :in-theory (enable pushStack current-thread-exists?))))


(defthm wff-thread-table-regular-popStack
  (implies (and (wff-thread-table-regular (thread-table s))
                (current-thread-exists? s))
           (wff-thread-table-regular (thread-table (popStack s))))
  :hints (("Goal" :in-theory (enable popStack current-thread-exists?))))



(defthm wff-thread-table-regular-state-set-local-at
  (implies (and (wff-thread-table-regular (thread-table s))
                (current-thread-exists? s))
           (wff-thread-table-regular (thread-table (state-set-local-at i v s))))
  :hints (("Goal" :in-theory (enable state-set-local-at current-thread-exists?))))

;----------------------------------------------------------------------

(defthm first-is-correct-4
  (let ((old (local-at 2 s1)))
  (implies (and (equiv-state s1 (init-state))
                (current-thread-exists? s1)
                (wff-state-regular s1)
                (wff-thread-table-regular (thread-table s1))
                (wff-call-frame-regular (current-frame s1))
                (unique-id-thread-table (thread-table s1))
                (equal (pc s1) 0)
                (integerp old))
           (equal (local-at 2 (round-robin-run s1 7))
                  (int-fix (+ 1 old)))))
  :hints (("Goal" :in-theory (disable unique-id-thread-table))))


;----------------------------------------------------------------------


;----------------------------------------------------------------------

;; EXTENDED DEMO: STRAIGHT LINE CODE!!

#|
(defconst *FirstX*
 (make-class-def
      '(class "FirstX"
            "java.lang.Object"
            (constant_pool)
            (fields)
            (methods
                        (method "<init>"
                              (parameters )
                              (returntype void)
                              (accessflags  *class*  *public* )
                              (code
                                   (max_stack 1) (max_locals 1) (code_length 5)
                                   (parsedcode
                                      (0 (aload_0))
                                      (1 (invokespecial
					(methodCP "<init>" "java.lang.Object" () void)))
                                      (4 (return))
                                      (endofcode 5))
                                   (Exceptions )
                                   (StackMap )))
                        (method "main"
                              (parameters (array (class "java.lang.String")))
                              (returntype void)
                              (accessflags  *class*  *public*  *static* )
                              (code
                                   (max_stack 2) (max_locals 3) (code_length 14)
                                   (parsedcode
                                      (0 (iload_2)) 
                                      (1 (istore_1))
                                      (2 (iload_1))
                                      (3 (iconst_1))
                                      (4 (iadd))
                                      (5 (istore_2))
                                      (6 (iload_2))
                                      (7 (istore_1))
                                      (8 (iconst_2))
                                      (9 (iload_2))
                                      (10 (iload_1))
                                      (11 (iadd))
                                      (12 (iadd))
                                      (13 (istore_2))
                                      (14 (return))
                                      (endofcode 14))
                                   (Exceptions )
                                   (StackMap ))))
            (interfaces)
            (accessflags  *class*  *public*  *super*  *synchronized* )
            (attributes
              (attribute "SourceFile")))))

|#
;----------------------------------------------------------------------

;----------------------------------------------------------------------

(defun first-method-ptr-x ()
  '(METHOD-PTR "FirstX"
               "main" ((ARRAY "java.lang.String"))
               VOID))


(defun theMethod-x ()
  '(METHOD "FirstX" "main"
        (PARAMETERS (ARRAY "java.lang.String"))
        (RETURNTYPE . VOID)
        (ACCESSFLAGS *CLASS* *PUBLIC* *STATIC*)
        (CODE (MAX_STACK . 2)
              (MAX_LOCAL . 3)
              (CODE_LENGTH . 14)
              (PARSEDCODE (0 (ILOAD_2))
                          (1 (ISTORE_1))
                          (2 (ILOAD_1))
                          (3 (ICONST_1))
                          (4 (IADD))
                          (5 (ISTORE_2))
                          (6 (ILOAD_2))
                          (7 (ISTORE_1))
                          (8 (ICONST_2))
                          (9 (ILOAD_2))
                          (10 (ILOAD_1))
                          (11 (IADD))
                          (12 (IADD))
                          (13 (ISTORE_2))
                          (14 (RETURN))
                          (ENDOFCODE 14))
              (EXCEPTIONS)
              (STACKMAP))))

(defthm deref-method-first-method-ptr-x
  (equal (deref-method (first-method-ptr-x) (instance-class-table (init-state-x)))
         (theMethod-x)))

;----------------------------------------------------------------------


(defthm init-state-current-thread-x
  (equal (current-thread (init-state-x)) 0))

(defthm init-state-current-method-ptr-x
  (equal (current-method-ptr (init-state-x))
         (first-method-ptr-x))
  :hints (("Goal" :in-theory (enable (init-state-x)))))

(defthm init-state-no-fatal-error?-x
  (no-fatal-error? (init-state-x))
  :hints (("Goal" :in-theory (enable (init-state-x)))))

;----------------------------------------------------------------------
(in-theory (disable first-method-ptr-x (first-method-ptr-x) theMethod-x init-state-x (init-state-x)))
;----------------------------------------------------------------------

(defthm round-robin-schedule-init-state-x
  (equal (round-robin-schedule (init-state-x)) 0)
  :hints (("Goal" :in-theory (enable (init-state-x)))))


(defthm equal-round-robin-schedule-0-x
  (implies (equiv-state s (init-state-x))
           (equal (round-robin-schedule s) 0)))


;----------------------------------------------------------------------


(defthm equiv-state-init-state-next-inst-x
  (implies (equiv-state s (init-state-x))
           (equal (next-inst s)
                  (inst-by-offset (pc s) (theMethod-x))))
  :hints (("Goal" :in-theory (enable next-inst))))

;; ;----------------------------------------------------------------------
;;
;; (defthm first-is-correct-4-x
;;   (let ((old (local-at 2 s1)))
;;   (implies (and (equiv-state s1 (init-state-x))
;;                 (current-thread-exists? s1)
;;                 (wff-state-regular s1)
;;                 (wff-thread-table-regular (thread-table s1))
;;                 (wff-call-frame-regular (current-frame s1))
;;                 (unique-id-thread-table (thread-table s1))
;;                 (equal (pc s1) 0)
;;                 (integerp old))
;;            (equal (local-at 2 (round-robin-run s1 7))
;;                   (int-fix (+ 1 old)))))
;;   :hints (("Goal" :in-theory (disable unique-id-thread-table))))
;;
;; ;----------------------------------------------------------------------

(include-book "arithmetic-2/meta/top" :dir :system)

(include-book "arithmetic-2/floor-mod/floor-mod" :dir :system)

(defthm int-fix-int-fix-plus
  (implies (and (integerp x)
                (integerp y))
           (equal (int-fix (+ x (int-fix y)))
                  (int-fix (+ x y))))
   :hints (("Goal" :in-theory (enable int-fix))))


(defthm mod-n-a-multpliy-n
  (implies (and (integerp n)
                (integerp y))
           (equal (mod (* n y) n)
                  0))
  :hints (("Goal" :in-theory (enable mod))))


(defthm mod-plus
  (implies (and (integerp x)
                (integerp n)
                (integerp y))
           (equal (mod (+ x (mod y n)) n)
                  (mod (+ x y) n))))


(defthm mod-plus-collorary
  (implies (and (integerp x)
                (integerp n)
                (integerp y))
           (equal (mod (+ (mod x n) (mod y n)) n)
                  (mod (+ x y) n))))


(defthm mod-n-multiply-y-plus
  (implies (and (integerp x)
                (integerp n)
                (integerp y))
           (equal (mod (+ x (* n y)) n)
                  (mod x n))))

;; (defthm mod-n-multiply-specific
;;   (implies (and (integerp x)
;;                 (integerp i)
;;                 (integerp i0))
;;            (equal (mod (* x (+ I (* 4294967296 i0))) 4294967296)
;;                   (mod (* x i) 4294967296))))

(defthm integerp-multiply
  (implies (and (integerp i)
                (integerp x))
           (integerp (* i x))))

(defthm int-fix-multiply
  (implies (and (integerp x)
                (integerp y))
           (equal (int-fix (* x (int-fix y)))
                  (int-fix (* x y))))
  :hints (("Goal" :in-theory (e/d (int-fix)))))



;; (skip-proofs
;;  (defthm int-fix-int-fix-plus
;;    (equal (int-fix (+ x (int-fix y)))
;;           (int-fix (+ x y)))
;;    :hints (("Goal" :in-theory (enable int-fix)))))

;; (skip-proofs
;;  (defthm int-fix-multiply
;;    (equal (int-fix (* x (int-fix y)))
;;           (int-fix (* x y)))
;;    :hints (("Goal" :in-theory (enable int-fix)))))



(defthm first-is-correct-5-x
  (let ((old (local-at 2 s1)))
  (implies (and (equiv-state s1 (init-state-x))
                (current-thread-exists? s1)
                (wff-state-regular s1)
                (wff-thread-table-regular (thread-table s1))
                (wff-call-frame-regular (current-frame s1))
                (unique-id-thread-table (thread-table s1))
                (equal (pc s1) 0)
                (integerp old))
           (equal (local-at 2 (round-robin-run s1 14))
                  (INT-FIX (+ 4 (* 2 old))))))
  :hints (("Goal" :in-theory (disable unique-id-thread-table))))

