(in-package "M6")

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(include-book "../M6/m6-state")
(include-book "../M6/m6-frame-manipulation-primitives")
(include-book "../M6/m6-exceptions")
(include-book "../M6/m6-object-manipulation-primitives")
(include-book "../M6-DJVM-shared/jvm-bytecode")
(include-book "../M6/m6-native")
(include-book "../M6/m6-type-value")
(include-book "../M6/m6-static-initializer")
(include-book "../M6/m6-loader")
(include-book "../M6/m6-linker")

;; ;; not ready to really write down the JVM definition...
;; ;; I need a set of macros. 
;; ;; i need to be familiar with the macros, and decide what I need.

;; ;; but now I am just writing down definitions of a few typical instructions
;; ;; manually to decide what basic operations I need. 

;; ;; assertions. 
;; ;; etc. etc.

;; (acl2::set-verify-guards-eagerness 0)

(defmacro ADVANCE-PC (s)
  `(state-set-pc (+ (pc ,s)
                    (inst-size inst))
                 ,s))


(defmacro LLP (index)
  `(local-at ,index s))

;---------------------------------------------------------------------

;---------------------------------------------------------------------
;-------------------------        A         --------------------------
;---------------------------------------------------------------------

(defun CHECK-ARRAY (array-ref index s)
  (let* ((array (binding array-ref (heap s)))
         (bound (array-bound array)))
    (and (<= 0 index)
         (< index bound))))
               
(defun CHECK-NULL (ref)
  (equal ref -1))

(defun element-at-array (index array-ref s)
  (let ((array-obj (binding array-ref (heap s))))
    (element-at index array-obj)))


(defun execute-AALOAD (inst s)
  (let* ((index (topStack s))
         (array-ref (secondStack s)))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (if (check-array array-ref index s)
          (ADVANCE-PC (pushStack (element-at-array index array-ref s)
                                 (popStack (popStack s))))
        (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))

; Note: 
;;; Only NEWARRAY instruction involves access control during resolution of
;;; symbolic links.

;Defensive: 
;;; REF if not null, points to an object of valid type. (?) 
;;; Check for op stack UNDERFLOW 

;;; Question: How defensive we want AALOAD??

;;;
;;; Maybe it is ok to guarantee that AALOAD points to a object with the outer
;;; most type is ARRAY. (not need to follow the definition of array's element
;;; type, to verify it is still a valid type.
;;; 
;;; The other is implied by consistent-state. To demonstrate the purpose of
;;; bytecode verification, we may want to check more to show that we saved a
;;; lot of runtime checking.

; Bytecode verifier:
;;; Guarantee a valid type and assignable to Array("java.lang.Object")
;;; Guarantee availability of the 

; Informal proof 
;;; BCV ==> No error


; TOP LEVEL Formal proof
; 
; GOAL ONE: show DEFENSIVE MACHINE is MEANINGFUL
;   
;  i.e. by code inspection (1)
;       by proving DEFENSIVE MACHINE preserves an STRONG and intuitive
;       CONSISTENT-STATE  (2)
; 
; GOAL TWO: show current efficient IMPLEMENTATION is legitimate. 
;  i.e. by proving with bytecode verification, the efficient implementation IS
;  the "defensive" version (producing the same state)   
;       
;     1. BCV succeed could guarantee the defensive check on the first
;     instruction succeed. (under consistent-state hyp) 
;
;     2. BCV will succeed on all states  after sig-step  
;        Step defensive machine, the resulting state is more specific than 
;        One of the sig state after the sig-step
;        We proved BCV succeed on general will succeed on specific
;        Thus next Defensive will still succeed. 
;
;     3. IF all defensive check succeed, non-defensive behaves the same as the
;        defensive machine.
;        
; NOTE: consistent-state is needed (probably need to be strenghtened along the
; way for proving BCV succeeds implies defensive succeed.
;
;     
;
; The question: Distinguish runtime EXCEPTIONS with unexpected error! 
;
;     The current JVM some fatalError in fact is unvoidable by BCV (both
;     defensive and non defensive machine will behave the same)
;     
;     Maybe defensive preserves the consistent-state and non-defensive behave
;     the same is good enough to say BCV is useful (because defensive machine
;     is useful, and after using BCV we know, non-defensive machine behave the
;     same, thus also useful.)
;
;     So the goal two is transformed into 
;     BCV ==> defensive == nondefensive 
;     
;  Mon Dec 19 21:02:40 2005: 
;     DJVM checks for extra conditions. Those conditions should never be
;     violated while exeucting a verified program. 



;  AASTORE 
;; 
;; ;---------------------------------------------------------
;; (defun execute-AASTORE1 (obj-ref index array-ref s)
;;   (let* ((value-obj  (binding obj-ref (heap s)))
;;          (array-obj  (binding array-ref (heap s)))
;;          (array-type (array-type array-obj))
;;          (base-type  (array-base-type array-type)))
;;     (mv-let (status new-s)
;;             (isAssignableTo (obj-type value-obj) base-type s)
;;             (if status
;;                 (set-element-at-array index obj-ref array-ref (popStack
;;                                                                (popStack
;;                                                                 (popStack new-s))))
;;               (raise-exception "java.lang.ArrayStoreException" new-s)))))




; IF a value of particular exists, we can be sure that isAssignableTo won't
; cause class loading!!
; 
; isAssignableTo may only causes class loading in CHECKCAST, INSTANCEOF
; AssignmentCompatible in defensive machine is more like bytecode verifier's
; isAssignableTo.  I don't want it to cause class loading. 
;
; changed "arrayStoreException" to "ArrayStoreException"
;;
;; Note: AASTORE check store respect to the isAssignable relation at runtime
;; That is this is not guaranteed by Bytecode verifier however in principle
;; this can be enforced by the bytecode verifer To compile Java, compiler will
;; need to insert more CHECKCAST so that bytecode could pass.
;; 

; JVMS 2.6.7
; value of type S is assignable to variable/slot of type T.
;
;     * If S is a class type, then:
;           o If T is a class type, then S must be the same class (?2.8.1) as T, or S must be a subclass of T;
;           o If T is an interface type, S must implement (?2.13) interface T.
;     * If S is an interface type, then:
;           o If T is a class type, then T must be Object (?2.4.7).
;           o If T is an interface type, then T must be the same interface as S or a superinterface of S (?2.13.2).
;     * If S is an array type, namely, the type SC[], that is, an array of components of type SC, then:
;           o If T is a class type, then T must be Object (?2.4.7).
;           o If T is an array type TC[], that is, an array of components of type TC, then one of the following must be true:
;                 + TC and SC are the same primitive type (?2.4.1).
;                 + TC and SC are reference types (?2.4.6), and type SC is assignable to TC by these runtime rules.
; o If T is an interface type, T must be one of the interfaces implemented by arrays (?2.15). 
; Here 

; Here at isAssignable is checked at runtime, so (obj-type value-obj) must be a
; class type. It is not possible for obj-type to be an interface type. 
; However in the bytecode verifier, it could be an interface type though.
;
; isAssignableTo is rather complicated. It is different from the isAssignableTo
; in the BCV. BCV's isAssignable is more generaous in return t.
; 



;; ;---------------------------------------------------------
;; (defun execute-AASTORE1 (obj-ref index array-ref s)
;;   (let* ((value-obj  (binding obj-ref (heap s)))
;;          (array-obj  (binding array-ref (heap s)))
;;          (array-type (array-type array-obj))
;;          (base-type  (array-base-type array-type)))
;;     (mv-let (status new-s)
;;             (isAssignableTo (obj-type value-obj) base-type s)
;;             (if status
;;                 (set-element-at-array index obj-ref array-ref (popStack
;;                                                                (popStack
;;                                                                 (popStack new-s))))
;;               (raise-exception "java.lang.ArrayStoreException" new-s)))))

(defun execute-AASTORE (inst s)
  (let* ((obj-ref (topStack s))
         (index   (secondStack s))
         (array-ref (thirdStack s)))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (if (check-array array-ref index s)
          (if (not (CHECK-NULL obj-ref))
              (let* ((value-obj  (binding obj-ref (heap s)))
                     (array-obj  (binding array-ref (heap s)))
                     (array-type (array-type array-obj))
                     (base-type  (array-base-type array-type)))
                (mv-let (status new-s)
                        (isAssignableTo (obj-type value-obj) base-type s)
                        (if status
                            (ADVANCE-PC (set-element-at-array index obj-ref array-ref 
                                                              (popStack (popStack (popStack new-s)))))
                          (raise-exception "java.lang.ArrayStoreException" new-s))))
            (ADVANCE-PC (set-element-at-array index obj-ref array-ref 
                                              (popStack (popStack (popStack s))))))
        (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))

; Defensive:
;; REF is null or REF refers to an object with a valid type. 
;; Check UNDERFLOW. Do I also need to check the max stack of the input state?? 
;; May be that is also a part of the global invariant. 
;
;  (Object  to store is isAssignable to ArrayType) not checked, this is checked
;  at runtime!!
;
;  May need some well form state predicated saying if safe check succeeds,
;  wellformedness are preserved before we can reason about getfield and putfield.

; Bytecode verifier
;; REF is null or REF refers to a valid type 

; Informal proof: 
; quite similiar, invariant is that REF seen by BCV is more general than the
; concrete type seem by Safe JVM
; stack is in range. 

; Note: the difference between proofs for AASTORE and AALOAD are none. 
; AASTORE is different from AALOAD is that it checks more information at
; runtime, in both defensive and non-defensive JVM. Exceptions are thrown.
; 
; Justification for it is because it may not be possible to do bytecode
; verification statically when both Array REF 
; 

;---------------------------------------------------------------------

(defun execute-ACONST_NULL (inst s)
  (ADVANCE-PC (pushStack -1 s)))

; Defensive: check for Stack overflow
;
;
; Bytecode verifier: check for with in range.  
;
;
; Informal proof: 
;; Same 
;

;---------------------------------------------------------------------

(defun execute-ALOAD (inst s)
  (ADVANCE-PC (pushStack (LLP (arg inst)) s)))

; Defensive: 
;    OP STACK OVERFLOW 
;    LOCAL BOUND in RANGE 
;    VALID REF or null 
;   
; BCV:
;    IN RANGE, op, locals
;    valid type
; 
; Informal Proof:
;
;   Invariant guarantee: VALID REF 
;   not relate to valid type result from BCV   
;
;---------------------------------------------------------------------

(defun execute-ALOAD_0 (inst s)
  (ADVANCE-PC (pushStack (LLP 0) s)))

(defun execute-ALOAD_1 (inst s)
  (ADVANCE-PC (pushStack (LLP 1) s)))


(defun execute-ALOAD_2 (inst s)
  (ADVANCE-PC (pushStack (LLP 2) s)))

(defun execute-ALOAD_3 (inst s)
  (ADVANCE-PC (pushStack (LLP 3) s)))


;--------------------------------------------------------------------
; SAME AS ALOAD 
;---------------------------------------------------------------------

(defun execute-anewarray (inst s)
  (let* ((basetype (normalize-type-rep (arg inst)))
         (new-s    (resolveClassReference basetype s))
         (new-s2   (getArrayClass basetype new-s)))
    (if (not (no-fatal-error? new-s))
        new-s
      (if (pending-exception new-s) 
          (raise-exception (pending-exception new-s) new-s)
        (if (not (no-fatal-error? new-s2))
            new-s2
          (if (< (topStack s) 0)
              (raise-exception "java.lang.NegativeArraySizeException" new-s2)
            (ADVANCE-PC (new-array basetype (topStack s) (popStack new-s2)))))))))


;; Tue May 31 17:25:23 2005 Modified to match with DJVM's ANEWARRAY. note this
;; is not an effciency loss.  Tue May 31 17:27:17 2005.

;; (defun execute-anewarray (inst s)
;;   (let* ((basetype (normalize-type-rep (arg inst)))
;;          (new-s    (resolveClassReference basetype s))
;;          (new-s2   (getArrayClass basetype new-s)))
;;     (if (pending-exception new-s) 
;;         (raise-exception (pending-exception new-s) new-s)
;;       ;; check possible exception. 
;;       ;; access permission is checked at resolution time. 
;;       (if (< (topStack s) 0)
;;           (raise-exception "java.lang.NegativeArraySizeException" new-s2)
;;       (ADVANCE-PC (new-array basetype (topStack s) (popStack new-s2)))))))


;; ;;; Fri Apr  2 13:04:54 2004



;
; Defensive: 
;   Resolution succeed/fail link time (shared with BCV?) 
;   no. BCV does not cause resolution. just trust the constant pool entry
;   
;   count < 0 is runtime error.
;   OVERFLOW ??  
;
;   ACCESS PERMISION TO THE RESOLVED FIELD ?? No need to check that 
;   because same resolution step will be doing the checking.
;   Resolution is shared with non-defensive machine 
;   
;   the base type can't be interface type?? It can. 
;   
; BCV:
;
;   BCV does not need to do the resolution.  
;  
;   HOW ABOUT ACCESS PERMISSION? No need. BCV trust the constant pool entry
;   discription.
;
;   Resolution + loader will check that constant pool is telling the truth and
;   catch the inconsistency
;     
;
; Informal Proof:
;   
;   Only real constraints are OP stack etc.  Need invariant that if resolution
;   succeed, the resolved one matches up with constant pool entry description.
;   The invariant is ensured by a careful class loader. (class definition)
;
; Actual Experience:
;  
;   Class loading introduces quite some complexity that we need to say the type
;   hierachy are maintained. Judgement for assignment compatibilty between
;   classes are maintained. And class loading preserve the global invariant. 
; 
;   A lot work. 9000+ lines of proof script. 
;
;
; NOTE: 
;   However the problem of global invariant. 
;
;
;  
;   Thrown exception resulting in a welformed state.  (skip proof?)
;   BCV's next state covers all possible next state.
;  
;---------------------------------------------------------------------



;---------------------------------------------------------------------
;
; ARETURN and RETURNs 
;
; These are complicated, because this need to handle thread, synchronization
; flags correctly.
; (execute-return inst s '1) is ARETURN, IRETURN, FRETURN ... 
;
; In a non-defensive, areturn is similiar to other return
; copy the top entry on the current op stack to ...
; 


(defun isThreadAlive (thread)
  (or (mem 'JVM::thread_suspended (thread-state thread))
      (mem 'JVM::thread_active    (thread-state thread))))

(defun areAliveThreads1 (threads)
  (if (endp threads)
      nil
    (or (isThreadAlive (car threads))
        (areAliveThreads1 (cdr threads)))))

;; it is possible to have suspended thread, but no active thread.

(defun areAliveThreads (s)
  (let ((tt (thread-table s)))
    (areAliveThreads1 tt)))


;; tmp implementation: reschedule 
(defun reschedule (s) 
  s)

;; tmp implementation: terminate 
(defun terminate (s) 
  s)


(defun execute-return1 (return-pc s c)
  (if (equal return-pc 'KILL_THREAD)
      (let ((new-s (stopThread s)))
        (if (areAliveThreads new-s)
            (reschedule new-s) 
          ;; may add a flag to indicate forced the reschedule or do nothing.
          ;; let the top level scheduler decide when to schedule
          (prog2$ (acl2::debug-print "No Thread alive Program Terminated!~%")
                  (terminate new-s)))) 
    (if (equal c 0)
        (popFrame s)
      (if (equal c 1)
          (pushStack (topStack s) (popFrame s))
        (if (equal c 2)
            (pushStack (topStack s)
                       (pushStack (secondStack s) (popFrame s)))
        ;; the last case should be impossible
          s)))))

;; NOTE: is it possible for a JVM to reach a deadlock state? (No active
;; thread?) YES. 
;;
;; Is it possible to have a thread that tries to return from the last call
;; frame? if thread table is well formed, we know every frame has a KILL_THREAD
;; return address.
;; 



;; all returns are the same after bytecode verification, as long as they are
;; returning the same number of entries from the op stack
(defun execute-return (inst s c)
  (declare (ignore inst))
  (let* ((curframe   (current-frame s))
         (return-pc  (return-pc curframe))
         (sync-obj-ref (sync-obj-ref curframe)))
    (if (not (equal sync-obj-ref -1))
        (mv-let (mstatus exceptionname s1)
                (monitorExit sync-obj-ref s)
                (if (equal mstatus 'MonitorStatusError)
                    (raise-exception exceptionname s)
                  (execute-return1 return-pc s1 c)))
      (execute-return1 return-pc s c))))

;--------------------
; Defensive: 
;
;    Check ref refers to valid objects. 
;    return type matches. (isAssignable relation) 
;    
;    Monitor always exists in M6. Non defensive also checks that correct
;    synchronization state. Exceptions are thrown. 
;    
; 
; BCV:
;    Check ref of valid type, isAssignable to return type.    
;
; Informal Proof:
;
;    Invariant is that ref seen by BCV is more general than the one seen by
;    defensive ones.  
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------
; 
; Only requirement is ref refering to an array or is null. 
    
(defun execute-ARRAYLENGTH (inst s)
  (let ((array-ref (topStack s)))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (ADVANCE-PC (pushStack (array-bound (deref array-ref (heap s)))
                             (popStack s))))))


; Defensive: 
;   Valid Array Objects.  check for ? negative length. 
;   or null.
;
; BCV:
;   
;   Valid Type, can be null though.  
;  
; Informal Proof:
;
;   Well formed invariant guarantees every value has the valid type 
;   BCV guarantees the array type. 
;   
;   The difficulty is to prove Defensive machine is somewhat in sync with BCV
;   We can easily prove the first instructions from both model in sync
;   We have to somehow talk about relation between (BCV s) and (BCV  (step s))
;---------------------------------------------------------------------

;---------------------------------------------------------------------
;
; ASTORE 

;; (defun set-local-at-of-thread (index value old-thread)
;;   (let* ((old-call-stack (thread-call-stack old-thread))
;;          (old-top-frame  (top old-call-stack))
;;          (old-locals     (locals old-top-frame))
;;          (new-locals     (update-nth index value old-locals))
;;          (new-top-frame  (frame-set-locals new-locals old-top-frame))
;;          (new-call-stack (push new-top-frame (pop old-call-stack)))
;;          (new-thread     (thread-set-call-stack new-call-stack old-thread)))
;;     new-thread))


;; (defun state-set-local-at (index value s)
;;   (let* ((old-thread-table (thread-table s))
;;          (old-thread (thread-by-id (current-thread s) old-thread-table))
;;          (new-thread (set-local-at-of-thread index value old-thread))
;;          (new-thread-table (replace-thread-table-entry old-thread new-thread
;;                                                        old-thread-table)))
;;     (state-set-thread-table new-thread-table s)))


;;; move to jvm-frame-manipulation-primitives.lisp Tue Mar  9 18:48:08 2004

;; (defun state-set-local-at (index value s)
;;   (let* ((old-thread-table (thread-table s))
;;          (old-thread (thread-by-id (current-thread s) old-thread-table))
;;          (new-thread (set-local-at-of-thread index value old-thread))
;;          (new-thread-table (replace-thread-table-entry old-thread new-thread
;;                                                        old-thread-table)))
;;     (if (current-thread-exists? s)
;;         (state-set-thread-table new-thread-table s)
;;       s)))

(defmacro SET-LP (index value)
  `(state-set-local-at ,index ,value s))

(defun execute-ASTORE (inst s)
  (let* ((index (arg inst))
         (v1 (topStack s)))
    (let ((s (popStack s)))
      (ADVANCE-PC (SET-LP index v1)))))
;
; HANDLING OF WIDE is ignored. 


(defun execute-ASTORE_0 (inst s)
  (ADVANCE-PC (popStack (SET-LP 0 (topStack s)))))

(defun execute-ASTORE_1 (inst s)
  (ADVANCE-PC (popStack (SET-LP 1 (topStack s)))))

(defun execute-ASTORE_2 (inst s)
  (ADVANCE-PC (popStack (SET-LP 2 (topStack s)))))

(defun execute-ASTORE_3 (inst s)
  (ADVANCE-PC (popStack (SET-LP 3 (topStack s)))))

; Defensive: 
;   Valid REF (ensured by invariant) 
;   Within BOUND 
;   or 
;   RETURN ADDRESS (different from ALOAD )
;    
;  
; BCV:
;
;   Within BOUND, REF pointer, null, or RETURN ADDRESS
;   
; 
; Informal Proof:
;
;   Within BOUND BCV
;   Code array remain the same. 
;   (instruction do not change)
;   
;---------------------------------------------------------------------

;---------------------------------------------------------------------

(defun execute-ATHROW (inst s)
  (declare (ignore inst))
  (throw-exception (topStack s) s))


; NOTE: type reference 
;
; Defensive: 
;    must be assignable to Throwable 
; BCV:
;    reference type assignable to Throwable 
;    BCV's assignable is between classes.
;
;    Defensive machine's assignable also talks about Interfaces. 
;    However here Throwable is a CLASS and the actual thing is a CLASS
;    so fine. They should behave the same. 
;
; Informal Proof:
;
;   Invariant, the type that BCV sees always more general
;   The problem is that we need to show BCV in sync with the JVM
;   In sync, BCV will succeed on the more specific state. 
;---------------------------------------------------------------------

; CONVINCE MYSELF 

;---------------------------------------------------------------------
;-------------------------        B         --------------------------
;---------------------------------------------------------------------



;---------------------------------------------------------------------

(defun array-ref-type (array-ref s)
  (array-type (deref array-ref (heap s))))


; (defun execute-BALOAD (inst s)
;   (let* ((index (topStack s))
;          (array-ref (secondStack s)))
;     (if (CHECK-NULL array-ref)
;         (raise-exception "java.lang.NullPointerException" s)
;       (if (check-array array-ref index s)
;           (ADVANCE-PC (pushStack (element-at-array index array-ref s)
;                                  (popStack (popStack ))))
;       (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))

;;
;; this version relies on the fact that in a consistent state, the
;; representation of any array-boolean and array-byte have values of correct
;; range. checking for the type and do the fixing is not necessary.
;; 
;; Bytecode verifier does not distinguish between boolean array and
;; bytearray. However it is not possible to mistreat a boolean array and a int-array,
;; if BASTORE is implemented correctly.
;;



(defun execute-BALOAD (inst s)
 (let* ((index (topStack s))
        (array-ref (secondStack s)))
   (if (CHECK-NULL array-ref)
       (raise-exception "java.lang.NullPointerException" s)
     (if (check-array array-ref index s)
         (let ((array-type (array-ref-type array-ref s)))
           (if (equal array-type '(array boolean))
               (ADVANCE-PC (pushStack (uint-fix (element-at-array index array-ref s))
                                      (popStack (popStack s))))
             (ADVANCE-PC (pushStack (int-fix (element-at-array index array-ref s))
                                    (popStack (popStack s))))))
       (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))

;
; here we assume if not array boolean, not null,  it must be array byte.
;

;
; NOTE: Similar to AALOAD. However type BCV check is the same with defensive check
;
; It is not clear whether loading from a array of boolean we get 1 or 0.
; however the definition of bastore and consistent-state invariant can ensure that.
;
; Defensive: 
;
;    Object of array type, byte array, or boolean array or null.  in principle,
;    we don't have to do uint-fix or int-fix during loading because
;    consistent-state checking will guarantee it. However in a hardware
;    implementation, doing int-fix or uint-fix may not have efficency problem.
; 
; BCV:
;   array type, 
;
;   in fact, small array test.
;   guarantee it is boolean or byte array or null
;
; Informal Proof:
;   Invariant about more general 
;   and more general here is same 
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------
; BASTORE 
;
;; call i-fix etc.
(defun execute-BASTORE (inst s) 
  (let* ((value (topStack s))
         (index (secondStack s))
         (array-ref (thirdStack s)))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (if (check-array array-ref index s)
          (let ((array-type (array-ref-type array-ref s)))
            (if (equal array-type '(array boolean))
                (ADVANCE-PC (popStack 
                             (popStack 
                              (popStack (set-element-at-array index (u-fix value 1) array-ref s)))))
               (ADVANCE-PC (popStack 
                             (popStack 
                              (popStack (set-element-at-array index (byte-fix value) array-ref s)))))))
        (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))

;
; NOTE: 
;   
;   no byte value on stack or in the local. They are treated as normal
;   integers. When store happens, chop the low bits into bytes and packged in
;   the array. 
; 
;   Special handling of boolean type and actual byte type. 
;
; Defensive: 
;
;   check either array of boolean or array of byte or null
;   link AASTORE, check ARRAY TYPE, index type. number of arguments
;   no defensive will assume if not boolean, then it is byte array. 
;
; BCV:
;
; Informal Proof:
;    
;    BCV test and Defensive test are the same. (assuming BCV type is more
;    general).
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------
; BIPUSH 

(defun execute-BIPUSH (inst s)
  (ADVANCE-PC (pushStack (byte-fix (arg inst)) s)))


; NOTE: byte-fix may not be necessary, guaranteed by correctness of jvm2acl2
;       which should never generate a larger int.
;
; Defensive: 
;      stack limit. 
;
; BCV:
;      stack limit checked. 
;
; Informal Proof:
;      
;     same stack limit check. invariant guarantee the stack of the same size.
;   
;---------------------------------------------------------------------

;---------------------------------------------------------------------
;-------------------------        C         --------------------------
;---------------------------------------------------------------------

;---------------------------------------------------------------------
; CALOAD 
;


(defun execute-CALOAD (inst s)
  (let* ((index (topStack s))
         (array-ref (secondStack s)))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (if (check-array array-ref index s)
          (ADVANCE-PC (pushStack (uint-fix (element-at-array index array-ref s))
                                 (popStack (popStack s))))
      (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))

;
; NOTE:
;
;   check-array only check array access bound? 
;   assuming the array-ref point to a valid array object
;   in a valid array of char, zero-extend does not matter.
;  
; Defensive: 
;
;   check array type is null or (array char) check invariant?  (should we check
;   invariant all the time, should we prove that adequate check perserves the
;   invariant)
;
; BCV:
;   check array type (null or array of char)
; Informal Proof:
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------
; CASTORE

(defun execute-CASTORE (inst s)
  (let* ((value (topStack s))
         (index (secondStack s))
         (array-ref (thirdStack s)))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (if (check-array array-ref index s)
          (prog2$ (acl2::debug-print "here")
          (ADVANCE-PC (popStack 
                       (popStack 
                         (popStack (set-element-at-array index (char-fix value) array-ref s))))))
      (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))

; NOTE: 
;
;  basically we want the same structure in defensive machine check and typechecker check 
;  
;  and prove canPop in typechecker.lisp implies canPop in defensive machine on
;  a more specific input.
;  
; Defensive: 
;
;   Check the index is of type integer, array-ref is a array ref or null, value is int type.
;
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------
; CHECKCAST
;
(defun execute-checkcast (inst s)
  (let* ((toClass (normalize-type-rep (arg inst)))
         (new-s   (resolveClassReference toClass s))
         ;; our resolveClassReference is a bit strange in that it doesn't
         ;; actually returns the reference to the class, instead it returns a
         ;; new state. in which class-by-name will give you the representation.
         (obj-ref (topStack s)))
    (if (pending-exception new-s)
        (raise-exception (pending-exception new-s) s)
      ;; possible class not found, access permission etc. 
      (if (no-fatal-error? new-s)
          (if (CHECK-NULL obj-ref)
              (ADVANCE-PC new-s)
            (mv-let (ret new-s2)
                    (isAssignableTo (obj-type (binding obj-ref (heap new-s)))
                                    toClass
                                    new-s)
                    (if ret 
                        (ADVANCE-PC new-s2)
                      (raise-exception "java.lang.ClassCastException" new-s2))))
        new-s))))

; resolveClassReference does not throw any exception, it set fatal error flags.
; This implementation does not throw any exception during resolution. Maybe
; people are not interested in it. (concerning the correctness of the bytecode verifier)
; 
; FIXED. August 13th. 2003
; 
; NOTE:
;
;    CHECKCAST will cause class resoltuion at the runtime. 
;    instruction should check whether exception is thrown during resolution  
;  
; Defensive: 
; 
;  Even defensive machine does not need to guarantee the symbolic references
;  Refers to some class. the exception is treated as an exception.
;  
;  check the value on top of the stack is a reference   
;
; BCV:
;
;  check the value on stack is a reference 
;  
; Informal Proof:
;  
;  same check at BCV time and defensive time. 
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------
;-------------------------        D         --------------------------
;---------------------------------------------------------------------

;---------------------------------------------------------------------
; D2F 
; D2I 
; D2L 
; DADD
; DALOAD
; DASTORE
; DCMP
; DCONST_0
; DCONST_1
; DDIV
; DLOAD
; DLOAD_0
; DLOAD_1
; DLOAD_2
; DLOAD_3
; DMUL
; DNEG
; DREM
; DRETURN -- is return with 2 things current method must have a double
; DSTORE
; DSTORE_0
; DSTORE_1
; DSTORE_2
; DSTORE_3
; DSUB
;
; Above Not Implemented -----------------------------------------------

;---------------------------------------------------------------------
;  DUP  

(defun execute-DUP (inst s)
  (ADVANCE-PC (pushStack (topStack s) s)))

; NOTE: 
;
; Defensive: 
;
;    Category 1 type on top
;    enough stack space 
;
; BCV:
;    Category 1 type on top    
;    enough op stack 
;    
; Informal Proof:
;    Same 
;---------------------------------------------------------------------

;---------------------------------------------------------------------
;

(defun execute-DUP_X1 (inst s)
  (ADVANCE-PC (pushStack (topStack s)
                         (pushStack (secondStack s)
                                    (pushStack (topStack s)
                                               (popStack (popStack s)))))))

;
; NOTE:  
;        
; Defensive: 
;   check category 1 type. (category 1 type occupies one slot)
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------

(defun execute-DUP_X2 (inst s)
  (ADVANCE-PC (pushStack (topStack s)
                (pushStack (secondStack s)
                   (pushStack (thirdStack s)
                       (pushStack (topStack s)
                             (popStack (popStack (popStack s)))))))))

; NOTE:
;
; Defensive: 
;
; BCV:
;
; Informal Proof:
;---------------------------------------------------------------------

;---------------------------------------------------------------------
;

(defun execute-DUP2 (inst s)
  (ADVANCE-PC (pushStack (topStack s)
                         (pushStack (secondStack s) s))))

; NOTE:
;
; Defensive: 
;          form1 2 category 1
;          form2 1 category 2
; BCV:
;
; Informal Proof:
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------
(defun execute-DUP2_X1 (inst s)
  (ADVANCE-PC (pushStack (topStack s)
                (pushStack (secondStack s)
                   (pushStack (thirdStack s)
                       (pushStack (topStack s)
                           (pushStack (secondStack s)
                                (popStack (popStack (popStack s))))))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------
;
(defun execute-DUP2_X2 (inst s)
  (ADVANCE-PC (pushStack (topStack s)
                 (pushStack (secondStack s)
                      (pushStack (thirdStack s)
                          (pushStack (fourthStack s)
                              (pushStack (topStack s)
                                  (pushStack (secondStack s) 
                                        (popStack (popStack (popStack (popStack s))))))))))))
       

; NOTE:
;
; Defensive: 
;   form1 form2 form3 form4
;
; BCV:
;
; Informal Proof:
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------
;-------------------------        F         --------------------------
;---------------------------------------------------------------------

;---------------------------------------------------------------------
; F2D 
; F2I 
; F2L 
; FADD
; FALOAD
; FASTORE
; FCMPG
; FCMPL
; FCONST_0
; FCONST_1
; FCONST_2
; FDIV
; FLOAD
; FLOAD_0
; FLOAD_1
; FLOAD_2
; FLOAD_3
; FMUL
; FNEG
; FREM
; FRETURN -- is return with 2 things current method must have a double
; FSTORE
; FSTORE_0
; FSTORE_1
; FSTORE_2
; FSTORE_3
; FSUB
;
; Above Not Implemented -----------------------------------------------


;---------------------------------------------------------------------
;-------------------------        G         --------------------------
;---------------------------------------------------------------------

;---------------------------------------------------------------------
; GETFIELD 
; 

;; (defun field-size (field-rep) 
;;   (type-size (field-fieldtype field-rep)))

;; Sun May 16 17:17:15 2004. moved to jvm-bytecode.lisp
;; guard verification is skipped in jvm-bytecode-guard-verification.lisp

(defun execute-getfield1 (field-rep s)
  (let* ((obj-ref   (topStack s))
         (classname (field-classname field-rep))
         (fieldname (field-fieldname field-rep))
         (value     (m6-getfield classname fieldname obj-ref s)))
         (if (CHECK-NULL obj-ref)
             ;;(raise-exception "java.lang.NullPointerException" s)
             (state-set-pending-exception-safe "java.lang.NullPointerException" s)
           (if (equal (field-size field-rep) 2)
               (pushLong value (popStack s))
             (pushStack value (popStack s))))))
           


;; (defun fatalSlotError (fieldCP s)
;;   (declare (ignore fieldCP))
;;   (fatalError "field not found" s))

;; moved to jvm-bytecode.lisp
;; Sun May 16 17:17:52 2004


(defun execute-getfield (inst s)
    (let* ((fieldCP (arg inst)))
    (mv-let (field-rep new-s)
            (resolveFieldReference fieldCP s)
            (if (not (no-fatal-error? new-s))
                new-s
              (if (pending-exception s)
                  (raise-exception (pending-exception s) s)
                (if field-rep  ;; if resolve failed, field-rep is nil
                    (let ((new-s2 (execute-getfield1 field-rep new-s)))
                      (if (pending-exception new-s2)
                          (raise-exception (pending-exception new-s2) new-s2)
                        (ADVANCE-PC new-s2)))
                  (fatalSlotError fieldCP new-s)))))))



;;; We know that resolveClassReference will not thrown exception..
;;; .... resolveFieldReference may be. (in fact, it will only thrown 
;;; an exception 


; NOTE:
;    
; This implementation does not throw exception properly. 
; FIXED: August 13, 2003.        
;
; Defensive: 
;   check access permission. 
;
;     1) from the current class to the resolved class
;
;     2) from the current object to the resolved class 
;          if resolved class is a superclass of the current class
;          the resolved field is protected
;          current class is not in the same package
;
;             ensure current object is an instance of the current class or an
;             instance of a subclass of the current class.
; 
;   check the object used to get the field, is an instance assignable to the
;   class. (whether it is accessible is not checked)
;   
;   IN FACT, WE ARE ALLOWED TO ACCESS THE PRIVATED MEMBER OF A SUPERCLASS  
;   AS LONG AS THE ACCESS HAPPENS IN a METHOD of A SUPERCLASS.
;
;   One can pass a reference/pointer to a object of type A to a method of B'
;   where B happens to be A's superclass. In that method, we could use the
;   reference to access the private field of that object. 
; 
;   This is getfield, in case of invokevirtual, defensive machine needs check
;   the object has access to the method to be invoked (?) NO. THIS IS NOT
;   Necessary.  We can use an object of subclass and invoke a private method of
;   a superclass. (quite unexpected?) (This is prevented by the JVM spec but
;   not enforced by JVM implementation. The problem is that JVM may not want to
;   enforce this, because getting rid of this is a performance improvement, and
;   can still provide the guarantee.) ACCESS CONTROL is only checked from
;   CURRENT CLASS to the RESOLVED CLASS. (the look up procedure in invokevirtual
;   find the first accessible method with the right sig to the class of the
;   object. MAYBE not necessary, however the JVM implementation does not
;   enforce it. How about Java Language Spec?)
;   
;   Assuming resolution succeed, the current class has to
;    
;   check whether it is not an array type. (this can be the part that are
;   checked at runtime, but the bytecode verifier can check for it.)
;
; BCV: 
;
;   Enforce the protected check. semms to need to rely on the resolution to be
;   correct. If protected and not same package, then enforcing the type of
;   objref is a subclass of current class.
;
;   check not array type, null or a class type.
;     
; Informal Proof:
;
;   BCV, DJVM checks are same?? YES. same, resolution is the from the same
;   class.  No. BCV + M6 + properties of resolveXXX implies DJVM DJVM may
;   detect need to make sure resolveXXX cause an fatal error that are checked
;   by both the DJVM and the M6. If error at resolution time, error at both M6
;   and Defensive machine. (Mmm. I have forgot my plan for how to deal with
;   resolution issue. I seemed to assumed that one will not thrown exception
;   during resolution, but set the fatal error flag. However with the access
;   control stuff (in Summer, 2003) I decided to add the exception facility at
;   this stage (which CLDC may not be supporting). Anyway, the actual run of a
;   JVM need an arbitary scheduler and allow arbitary exception being thrown at
;   any point ..... BCV will still guarantee that non defensive machine will
;   behave similarly.)
;  
;---------------------------------------------------------------------


;---------------------------------------------------------------------

;; (defun static-field-size (static-field-rep)
;;   (type-size (static-field-fieldtype static-field-rep)))


(defun execute-getstatic1 (field-rep s)
  (if (equal (static-field-size field-rep) 2)
      (pushLong (static-field-fieldvalue field-rep) s)
    (pushStack (static-field-fieldvalue field-rep) s)))
               

;; (defun static-field-class-rep (static-field-rep s)
;;   (class-by-name (static-field-classname static-field-rep)
;;                  (instance-class-table s)))
;;
;; in jvm-linker.lisp

;;
;; no need to check access. because our access is checked in the
;; resovleStaticFieldReferences.
;; should defensive check for access explicitly? And we show that check is not
;; necessary because the exact same check is done at the runtime by the resol 
;;

(defun execute-getstatic (inst s)
  (let* ((fieldCP   (arg inst)))
         (mv-let (field-rep new-s)
                 (resolveStaticFieldReference fieldCP s) ;; atomic operation. 
                 (if (pending-exception s)
                     (raise-exception (pending-exception s) s)
                   (if field-rep
                       (let* ((field-class-rep (static-field-class-rep field-rep new-s))
                              (fclassname      (classname field-class-rep)))
                         (if (not (class-initialized? fclassname  new-s))
                             (reschedule (initializeClass fclassname new-s))
                           ;; re-execute the same instruction. 
                           (if (class-rep-in-error-state? field-class-rep) 
                               (fatalError "initialized class expected" new-s)
                             (ADVANCE-PC (execute-getstatic1 field-rep new-s))))) ;; only here advance pc
                     (fatalSlotError fieldCP new-s))))))

; NOTE:
;  
;    Current resolveXXX does not check for access permissions now.  Because of
;    this, a defensive machine can not be guaranteed to never access a protected
;    member. (same with getfield). Check access control
;    
;    FIXED.  08/14/03 
;  
; Defensive: 
;    
;    check well formedness of a class rep? (this is implied by other parts)
;    bytecode verifier can't guarantee this. the combination of bcv + correct
;    jvm implementation guarantee well-formedness of a class rep.  do we want
;    to check for it?  Do we check for consistent-state, before doing any
;    defensive machine step?  this is part of the big consistent-state
;    invariant, providing step safe machine preserve the invariant.
; 
;    If we don't check consistent-state every step, we proved consistent-state
;    is preserved. Then this will be good. Goal One
;    
;    If we check consistent-state every step, stop proceeding if next step
;    causes an error, Goal One is trivial. However to prove defensive == non
;    defensive + BCV still give us the obligation to prove step preserve
;    consistency.
;
;    That's probably what we want to do. NO. I want the first approach.
;    08/14/03 the decision is NOT (08/14/03) to put consistent-state predicate
;    in every defensive.  check every assumption. for example, successful
;    resolution returns a field has matching sig and accessible permission from
;    the current class.
;    
; BCV:
;
;    check getstatic is very simple. 
;    check getfield is more elaborated.  
;  
; Informal Proof:
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------

(defun execute-GOTO (inst s)
  (state-set-pc (arg inst) s))

; NOTE: 
;
;    Goto to an offset in bytecode 
;
; Defensive: 
;     
;    target is a place where an instruction starts.  
;  
;
; BCV:
;    check the same thing. 
;    
; Informal Proof:
;
;   (invariant: program code does not change) ==> both checks are exactly the same
;   
;---------------------------------------------------------------------

;---------------------------------------------------------------------
;
; GOTO_W   This is eliminated by jvm2acl2, guarantee to not appear.
;  


;---------------------------------------------------------------------
;I2B ;   should be implemented
; 
(defun execute-I2B (inst s)
  (ADVANCE-PC (pushStack (byte-fix (topStack s))
                         (popStack s))))

; NOTE:
;   
;   check type and value is intp (however in M5 this can never be false? ("what
;   this mean?  08/14/03) 

;   anything on opstack is int or a long (not particular byte, boolean or char
;   type)
;   
;   need to distinguish between Long and ReturnAddress and Int (byte, char, boolean)
;   
; Defensive: 
;
;   check the flag, when push a byte, push an int instead.
;
; BCV:
;
; Informal Proof:
;
;---------------------------------------------------------------------



;---------------------------------------------------------------------
;I2C ;   should implement these...
(defun execute-I2C (inst s)
  (ADVANCE-PC (pushStack (char-fix (topStack s))
                         (popStack s))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;---------------------------------------------------------------------

;I2D
;I2F
;I2L ;  should be implemented   

;---------------------------------------------------------------------
;

(defun execute-I2L (inst s)
  (ADVANCE-PC (pushLong (long-fix (topStack s))
                        (popStack s))))

; NOTE:
;
;   PUSH a long, need to check the limited on max stack
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------
(defun execute-I2S (inst s)
  (ADVANCE-PC (pushStack  (short-fix (topStack s))
                          (popStack s))))
; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------
;  IADD

(defun execute-IADD (inst s)
  (let ((v1 (topStack s))
        (v2 (secondStack s)))
    (ADVANCE-PC (pushStack  (int-fix (+ v1 v2)) 
                            (popStack (popStack s))))))

; NOTE:
;     Not much interesting
;
; Defensive: 
;
;    check type, number of argument, resulting stack 
;    check next PC 
;
; BCV:
;    same thing.
;    
; Informal Proof:
;    invariant, DJVM frame, matches the BCV frame
;    BCV frame is just more general type
;
;---------------------------------------------------------------------



;---------------------------------------------------------------------
;
(defun execute-IALOAD (inst s)
  (let* ((index (topStack s))
         (array-ref (secondStack s)))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (if (check-array array-ref index s)
          (ADVANCE-PC (pushStack (element-at-array index array-ref s)
                                (popStack (popStack s))))
        (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))

; NOTE:
;    See discussion in AALOAD
;  
; Defensive: How explict we want defensive machine be?  In consistent state, if
;
;    we know a type has an outer '(ARRAY' we know its component type is valid.
;    So if we put consistent state in each instruction, we know checking array
;    has an outer "array" array is adequate to know its component type is
;    valid.
;    Similarly is (REF values). In a consistent state, we know if a REF is
;    bounded, the object that it points to are consistent.
;    
;    Consistent heap object make sure an object refers to an object that is
;    consistent with its field declaration. 
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------
; 
;  IAND 

(defun execute-IAND (inst s)
  (let ((v1 (topStack s))
        (v2 (secondStack s)))
    (ADVANCE-PC (pushStack  (int-fix (logand v1 v2))
                            (popStack (popStack s))))))

; NOTE:
;
;     Assuming v1, v2 are integers, logand returns bitwise AND logand always
;     return a value in range so there is no need to give a int-fix
;
; Defensive: 
;
;     check intp, intp. implication is the returning value is a 32 bit int.
;     
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------
;
;  IASTORE 

(defun execute-IASTORE (inst s)
  (let* ((value (topStack s))
         (index (secondStack s))
         (array-ref (thirdStack s)))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (if (check-array array-ref index s)
          (ADVANCE-PC (popStack 
                       (popStack 
                         (popStack (set-element-at-array index value array-ref s)))))
      (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))

; NOTE:
;
;   This instruction is like AASTORE, need to check whether the array is an ARRAY of INT, value
;   on stack is an INT. It also need to ocheck whether bounds are ok
;
; Defensive: 
;     
;    
;
; BCV:
;  
;  Notice: valid state transition is from (int int (Array int) ... ) to (...)
;  In fact, (int int null) is allowed. (one path can reach an array instruction
;  does not mean we should reject this bytecode, maybe it is possible at run
;  time this path is never taken. So null is needed. 
;  
; Informal Proof:
;
;  Same check. 
;  
;---------------------------------------------------------------------


;---------------------------------------------------------------------

(defun execute-ICONST_M1 (inst s)
  (ADVANCE-PC (pushStack -1 s)))

(defun execute-ICONST_0 (inst s)
  (ADVANCE-PC (pushStack 0 s)))

(defun execute-ICONST_1 (inst s)
  (ADVANCE-PC (pushStack 1 s)))

(defun execute-ICONST_2 (inst s)
  (ADVANCE-PC (pushStack 2 s)))

(defun execute-ICONST_3 (inst s)
  (ADVANCE-PC (pushStack 3 s)))

(defun execute-ICONST_4 (inst s)
  (ADVANCE-PC (pushStack 4 s)))

(defun execute-ICONST_5 (inst s)
  (ADVANCE-PC (pushStack 5 s)))

; NOTE:
;
;   only check minimum: Stack limit, PC in range.
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;        
;   Checks are same, if defensive state are in sync with BCV state. (same
;   number of values on op stack. (in sync invariant, maybe part of more
;   general state predicate. 
; 
;---------------------------------------------------------------------

;---------------------------------------------------------------------
;
;

(defun execute-IDIV (inst s)
  (let ((v2 (topStack s))
        (v1 (secondStack s)))
    (if (equal v2 0)
        (raise-exception "java.lang.ArithmeticException" s)
      (ADVANCE-PC (pushStack  (int-fix (truncate v1 v2))
                              (popStack (popStack s)))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------

(defmacro BRANCHIF (cond) 
  `(if ,cond 
       (state-set-pc (arg inst) 
                     (popStack s))
     (ADVANCE-PC (popStack s))))


(defmacro BRANCHIF2 (cond) 
  `(if ,cond 
       (state-set-pc (arg inst) 
                     (popStack (popStack s)))
     (ADVANCE-PC (popStack (popStack s)))))



;---------------------------------------------------------------------

; IF_ACMPEQ

(defun execute-IF_ACMPEQ (inst s)
  (BRANCHIF2 (equal (topStack s) (secondStack s))))


; NOTE:
;
; Defensive: 
;    CHECK reference type.
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------
;

(defun execute-IF_ACMPNE (inst s)
  (BRANCHIF2 (not (equal (topStack s) (secondStack s)))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------

(defun execute-IF_ICMPEQ (inst s)
  (BRANCHIF2 (= (topStack s) (secondStack s))))

(defun execute-IF_ICMPNE (inst s)
  (BRANCHIF2 (not (= (topStack s) (secondStack s)))))

(defun execute-IF_ICMPLT (inst s)
  (BRANCHIF2 (< (secondStack s) (topStack s))))

(defun execute-IF_ICMPGE (inst s)
  (BRANCHIF2 (>= (secondStack s) (topStack s))))

(defun execute-IF_ICMPGT (inst s)
  (BRANCHIF2 (> (secondStack s) (topStack s))))

(defun execute-IF_ICMPLE (inst s)
  (BRANCHIF2 (<= (secondStack s)  (topStack s))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------



;---------------------------------------------------------------------
;; because the branch address is already resovlved

(defun execute-IFEQ (inst s)
  (BRANCHIF (= (topStack s) 0)))

(defun execute-IFNE (inst s)
  (BRANCHIF (not (= (topStack s) 0))))

(defun execute-IFLT (inst s)
  (BRANCHIF  (< (topStack s) 0)))

(defun execute-IFGE (inst s)
  (BRANCHIF  (>= (topStack s) 0)))

(defun execute-IFGT (inst s)
  (BRANCHIF  (> (topStack s) 0)))

(defun execute-IFLE (inst s)
  (BRANCHIF  (<= (topStack s) 0)))


;
; NOTE:
;
;  Branch is already resolved. In our branch instruction
;  offset is already added. 
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
; 
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------

(defun execute-ifnonnull (inst s)
  (BRANCHIF (not (equal (topStack s) -1)))) ;; -1 is null

; NOTE:  
;       Branch offset is already computed by JVM2ACL2
;
; Defensive: 
;       Check the reference type (including null type)
;
; BCV:
;
;       Same. 
;
; Informal Proof:
;      
;      need the invariant, BCV step produce more general type state than
;      Defensive machine
;
;---------------------------------------------------------------------
    

;---------------------------------------------------------------------

(defun execute-ifnull (inst s)
  (BRANCHIF (equal (topStack s) -1))) ;; -1 is null

; NOTE:
;
;    Same with ifnotnull
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------

(defun arg2 (inst)
  (nth 2 (nth 1 inst)))

(defun execute-IINC (inst s)
  (let* ((index (arg inst))
         (value (arg2 inst)))
   (ADVANCE-PC (SET-LP index (int-fix (+ (LLP index) value))))))

; NOTE:
;
;   Increase local i by a const. do not change stack
;
; Defensive: 
;   
;   expect the local be of correct type. In op stack and local, boolean, short,
;   char are all treated as int.
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------



(defun execute-ILOAD (inst s)
  (ADVANCE-PC (pushStack (LLP (arg inst)) s)))

(defun execute-ILOAD_0 (inst s)
  (ADVANCE-PC (pushStack (LLP 0) s)))

(defun execute-ILOAD_1 (inst s)
  (ADVANCE-PC (pushStack (LLP 1) s)))

(defun execute-ILOAD_2 (inst s)
  (ADVANCE-PC (pushStack (LLP 2) s)))

(defun execute-ILOAD_3 (inst s)
  (ADVANCE-PC (pushStack (LLP 3) s)))



; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------
;
(defun execute-IMUL (inst s)
  (let ((v1 (topStack s))
        (v2 (secondStack s)))
    (ADVANCE-PC (pushStack  (int-fix (* v1 v2)) 
                            (popStack (popStack s))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------

(defun execute-IMUL (inst s)
  (let ((v1 (topStack s))
        (v2 (secondStack s)))
    (ADVANCE-PC (pushStack  (int-fix (* v1 v2)) 
                            (popStack (popStack s))))))

; NOTE:
;
;    like  IADD 
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------



;---------------------------------------------------------------------
(defun execute-INEG (inst s)
  (ADVANCE-PC (pushStack (- 0 (topStack s))
                         (popStack s))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------
;
(defun execute-instanceof (inst s)
  (let* ((toClass (arg inst))
         (new-s   (resolveClassReference toClass s)) 
         (obj-ref (topStack s)))
    (if (not (equal obj-ref -1))
        (mv-let (ret new-s2)
                (isAssignableTo (obj-type (binding obj-ref (heap new-s)))
                                toClass
                                new-s)
                (if ret 
                    (ADVANCE-PC (popStack new-s2))
                  (raise-exception "java.lang.ClassCastException" new-s2)))
      (ADVANCE-PC (popStack new-s)))))

; NOTE:
;
;    This one will cause resolution and may cause class loading.  If format of
;    symbolic link must be right, but if the link points to something that does
;    not exists, not accessible, exception is thrown.
;
; Defensive: 
;   
;   Verify after resolution, if no exception, the field is in fact exists. 
;   And have accessible permission
;
; BCV:
; 
;   only check it is a reference type (has the format (class ...)) or null or
;   array... AssignableTo java.lang.Object. The real checking has to be done
;   using the runtime data. 
; 
; Informal Proof:
;
;   Defensive and non Defensive is the same.
;   In some sense, bytecode verifier does not need to check at all.
;   What does it saved? only catch some error early.
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------


(defun method-rep-to-method-ptr (method-rep)
  (make-method-ptr (method-classname method-rep)
                   (method-methodname method-rep)
                   (method-args       method-rep)
                   (method-returntype method-rep)))



(defun call_method_general (this-ref method s0 invokerSize)
  (let ((accessflags (method-accessflags method))
        (s1 (state-set-pc (+ (pc s0) invokerSize) s0)))
    (cond ((mem '*native* accessflags)
           (invokeNativeFunction method s1))
          ((mem '*abstract* accessflags)
           (fatalError "abstract_method invoked" s0))
          (t (let ((s2 (pushFrameWithPop this-ref method s1)))
               ;; assuming pushFrame always succeed, we can increase our PC
               ;; now. 
               (if (mem '*synchronized* accessflags)
                   (mv-let (mstatus s3)
                           (monitorEnter this-ref s2)
                           (declare (ignore mstatus))
                           (set-curframe-sync-obj this-ref s3))
                 s2))))))



(defun call_interface_method (this-ref method-rep s)
  (call_method_general this-ref method-rep s 5))


(defun isImplementationOf (c1 c2 s)
  (declare (ignore c1 c2 s))
  ;;
  ;; tmp implementation
  ;; depends one whether class loader want to collapse the implements pointers.  
  ;; if so, then isImplementationOf is easier.
  ;; 
  ;; However this is no essential on whether the JVM will crash, 
  ;; defensive machine and none defensive machine will behave the same. 
  ;; It is a point how accurately we model the JVM...
  ;;
  t)


(defun execute-invokeinterface (inst s)
  (let* ((methodCP (arg inst))
         (argCount (arg2 inst))
         (method-ptr (methodCP-to-method-ptr methodCP)))
    (mv-let (method-rep new-s)
            (resolveMethodReference method-ptr nil s)
            (if (pending-exception s)
                (raise-exception (pending-exception s) s)
              (let ((this-ref (top (popStackN argCount new-s))))
                (if (CHECK-NULL this-ref)
                    (raise-exception "java.lang.NullPointerException" s)
                  ;; don't check access
                  (if method-rep                        
                      ;; * need to check if there is execeptions pending... ****
                      ;; RESOLVE is defined in such a way no exceptions are thrown
                      ;; the return value encoded the type of exceptions.
                      (let* ((dynamicClass   
                              (obj-type (binding this-ref (heap s))))
                           ;; actually type of object used to invoke the
                           ;; interface method.  
                           ;; all superclasses are loaded
                             (new-method-ptr (make-method-ptr dynamicClass
                                                              (method-ptr-methodname method-ptr)
                                                              (method-ptr-args-type  method-ptr)
                                                              (method-ptr-returntype  method-ptr)))
                             (closest-method (lookupMethod new-method-ptr new-s))
                             (accessflags    (method-accessflags closest-method)))
                        ;; this doesn't change s
                        ;;
                        ;; The CLDC Bytecode verifier does not guarantee that
                        ;; this lookup procedure will find a method (this is
                        ;; different from the case of invokevirtual, where
                        ;; bytecode verifier guarantee that the type of actual
                        ;; object will be a subclass of the type of the method
                        ;; as refered in the Constant Pool entry. 
                        ;;
                        ;; invokeinterface does not guarantee a object will
                        ;; implement the interfaces. Runtime check must be done
                        ;; to ensure the object really implement the
                        ;; interface! 
                        ;; 
                        ;; Should JVM check for interface is really implemented
                        ;; (which can be quite hard to check)? or Should it
                        ;; check that a method of the right name happen to exists?
                        ;; 
                        ;; invokeinterface here should check that current obj
                        ;; implement the interface, 
                        ;;
                        ;; The class loader should ensure when an class claim
                        ;; to implement a class, corresponding method must
                        ;; exist!!!
                        ;; 
                        ;; Otherwise on every interface method dispatch, such
                        ;; an expensive would be checked. 
                        ;;
                        ;; SO we need to FIX class_loader!!! August 10th, 2003
                        ;;
                        ;; Class loader must maintain such an invariant on the
                        ;; loaded class table
                        ;;
                        ;; in the lookup step, access permission is not
                        ;; checked. private method could be invoked, even some
                        ;; superclass has an public implementation. 
                        ;; 
                        ;; programming convention is that we never strengthen
                        ;; the accesss permissions in subclasses. that could
                        ;; cause unexpected behavior (compiler enforces this
                        ;; but not JVM. JVM allow invoke private method)
                        ;; 
                        ;; depend on how we write class loader, testing a class
                        ;; implementing interface could be quiet difficult.
                        ;;
                        (if (not (isImplementationOf 
                                  dynamicClass (method-ptr-classname method-ptr) new-s))
                            (fatalError "IncompatilbeClassChangeError" new-s)
                          ;;
                          ;; it seems that CLDC does not has this
                          ;; IncompatibleClassChangeError
                          ;;
                          (if (and closest-method
                                   (mem '*public* accessflags)
                                   (not (mem '*static* accessflags)))
                              (call_interface_method this-ref closest-method new-s)
                            (fatalSlotError methodCP new-s))))
                        (fatalSlotError methodCP new-s))))))))

; NOTE:
;
;    Currently, the method for resolve interface method and a normal method is
;    the same. Although it is different in JVMS. However, under the condition
;    that java.lang.Object does not 
; 
;    Question!!: How to guarantee the native function does the right thing?
;    we have to trust it, but how to express this trust?? an axiom says, ...
;
;    This VERSION has a problem. IT DOES NOT CHECK that dynamic class
;    implemented the Interface JUST RESOLVED! NEED TO ADD THAT JUNE 19th 2003
;
; Defensive: 
;     
;    check *method-to-invoke* matches the description of method, types, args. 
;
; BCV:
;
;    check enough argument, check proper types (in fact only object-ref) no 
;    resolution in BCV. check count consistent? 
; 
; Informal Proof:
;  
;    why check count consistent in BCV? catch some error early?  So that native
;    method don't have to understand java type? native will use it to pop n
;    element off?  native method does not has a new frame on the java
;    call-stack.  In fact, in the efficent implementation, parameters are not
;    push into the locals of the native function, native function directly
;    change the state.  without first popping all the parameters on the current
;    op stack and put them into the locals of the native function.
;
;    two lookup procedures are different, however since they look for the same
;    method, if found, we know the found one matches. (because looking-up uses
;    the) in BCV, no resolution is done. 
;   
;    This above paragraph is wrong. In the BCV there is no look up procedure, 
;    performed. it is performed in both defensive and non defensive look.
;    if lookup succeed, it is should match the check at the BCV stage. 
;
;
;    Since in current model, anyone can assign a reference value to a variable
;    of type interface. The safty guarantee is provided by the special
;    interface method resolution procedure and 
;---------------------------------------------------------------------


;---------------------------------------------------------------------
;

(defun method-args-count1 (types)
  (if (endp types)
      0
    (+ (type-size (car types))
       (method-args-count1 (cdr types)))))


(defun method-args-count (method-rep)
  (let ((args (method-args method-rep)))
    (method-args-count1 args)))


(defun call_special_method (this-ref method s)
  (call_method_general this-ref method s 3 ))


(defun execute-invokespecial (inst s)
    (mylet* ((methodCP (arg inst))
             (method-ptr (methodCP-to-method-ptr methodCP)))
    (mv-let (method-rep new-s)
            (resolveMethodReference method-ptr nil s) 
            (if (pending-exception s)
                (raise-exception (pending-exception s) s)
              (let ((this-ref (topStack (popStackN 
                                         (method-args-count method-rep) new-s))))
                (if (CHECK-NULL this-ref)
                    (raise-exception "java.lang.NullPointerException" s)
                  ;; don't check access
                  (if method-rep                        
                      ;; for those special method no dynamic binding. <init> 
                      (call_special_method this-ref method-rep new-s)
                    (fatalSlotError methodCP new-s))))))))

; NOTE:
;
;    invokespecial has complicated behavior to deal with class's with *super*
;    flags on. Resolution changes. What should I do here??
;     
;    Assume that condition: ACC_SUPER set, resolved class is superclass of the
;    current class, resolved class is not <init>, is never satisfied.
;  
;     
;    For example ensure, invokespecial is always used to invoke <init> methods.
; 
;    New JVM spec will also check the access from current class to the resolved class.
;    In particular BCV, need to check the object used to access a protected
;    method     
;
; Defensive: 
;     
;    If we make such assumption, we need to check the resolve method is <init> 
;    ...
;
; BCV:
;
;    BCV need to do something about protected access, besides that it is
;    regular checking check OP stack matches the types indicated in the CP
;    entry.
; 
; Informal Proof:
;
;    If resolve fail, fail both in non defensive and defensive,     
;    if succeed, find the right method with right signature, so BCV sig match
;    will guarantee the defensive match? because BCV's op stack is always more
;    general than defensive machine's op stack.
;  
;    The key it to write out the "more general" and prove that stepping
;    defensive machine is still more specific than stepping the BCV. (if BCV
;    succeeded in the first place
;
;    Although this is the hard part, it may not be the most problematic part.
;        
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------
;  FIXME!!

(defun static-method-class-rep (method-rep s)
  (class-by-name (method-classname method-rep) (instance-class-table s)))


(defun call_static_method (class-ref method-rep s)
  (call_method_general class-ref method-rep s 3))


(defun execute-invokestatic (inst s)
    (let* ((methodCP (arg inst))
           (method-ptr (methodCP-to-method-ptr methodCP)))
    (mv-let (method-rep new-s)
            (resolveMethodReference method-ptr t s) ;; we know class is loaded
            (if (pending-exception s)
                (raise-exception (pending-exception s) s)
              (if method-rep
                  (let* ((class-rep  (static-method-class-rep method-rep new-s))
                         (mclassname (classname class-rep))
                         (class-ref  (class-ref class-rep)))
                    (if (class-rep-in-error-state? class-rep)
                        (fatalError "expected initialized class" new-s)
                      (if (not (class-initialized? mclassname  new-s))
                          (prog2$ (acl2::debug-print "hereXXX")
                                  (reschedule (initializeClass mclassname new-s))) 
                        ;; re-execute the same instruction. 
                        (call_static_method class-ref method-rep new-s))))
                (fatalSlotError methodCP new-s))))))

; NOTE:
;      Why not using resolveStaticMethodReference? check the resolved method is
;      really static?? 
;   
;      Need to update it to check the found one is really "static" and none abstract
;      Also need to check the resolve the method is not <init> or <clinit>
;      
; Defensive: 
;    do resolution succeed check, consistent-state etc.  
;      
;
; BCV:  
;      BCV is really doing the same check for method invocation, op stack
;      matches the function sig.
;
; Informal Proof:
;
;      need the invariant that resolution preserves the consistent-state 
;      
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------
;
;

(defun call_virtual_method (this-ref method s)
  (call_method_general this-ref method s 3 ))


(defun execute-INVOKEVIRTUAL (inst s)
  (let* ((methodCP (arg inst))
         (method-ptr (methodCP-to-method-ptr methodCP)))
    (mv-let (method-rep new-s)
            (resolveMethodReference method-ptr nil s)
            (if (pending-exception s)
                (raise-exception (pending-exception s) s)
              (let ((this-ref (topStack (popStackN 
                                         (method-args-count method-rep) new-s))))
                (if (CHECK-NULL this-ref)
                    (raise-exception "java.lang.NullPointerException" s)
                  ;; don't check access
                  (if method-rep                        
                      ;; * need to check if there is execeptions pending... ****
                      ;; RESOLVE is defined in such a way no exceptions are thrown
                      ;; the return value encoded the type of exceptions.
                      (let* ((dynamicClass   (obj-type (binding this-ref (heap s))))
                             ;; all superclasses are loaded
                             ;; original implementation is wrong, we should
                             ;; start the method lookup from the actual type of
                             ;; the object.
                             ;;
                             ;; Here we have an issue about object having array-type 
                             ;; We need to handle it correctly in
                             ;; lookupMethod!! August 10th. 2003
                             ;;

                             (new-method-ptr (make-method-ptr dynamicClass
                                                              (method-ptr-methodname method-ptr)
                                                              (method-ptr-args-type  method-ptr)
                                                              (method-ptr-returntype  method-ptr)))
                             (closest-method (lookupMethod new-method-ptr new-s)))
                        ;; this doesn't change s
                        (if closest-method
                            (call_virtual_method this-ref closest-method new-s)
                          (fatalSlotError methodCP new-s)))
                    (fatalSlotError methodCP new-s))))))))

; NOTE:
;        access control is only checked at resolution time from current class
;        to the class that the resolved method comes from.
;
; Defensive: 
;
;        Defensive check the protected access (if the resolved method is from a
;        superclass of the current class the object should be subclass of the
;        current class. (However in other cases, access control is not checked
;        at runtime. The lookup process does not guarantee the method found are
;        accessible. 
;
;        Most of access control is done at the resolution time. A little bit at
;        bytecode verification time, a little bit at runtime (check
;        objref implement interfaces -- invokeinterface etc??)
;  
;        The security model is quite subtle here. Only guarantees the source
;        code level access control + special case for protected access. One can
;        constructs a case to invoke a private method, (but not private field)
;        -- because of dynamic binding.
;
; BCV:  
;         
;        
;
; Informal Proof:
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------

(defun execute-IOR (inst s)
  (let ((v1 (topStack s))
        (v2 (secondStack s)))
    (ADVANCE-PC (pushStack  (logior v1 v2)
                            (popStack (popStack s))))))

; NOTE:
;
;    nothing special
;
; Defensive: 
;    
;    check op has enough int type input.
;
; BCV:
;
; Informal Proof:
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------
; 
(defun execute-IREM (inst s)
  (let* ((v2 (topStack s))
         (v1 (secondStack s)))
    (if (equal v1 0)
        (raise-exception "java.lang.ArithmeticException" s)
      (ADVANCE-PC (pushStack (- v1 (* (truncate v1 v2) v2))
                             (popStack (popStack s)))))))

; NOTE:
;   like IDIV 
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------




;---------------------------------------------------------------------
;
; IRETURN

; NOTE:
;
;    Covered in ARETURN
;
; Defensive: 
;    
;   Check the return value matches the return type of the current method
;   non defensive relies on BCV checked it.
;
; BCV:
;   Check the return type 
;
; Informal Proof:
;
;   Invariant the defensive state is more specific
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------


(defun execute-ISHL (inst s)
  (let* ((v2 (topStack s))
         (v1 (secondStack s))
         (shiftval (5-bit-fix v2))
         (rslt (shl v1 shiftval)))
    (ADVANCE-PC (pushStack  (int-fix rslt)
                            (popStack (popStack s))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------;


;---------------------------------------------------------------------


(defun execute-ISHR (inst s)
  (let* ((v2 (topStack s))
         (v1 (secondStack s))
         (shiftval (5-bit-fix v2))
         (rslt (shr v1 shiftval)))
    (ADVANCE-PC (pushStack  (int-fix rslt)
                            (popStack (popStack s))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------;


;---------------------------------------------------------------------

(defun execute-ISTORE (inst s)
  (let* ((index (arg inst))
         (v1 (topStack s)))
    (ADVANCE-PC (popStack (SET-LP index v1)))))

(defun execute-ISTORE_0 (inst s)
  (ADVANCE-PC (popStack (SET-LP 0 (topStack s)))))

(defun execute-ISTORE_1 (inst s)
  (ADVANCE-PC (popStack (SET-LP 1 (topStack s)))))

(defun execute-ISTORE_2 (inst s)
  (ADVANCE-PC (popStack (SET-LP 2 (topStack s)))))

(defun execute-ISTORE_3 (inst s)
  (ADVANCE-PC (popStack (SET-LP 3 (topStack s)))))


; NOTE: 
;
;   how about wide instruction??? Assume translator dealt with it.
;
; Defensive: 
;    check offset in range (<= 0 < maxlocal). need to take care of invalidate
;    any two byte value. 
;
; BCV:
;
;    check range
;
; Informal Proof:
;
;    code won't change 
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------


(defun execute-ISUB (inst s)
  (let ((v2 (topStack s))
        (v1 (secondStack s)))
    (ADVANCE-PC (pushStack  (int-fix (- v1 v2)) 
                            (popStack (popStack s))))))



; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------

(defun iushr (val1 shft)
  (if (< val1 0)
      (+ (shr val1 shft) (shl 1 (- 32 shft)))
    (shr val1 shft)))


(defun execute-IUSHR (inst s)
  (let* ((v2 (topStack s))
         (v1 (secondStack s))
         (shiftval (5-bit-fix v2))
         (rslt (iushr v1 shiftval)))
    (ADVANCE-PC (pushStack  (int-fix rslt)
                            (popStack (popStack s))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------
(defun execute-IXOR (inst s)
  (let ((v1 (topStack s))
        (v2 (secondStack s)))
    (ADVANCE-PC (pushStack  (logxor v1 v2)
                            (popStack (popStack s))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------




;---------------------------------------------------------------------
;-------------------------        J         --------------------------
;---------------------------------------------------------------------


;---------------------------------------------------------------------

(defun execute-jsr (inst s)
  (let ((target (arg inst)))
    (state-set-pc target 
                  (pushStack 
                   (+ (pc s) (inst-size inst)) s))))

; NOTE:
;      NOT PRESENT IN CLDC model 
; Defensive: 
;
;
; BCV:
;
;     not handled. bcv will fail.
;
; Informal Proof:
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------
;-------------------------        L         --------------------------
;---------------------------------------------------------------------

;---------------------------------------------------------------------
; L2D 
; L2F 
; --- NOT IMPLEMENTED 
;---------------------------------------------------------------------


;---------------------------------------------------------------------
(defun execute-L2I (inst s)
  (let ((v1 (topLong s)))
    (ADVANCE-PC (pushStack  (int-fix v1)
                            (popStack (popStack s))))))

; NOTE:
;
; Defensive: 
;    CHECK type, 
;
; BCV:
;
; Informal Proof:
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------
; LADD

(defun execute-LADD (inst s)
  (let ((v1 (topLong s))
        (v2 (topLong (popLong s))))
    (ADVANCE-PC  (pushLong (long-fix (+ v1 v2))
                           (popLong (popLong s))))))

; NOTE:
;    just check types. 
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------

(defun execute-LALOAD (inst s)
  (let* ((index (topStack s))
         (array-ref (secondStack s)))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (if (check-array array-ref index s)
          (ADVANCE-PC (pushLong (element-at-array index array-ref s) 
                                ;; (popStack (popLong s))))
                                (popStack (popStack s)))) ;;; Mon Feb 28
                                  ;;; 16:32:56 2005 qzhang! 
                                  
        (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------


(defun execute-LAND (inst s)
  (let ((v1 (topLong s))
        (v2 (topLong (popLong s))))
    (ADVANCE-PC (pushStack  (long-fix (logand v1 v2))
                            (popStack (popStack s))))))


; NOTE:
;        bitwise AND so no need to have the long-fix
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------
(defun execute-LASTORE (inst s)
  (let* ((value (topLong s))
         (index (topStack (popLong s)))
         (array-ref (secondStack (popLong s))))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (if (check-array array-ref index s)
          (ADVANCE-PC (popStack 
                       (popStack 
                         (popLong (set-element-at-array index value array-ref s)))))
      (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))


; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------
;LCMP

(defun execute-LCMP (inst s)
  (let* ((v2 (topLong s))
         (v1 (topLong (popLong s)))
         (rslt (cond ((< v1 v2) -1)
                     ((equal v1 v2) 0)
                     (t 1))))
    (ADVANCE-PC (pushLong (long-fix rslt)
                          (popStack (popStack s))))))


; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------
;LCONST_0
;LCONST_1

(defun execute-LCONST_0 (inst s)
  (ADVANCE-PC (pushLong 0 s)))

(defun execute-LCONST_1 (inst s)
  (ADVANCE-PC (pushLong 1 s)))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------
; LDC, LDC_W
;

;; should move those around!!

(defun cpentry (index cp)
  (cpentry-value (nth index cp)))

(defun cpentry-at (index s)
  (let* ((class-rep (current-class s))
         (cp (constantpool class-rep)))
      (cpentry index cp)))

(defun execute-LDC (inst s)
  (ADVANCE-PC (pushStack (cpentry-at (arg inst) s) s)))


; NOTE:
;
;    ASSUME LDC_W does not exists after jvm2acl2
;
; Defensive: 
;
;
; BCV: bcv check valid index. runtime check can be avoid.
;      LDC load only int, float, and string reference 
;
; Informal Proof:
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------
; LDC2_W 
; LOAD LONG DOUBLE Assume after jvm2ac2 it does not exists.

(defun execute-LDC2 (inst s)
  (ADVANCE-PC (pushStack (cpentry-at (arg inst) s) s)))

; NOTE:
;
;    need to check the entry really contains a LONG or DOUBLE
;    check the op stack limit
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------
;LDIV
; To be implemented 

(defun execute-LDIV (inst s)
  (let ((v2 (topLong s))
        (v1 (topLong (popLong s))))
    (if (equal v2 0)
        (raise-exception "java.lang.ArithmeticException" s)
      (ADVANCE-PC  (pushLong (long-fix (/ v1 v2))
                             (popLong (popLong s)))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------



;---------------------------------------------------------------------
;LLOAD
;LLOAD_0
;LLOAD_1
;LLOAD_2
;LLOAD_3


(defun execute-LLOAD_0 (inst s)
  (ADVANCE-PC (pushLong (LLP 0) s)))

(defun execute-LLOAD_1 (inst s)
  (ADVANCE-PC (pushLong (LLP 1) s)))

(defun execute-LLOAD_2 (inst s)
  (ADVANCE-PC (pushLong (LLP 2) s)))

(defun execute-LLOAD_3 (inst s)
  (ADVANCE-PC (pushLong (LLP 3) s)))

(defun execute-LLOAD (inst s)
  (ADVANCE-PC (pushLong (LLP (arg inst))
                        s)))

; NOTE:
;
;   In our implementation, long is occupying two slots,
;   however, only the first slot contains the value 
;   LSTORE only write to correct location. 
;   in the defensive 
;   
; Defensive: 
;
;   check the local at the offset are really containing long   
;   
;
; BCV:
;   similar checks 
;
; Informal Proof:
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------

(defun execute-LMUL (inst s)
  (let ((v2 (topLong s))
        (v1 (topLong (popLong s))))
    (ADVANCE-PC  (pushLong (long-fix (* v1 v2))
                           (popLong (popLong s))))))


; LMUL

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------
;LNEG

(defun execute-LNEG (inst s)
  (ADVANCE-PC (pushLong (long-fix (- 0 (topLong s)))
                        (popLong s))))


; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------

(defun lookupswitch-default-target (lookupswitchinfo)
  (nth 1 lookupswitchinfo))

(defun lookupswitch-target-pairs (lookupswitchinfo)
  (nth 3 lookupswitchinfo))

(defun lookupswitch-paircount (lookupswitchinfo)
  (nth 2 lookupswitchinfo))

(defun lookup-lookupswitch (v lookupswitchinfo)
  (if (bound? v (lookupswitch-target-pairs lookupswitchinfo))
      (binding v (lookupswitch-target-pairs lookupswitchinfo))
    (lookupswitch-default-target lookupswitchinfo)))


(defun execute-lookupswitch (inst s)
  (state-set-pc (lookup-lookupswitch (topStack s)
                                     (arg inst))
                (popStack s)))

; NOTE:
;
;     BCV check the keys are ordered of type int
;     offset point to valid instructions. CP entry exists.
;     
; Defensive: 
;     defensive check the similar things. 
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------

; LOR


(defun execute-LOR (inst s)
  (let ((v1 (topLong s))
        (v2 (topLong (popLong s))))
    (ADVANCE-PC (pushLong   (logior v1 v2)
                            (popLong (popLong s))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------

;LREM


(defun execute-LREM (inst s)
  (let ((v2 (topLong s))
        (v1 (topLong (popLong s))))
    (if (equal v2 0)
        (raise-exception "java.lang.ArithmeticException" s)
      (ADVANCE-PC  (pushLong (- v1 (* (truncate v1 v2) v2))
                             (popLong (popLong s)))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


; LRETURN is handled in ARETURN



;---------------------------------------------------------------------
;

(defun execute-LSHL (inst s)
  (let* ((v2 (topLong s))
         (v1 (topLong (popLong s)))
         (shiftval (6-bit-fix v2))
         (rslt (shl v1 shiftval)))
    (ADVANCE-PC (pushLong   (long-fix rslt)
                            (popLong (popLong s))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------


(defun execute-LSHR (inst s)
  (let* ((v2 (topLong s))
         (v1 (topLong (popLong s)))
         (shiftval (6-bit-fix v2))
         (rslt (shr v1 shiftval)))
    (ADVANCE-PC (pushLong   (long-fix rslt)
                            (popLong (popLong s))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------

;LSTORE
;LSTORE_0
;LSTORE_1
;LSTORE_2
;LSTORE_3

(defun execute-LSTORE_0 (inst s)
  (ADVANCE-PC (popLong (SET-LP 0 (topLong s)))))

(defun execute-LSTORE_1 (inst s)
  (ADVANCE-PC (popLong (SET-LP 1 (topLong s)))))

(defun execute-LSTORE_2 (inst s)
  (ADVANCE-PC (popLong (SET-LP 2 (topLong s)))))

(defun execute-LSTORE_3 (inst s)
  (ADVANCE-PC (popStack (SET-LP 3 (topStack s)))))

(defun execute-LSTORE (inst s)
  (ADVANCE-PC (popLong (SET-LP (arg inst) (topLong s)))))

; NOTE:
;
;    In this version we do not try to update (arg inst) + 1 location with `top
;    In defensive version, we will need to do that. or correctly tag the value
;    invalidate the value in (arg inst) + 1
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;---------------------------------------------------------------------

;---------------------------------------------------------------------

; LSUB

(defun execute-LSUB (inst s)
  (let* ((v2 (topLong s))
         (v1 (topLong (popLong s)))
         (rslt (- v1 v2)))
    (ADVANCE-PC (pushLong  (long-fix rslt)
                           (popLong (popLong s))))))


; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------
; LUSHR

(defun lushr (val1 shft)
  (if (< val1 0)
      (+ (shr val1 shft) (shl 1 (- 64 shft)))
    (shr val1 shft)))

(defun execute-LUSHR (inst s)
  (let* ((v2 (topLong s))
         (v1 (topLong (popLong s)))
         (shiftval (6-bit-fix v2))
         (rslt (lushr v1 shiftval)))
    (ADVANCE-PC (pushLong   (long-fix rslt)
                            (popLong (popLong s))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------
(defun execute-LXOR (inst s)
  (let* ((v2 (topLong s))
         (v1 (topLong (popLong s)))
         (rslt (logxor v1 v2)))
    (ADVANCE-PC (pushLong  (long-fix rslt)
                           (popLong (popLong s))))))

; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------
;-------------------------        M         --------------------------
;---------------------------------------------------------------------



;---------------------------------------------------------------------

(defun execute-monitorenter (inst s)
  (let* ((obj-ref (topStack s))
         (new-s   (popStack s)))
    (if (CHECK-NULL obj-ref)
        (raise-exception "java.lang.NullPointerException" new-s)
      (mv-let (mstatus new-s2)
              (monitorEnter obj-ref (ADVANCE-PC new-s))
              (declare (ignore mstatus))
              new-s2))))

; NOTE: 
;    
; Defensive: 
;   check it is a reference type. + whatever is checked by non-defensive machine
;
; BCV:
;
;   check a reference type (notice, null type is also a reference type)
;   we could check null (however the preverify should allow null be passed)
;
; Informal Proof:
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------

(defun execute-monitorexit (inst s)
  (let* ((obj-ref (topStack s))
         (new-s   (popStack s)))
    (if (CHECK-NULL obj-ref)
        (raise-exception "java.lang.NullPointerException" new-s)
      (mv-let (mstatus exceptionname new-s2)
              (monitorexit obj-ref (ADVANCE-PC new-s))
              (if (equal mstatus 'MonitorStatusError)
                  (raise-exception exceptionname s)
              new-s2)))))


; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------
;;   (4 (multianewarray (array (array byte)) 2))
;
; FIXME: resolution may raise exception, current ignored.  The new-multiarray
;        may cause exception, however, now it is a fatal error



(defun multiarray-measure (counts length)
  (if (zp length)
      (cons (cons (+ (len counts) 1) 0) 0)
    (cons (cons (+ (len counts) 1) 0) (+ length 1))))



(mutual-recursion 
 (defun make-multiarray1 (array-type counts s)
   (declare (xargs :measure (multiarray-measure counts 0)))
   (if (endp counts)
       (pushStack -1 s)  
     ;; with the array-ref on the top of the stack
     (mv-let (obj-refs s1)
             (make-multiarray2 (array-base-type array-type)
                               (cdr counts) 
                               (car counts) 
                               s)
             ;; first create all elements of the array
             (let* ((s2 (new-array (array-base-type array-type) 
                                   (car counts)
                                   s1))
                    (array-ref (topStack s2))
                    (s3 (set-array-content obj-refs array-ref s2)))
               s3))))

 (defun make-multiarray2 (array-type counts length s)
   (declare (xargs :measure (multiarray-measure counts length)))
   (if (zp length)
       (mv nil s)
     (mv-let (obj-refs new-s)
             (make-multiarray2 array-type counts (- length 1) s)
             (let* ((new-s2 (make-multiarray1 array-type counts new-s))
                    (obj-ref (topStack new-s2)))
               (mv (cons obj-ref obj-refs) (popStack new-s2)))))))


;; bytecode verifier would ensure the array-type is actually has more depths
;; than dim, here we check the runtime data from stack to ensure there are 
(defun multiarray-stack-non-negative (dim s)
  (if (zp dim)
      t
    (if (< (topStack s) 0)
        nil
      (multiarray-stack-non-negative (- dim 1) (popStack s)))))
  






;; similiar to new-array, assume exception is not thrown here.
(defun new-multiarray (array-type dim s)
  (if (multiarray-stack-non-negative dim s)
      (m6-internal-error "new-multiarray precondition violated" s)
    (let ((counts (reverse (take dim (operand-stack (current-frame s))))))
      (make-multiarray1 array-type counts s))))
    









(defun execute-multianewarray (inst s)
  (let* ((type  (normalize-type-rep (arg inst))) ;; strip off the class
         (dim   (arg2 inst))
         (new-s (resolveClassReference type s))) ;; load all related classes.
    ;; should check exception. currently ignored
    (ADVANCE-PC (new-multiarray type dim new-s))))

; NOTE: 
;
;    will access control be checked at runtime??
;    no. always from the current class to ... 
;    how about array access? no runtime.
;    size for each dimension must be positive. (must be checked at runtime)
;    
;    the dim tells how many argument is provided. 
;    while, the type tell the actual dimension of the array.
;   
;    the type can be class, array, interfaces 
;
; Defensive: access control? 
;    
;
; BCV:  
;
; Informal Proof:
;
;---------------------------------------------------------------------


;---------------------------------------------------------------------
;-------------------------        N         --------------------------
;---------------------------------------------------------------------

;---------------------------------------------------------------------

(defun execute-new (inst s)
  (mylet* ((classname (normalize-type-rep (arg inst)))
           (new-s     (resolveClassReference classname s))
           (class-rep  (class-by-name classname (instance-class-table new-s)))
           (accessflags (class-accessflags class-rep)))
    (if (or (class-rep-in-error-state? class-rep)
            (mem '*interface* accessflags)
            (mem '*abstract*  accessflags))
        (fatalError "bad class can't instantiate" new-s) 
      ;; the conflict between fatal error and exception.
      (if (not (class-initialized? classname new-s))
          (reschedule (initializeClass classname new-s))
        (mv-let (new-obj-ref new-s2)
                (new-instance classname new-s)
                (ADVANCE-PC (pushStack new-obj-ref new-s2)))))))


; NOTE:  
;    non defensive version just assume the class resolved is not array,
;    or interface etc. 
;
;    JVM spec says if the class init failed, execute new may behave like
;    exception are thrown at this instruction. 
;
;    currently class our class initialization implementation won't unroll pass
;    a native call, if class initialization method thrown exception, fail error
;    accurs.
;
; Defensive: 
;
;   check whether it is interface or a array type. 
;   if not accessible, throw error, (access control are the same with non
;   defensive machine)
;   
;
; BCV:
;
;    need to check we are not call new on an array type
;  
; Informal Proof:
;
;    similarity between BCV and defensive and 
;    between defensive and non defensive
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------
          
;; create primitive array. 
;; assuming primitiveArray types are preloaded.      
;; (newarray CHAR)
;; we could in fact check for that.
(defun execute-newarray (inst s)
  (let* ((basetype    (arg inst))
         (arraylength (topStack s)))
    (ADVANCE-PC (new-array basetype arraylength (popStack s)))))

; NOTE:
;
;     check the count on the op stack 
;
; Defensive: 
;    
;        
;  
; BCV:
; 
;    just make sure the type refered by instruction is a primitive type. 
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------


(defun execute-NOP (inst s)
  (ADVANCE-PC s))


; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------



;---------------------------------------------------------------------
;-------------------------        P         --------------------------
;---------------------------------------------------------------------


;---------------------------------------------------------------------
;

(defun execute-POP (inst s)
  (ADVANCE-PC (popStack s)))

(defun execute-POP2 (inst s)
  (ADVANCE-PC (popStack (popStack  s))))


; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------

(defun execute-putfield1 (field-rep s)
  (let* ((classname (field-classname field-rep))
         (fieldname (field-fieldname field-rep)))
    (if (equal (field-size field-rep) 2)
        (let ((obj-ref (topStack (popLong s))))
          (if (CHECK-NULL obj-ref)
              (raise-exception "java.lang.NullPointerException" s)
            (m6-putfield classname fieldname 
                         (topLong s) 
                         obj-ref
                         (popStack (popLong s)))))
      (let ((obj-ref (topStack (popStack s))))
        (if (CHECK-NULL obj-ref)
            (raise-exception "java.lang.NullPointerException" s)
          (m6-putfield classname fieldname 
                         (topStack s) 
                         obj-ref
                         (popStack (popStack s))))))))


(defun execute-putfield (inst s)
    (let* ((fieldCP (arg inst)))
    (mv-let (field-rep new-s)
            (resolveFieldReference fieldCP s)
            (if (pending-exception s)
                (raise-exception (pending-exception s) s)
              (if field-rep
                  (ADVANCE-PC (execute-putfield1 field-rep new-s))
                (fatalSlotError fieldCP new-s))))))



; NOTE: putfield has the same issue as access control and checking on access to
; the protected fields from the current class.
;
; Needs special handling of assign to a field of type Interface!! WRONG! 
; No special handling of assigning to an variable for type interfaces.
; 
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------



(defun set-fieldvalue (field-rep s)
  (if (equal (static-field-size field-rep) 2)
      (let ((value (topStack (popStack s)))) ;; where real value is stored 
        (static-field-set-value value field-rep))
      (let ((value (topStack s))) ;; where real value is stored 
        (static-field-set-value value field-rep))))
    


(defun replace-static-fields-entry (old new tt)
  (if (endp tt)
      nil
    (if (equal (car tt) old)
        (cons new (cdr tt))
      (cons (car tt) (replace-static-fields-entry old new (cdr tt))))))



;; this field-rep must be static 
(defun execute-putstatic1 (old-field-rep s)
  (let* ((classname (static-field-classname old-field-rep))
         (old-instance-class-table (instance-class-table s))
         (old-class-rep (class-by-name classname old-instance-class-table))
         (old-static-fields (static-fields old-class-rep))
         (new-field-rep  (set-fieldvalue old-field-rep s))
         (new-static-fields (replace-static-fields-entry old-field-rep
                                                         new-field-rep
                                                         old-static-fields))
         (new-class-rep (class-rep-set-static-fields new-static-fields
                                                     old-class-rep))
         (new-instance-class-table (replace-class-table-entry old-class-rep
                                                              new-class-rep
                                                              old-instance-class-table)))
    (if (equal (static-field-size old-field-rep) 2)
        (state-set-instance-class-table new-instance-class-table (popLong s))
      (state-set-instance-class-table new-instance-class-table (popStack s)))))
      
                                                              
                                                              
  


(defun execute-putstatic (inst s)
  (let* ((fieldCP (arg inst)))
    (mv-let (field-rep new-s)
            (resolveStaticFieldReference fieldCP s)
            (if (pending-exception s)
                (raise-exception (pending-exception s) s)
              (if field-rep
                  (let* ((field-class-rep (static-field-class-rep field-rep s))
                         (fclassname      (classname field-class-rep)))
                    (if (not (class-initialized? fclassname  new-s))
                        (reschedule (initializeClass fclassname new-s)) ;; re-execute the same instruction. 
                      (if (class-rep-in-error-state? field-class-rep)
                          (fatalError "initialized class expected" new-s)
                        (ADVANCE-PC (execute-putstatic1 field-rep new-s)))))
                   (fatalSlotError fieldCP new-s))))))

; NOTE:
;    put static can cause class initialization. .. (happening in both defensive
;    and non defensive machine
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------
;-------------------------        R         --------------------------
;---------------------------------------------------------------------

;---------------------------------------------------------------------

(defun execute-ret (inst s)
  (let ((retAddrReg (arg inst)))
    (state-set-pc (LLP retAddrReg) s)))


; NOTE:
;
;     RET jump to a location of type returnAddress 
;     The only way to create a returnAddress type value is use jsr
;
; Defensive: 
;     
;
; BCV:
;
;     not present in the CLDC version 
;
; Informal Proof:
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------
;-------------------------        S         --------------------------
;---------------------------------------------------------------------

;---------------------------------------------------------------------

(defun execute-SALOAD (inst s)
  (let* ((index (topStack s))
         (array-ref (secondStack s)))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (if (check-array array-ref index s)
          (ADVANCE-PC (pushStack (int-fix (element-at-array index array-ref s))
                                 (popStack (popStack s))))
      (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))

; NOTE:
;   
;  nothing special, only remark is when a value is loaded, it is sign extended
;  to int. 
;
;  Global invariant should say, an array of short always contains a array of
;  values that can be represented in 16 bits 
; 
;  Care must be taken to ensure that satore to preserve the invariant.
;
; Defensive: 
;  
;  
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------
;; need some n-fix value
(defun execute-SASTORE (inst s)
  (let* ((value (topStack s))
         (index (secondStack s))
         (array-ref (thirdStack s)))
    (if (CHECK-NULL array-ref)
        (raise-exception "java.lang.NullPointerException" s)
      (if (check-array array-ref index s)
          (ADVANCE-PC (popStack 
                       (popStack 
                         (popStack (set-element-at-array index (short-fix value) array-ref s)))))
      (raise-exception "java.lang.ArrayIndexOutOfBoundsException" s)))))


; NOTE:
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------
(defun execute-SIPUSH (inst s)
  (ADVANCE-PC (pushStack (int-fix (arg inst)) s)))

; NOTE:
;
;   assume sipush valid instruction. (arg inst) in range of short
;   int-fix of not does not matter
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------

(defun execute-SWAP (inst s)
  (ADVANCE-PC (pushStack (secondStack s)
                         (pushStack (topStack s)
                                    (popStack (popStack s))))))

; NOTE:
;
;   only works when top two are category 1
;   note: in a defensive machine, values are tagged with data. 
;
; Defensive: 
;
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------

;---------------------------------------------------------------------
;-------------------------        T         --------------------------
;---------------------------------------------------------------------

;---------------------------------------------------------------------
; 

(defun tableswitch-default-target (tableswitchinfo)
  (nth 1 tableswitchinfo))

(defun tableswitch-low-range (tableswitchinfo)
  (car (nth 2 tableswitchinfo)))

(defun tableswitch-high-range (tableswitchinfo)
  (cdr (nth 2 tableswitchinfo)))

(defun tableswitch-table (tableswitchinfo)
  (nth 3 tableswitchinfo))

(defun lookup-tableswitch (index tableswitchinfo)
  (let* ((default (tableswitch-default-target tableswitchinfo))
         (low     (tableswitch-low-range tableswitchinfo))
         (high    (tableswitch-high-range tableswitchinfo)))
    (cond ((and (<= low index)
                (<= index high))
           (nth (- index low) (tableswitch-table tableswitchinfo)))
          (t default))))


(defun execute-tableswitch (inst s)
  (state-set-pc (lookup-tableswitch (topStack s)
                                    (arg inst))
                (popStack s)))


; NOTE:
;
; Defensive: 
;
; BCV:
;
; Informal Proof:
;
;;---------------------------------------------------------------------


;---------------------------------------------------------------------
;-------------------------        W         --------------------------
;---------------------------------------------------------------------

;
; WIDE is eliminated by jvm2acl2 
;

;====================== OLD STUFF ====================


;;; use top to indicate long value.

(defun execute-CUSTOMCODE (inst s)
  (declare (ignore inst))
  (invoke-CUSTOMCODE s))


;;---


;; assume already resolved the offset into absolute addresses.
;; 



;; The purpose of VMSAVE and VMSTORE is to use model context switches before
;; invoking a method that might cause context switch, we need to store the
;; current context. 

;; VMSAVE and VMSTORE is used for debug purprose? have local ip, global ip.
;;
;; save the current addresses, when we pop_off the frame, VMRESTORE will
;; reloaded the 



;; in real jvm a alivethread count is maintained.  in ours, which cares little
;; about performance, will search through the thread-table.
;; 

(defun isThreadAlive (thread)
  (or (mem 'thread_suspended (thread-state thread))
      (mem 'thread_active    (thread-state thread))))

(defun areAliveThreads1 (threads)
  (if (endp threads)
      nil
    (or (isThreadAlive (car threads))
        (areAliveThreads1 (cdr threads)))))

;; it is possible to have suspended thread, but no active thread.

(defun areAliveThreads (s)
  (let ((tt (thread-table s)))
    (areAliveThreads1 tt)))



;;
;; I think we don't need VMSAVE and VMRESTORE ?? VMSAVE and VMRESTORE is for debugger.
;; but how about a context switch happens? 
;;
;; only when we do context switches, we need to save the current pc to
;; saved-pc, when we switch back, we need to do load Execution Env.
;; 
;; we need to record the current PC we are at to re-excute the instruction.
;; Because when context switch happens, we pushed a new frame on to call-stack
;; the return address of that frame natually recorded the 
;; 


;; have a big problem of handling exception.  currently, if A calls B and B
;; raises an exception, because we don't check for exception in A, we
;; procceed.  However as required by JVM spec, we need to abruptly return from
;; A. 

;; we need to add some exception detect test on any function, so that if some
;; callee return a state with exception flags on, we should return the
;; exception state until we read the top-level interpreter loop to handle it.

;; let me proceed to define invokevirtua, when we add exception
;; handling. remember to change...


;; this method won't cause class loading. or method initialization.

;; don't check access now. 


    


 
