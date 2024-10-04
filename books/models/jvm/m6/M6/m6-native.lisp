(in-package "M6")
(include-book "../M6/m6-internal-primitives")
(include-book "../M6/m6-state")
(include-book "../M6/m6-obj")
(include-book "../M6/m6-type-value")
(include-book "../M6/m6-thread")
(include-book "../M6/m6-frame-manipulation-primitives")
(include-book "../M6/m6-monitor-failure-as-java-Exception")
(include-book "../M6/m6-object-manipulation-primitives")
(include-book "../M6/m6-static-initializer")
(include-book "../M6/m6-semantic-primitives-2")
(include-book "../M6/m6-exceptions")

;;(acl2::set-verify-guards-eagerness 0)

(defun obj-class-ref (obj-ref s)
  (let* ((obj (deref obj-ref (heap s)))
         (obj-type (obj-type obj)))
    (if (array-type? obj-type)
        (array-class-ref (array-class-by-name obj-type (array-class-table s)))
      (class-ref (class-by-name obj-type (instance-class-table s))))))


(defconst *Java_java_lang_Object_getClass* 
  (make-method-ptr "java.lang.Object" "getClass" '() "java.lang.Class"))

(defun Java_java_lang_Object_getClass (s)
  (pushStack (obj-class-ref (topStack s) s)
             (popStack s)))

(defconst *Java_java_lang_Object_hashCode* 
  (make-method-ptr "java.lang.Object" "hashCode" '() 'INT))


(defun Java_java_lang_Object_hashCode (s)
  (pushStack (obj-hashcode (deref (topStack s) (heap s)))
             (popStack s)))







(defconst *Java_java_lang_Object_wait_0* 
  (make-method-ptr "java.lang.Object" "wait" '() 'void))

;;  different from KVM source code
(defun Java_java_lang_Object_wait_0 (s)
  (let* ((obj-ref (topStack s)))
    (mv-let (status new-s)
            (monitorWait obj-ref 0 (popStack s))
            (declare (ignore status))
            new-s)))





(defun ll_zero_ge(v)
  (= v 0))


(defconst *Java_java_lang_Object_wait_1* 
  (make-method-ptr "java.lang.Object" "wait" '(LONG) 'void))

;;  different from KVM source code
(defun Java_java_lang_Object_wait_1(s)
  (let* ((period  (topLong s))  ;; Mon May  1 19:43:21 2006!! 
         (obj-ref (topStack (popLong s))))
    (if (ll_zero_ge period)
        (mv-let (status new-s)
                (monitorWait obj-ref period (popStack (popLong s)))
                (declare (ignore status))
                new-s)
      (raise-exception "java.lang.IllegalArgumentException" (popStack (popLong s))))))


(defconst *Java_java_lang_Object_notify* 
  (make-method-ptr "java.lang.Object" "notify" '() 'void))

(defun Java_java_lang_Object_notify(s)
  (let* ((obj-ref (topStack s)))
    (mv-let (status new-s)
            (monitorNotify obj-ref 'SINGLE (popStack s))
            (declare (ignore status))
            new-s)))


(defconst *Java_java_lang_Object_notifyAll* 
  (make-method-ptr "java.lang.Object" "notifyAll" '() 'void))

(defun Java_java_lang_Object_notifyAll(s)
  (let ((obj-ref (topStack s)))
   (mv-let (status new-s)
            (monitorNotify obj-ref 'ALL (popStack s))
            (declare (ignore status))
            new-s)))













;; and so on .... 
(defconst *Java_java_lang_String_charAt* 
  (make-method-ptr "java.lang.String" "charAt" '(INT) 'CHAR))


(defun Java_java_lang_String_charAt (s)
  (let* ((obj-ref (topStack (popStack s)))
         (array-obj-ref (m6-getfield "java.lang.String" "value" obj-ref s)))
    (pushStack (element-at (topStack s)
                           (deref array-obj-ref 
                                  (heap s)))
                           (popStack (popStack s)))))

(defconst *false* 0)
(defconst *true*  1)

(defun sub-array-data (offset count array)
  (if (zp count)
      nil
    (cons (element-at offset array)
          (sub-array-data (+ offset 1)
                          (- count  1)
                          array))))

(defconst *Java_java_lang_String_equals* 
  (make-method-ptr "java.lang.String" "equals" '("java.lang.Object") 'BOOLEAN))


(defun getStringContents (str-ref s)
  (let* ((arr-ref (m6-getfield "java.lang.String" "value" str-ref s))
         (arr-off (m6-getfield "java.lang.String" "offset" str-ref s))
         (arr-cnt (m6-getfield "java.lang.String" "count"  str-ref s))
         (array   (deref arr-ref (heap s))))
    (sub-array-data arr-off arr-cnt array)))



(defun Java_java_lang_String_equals (s) 
  (let* ((obj-ref1 (topStack (popStack s)))
         (obj-ref2 (topStack s)))
    (if (not (equal (obj-type (deref obj-ref1 (heap s)))
                    "java.lang.String"))
        (pushStack *false* (popStack (popStack s)))
      (let ((array-content1 (getStringContents obj-ref1 s))
            (array-content2 (getStringContents obj-ref2 s)))
      (if (equal array-content1 array-content2)
          (pushStack *true* (popStack (popStack s)))
        (pushStack *false* (popStack (popStack s))))))))


;; ;; not used 
;; (defun make-acl2-string (chars)
;;   (coerce chars 'string))

;; (defun code-to-chars (nums)
;;   (if (endp nums)
;;       nil
;;     (cons (code-char (car nums))
;;           (code-to-chars (cdr nums)))))



(defconst *property-configuration* 
  (str-to-array-char-data "microedition.configuration" 0 (length "microedition.configuration")))

(defconst *property-platform* 
  (str-to-array-char-data "microedition.platform"  0 (length  "microedition.platform")))

(defconst *property-encoding* 
  (str-to-array-char-data "microedition.encoding"  0 (length"microedition.encoding")))

(defun getSystemProperty (key)
  (cond ((equal key *property-configuration*)
         "CLDC-1.0")
        ((equal key *property-platform*)
         "palm")
        ((equal key *property-encoding*)
         "ISO8859_1")))
         
(defconst *Java_java_lang_System_getProperty0* 
  (make-method-ptr "java.lang.System" "getProperty0" '("java.lang.String") "java.lang.String"))
    
(defun Java_java_lang_System_getProperty0 (s)
  (let* ((str-ref (topStack s))
         (key     (getStringContents str-ref s)))
    (let ((value (getSystemProperty key)))
      (if (equal value nil)
          (pushStack -1 (popStack s))
        (mv-let (str-ref s1)
                (ACL2-str-to-JavaString-ref  value s)
                (pushStack str-ref (popStack s1)))))))
    
    
(defconst *Java_java_lang_String_indexOf_1*
  (make-method-ptr "java.lang.String" "indexOf" '(INT) 'INT))

(defun indexOf1 (value list from)
  (if (endp list)
      -1
    (if (equal (car list) value)
        from
      (indexOf1 value (cdr list) (+ from 1)))))



(defun indexOf (value list)
  (indexOf1 value list 0))

(defun Java_java_lang_String_indexOf_1 (s)
  (let* ((str-ref (topStack (popStack s)))
         (value   (topStack s))
         (array-data (getStringContents str-ref s)))
    (pushStack (indexOf value array-data)
               (popStack (popStack s)))))

(defconst *Java_java_lang_String_indexOf_2*
  (make-method-ptr "java.lang.String" "indexOf" '(INT INT) 'INT))

(defun Java_java_lang_String_indexOf_2 (s)
  (let* ((str-ref (topStack (popStack (popStack s))))
         (value   (topStack (popStack s)))
         (from    (topStack s))
         (array-data (getStringContents str-ref s)))
    (pushStack (indexOf1 value array-data from)
               (popStack (popStack (popStack s))))))


(defconst *Java_java_lang_StringBuffer_append*
  (make-method-ptr "java.lang.StringBuffer"
                   "append" '("java.lang.String")
                   "java.lang.StringBuffer"))

(defun Java_java_lang_StringBuffer_append (s) 
  ;; I changed the src of CLDC code, so that this method is no longer native.
  s)

(defconst *Java_java_lang_System_arraycopy*
  (make-method-ptr"java.lang.System" "arraycopy"
                  '("java.lang.Object" INT (CLASS "java.lang.Object") INT INT)
                  'VOID))


;; this is called after we know obj-refs are refs 
(defun check-entries (obj-refs type s)
  (if (endp obj-refs)
      (mv t s)
    (if (equal (car obj-refs) -1)
        (check-entries (cdr obj-refs) type s)
      (let* ((obj (deref (car obj-refs) (heap s)))
             (obj-type (obj-type obj)))
        (mv-let (assignable new-s)
                (isAssignableTo obj-type type s)
                (if assignable 
                    (check-entries (cdr obj-refs) type new-s)
                  (mv nil new-s)))))))

;; (defun sub-list (l1 s1 len)
;;   (if (endp l1)
;;       nil
;;     (if (zp s1)
;;         (if (zp len)
;;             nil
;;           (cons (car l1) (sub-list (cdr l1) 0 (- len 1))))
;;       (sub-list (cdr l1) (- s1 1) len))))


;; (defun setChars (l1 s1 l2 s2 len)
;;   (app (sub-list l2 0 s2)
;;        (app (sub-list l1 s1 len)
;;             (sub-list l2 (+ s2 len) (- (len l2) (+ s2 len))))))



(defun Java_java_lang_System_arraycopy (s)
  (let ((length  (topStack s))
        (dstPos  (secondStack s))
        (dst-ref (thirdStack s))
        (srcPos  (fourthStack s))
        (src-ref (fifthStack s))
        (s1      (popStackN 5 s)))
    (if (or (equal dst-ref -1)
            (equal src-ref -1))
        (raise-exception "null pointer" s)
      (let* ((src (deref src-ref (heap s)))
             (dst (deref dst-ref (heap s))))
        (if (or (not (array-type? (obj-type src)))
                (not (array-type? (obj-type dst))))
            (raise-exception "java.lang.ArrayStoreException" s)
          (let* ((src-elem (array-base-type (obj-type src)))
                 (dst-elem (array-base-type (obj-type dst))))
            (if (or  (and (primitive-type?      src-elem)
                          (not (primitive-type? dst-elem)))
                     (and (not (primitive-type? src-elem))
                          (primitive-type?      dst-elem)
                     (and (primitive-type?      src-elem)
                          (primitive-type?      dst-elem)
                          (not (equal src-elem dst-elem)))))
                (raise-exception "java.lang.ArrayStoreException" s)


              (let ((srcEnd (+ length srcPos))
                    (dstEnd (+ length dstPos))
                    (srcLen (array-bound src))
                    (dstLen (array-bound dst)))
                (if (or (< length 0)
                        (< srcPos 0)
                        (< dstPos 0)
                        (and (> length 0)     ;; the case when + warp...
                             (or (< srcEnd 0)
                                 (< dstEnd 0)))
                        (> srcEnd srcLen)
                        (> dstEnd dstLen))
                    (raise-exception 
                     "java.lang.ArrayIndexOutOfBoundsException" s)
                  (if (primitive-type? dst-elem)
                        ;; just copy .. 
                        (let* ((src-data (array-data src))
                               (dst-data (array-data dst))
                               (new-dst-data 
                                (setChars src-data srcPos dst-data dstPos length)))
                          (prog2$ (acl2::debug-print "new dst data ~p0~%" new-dst-data)
                                  (set-array-content new-dst-data dst-ref s)))
                      (mv-let (assignable s2)
                              (isAssignableTo  src-elem dst-elem s1)
                              (if assignable
                                  (let* ((src-data (array-data src))
                                         (dst-data (array-data dst))
                                         (new-dst-data 
                                          (setChars src-data srcPos dst-data dstPos length)))
                                    (set-array-content new-dst-data dst-ref s2))
                                ;; while in case of instance class. more complicated 
                                ;; check one by one.
                                (let ((new-data (sub-array-data srcPos length src)))
                                  (mv-let (assignable s3)
                                          (check-entries new-data dst-elem s2)
                                          (if (not assignable)
                                              (raise-exception 
                                               "java.lang.ArrayStoreException" s)
                                            (let* ((src-data (array-data src))
                                                   (dst-data (array-data dst))
                                                   (new-dst-data 
                                                    (setChars src-data srcPos dst-data dstPos length)))
                                              (set-array-content new-dst-data dst-ref s3)))))))))))))))))


                            
                            
(defconst *Java_java_lang_Class_forName* 
  (make-method-ptr 
   "java.lang.Class"  "forName" 
   '("java.lang.String") "java.lang.Class"))


(defun replaceLetters (chars c1 c2)
  (if (endp chars)
      nil
    (if (equal (car chars) c2)
        (cons c1 (replaceLetters (cdr chars) c1 c2))
      (cons (car chars) (replaceLetters (cdr chars) c1 c2)))))



;; tmp implementation.
(defun verifyName (name env)
  (declare (ignore name env))
  t)
  
(defun Java_java_lang_Class_forName (s)
  (let ((str-ref (topStack s)))
    (if (equal str-ref -1)
        (raise-exception "nullpointer exception" s)
      (let* ((classname0 (getStringContents str-ref s))
             (classname1 (replaceLetters classname0 (char-code #\.) (char-code #\/)))
             (classname  (make-acl2-string (code-to-chars classname1))))
        (if (verifyName classname1 (env s))
            (let* ((s1 (getClass classname s))
                   (class-rep (class-by-name classname (instance-class-table s1))))
              (if class-rep
                  (let ((class-ref (class-ref class-rep)))
                    ;; impossible to have array class loaded here using getClass
                    (if (not (class-initialized? classname s1))
                        (initializeClass classname (pushStack class-ref (popStack s1)))
                      (pushStack class-ref (popStack s1))))
                ;;(raise-exception "class not found" s1))) ;; Mon May  1
                ;;17:58:47 2006
                (raise-exception "java.lang.ClassNotFoundException" s1)))
          (fatalError "wrong name format" s))))))


;; (defun Java_java_lang_Class_forName (s)
;;   (let ((str-ref (topStack s)))
;;     (if (equal str-ref -1)
;;         (raise-exception "nullpointer exception" s)
;;       (let* ((classname0 (getStringContents str-ref s))
;;              (classname1 (replaceLetters classname0 (char-code #\.) (char-code #\/)))
;;              (classname  (make-acl2-string (code-to-chars classname1))))
;;         (if (verifyName classname1 (env s))
;;             (let* ((s1 (getClass classname s))
;;                    (class-rep (class-by-name classname (instance-class-table s1))))
;;               (if class-rep
;;                   (let ((class-ref (class-ref class-rep)))
;;                     ;; impossible to have array class loaded here using getClass
;;                     (if (not (class-initialized? classname s1))
;;                         (initializeClass classname (pushStack class-ref (popStack s1)))
;;                       (pushStack class-ref (popStack s1))))
;;                 (raise-exception "class not found" s1)))
;;           (fatalError "wrong name format" s))))))



(defconst *Java_java_lang_System_getOutput* 
  (make-method-ptr 
   "java.lang.System"  "getOutput" '() "java.io.PrintStream"))






(defun Java_java_lang_System_getOutput1 (s)
  (let ((class-rep (class-by-name "java.io.PrintStream" (instance-class-table
                                                         s))))
    (if (not class-rep)
        (raise-exception "class not found" s)
      (if (not (class-initialized? "java.io.PrintStream" s))
          (mylet* ((s1 (pushFrame (RunCustomCode-method-ptr) nil s))
                   (s2 (pushStack (make-callback-func-ptr
                                   '*interruptedGetOutput1Behavior*) s1)))
            (initializeClass "java.io.PrintStream" 
             ;; fake a call frame so that when java.io.PrintStream comes back,
             ;; continue the call.
                             s2))
        (mv-let (os-ref s1)
                (new-instance "java.io.PrintStream" s)
                ;; fake it now. ignore the details of initialization for now.
                ;; need to fake a frame to call PrintStream <init>
                ;; to call interpreter?
                ;; eventaully, any I/O operation is direct to the native
                ;; instance. 
                (pushStack os-ref s1))))))
        


(defun Java_java_lang_System_getOutput (s)
  ;; should properly set up the java.lang.System.out, in, err
  ;; currently left it trival implementation. Implementating IO ??
  (if (not (class-loaded? "java.io.PrintStream" s))
      (let ((s1 (load_class "java.io.PrintStream" s)))
        (Java_java_lang_System_getOutput1 s1))
    (Java_java_lang_System_getOutput1 s)))


(defconst *Java_java_lang_Class_newInstance* 
  (make-method-ptr 
   "java.lang.Class"  "newInstance" '() "java.lang.Object"))

; tmp implementation
(defun classHasAccessToClass (classname type s)
  (declare (ignore classname type))
  (mv t s))
           


(defun Java_java_lang_Class_newInstance (s)
  (let* ((current-class-rep (current-class s))
         (accessflags       (class-accessflags current-class-rep))
         (class-ref (topStack s))
         (type-rep  (type-by-class-ref class-ref s)))
    (if (or (Array-Type? type-rep)
            (or (mem '*interface* accessflags)
                (mem '*abstract*  accessflags)))
        (raise-exception "java.lang.InstantiationException" s)
      (mv-let (accessible s1)
              (classHasAccessToClass (classname current-class-rep) type-rep s)
              (if accessible
                  (let ((method-rep (lookupMethod (initMethod-ptr type-rep) s1)))
                    (if (and method-rep
                             (equal (method-classname method-rep) type-rep))
                             ;; we omit the check to prevent invoking a protected init of
                             ;; superclass.
                        (mv-let (obj-ref s2)
                                (new-instance type-rep s1)
                                (if obj-ref 
                                    (let* ((s3 (pushStack obj-ref s2))
                                           (s4 (pushFrame
                                                (RunCustomCode-method-ptr) nil s3))

                                           (s5 (pushStack
                                                (make-callback-func-ptr
                                                 '*newInstanceReturnObject*)
                                                s4))
                                           (s6 (pushStack obj-ref s5))
                                           (s7 (pushFrameWithPop obj-ref
                                                                 method-rep s6)))
                                      s7)
                                  s2)) ;; some exception has been thrown.
                      (raise-exception "java/lang/IllegalAccessException" s1)))
                (raise-exception "java/lang/IllegalAccessException" s1))))))

                                  
                                      
                                

(defconst *Java_java_lang_Thread_currentThread* 
  (make-method-ptr 
   "java.lang.Thread"  "currentThread" '() "java.lang.Thread"))

(defun Java_java_lang_Thread_currentThread (s) 
  (let* ((tid (current-thread s))
         (thread-rep (thread-by-id tid (thread-table s)))
         (thread-ref (thread-ref thread-rep)))
    (pushStack thread-ref s)))
          
            
        
(defconst *Java_java_lang_Thread_start* 
  (make-method-ptr 
   "java.lang.Thread"  "start" '() 'VOID))


(defun Java_java_lang_Thread_yield (s)
  s)

;; in our implementation, schedule is provided. 


;; doesn't support sleep on a timer...

;; our handling of suspendThread, place thread 0 in an advanteous position in
;; round robin algorithm.
(defun Java_java_lang_Thread_sleep (s)
  (let ((period (popLong s)))
    (if (not (equal period 0))
        (fatalError "not implemented" s)
      (suspendThread s))))
  




(defun runMethod-ptr (classname)
  (make-method-ptr classname "run" '() 'void))


(defun initThreadBehavior2 (ptid s)
  (if (not (equal ptid -1))
      (state-set-current-thread 
       ptid (loadExecutionEnvironment 
             ptid (storeExecutionEnvironment s)))
    (state-set-current-thread 
     ptid (storeExecutionEnvironment s))))
                              
  

        
        

(defun initThreadBehavior1 (ptid tid thisMethod sync-obj-ref s)
  (let* ((method-ptr (method-rep-to-method-ptr thisMethod))
         (s1 (state-set-current-thread tid s))
         (s2 (pushFrame method-ptr (list sync-obj-ref) s1))
         (s3 (set-top-frame-return-pc 'KILL_THREAD s2))
         (accessflags (method-accessflags thisMethod)))
    (if (mem '*synchronized* accessflags)
       (let*  ((s4 (pushFrame (RunCustomCode-method-ptr) nil s3))
               (s5 (pushStack (make-callback-func-ptr
                               '*initThreadBehaviorFromThread*) s4)))
        (initThreadBehavior2 ptid s5))
      (initThreadBehavior2 ptid (set-curframe-sync-obj -1 s3)))))
      
               
      


(defun initThreadBehavior (tid thisMethod sync-obj-ref s)
  (let ((ptid (current-thread s)))
    (if (not (equal ptid -1))
        (initThreadBehavior1 ptid tid thisMethod sync-obj-ref
                             (storeExecutionEnvironment s))
        (initThreadBehavior1 ptid tid thisMethod sync-obj-ref s))))
                             

;; we know this obj is
;; of type runnable. so 
;; top so stack has no target-ref 
(defun Java_java_lang_Thread_start1 (tid target-ref s)
  (let* ((classname  (obj-type (deref target-ref (heap s))))
         (thisMethod (lookupMethod (runMethod-ptr classname) s)))
    (let* ((s1 (initThreadBehavior tid thisMethod target-ref s))
           (s2 s1)
           ;;(s2 (pushStack target-ref s1))
           (s3 (startThread tid s2))
           (s4 (resumeThread tid s3)))
      s4)))
    


;; assume  top of stack is the thread-ref
(defun Java_java_lang_Thread_start (s)
  (let* ((thread-ref (topStack s))
         (target     (m6-getfield "java.lang.Thread" "target" thread-ref s))
         (s1         (popStack s)))
    (mv-let (tid s2)
            (getVMthread thread-ref s1)
            (let* ((thread-rep (thread-by-id tid (thread-table s2)))
                   (thread-state (thread-state thread-rep)))
              (if (not (equal thread-state '(thread_just_born)))
                  (raise-exception "java.lang.IllegalThreadStateException" s2)
                (if (not (equal target -1))
                    (Java_java_lang_Thread_start1 tid target  s2)
                  (Java_java_lang_Thread_start1 tid thread-ref s2)))))))




(defconst *Java_java_lang_Thread_setPriority0* 
  (make-method-ptr 
   "java.lang.Thread"  "setPriority0" '(int) 'VOID))


(defun Java_java_lang_Thread_setPriority0 (s)
  ;; trival implementation
  (popStack (popStack s)))




(defconst *Java_java_io_PrintStream_write* 
  (make-method-ptr 
   "java.io.PrintStream"  "write" '("java.lang.String") 'VOID))


(defun Java_java_io_PrintStream_write (s)
  (let* ((obj-str-ref (topStack s))
         (printStream-ref (secondStack s))
         (acl2string  (JavaString-to-ACL2-str obj-str-ref s)))
    (prog2$ (acl2::cw "output from the stream at heap ref ~p0 is ~p1~%"  printStream-ref acl2string)
            (popStack (popStack s)))))


(defconst *Java_java_io_PrintStream_newLine* 
  (make-method-ptr 
   "java.io.PrintStream"  "newLine" '() 'VOID))


(defun Java_java_io_PrintStream_newLine (s)
  (let* ((printStream-ref (topStack s)))
    (prog2$ (acl2::cw "output from the stream at heap ref ~p0 is ~p1~%"  printStream-ref "newline")
            (popStack s))))
    

(defun newInstanceReturnObject (s)
  (popFrame s))


(defun gen-method-nsig (method)
  (make-method-ptr (method-classname method)
                   (method-methodname method)
                   (method-args       method)
                   (method-returntype method)))


;; i modify the code of StringBuffer implementation, it is now not a native
;; implementation but implemented in Java.

(defun invokeNativeFunction (method s)
  (prog2$ 
      (acl2::debug-print "call native method ~p0~%" method)
      (let ((nsig (gen-method-nsig method)))
        (cond ((equal nsig *Java_java_lang_Object_getClass*)
               (Java_java_lang_Object_getClass s))
              ((equal nsig *Java_java_lang_Object_hashCode*)
               (Java_java_lang_Object_hashCode s))
              ((equal nsig *Java_java_lang_Object_wait_0*)
               (Java_java_lang_Object_wait_0 s))
              ((equal nsig *Java_java_lang_Object_wait_1*)
               (Java_java_lang_Object_wait_1 s))
              ((equal nsig *Java_java_lang_Object_notify*)
               (Java_java_lang_Object_notify s))
              ((equal nsig *Java_java_lang_Object_notifyAll*)
               (Java_java_lang_Object_notifyAll s))


              ;; and so on. 
              ((equal nsig *Java_java_lang_String_charAt*)
               (Java_java_lang_String_charAt s))
              ((equal nsig *Java_java_lang_String_equals*)
               (Java_java_lang_String_equals s))
              ((equal nsig *Java_java_lang_System_getProperty0*)
               (Java_java_lang_System_getProperty0 s))
              ((equal nsig *Java_java_lang_String_indexOf_1*) ;; could be not native.
               (Java_java_lang_String_indexOf_1 s))
              ((equal nsig *Java_java_lang_String_indexOf_2*) ;; could be not native.
               (Java_java_lang_String_indexOf_2 s))

              ((equal nsig *Java_java_lang_System_arraycopy*)
               (Java_java_lang_System_arraycopy s))
              ((equal nsig *Java_java_lang_Class_forName*)
               (Java_java_lang_Class_forName s))
              ((equal nsig *Java_java_lang_System_getOutput*)
               (Java_java_lang_System_getOutput s))
              ((equal nsig *Java_java_lang_Class_newInstance*)
               (Java_java_lang_Class_newInstance s))
              ((equal nsig *Java_java_lang_Thread_currentThread*)
               (Java_java_lang_Thread_currentThread s))
              ((equal nsig *Java_java_lang_Thread_start*)
               (Java_java_lang_Thread_start s))
              ((equal nsig *Java_java_lang_Thread_setPriority0*)
               (Java_java_lang_Thread_setPriority0 s))

              ((equal nsig *Java_java_io_PrintStream_write*)
               (Java_java_io_PrintStream_write s))
              ((equal nsig *Java_java_io_PrintStream_newLine*)
               (Java_java_io_PrintStream_newLine s))

              (t (prog2$ (acl2::debug-print "function undefined yet ~p0~%" nsig)

                         s))))))




