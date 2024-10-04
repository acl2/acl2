(in-package "M6")
(include-book "../M6/m6-bytecode")

(defun m6step (s) 
  (let* ((inst (next-inst s))
         (op  (inst-opcode inst)))
    (if (no-fatal-error? s)
        (prog2$ (acl2::debug-print "thread ~p0 executing inst ~p1~%Current pc ~p2~%"
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

               (JVM::LCONST_0   (execute-LCONST_0   inst s))
               (JVM::LCONST_1   (execute-LCONST_1   inst s))
               (JVM::LCMP       (execute-LCMP       inst s))
             
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
         s)))

#|
(defun m6step (s) 
  (let* ((inst (next-inst s))
         (op  (inst-opcode inst)))
    (if (no-fatal-error? s)
        (prog2$ (acl2::debug-print "executing inst ~p0~%Current pc ~p1~%" inst (pc s))
         (if (equal op 'invalid-op-code) ;; shouldn't happen if verified.
             (fatalError  "impossible: opcode invalid" s)
           (case  op 
             (customcode (execute-customcode inst s))
             (bipush     (execute-bipush inst s))
             (aload_0 (execute-aload_0 inst s))
             (invokespecial (execute-invokespecial inst s))
             (invokestatic  (execute-invokestatic inst s))
             (return   (execute-return inst s 0))
             (iconst_1 (execute-iconst_1 inst s))
             (istore_1 (execute-istore_1 inst s))
             (iload_0 (execute-iload_0 inst s))
             (iload_1 (execute-iload_1 inst s))
             (iload_2 (execute-iload_2 inst s))
             (iadd     (execute-iadd inst s))
             (ireturn  (execute-return inst s 1))
             (isub (execute-isub inst s))
             (ifgt (execute-ifgt inst s))
             (istore_2 (execute-istore_2 inst s))
             (t s))))
  s)))
|#


(defun simple-run (s n)
  (if (zp n)
      s
    (simple-run (m6step s) (- n 1))))
    
(defun search-measure (start end)
  (if (zp (- end start))
      0
    (+ 1 (- end start))))


(defun search-active-thread-in-range (start end thread-table)
  (declare (xargs :measure (search-measure start end)))
  (if (zp (- end start))
      -1
    (let ((thread (thread-by-id start thread-table)))
      (if (and  (mem 'thread_active (thread-state thread))
                (not (mem 'thread_suspended (thread-state thread))))
          start
        (search-active-thread-in-range (+ start 1) end thread-table)))))
        


(defun round-robin-schedule (s)
  (let* ((thread-table (thread-table s))
         (l (len thread-table))
         (tid (current-thread s))
         (up  (search-active-thread-in-range (+ tid 1) l thread-table)))
    (if (not (equal up -1))
        up
      (let ((up-warp (search-active-thread-in-range 0 (+ tid 1) thread-table)))
        up-warp))))

(defun round-robin-run-measure (n)
  (if (zp n)
      0
    (+ 1 n)))


(acl2::set-ignore-ok t)

;; if there is no active thread then terminate
(defun round-robin-run (s n)
  (declare (xargs :measure (round-robin-run-measure n)
                  :hints (("Goal" :in-theory (disable m6step)))))
  (if (zp n)
      s
    (let ((cid (current-thread s)))
      (if (equal cid -1)
          (prog2$ (acl2::debug-print "NO ACTIVE THREAD!~%") s)
        (prog2$ (acl2::debug-print "Executing Thread ~p0 Instruction ~p1~%" cid (next-inst s))
                (let* ((sn (m6step s))
                       (nid  (round-robin-schedule sn))
                       (ccid (current-thread sn)))
                  (if (equal nid -1)
                      (prog2$ (acl2::debug-print "Continue executing ~p0~%" ccid)
                              (round-robin-run sn (- n 1)))
                    (if (not (equal nid cid))
                        (prog2$ (acl2::debug-print 
                                 "~%~%***************~%switch from THREAD ~p0 to THREAD~p1 ~%**************~%~%" 
                                 cid nid )
                                (round-robin-run 
                                 (loadExecutionEnvironment nid 
                                   (storeExecutionEnvironment
                                      (state-set-current-thread cid sn))) (- n 1)))
                      (round-robin-run sn (- n 1))))))))))
 


(defun current-method (s)
  (deref-method (current-method-ptr s)
                (instance-class-table s)))


;; ;; if there is no active thread then terminate
;; (defun round-robin-run (s n)
;;   (declare (xargs :measure (round-robin-run-measure n)))
;;   (if (zp n)
;;       s
;;     (let ((nid (round-robin-schedule s))
;;           (cid (current-thread       s)))
;;       (prog2$ (acl2::debug-print "thread ~p0 selected for next round!~%" nid)
;;        (if (equal nid -1)
;;            (prog2$ (acl2::debug-print "NO ACTIVE THREAD!~%")
;;                    s)
;;          (if (equal cid -1)
;;              (round-robin-run (loadExecutionEnvironment nid s) (- n 1))
;;            (let ((sn (m6step s)))
;;              (if (equal (current-thread sn) -1)
;;                  (round-robin-run (loadExecutionEnvironment nid s) (- n 1))
;;                (if (not (equal nid cid))
;;                    (prog2$ (acl2::debug-print 
;;                             "~%~%***************~%switch from THREAD ~p0 to THREAD~p1 ~%**************~%~%" 
;;                             cid nid )
;;                            (round-robin-run (loadExecutionEnvironment 
;;                                             nid (storeExecutionEnvironment sn)) (- n 1)))
;;                 (round-robin-run sn (- n 1)))))))))))
  


      
          

(DEFMACRO TH (I)
  (CONS 'THREAD-TABLE
        (CONS (CONS 'ROUND-ROBIN-RUN
                    (CONS '*S1* (CONS I 'NIL)))
              'NIL)))


                 
(DEFMACRO HP (I)
  (CONS 'HEAP
        (CONS (CONS 'ROUND-ROBIN-RUN
                    (CONS '*S1* (CONS I 'NIL)))
              'NIL)))









