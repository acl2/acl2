(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-thread")
(include-book "../M6-DJVM-shared/jvm-frame-manipulation-primitives")
(include-book "../M6-DJVM-shared/jvm-linker")

(acl2::set-verify-guards-eagerness 2)

;-- primitives for accessing instructions 
;; because instrs is a list of (offset (opcode args))

(defun inst-by-offset1 (offset instrs)
  (declare (xargs :guard (wff-insts instrs)))
  (if (not (consp instrs))
      (list offset '(invalid-inst-offset))
    (if (equal (inst-offset (car instrs)) 'endofcode)
        (list offset '(invalid-inst-offset))
      (if (equal (inst-offset (car instrs)) offset)
          (car instrs)
        (inst-by-offset1 offset (cdr instrs))))))


(defun inst-by-offset (offset method-rep)
  (declare (xargs :guard (and (wff-method-decl method-rep)
                              (wff-code (method-code method-rep))
                              (wff-insts (code-instrs (method-code method-rep))))))
  (let ((instrs (code-instrs (method-code method-rep))))
    (inst-by-offset1 offset instrs)))


;;; this should be automatically derived!!! 

(defun next-inst (s)
  (declare (xargs :guard (and (wff-state s)
                              (CURRENT-FRAME-GUARD S)
                              (WFF-CALL-FRAME (CURRENT-FRAME S))
                              (WFF-METHOD-PTR (current-method-ptr s))
                              (wff-class-table (class-table s))
                              (WFF-INSTANCE-CLASS-TABLE 
                               (instance-class-table s))
                              (wff-method-decl (deref-method
                                                (current-method-ptr s)
                                                (instance-class-table s)))
                              (wff-code (method-code (deref-method
                                                      (current-method-ptr s)
                                                      (instance-class-table s))))
                              (wff-insts (code-instrs (method-code 
                                                       (deref-method
                                                        (current-method-ptr s)
                                                        (instance-class-table s))))))))
  (let* ((ip  (pc s))
         (method-ptr (current-method-ptr s))
         (method-rep (deref-method method-ptr (instance-class-table s))))
    (inst-by-offset ip method-rep)))


;--- primitives for implementing each execute-XXX 

;; (acl2::set-verify-guards-eagerness 2)

(defun wff-one-arg (inst)
  (and (wff-inst inst)
       (equal (len (cdr (nth 1 inst))) 1)))

;; ;;
;; ;; because of raise-exception is a conflict with jvm-exception. 
;; ;; we can not load both M6 and DJVM at the same time...
;; ;;
;;;;; is it still the case?? 

;; (defun arg (inst)
;;   (declare (xargs :guard (wff-one-arg inst)))
;;   (nth 1 (nth 1 inst)))

                 
(defun arg (inst)
  (declare (xargs :guard (wff-one-arg inst)))
  (nth 1 (nth 1 inst)))

;;
;; jvm-class-table.lisp inst-arg is not used. 
;; 

(defun local-at (i s)
  (declare (xargs :guard (and (current-frame-guard s)
                              (wff-call-frame (current-frame s))
                              (integerp i)
                              (true-listp (locals (current-frame s)))
                              (<= 0 i)
                              (< i (len (locals (current-frame s)))))))
  (nth i (locals (current-frame s))))

;; (defun local-at (i s)
;;   (declare (xargs :guard (and (consistent-state s)
;;                               (integerp i)
;;                               (<= 0 i)
;;                               (< i (len (locals (current-frame s)))))))
;;   (nth i (locals (current-frame s))))


;; (acl2::set-verify-guards-eagerness 0)

;-- top level loop ---



;; in principle, those callback function should always pop off the topframe 
;; or advance the ip to execute the next instruction 

;; in case of runClinit is pop off the frame when it finishes the initializing
;; the class. 
;; in case of initInitialThreadBehaviror, it is the first frame in any
;; execution. The result of excuting initInitialThreadBehavior is we create a
;; new frame on top of this first frame. We set the return address of that new
;; frame to be 'KILL_THREAD. System will terminates when we finished with the
;; excuting the new frame with a return.


(defun inst-size (inst)
  (declare (xargs :guard (wff-inst inst)))
  (case (inst-opcode inst)
    (CUSTOMCODE    1)

    (ICONST_0      1)
    (ICONST_1      1)
    (ICONST_2      1)
    (ICONST_3      1)
    (ICONST_4      1)
    (ICONST_5      1)
    (ICONST_M1     1)


    (JVM::LCONST_0  1)
    (JVM::LCONST_1  1)
    (JVM::LCMP      1)
    
    (ACONST_NULL   1)
    

    (ISTORE        2)
    (ISTORE_0      1)
    (ISTORE_1      1)
    (ISTORE_2      1)   
    (ISTORE_3      1)   

    (ILOAD         2)
    (ILOAD_0       1)
    (ILOAD_1       1)
    (ILOAD_2       1)
    (ILOAD_3       1)


    (ASTORE        2)
    (ASTORE_0      1)
    (ASTORE_1      1)
    (ASTORE_2      1)   
    (ASTORE_3      1)   

    (ALOAD         2)
    (ALOAD_0       1)
    (ALOAD_1       1)
    (ALOAD_2       1)
    (ALOAD_3       1)

    (AALOAD        1)
    (AASTORE       1)

    (IALOAD        1)
    (IASTORE       1)



    (LALOAD        1)
    (LASTORE       1)

    (BALOAD        1)
    (BASTORE       1)

    (CALOAD        1)
    (CASTORE       1)

    (SALOAD        1)
    (SASTORE       1)

    (IADD          1)
    (IINC          3)
    (INEG          1)

    (IMUL          1)
    (IDIV          1)
    (IREM          1)


    (ISUB          1)

    (POP           1)
    (POP2          1)

    (NEWARRAY      2)
    (ARRAYLENGTH   1)


    (MONITORENTER  1)
    (MONITOREXIT   1)

    (CHECKCAST     3)


    (RETURN        1)
    (NEW           3)
    (DUP           1)
    (DUP_X1        1)
    (DUP_X2        1)
    (DUP2          1)
    (DUP2_X1       1)
    (DUP2_X2       1)


    (INVOKESPECIAL 3)
    (INVOKESTATIC  3)
    (INVOKEVIRTUAL 3)
    (INVOKEINTERFACE 5)
    (PUTFIELD      3)

    (GETFIELD      3)
    (GETSTATIC     3)

    (PUTSTATIC     3)
    (BIPUSH        2)

    (CASTORE       1)
    (PUTSTATIC     3)
    (LDC           2)
    (IFNULL        3)
    (IFNONNULL     3)
    (IFEQ          3)
    (IFNE          3)
    (IFLT          3)
    (IFGE          3)
    (IFGT          3)
    (IFLE          3)
    (IF_ICMPEQ     3)
    (IF_ICMPNE     3)
    (IF_ICMPLT     3)
    (IF_ICMPGE     3)
    (IF_ICMPGT     3)
    (IF_ICMPLE     3)
    (GOTO          3)
    (IRETURN       1)
    (RETURN        1)
    (ARETURN       1)
    (ATHROW        1)
    (JSR           3)
    (RET           2)
    (t             0)))


;----------------------------------------------------------------------

; moved from m6-bytecode.lisp

(defun field-size (field-rep) 
  (declare (xargs :guard (wff-field field-rep)))
  (type-size (field-fieldtype field-rep)))


(defun fatalSlotError (fieldCP s)
   (declare (ignore fieldCP))
   (declare (xargs :guard (wff-state s)))
   (fatalError "field not found" s))



