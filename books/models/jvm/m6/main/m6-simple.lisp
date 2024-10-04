(in-package "M6")
(include-book "../M6/m6-bytecode")

(ENCAPSULATE NIL
             (DEFUN M6-STEP (INST S)
               (if (not (no-fatal-error? s)) s
                 (LET ((OPCODE (INST-OPCODE INST)))
                      (COND ((EQUAL OPCODE 'HALT) S)
                            ((EQUAL OPCODE 'AALOAD)
                             (EXECUTE-AALOAD INST S))
                            ((EQUAL OPCODE 'AASTORE)
                             (EXECUTE-AASTORE INST S))
                            ((EQUAL OPCODE 'ALOAD)
                             (EXECUTE-ALOAD INST S))
                            ((EQUAL OPCODE 'ASTORE)
                             (EXECUTE-ASTORE INST S))
                            ((EQUAL OPCODE 'ANEWARRAY)
                             (EXECUTE-ANEWARRAY INST S))
                            ((EQUAL OPCODE 'IFEQ)
                             (EXECUTE-IFEQ INST S))
                            ((EQUAL OPCODE 'GETFIELD)
                             (EXECUTE-GETFIELD INST S))
                            ((EQUAL OPCODE 'ACONST_NULL)
                             (EXECUTE-ACONST_NULL INST S))
                            (T 'ERROR_STATE))))))

;; (defun m6-simple-run (n program s)
;;   (if (zp n) s
;;     (mylet* ((inst (inst-by-offset1 (pc s) program))
;;              (ns   (m6-step inst s)))
;;             (m6-simple-run (- n 1) program ns))))



(defun m6-simple-run (n s)
  (if (zp n) s
    (mylet* ((inst (next-inst s))
             (ns   (m6-step inst s)))
            (m6-simple-run (- n 1) ns))))



;----------------------------------------------------------------------
