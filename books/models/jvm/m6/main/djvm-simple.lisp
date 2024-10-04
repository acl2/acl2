;;; this file (should be) generated with tool-gen-functions.lisp

; a place to define the top level DJVM
; As of Thu Aug 11 13:21:27 2005, we only have a simple execution engine. 
; that takes a sequence of instructions execute it. 

(in-package "DJVM")
(include-book "../DJVM/consistent-state-strong")
(include-book "../DJVM/INST/inst") ;; include all the instructions. 

;----------------------------------------------------------------------

(acl2::set-verify-guards-eagerness 0)

;;; note the following definition is incomplete. 
;;; We have not implement the full instruction set in INST/inst.lisp
;;; only a couple of them. 
(ENCAPSULATE
 NIL
 (DEFUN WFF-INST-STRONG (INST)
   (AND (WFF-INST INST)
        (LET ((OPCODE (INST-OPCODE INST)))
             (COND ((EQUAL OPCODE 'HALT)  t)
                   ((EQUAL OPCODE 'AALOAD)
                    (WFF-AALOAD INST))
                   ((EQUAL OPCODE 'AASTORE)
                    (WFF-AASTORE INST))
                   ((EQUAL OPCODE 'ALOAD) (WFF-ALOAD INST))
                   ((EQUAL OPCODE 'ASTORE)
                    (WFF-ASTORE INST))
                   ((EQUAL OPCODE 'ANEWARRAY)
                    (WFF-ANEWARRAY INST))
                   ((EQUAL OPCODE 'IFEQ) (WFF-IFEQ INST))
                   ((EQUAL OPCODE 'GETFIELD)
                    (WFF-GETFIELD INST))
                   ((EQUAL OPCODE 'ACONST_NULL)
                    (WFF-ACONST_NULL INST))))))
 (DEFUN ALL-INSTRS-WFF (INSTRS)
   (IF (NOT (CONSP INSTRS))
       T
       (AND (WFF-INST-STRONG (CAR INSTRS))
            (ALL-INSTRS-WFF (CDR INSTRS)))))
 (DEFUN DJVM-STEP (INST S)
   (DECLARE (XARGS :GUARD (AND (WFF-INST INST)
                               (CONSISTENT-STATE-STRONG S))))
   (if (not (no-fatal-error? s)) s
     (LET ((OPCODE (INST-OPCODE INST)))
          (COND ((EQUAL OPCODE 'HALT) S)
                ((EQUAL OPCODE 'AALOAD)
                 (IF (CHECK-AALOAD INST S)
                     (EXECUTE-AALOAD INST S)
                     S))
                ((EQUAL OPCODE 'AASTORE)
                 (IF (CHECK-AASTORE INST S)
                     (EXECUTE-AASTORE INST S)
                     S))
                ((EQUAL OPCODE 'ALOAD)
                 (IF (CHECK-ALOAD INST S)
                     (EXECUTE-ALOAD INST S)
                     S))
                ((EQUAL OPCODE 'ASTORE)
                 (IF (CHECK-ASTORE INST S)
                     (EXECUTE-ASTORE INST S)
                     S))
                ((EQUAL OPCODE 'ANEWARRAY)
                 (IF (CHECK-ANEWARRAY INST S)
                     (EXECUTE-ANEWARRAY INST S)
                     S))
                ((EQUAL OPCODE 'IFEQ)
                 (IF (CHECK-IFEQ INST S)
                     (EXECUTE-IFEQ INST S)
                     S))
                ((EQUAL OPCODE 'GETFIELD)
                 (IF (CHECK-GETFIELD INST S)
                     (EXECUTE-GETFIELD INST S)
                     S))
                ((EQUAL OPCODE 'ACONST_NULL)
                 (IF (CHECK-ACONST_NULL INST S)
                     (EXECUTE-ACONST_NULL INST S)
                     S))
                (T S))))))

(acl2::verify-guards WFF-INST-STRONG)
(acl2::verify-guards all-instrs-wff)


;;
;; Tue Oct 25 16:11:29 2005

;; We may have to modify djvm-step to check for wff-inst-strong!! 
;; or change the guard for djvm-step!! 
