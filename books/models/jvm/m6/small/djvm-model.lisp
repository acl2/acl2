(in-package "ACL2")
(include-book "jvm-model")
(include-book "consistent-state")


;----------------------------------------------------------------------
;
;   defensive-JVM
;
;----------------------------------------------------------------------

(defun djvm-check-IFEQ (inst st)
  (let* ((target (arg inst))
         (pc     (get-pc st)))
    (and (consistent-state st)
         (consp (op-stack st))
         (pc-in-range (set-pc (+ 1 pc) st))
         (pc-in-range (set-pc target st)))))



(defun djvm-execute-IFEQ (inst st)
  (let* ((target     (arg inst))
         (v          (topstack st))
         (pc         (get-pc st)))
    (if (equal v 0) 
        (set-pc target
                (popStack st))
      (set-pc (+ 1 pc)
              (popStack st)))))

;----------------------------------------------------------------------

(defun djvm-check-PUSH (inst st)
  (declare (ignore inst))
  (let* ((pc     (get-pc st)))
    (and (consistent-state st)
         (<= (+ 1 (len (op-stack st)))
             (g 'max-stack (topx (g 'call-stack st))))
         (pc-in-range (set-pc (+ 1 pc) st)))))


(defun djvm-execute-PUSH (inst st)
  (let* ((v     (arg inst))
         (pc    (get-pc st)))
    (set-pc (+ 1 pc)
            (pushStack v st))))

;----------------------------------------------------------------------

(defun djvm-check-INVOKE (inst st)
  (let* ((method-name  (arg inst))
         (method-table (g 'method-table st))
         (method   (binding method-name method-table))
         (nargs    (g 'nargs method)))
    (and (consistent-state st)
         (bound? method-name method-table)
         (<= 0 (g 'max-stack (binding method-name method-table)))
         (integerp nargs)
         (<= 0 nargs)
         (<= nargs (len (op-stack st)))
         (<= (+ 1 (- (len (op-stack st))
                     nargs))
             (g 'max-stack (topx (g 'call-stack st))))
         (pc-in-range (set-pc (+ 1 (get-pc st))
                              st)))))

;; this however does not guarantee that executing djvm-check will preserve
;; consistent-state
;;
;; because in the consistent-state we require that 

;;
;;          ;; the following two need to has to be true!!!  In the new BCV, we can
;;          ;; calculate the signiture at the each PC location!!
;;          ;; 
;;          (bound? pc (get-sig-vector caller method-table))
;;          (sig-frame-compatible
;;           (sig-frame-push-value (g 'ret callee) sig-frame)
;;           record-frame-sig))))
;;
;; However if we don't require this, we will have no way to show that BCV is
;; correct. 
;;
;; We know this is true, although djvm-check-INVOKE does not explicitly check
;; it!! 
;; ..... 
         
;;; Sun Nov 20 19:23:33 2005, we update consistent-state that assert bcv-method
;;; instead of bcv-simple-method!!!
;;;

(defun djvm-execute-INVOKE (inst st)
  (let* ((method-name  (arg inst))
         (method-table (g 'method-table st))
         (method   (binding method-name method-table))
         (nargs    (g 'nargs method)))
    (pushInitFrame
     method-name   ;; Thu Nov  3 21:44:09 2005. note. 
     ;; what if the method-table is not well formed, 
     ;; binding method-name does not give a method of the correct name?
     (init-locals (op-stack st) nargs)
     (set-pc (+ 1 (get-pc st))
               ;;
               ;; we could avoid modifying the pc
               ;; and make the return instruction to modify the pc of caller
               ;; however we still face the problem that 
               ;; the caller's operand stack does not comply with the signature
               ;;
               (popStack-n st nargs)))))

;----------------------------------------------------------------------

(defun djvm-check-HALT (inst st)
  (declare (ignore inst))
  (consistent-state st))


(defun djvm-execute-HALT (inst st)
  (declare (ignore inst))
  st)

;----------------------------------------------------------------------

(defun djvm-check-POP (inst st)
  (declare (ignore inst))
  (and (consistent-state st)
       (consp (op-stack st))
       (pc-in-range (set-pc (+ 1 (get-pc st))
                            st))))


(defun djvm-execute-POP (inst st)
  (declare (ignore inst))
  (set-pc (+ 1 (get-pc st))
          (popStack st)))

;----------------------------------------------------------------------

(defun djvm-check-RETURN (inst st)
  (declare (ignore inst))
  (and (consistent-state st)
       (or (not (consp (popx (g 'call-stack st))))
           (and (consp (op-stack st))
                (<= (+ 1 (len (g 'op-stack (topx (popx (g 'call-stack st))))))
                    (g 'max-stack (topx (popx (g 'call-stack st)))))))))
                      


(defun djvm-execute-RETURN (inst st)
  (declare (ignore inst))
  ;; update it to halt, when we know this is the very first frame!!  or update
  ;; our consistent-state predicate!
  (if (not (consp (popx (g 'call-stack st))))
      st
    (pushStack 
     (topStack st)
     (s 'call-stack
        (popx (g 'call-stack st))
        st))))

;----------------------------------------------------------------------


;----------------------------------------------------------------------


(defun djvm-check-step-g (inst st)
  (let* ((opcode (op-code inst)))
    (cond ((equal opcode 'INVOKE)
           (djvm-check-INVOKE inst st))
          ((equal opcode 'PUSH)
           (djvm-check-PUSH inst st))
          ((equal opcode 'IFEQ)
           (djvm-check-IFEQ inst st))
          ((equal opcode 'HALT)
           (djvm-check-HALT inst st))
          ((equal opcode 'POP)
           (djvm-check-POP inst st))
          ((equal opcode 'RETURN)
           (djvm-check-RETURN inst st))
          (t nil))))



(defun djvm-check-step (st)
  (let* ((inst (next-inst st))
         (opcode (op-code inst)))
    (cond ((equal opcode 'INVOKE)
           (djvm-check-INVOKE inst st))
          ((equal opcode 'PUSH)
           (djvm-check-PUSH inst st))
          ((equal opcode 'IFEQ)
           (djvm-check-IFEQ inst st))
          ((equal opcode 'HALT)
           (djvm-check-HALT inst st))
          ((equal opcode 'POP)
           (djvm-check-POP inst st))
          ((equal opcode 'RETURN)
           (djvm-check-RETURN inst st))
          (t nil))))


(defun djvm-step (st)
  (if (not (djvm-check-step st)) 
      st
    (let* ((inst (next-inst st))
           (opcode (op-code inst)))
      (cond ((equal opcode 'INVOKE)
             (djvm-execute-INVOKE inst st))
            ((equal opcode 'PUSH)
             (djvm-execute-PUSH inst st))
            ((equal opcode 'IFEQ)
             (djvm-execute-IFEQ inst st))
            ((equal opcode 'HALT)
             (djvm-execute-HALT inst st))
            ((equal opcode 'POP)
             (djvm-execute-POP inst st))
            ((equal opcode 'RETURN)
             (djvm-execute-RETURN inst st))
            (t st)))))


;----------------------------------------------------------------------

(defun djvm-run (st n)
  (if (zp n) st
    (djvm-run (djvm-step st) (- n 1))))

;----------------------------------------------------------------------

;;
;; testing.
;;

