(in-package "ACL2")
;; definition of a tiny machine + its safe version + its bcv.
;; 
;; with ifeq, push, pop, invoke, return, halt

;------------------------------------------------------------
;
;   The SMALL Machine (with a more "correct" BCV)
;
;------------------------------------------------------------

(include-book "misc/records" :dir :system)

; Stacks
(defun pushx (obj stack) (cons obj stack))
(defun topx (stack) (car stack))
(defun popx (stack) (cdr stack))


; Alists
(defun bound? (x alist) (assoc-equal x alist))

(defun bind (x y alist)
  (cond ((endp alist) (list (cons x y)))
        ((equal x (car (car alist)))
         (cons (cons x y) (cdr alist)))
        (t (cons (car alist) (bind x y (cdr alist))))))

(defun binding (x alist) (cdr (bound? x alist))) 

; Instructions
(defun op-code (inst) (car inst))
(defun arg (inst) (car (cdr inst)))


(defun popStack (st)
  (let* ((call-stack (g 'call-stack st))
         (top-frame  (topx call-stack))
         (op-stack   (g 'op-stack top-frame)))
    (s 'call-stack 
       (pushx (s 'op-stack 
                 (popx op-stack)
                 top-frame)
              (popx call-stack))
       st)))

(defun pushStack (v st)
  (let* ((call-stack (g 'call-stack st))
         (top-frame  (topx call-stack))
         (op-stack   (g 'op-stack top-frame)))
    (s 'call-stack 
       (pushx (s 'op-stack 
                 (pushx v op-stack)
                 top-frame)
              (popx call-stack))
       st)))

(defun topStack (st)
  (let* ((call-stack (g 'call-stack st))
         (top-frame  (topx call-stack))
         (op-stack   (g 'op-stack top-frame)))
    (topx op-stack)))


(defun set-pc (pc st)
  (let* ((call-stack (g 'call-stack st))
         (top-frame  (topx call-stack)))
    (s 'call-stack 
       (pushx (s 'pc pc top-frame)
              (popx call-stack))
       st)))


(defun get-pc (st)
  (g 'pc (topx (g 'call-stack st))))


;----------------------------------------------------------------------


;----------------------------------------------------------------------

(defun execute-IFEQ (inst st)
  (let* ((target     (arg inst))
         (v          (topstack st))
         (pc         (get-pc st)))
    (if (equal v 0) 
        (set-pc target
                (popStack st))
      (set-pc (+ 1 pc)
              (popStack st)))))

;----------------------------------------------------------------------


(defun execute-PUSH (inst st)
  (let* ((v     (arg inst))
         (pc    (get-pc st)))
    (set-pc (+ 1 pc)
            (pushStack v st))))

;----------------------------------------------------------------------

(defun createInitFrame (method-name initial-locals st)
  (s 'max-stack (g 'max-stack 
                   (binding method-name (g 'method-table st)))
     (s 'pc 0
        (s 'method-name method-name
           (s 'locals initial-locals
              (s 'op-stack nil nil))))))
  

(defun pushInitFrame (method-name initial-locals st)
  (s 'call-stack  
     (pushx 
      (createInitFrame method-name initial-locals st)
      (g 'call-stack st))
     st))


(defun op-stack (st)
  (g 'op-stack 
     (topx (g 'call-stack st))))

(defun popStack-n (st n) 
  (if (zp n) st
    (popStack-n (popStack st)
                (- n 1))))

(defun init-locals (stack n)
  (if (zp n) nil
    (s n (topx stack)
       (init-locals (popx stack) (- n 1)))))


(defun execute-INVOKE (inst st)
  (let* ((method-name  (arg inst))
         (method-table (g 'method-table st))
         (method   (binding method-name method-table))
         (nargs    (g 'nargs method)))
    (pushInitFrame
     method-name 
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

(defun execute-HALT (inst st)
  (declare (ignore inst))
  st)

;----------------------------------------------------------------------


(defun execute-POP (inst st)
  (declare (ignore inst))
  (set-pc (+ 1 (get-pc st))
          (popStack st)))

;----------------------------------------------------------------------


(defun execute-RETURN (inst st)
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
  
    
(defun current-method (st)
  (let* ((method-name (g 'method-name (topx (g 'call-stack st))))
         (method-table (g 'method-table st)))
    (binding method-name method-table)))


(defun pc-in-range (st)
  (let ((pc (g 'pc (topx (g 'call-stack st))))
        (code (g 'code (binding (g 'method-name 
                                   (topx (g 'call-stack st)))
                                (g 'method-table st)))))
    (and (integerp pc)
         (<= 0 pc)
         (< pc (len code)))))


(defun next-inst (st)
  (let* ((pc (get-pc st))
         (code (g 'code (current-method st))))
    (if (not (pc-in-range st))
        nil
      (nth pc code))))

;----------------------------------------------------------------------

(defun m-step (st)
  (let* ((inst (next-inst st))
         (opcode (op-code inst)))
    (cond ((equal opcode 'INVOKE) 
           (execute-INVOKE inst st))
          ((equal opcode 'PUSH)
           (execute-PUSH inst st))
          ((equal opcode 'IFEQ)
           (execute-IFEQ inst st))
          ((equal opcode 'HALT)
           (execute-HALT inst st))
          ((equal opcode 'POP)
           (execute-POP inst st))
          ((equal opcode 'RETURN)
           (execute-RETURN inst st))
          (t st))))


;----------------------------------------------------------------------

(defun m-run (st n)
  (if (zp n) st
    (m-run (m-step st) (- n 1))))

;----------------------------------------------------------------------


