; The WyoM1 Virtual Machine
; Copyright (C) 2004  J Strother Moore,
;               University of Texas at Austin

; This program is free software; you can redistribute it and/or
; modify it under the terms of the GNU General Public License as
; published by the Free Software Foundation; either version 2 of
; the License, or (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free
; Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139,
; USA.

; Written by: J Strother Moore
; email:      Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; Modified by: John Cowles
; email:       cowles@uwyo.edu
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071 U.S.A.
;==============================================================
; This file is a certified book that contains the definition of
; WyoM1.

; WyoM1 is M0 except that we now have function call and return.

; Instructions

; To certify this book, make sure it is on a directory on which
; you have write permission, fire up ACL2 while connected to that
; directory, and then execute the following two events.

#|
(defpkg "WYO-M1"
  (set-difference-equal
   (union-eq '(ASSOC-EQUAL LEN NTH ZP SYNTAXP
                           QUOTEP FIX NFIX E0-ORDINALP E0-ORD-<)
             (union-eq
	      *acl2-exports*
	      *common-lisp-symbols-from-main-lisp-package*))
   '(PC PROGRAM PUSH POP REVERSE STEP ++)))

(certify-book "WyoM1" 1)
|#

; The following was changed from "WyoM1" by Matt K. for ACL2 2.9.3 because
; package names may no longer contain lower case characters.
(in-package "WYO-M1")

; ---------------------------------------------------------------
;; An M0 state has the form (list pc locals stack program).

;; A WyoM1 state has the form (list call-stack defs).

;;   A call-stack is a stack of frames.
;;   A frame is an M0 state.

;;   defs is a list of function definitions.
;;   A definition is a list, fdef, of the form
;;      (first fdef) is the name of the function
;;      (second fdef) is the list of formal arguments
;;      (cddr fdef) is the body
; ----------------------------------------------------------------
; Utilities

(defun push (obj stack) (cons obj stack))
(defun top (stack) (car stack))
(defun pop (stack) (cdr stack))

(defun bound? (x alist) (assoc-equal x alist))

(defun bind (x y alist)
  (cond ((endp alist) (list (cons x y)))
        ((equal x (car (car alist)))
         (cons (cons x y) (cdr alist)))
        (t (cons (car alist) (bind x y (cdr alist))))))

(defun binding (x alist) (cdr (assoc-equal x alist)))

(defun op-code (inst) (car inst))
(defun arg1 (inst) (car (cdr inst)))
(defun arg2 (inst) (car (cdr (cdr inst))))
(defun arg3 (inst) (car (cdr (cdr (cdr inst)))))

; The Core of WyoM1

(defun make-state (call-stack defs) (list call-stack defs))

(defun call-stack (s) (car s))
(defun defs (s) (cadr s))

(defun top-frame (s) (top (call-stack s)))

(defun pc (s) (car (top-frame s)))
(defun locals (s) (cadr (top-frame s)))
(defun stack (s) (caddr (top-frame s)))
(defun program (s) (cadddr (top-frame s)))

(defun make-frame (pc locals stack program)
  (list pc locals stack program))

(defun next-inst (s)(nth (pc s) (program s)))

(defun suppliedp (key args)
  (cond ((endp args) nil)
        ((equal key (car args)) t)
        (t (suppliedp key (cdr args)))))

(defun actual (key args)
  (cond ((endp args) nil)
        ((equal key (car args)) (cadr args))
        (t (actual key (cdr args)))))

(defmacro modify (s &rest args)
  (list 'make-state
        (cond ((suppliedp :call-stack args)
               (actual :call-stack args))
              ((or (suppliedp :pc args)
                   (suppliedp :locals args)
                   (suppliedp :stack args)
                   (suppliedp :program args))
               (list 'push
                     (list 'make-frame
                           (if (suppliedp :pc args)
                               (actual :pc args)
                             (list 'pc s))
                           (if (suppliedp :locals args)
                               (actual :locals args)
                             (list 'locals s))
                           (if (suppliedp :stack args)
                               (actual :stack args)
                             (list 'stack s))
                           (if (suppliedp :program args)
                               (actual :program args)
                             (list 'program s)))
                     (list 'pop (list 'call-stack s))))
              (t (list 'call-stack s)))
        (if (suppliedp :defs args)
            (actual :defs args)
          (list 'defs s))))

; We now informally specify and then define each M0 instruction.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (PUSH c)
; Push the constant c onto the operand stack.

(defun execute-PUSH (inst s)
  (modify s
          :pc (+ 1 (pc s))
          :stack (push (arg1 inst) (stack s))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (POP)
; Pop the top item off the operand stack and discard it.

(defun execute-POP (inst s)
  (declare (ignore inst))
  (modify s
          :pc (+ 1 (pc s))
          :stack (pop (stack s))))

; Note: When you define an ACL2 function that ignores one of its
; arguments you must declare that you are doing it intentionally.
; That is the purpose of the DECLARE form above.  Why does
; execute-POP ignore inst?  The reason is that, by convention
; here, we know that inst is an instruction whose opcode is POP.
; Since the POP instruction contains no additional fields, there
; is nothing else we need from it.

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (LOAD v)
; Push the contents stored in local variable v onto the operand
; stack.

(defun execute-LOAD (inst s)
  (modify s
          :pc (+ 1 (pc s))
          :stack (push (binding (arg1 inst)
                                (locals s))
                       (stack s))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (STORE v)
; Pop the top item off the operand stack and store it into the
; local variable v.

(defun execute-STORE (inst s)
  (modify s
          :pc (+ 1 (pc s))
          :locals (bind (arg1 inst) (top (stack s)) (locals s))
          :stack (pop (stack s))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (DUP)
; Duplicate the top item on the stack.

(defun execute-DUP (inst s)
  (declare (ignore inst))
  (modify s
          :pc (+ 1 (pc s))
          :stack (push (top (stack s)) (stack s))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (ADD)
; Pop the top two items off the stack and push their sum.

(defun execute-ADD (inst s)
  (declare (ignore inst))
  (modify s
          :pc (+ 1 (pc s))
          :stack (push (+ (top (pop (stack s)))
                          (top (stack s)))
                       (pop (pop (stack s))))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (SUB)
; Pop the top two items off the stack and push their difference.
; (The top item should be subtracted from the one below it.)

(defun execute-SUB (inst s)
  (declare (ignore inst))
  (modify s
          :pc (+ 1 (pc s))
          :stack (push (- (top (pop (stack s)))
                          (top (stack s)))
                       (pop (pop (stack s))))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (MUL)
; Pop the top two items off the stack and push their product.

(defun execute-MUL (inst s)
  (declare (ignore inst))
  (modify s
          :pc (+ 1 (pc s))
          :stack (push (* (top (pop (stack s)))
                          (top (stack s)))
                       (pop (pop (stack s))))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (GOTO delta)
; Jump to the instruction delta steps from the current
; instruction.

(defun execute-GOTO (inst s)
  (modify s
          :pc (+ (arg1 inst) (pc s))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (IFEQ delta)
; Pop the top item off the stack and if it is 0, jump to the
; instruction delta steps from the current instruction; otherwise,
; step to the next instruction.

(defun execute-IFEQ (inst s)
  (modify s
          :pc (if (equal (top (stack s)) 0)
                  (+ (arg1 inst) (pc s))
                (+ 1 (pc s)))
          :stack (pop (stack s))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (IFNE delta)
; Pop the top item off the stack and if it is not 0, jump to the
; instruction delta steps from the current instruction; otherwise,
; step to the next instruction.;

(defun execute-IFNE (inst s)
  (modify s
          :pc (if (equal (top (stack s)) 0)
                  (+ 1 (pc s))
                (+ (arg1 inst) (pc s)))
          :stack (pop (stack s))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (IFGT delta)
; Pop the top item off the stack and if it is greater than 0, jump
; to the instruction delta steps from the current instruction;
; otherwise, step to the next instruction.;

(defun execute-IFGT (inst s)
  (modify s
          :pc (if (> (top (stack s)) 0)
                  (+ (arg1 inst) (pc s))
                (+ 1 (pc s)))
          :stack (pop (stack s))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (IFLE delta)
; Pop the top item off the stack and if it is less than or equal
; to 0, jump to the instruction delta steps from the current
; instruction; otherwise, step to the next instruction.;

(defun execute-IFLE (inst s)
  (modify s
          :pc (if (> (top (stack s)) 0)
		  (+ 1 (pc s))
		(+ (arg1 inst) (pc s)))
          :stack (pop (stack s))))

;---------------------------------------------------------------
; We now informally specify and then define the new WyoM1
; instructions.

(defun reverse (lst)
  (if (consp lst)
      (append (reverse (cdr lst)) (list (car lst)))
      nil))

(defun bind-formals (rformals stack)
  (if (endp rformals)
      nil
      (cons (cons (car rformals) (top stack))
	    (bind-formals (cdr rformals)
			  (pop stack)))))

(defun popn (n stack)
  (if (zp n)
      stack
      (popn (- n 1) (pop stack))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (CALL fname)
; Let fdef be the definition of the fname in defs and let L be the
; length of the formals of fdef. Bind the top L items of the
; operand stack to the formals, with the last formal bound to the
; top of the stack, etc. Modify the current top frame by incrementing
; the pc and poping the top L items off the operand stack.

; Push the following frame on top of the modified current frame on
; the call-stack:      pc: 0
;                  locals: binding of formals created above
;                   stack: empty stack
;                 program: body of fdef

(defun execute-CALL (inst s)
  (let* ((fn (arg1 inst))
         (def (binding fn (defs s)))
         (formals (car def))
         (body (cdr def))
         (s1 (modify s
                     :pc (+ 1 (pc s))
                     :stack (popn (len formals) (stack s)))))
    (modify s1
            :call-stack
            (push (make-frame 0
                              (reverse
                               (bind-formals (reverse formals)
                                             (stack s)))
                              nil
                              body)
                  (call-stack s1)))))

; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
; Informal Spec: (RET)
; Let val be the item on top of the operand stack of the top frame.
; Pop the top frame off the call-stack and push val on top of the
; operand stack of the newly exposed top frame.

(defun execute-RET (inst s)
  (declare (ignore inst))
  (let ((val (top (stack s)))
        (s1 (modify s
                    :call-stack (pop (call-stack s)))))
    (modify s1
            :stack (push val (stack s1)))))

; --------------------------------------------------------------

; Now we wrap it all up by defining the WyoM1 step function and the
; top-level interpreter.

(defun do-inst (inst s)
  (case (op-code inst)
    (PUSH   (execute-PUSH  inst s))
    (POP    (execute-POP   inst s))
    (LOAD   (execute-LOAD  inst s))
    (STORE  (execute-STORE inst s))
    (DUP    (execute-DUP   inst s))
    (ADD    (execute-ADD   inst s))
    (SUB    (execute-SUB   inst s))
    (MUL    (execute-MUL   inst s))
    (GOTO   (execute-GOTO  inst s))
    (IFEQ   (execute-IFEQ  inst s))
    (IFNE   (execute-IFNE  inst s))
    (IFGT   (execute-IFGT  inst s))
    (IFLE   (execute-IFLE  inst s))
    (CALL   (execute-CALL  inst s))
    (RET    (execute-RET   inst s))
    (otherwise s)))

; Notice that there is no instruction with op-code HALT.  But what
; is (do-inst '(HALT) s)?  The answer: s!  That is, every
; undefined op-code is a no-op, and a no-op is the same as a halt
; instruction in the sense that execution never gets past it.

(defun step (s)
  (do-inst (next-inst s) s))

; So here is the operational semantics for the WyoM1 virtual machine.

(defun run (s n)
  (if (zp n)
      s
      (run (step s) (- n 1))))
