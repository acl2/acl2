; Copyright (C) 1999 J Strother Moore

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; This book defines the ``Toy Java Virtual Machine'' tjvm, discussed in the
; paper

; Proving Theorems about Java-like Byte Code
; by J Strother Moore

#|
; Certification Instructions.

; To certify this book, connect to the directory containing this file, fire
; up ACL2 and execute

(DEFPKG "TJVM"
  (set-difference-equal (union-eq '(ASSOC-EQUAL LEN NTH ZP SYNTAXP
                                    QUOTEP FIX NFIX E0-ORDINALP E0-ORD-<)
                                  (union-eq *acl2-exports*
                                            *common-lisp-symbols-from-main-lisp-package*))
                        '(PC PROGRAM PUSH POP REVERSE STEP ++)))

; Notes on the Imports Above

; The first set of symbols, ASSOC-EQUAL, NTH, ..., NFIX are among many
; useful function symbols defined in ACL2 that have been omitted from
; *acl2-exports*!  I delete PUSH, ..., ++ because they are defined in
; Common Lisp in ways different than I wish to define them below.

; Then do

(certify-book "tjvm" 1)

|#
(in-package "TJVM")

; -----------------------------------------------------------------------------
; Utilities

(defun push (obj stack) (cons obj stack))
(defun top (stack) (car stack))
(defun pop (stack) (cdr stack))

;(defun assoc-equal (x alist)
;  (cond ((endp alist) nil)
;        ((equal x (car (car alist)))
;         (car alist))
;        (t (assoc-equal x (cdr alist)))))

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

;(defun nth (i lst)
;  (if (zp i)
;      (car lst)
;    (nth (- i 1) (cdr lst))))

(defun reverse (x)
  (if (consp x)
      (append (reverse (cdr x)) (list (car x)))
    nil))

; -----------------------------------------------------------------------------
; States

(defun make-state (call-stack heap class-table)
  (list call-stack heap class-table))
(defun call-stack  (s) (nth 0 s))
(defun heap        (s) (nth 1 s))
(defun class-table (s) (nth 2 s))

; -----------------------------------------------------------------------------
; Frames

(defun make-frame (pc locals stack program)
  (list pc locals stack program))

(defun pc      (frame) (nth 0 frame))
(defun locals  (frame) (nth 1 frame))
(defun stack   (frame) (nth 2 frame))
(defun program (frame) (nth 3 frame))

(defun top-frame (s) (top (call-stack s)))

; -----------------------------------------------------------------------------
; Class Declarations and the Class Table

; The class table of a state is an alist.  Each entry in a class table is
; a "class declaration" and is of the form

;   (class-name super-class-names fields defs)

(defun make-class-decl (name superclasses fields methods)
  (list name superclasses fields methods))

(defun class-decl-name (dcl)
  (nth 0 dcl))
(defun class-decl-superclasses (dcl)
  (nth 1 dcl))
(defun class-decl-fields (dcl)
  (nth 2 dcl))
(defun class-decl-methods (dcl)
  (nth 3 dcl))

; -----------------------------------------------------------------------------
; Method Declarations

; The methods component of a class declaration is a list of method definitions.
; A method definition is a list of the form

; (name formals . program)

; We never build these declarations but just enter list constants for them,

; Note the similarity to our old notion of a program definition.  We
; will use strings to name methods now.

; Method definitions will be constructed by expressions such as:

; ("move" (dx dy)
;   (load this)
;   (load this)
;   (getfield "Point" "x")
;   (load dx)
;   (add)
;   (putfield "Point" "x")    ; this.x = this.x + dx;
;   (load this)
;   (load this)
;   (getfield "Point" "y")
;   (load dy)
;   (add)
;   (putfield "Point" "y")    ; this.y = this.y + dy;
;   (push 1)
;   (xreturn)))                   ; return 1;

; Provided this method is defined in the class "Point" it can be invoked by

;   (invokevirtual "Point" "move" 2)

; This assumes that the stack, at the time of invocation, contains an
; reference to an object of type "Point" and two numbers, dx and dy.

; The accessors for methods are:

(defun method-name (m)
  (nth 0 m))
(defun method-formals (m)
  (nth 1 m))
(defun method-program (m)
  (cddr m))

; -----------------------------------------------------------------------------
; (PUSH const) Instruction

(defun execute-PUSH (inst s)
  (make-state
   (push (make-frame (+ 1 (pc (top-frame s)))
                     (locals (top-frame s))
                     (push (arg1 inst)
                           (stack (top-frame s)))
                     (program (top-frame s)))
         (pop (call-stack s)))
   (heap s)
   (class-table s)))

; -----------------------------------------------------------------------------
; (POP) Instruction

(defun execute-POP (inst s)
  (declare (ignore inst))
  (make-state
   (push (make-frame (+ 1 (pc (top-frame s)))
                     (locals (top-frame s))
                     (pop (stack (top-frame s)))
                     (program (top-frame s)))
         (pop (call-stack s)))
   (heap s)
   (class-table s)))

; -----------------------------------------------------------------------------
; (LOAD var) Instruction

(defun execute-LOAD (inst s)
  (make-state
   (push (make-frame (+ 1 (pc (top-frame s)))
                     (locals (top-frame s))
                     (push (binding (arg1 inst)
                                    (locals (top-frame s)))
                           (stack (top-frame s)))
                     (program (top-frame s)))
         (pop (call-stack s)))
   (heap s)
   (class-table s)))

; -----------------------------------------------------------------------------
; (STORE var) Instruction

(defun execute-STORE (inst s)
  (make-state
   (push (make-frame (+ 1 (pc (top-frame s)))
                     (bind (arg1 inst)
                           (top (stack (top-frame s)))
                           (locals (top-frame s)))
                     (pop (stack (top-frame s)))
                     (program (top-frame s)))
         (pop (call-stack s)))
   (heap s)
   (class-table s)))

; -----------------------------------------------------------------------------
; (ADD) Instruction

(defun execute-ADD (inst s)
  (declare (ignore inst))
  (make-state
   (push (make-frame (+ 1 (pc (top-frame s)))
                     (locals (top-frame s))
                     (push (+ (top (pop (stack (top-frame s))))
                              (top (stack (top-frame s))))
                           (pop (pop (stack (top-frame s)))))
                     (program (top-frame s)))
         (pop (call-stack s)))
   (heap s)
   (class-table s)))

; -----------------------------------------------------------------------------
; (SUB) Instruction

(defun execute-SUB (inst s)
  (declare (ignore inst))
  (make-state
   (push (make-frame (+ 1 (pc (top-frame s)))
                     (locals (top-frame s))
                     (push (- (top (pop (stack (top-frame s))))
                              (top (stack (top-frame s))))
                           (pop (pop (stack (top-frame s)))))
                     (program (top-frame s)))
         (pop (call-stack s)))
   (heap s)
   (class-table s)))

; -----------------------------------------------------------------------------
; (MUL) Instruction

(defun execute-MUL (inst s)
  (declare (ignore inst))
  (make-state
   (push (make-frame (+ 1 (pc (top-frame s)))
                     (locals (top-frame s))
                     (push (* (top (pop (stack (top-frame s))))
                              (top (stack (top-frame s))))
                           (pop (pop (stack (top-frame s)))))
                     (program (top-frame s)))
         (pop (call-stack s)))
   (heap s)
   (class-table s)))

; -----------------------------------------------------------------------------
; (GOTO pc) Instruction

(defun execute-GOTO (inst s)
  (make-state
   (push (make-frame (+ (arg1 inst) (pc (top-frame s)))
                     (locals (top-frame s))
                     (stack (top-frame s))
                     (program (top-frame s)))
         (pop (call-stack s)))
   (heap s)
   (class-table s)))

; -----------------------------------------------------------------------------
; (IFEQ pc) Instruction

(defun execute-IFEQ (inst s)
  (make-state
   (push (make-frame (if (equal (top (stack (top-frame s))) 0)
                         (+ (arg1 inst) (pc (top-frame s)))
                       (+ 1 (pc (top-frame s))))
                     (locals (top-frame s))
                     (pop (stack (top-frame s)))
                     (program (top-frame s)))
         (pop (call-stack s)))
   (heap s)
   (class-table s)))

; -----------------------------------------------------------------------------
; (IFGT pc) Instruction

(defun execute-IFGT (inst s)
  (make-state
   (push (make-frame (if (> (top (stack (top-frame s))) 0)
                         (+ (arg1 inst) (pc (top-frame s)))
                       (+ 1 (pc (top-frame s))))
                     (locals (top-frame s))
                     (pop (stack (top-frame s)))
                     (program (top-frame s)))
         (pop (call-stack s)))
   (heap s)
   (class-table s)))

; -----------------------------------------------------------------------------
; (IFLE pc) Instruction

(defun execute-IFLE (inst s)
  (make-state
   (push (make-frame (if (<= (top (stack (top-frame s))) 0)
                         (+ (arg1 inst) (pc (top-frame s)))
                       (+ 1 (pc (top-frame s))))
                     (locals (top-frame s))
                     (pop (stack (top-frame s)))
                     (program (top-frame s)))
         (pop (call-stack s)))
   (heap s)
   (class-table s)))


; -----------------------------------------------------------------------------
; (NEW "class") Instruction

(defun build-class-field-bindings (field-names)
  (if (endp field-names)
      nil
    (cons (cons (car field-names) 0)
          (build-class-field-bindings (cdr field-names)))))

(defun build-immediate-instance-data (class-name class-table)
  (cons class-name
        (build-class-field-bindings
         (class-decl-fields
          (bound? class-name class-table)))))

(defun build-an-instance (class-names class-table)
  (if (endp class-names)
      nil
    (cons (build-immediate-instance-data (car class-names) class-table)
          (build-an-instance (cdr class-names) class-table))))

(defun refp (x)
  (and (consp x)
       (equal (car x) 'ref)
       (consp (cdr x))
       (integerp (cadr x))
       (equal (cddr x) nil)))

(defun execute-NEW (inst s)
  (let* ((class-name (arg1 inst))
         (class-table (class-table s))
         (new-object (build-an-instance
                      (cons class-name
                            (class-decl-superclasses
                             (bound? class-name class-table)))
                      class-table))
         (new-address (len (heap s))))
    (make-state
     (push (make-frame (+ 1 (pc (top-frame s)))
                       (locals (top-frame s))
                       (push (list 'REF new-address)
                             (stack (top-frame s)))
                       (program (top-frame s)))
           (pop (call-stack s)))
     (bind new-address new-object (heap s))
     (class-table s))))


; -----------------------------------------------------------------------------
; (GETFIELD "class" "field") Instruction

(defun deref (ref heap)
  (binding (cadr ref) heap))

(defun field-value (class-name field-name instance)
  (binding field-name
           (binding class-name instance)))

(defun execute-GETFIELD (inst s)
  (let* ((class-name (arg1 inst))
         (field-name (arg2 inst))
         (instance (deref (top (stack (top-frame s))) (heap s)))
         (field-value (field-value class-name field-name instance)))
    (make-state
     (push (make-frame (+ 1 (pc (top-frame s)))
                       (locals (top-frame s))
                       (push field-value
                             (pop (stack (top-frame s))))
                       (program (top-frame s)))
           (pop (call-stack s)))
     (heap s)
     (class-table s))))

; -----------------------------------------------------------------------------
; (PUTFIELD "class" "field") Instruction

(defun set-instance-field (class-name field-name value instance)
  (bind class-name
        (bind field-name value
              (binding class-name instance))
        instance))

(defun execute-PUTFIELD (inst s)
  (let* ((class-name (arg1 inst))
         (field-name (arg2 inst))
         (value (top (stack (top-frame s))))
         (instance (deref (top (pop (stack (top-frame s)))) (heap s)))
         (address (cadr (top (pop (stack (top-frame s)))))))
        (make-state
         (push (make-frame (+ 1 (pc (top-frame s)))
                           (locals (top-frame s))
                           (pop (pop (stack (top-frame s))))
                           (program (top-frame s)))
               (pop (call-stack s)))
         (bind address
               (set-instance-field class-name field-name value instance)
               (heap s))
         (class-table s))))


; -----------------------------------------------------------------------------
; (INSTANCEOF "class")

(defun execute-INSTANCEOF (inst s)
  (let* ((class-name (arg1 inst))
         (instance (deref (top (stack (top-frame s))) (heap s))))
    (make-state
     (push (make-frame (+ 1 (pc (top-frame s)))
                       (locals (top-frame s))
                       (push (if (bound? class-name instance)
                                 1
                               0)
                             (pop (stack (top-frame s))))
                       (program (top-frame s)))
           (pop (call-stack s)))
     (heap s)
     (class-table s))))



; -----------------------------------------------------------------------------
; (INVOKEVIRTUAL "class" "name" n) Instruction

(defun bind-formals (rformals stack)
  (if (endp rformals)
      nil
    (cons (cons (car rformals) (top stack))
          (bind-formals (cdr rformals) (pop stack)))))

(defun popn (n stack)
  (if (zp n)
      stack
    (popn (- n 1) (pop stack))))

(defun class-name-of-ref (ref heap)
  (car (car (deref ref heap))))

(defun lookup-method-in-superclasses (name classes class-table)
  (cond ((endp classes) nil)
        (t (let* ((class-name (car classes))
                  (class-decl (bound? class-name class-table))
                  (method (bound? name (class-decl-methods class-decl))))
             (if method
                 method
                (lookup-method-in-superclasses name (cdr classes)
                                               class-table))))))

(defun lookup-method (name class-name class-table)
  (lookup-method-in-superclasses name
                                 (cons class-name
                                       (class-decl-superclasses
                                        (bound? class-name class-table)))
                                 class-table))

(defun execute-INVOKEVIRTUAL (inst s)
  (let* ((method-name (arg2 inst))
         (nformals (arg3 inst))
         (obj-ref (top (popn nformals (stack (top-frame s)))))
         (obj-class-name (class-name-of-ref obj-ref (heap s)))
         (closest-method
          (lookup-method method-name
                         obj-class-name
                         (class-table s)))
         (vars (cons 'this (method-formals closest-method)))
         (prog (method-program closest-method)))
    (make-state
     (push (make-frame 0
                       (reverse
                        (bind-formals (reverse vars)
                                      (stack (top-frame s))))
                       nil
                       prog)
           (push (make-frame (+ 1 (pc (top-frame s)))
                             (locals (top-frame s))
                             (popn (len vars)
                                   (stack (top-frame s)))
                             (program (top-frame s)))
                 (pop (call-stack s))))
     (heap s)
     (class-table s))))

; -----------------------------------------------------------------------------
; (INVOKESTATIC "class" "name" n) Instruction

(defun execute-INVOKESTATIC (inst s)
  (let* ((class-name (arg1 inst))
         (method-name (arg2 inst))
         (closest-method
          (lookup-method method-name
                         class-name
                         (class-table s)))
         (vars (method-formals closest-method))
         (prog (method-program closest-method)))
    (make-state
     (push (make-frame 0
                       (reverse
                        (bind-formals (reverse vars)
                                      (stack (top-frame s))))
                       nil
                       prog)
           (push (make-frame (+ 1 (pc (top-frame s)))
                             (locals (top-frame s))
                             (popn (len vars)
                                   (stack (top-frame s)))
                             (program (top-frame s)))
                 (pop (call-stack s))))
     (heap s)
     (class-table s))))

; -----------------------------------------------------------------------------
; (RETURN) Instruction

(defun execute-RETURN (inst s)
  (declare (ignore inst))
  (let ((caller-frame (top (pop (call-stack s)))))
    (make-state
     (push (make-frame (pc caller-frame)
                       (locals caller-frame)
                       (stack caller-frame)
                       (program caller-frame))
           (pop (pop (call-stack s))))
     (heap s)
     (class-table s))))

; -----------------------------------------------------------------------------
; (XRETURN) Instruction

(defun execute-XRETURN (inst s)
  (declare (ignore inst))
  (let ((val (top (stack (top-frame s))))
        (caller-frame (top (pop (call-stack s)))))
    (make-state
     (push (make-frame (pc caller-frame)
                       (locals caller-frame)
                       (push val (stack caller-frame))
                       (program caller-frame))
           (pop (pop (call-stack s))))
     (heap s)
     (class-table s))))

; -----------------------------------------------------------------------------
; Putting it all together

(defun next-inst (s)
  (nth (pc (top-frame s))
       (program (top-frame s))))

(defun do-inst (inst s)
  (case (op-code inst)
    (PUSH           (execute-PUSH inst s))
    (POP            (execute-POP  inst s))
    (LOAD           (execute-LOAD inst s))
    (STORE          (execute-STORE inst s))
    (ADD            (execute-ADD inst s))
    (SUB            (execute-SUB inst s))
    (MUL            (execute-MUL inst s))
    (GOTO           (execute-GOTO inst s))
    (IFEQ           (execute-IFEQ inst s))
    (IFGT           (execute-IFGT inst s))
    (IFLE           (execute-IFLE inst s))
    (INVOKEVIRTUAL  (execute-INVOKEVIRTUAL inst s))
    (INVOKESTATIC   (execute-INVOKESTATIC inst s))
    (RETURN         (execute-RETURN inst s))
    (XRETURN        (execute-XRETURN inst s))
    (NEW            (execute-NEW inst s))
    (GETFIELD       (execute-GETFIELD inst s))
    (PUTFIELD       (execute-PUTFIELD inst s))
    (INSTANCEOF     (execute-INSTANCEOF inst s))
    (HALT           s)
    (otherwise s)))

(defun step (s)
  (do-inst (next-inst s) s))

(defun tjvm (s n)
  (if (zp n)
      s
    (tjvm (step s) (- n 1))))

