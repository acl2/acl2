; Copyright (C) 2001, Regents of the University of Texas
; Written by J Strother Moore and George Porter
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; M5.lisp
; J Strother Moore <moore@cs.utexas.edu>
; George Porter <george@cs.utexas.edu>
;
; Fixed arithmetic work by Robert Krug <rkrug@cs.utexas.edu>
; Support for Arrays by Hanbing Liu <hbl@cs.utexas.edu>
;
; $Id: m5.lisp,v 1.1 2001/07/10 17:37:06 george Exp $

#|

(defpkg "LABEL" '(nil t))
(defpkg "JVM" '(nil t))

(DEFPKG "M5"
  (set-difference-equal
   (union-eq '(JVM::SCHEDULED
               JVM::UNSCHEDULED
               JVM::REF
               JVM::LOCKED
               JVM::S_LOCKED
               JVM::UNLOCKED
               JVM::AALOAD
               JVM::AASTORE
               JVM::ACONST_NULL
               JVM::ALOAD
               JVM::ALOAD_0
               JVM::ALOAD_1
               JVM::ALOAD_2
               JVM::ALOAD_3
               JVM::ANEWARRAY
               JVM::ARETURN
               JVM::ARRAYLENGTH
               JVM::ASTORE
               JVM::ASTORE_0
               JVM::ASTORE_1
               JVM::ASTORE_2
               JVM::ASTORE_3
               JVM::BALOAD
               JVM::BASTORE
               JVM::BIPUSH
               JVM::CALOAD
               JVM::CASTORE
               JVM::DUP
               JVM::DUP_X1
               JVM::DUP_X2
               JVM::DUP2
               JVM::DUP2_X1
               JVM::DUP2_X2
               JVM::GETFIELD
               JVM::GETSTATIC
               JVM::GOTO
               JVM::GOTO_W
               JVM::I2B
               JVM::I2C
               JVM::I2L
               JVM::I2S
               JVM::IADD
               JVM::IALOAD
               JVM::IAND
               JVM::IASTORE
               JVM::ICONST_M1
               JVM::ICONST_0
               JVM::ICONST_1
               JVM::ICONST_2
               JVM::ICONST_3
               JVM::ICONST_4
               JVM::ICONST_5
               JVM::IDIV
               JVM::IF_ACMPEQ
               JVM::IF_ACMPNE
               JVM::IF_ICMPEQ
               JVM::IF_ICMPGE
               JVM::IF_ICMPGT
               JVM::IF_ICMPLE
               JVM::IF_ICMPLT
               JVM::IF_ICMPNE
               JVM::IFEQ
               JVM::IFGE
               JVM::IFGT
               JVM::IFLE
               JVM::IFLT
               JVM::IFNE
               JVM::IFNONNULL
               JVM::IFNULL
               JVM::IINC
               JVM::ILOAD
               JVM::ILOAD_0
               JVM::ILOAD_1
               JVM::ILOAD_2
               JVM::ILOAD_3
               JVM::IMUL
               JVM::INEG
               JVM::INSTANCEOF
               JVM::INVOKESPECIAL
               JVM::INVOKESTATIC
               JVM::INVOKEVIRTUAL
               JVM::IOR
               JVM::IREM
               JVM::IRETURN
               JVM::ISHL
               JVM::ISHR
               JVM::ISTORE
               JVM::ISTORE_0
               JVM::ISTORE_1
               JVM::ISTORE_2
               JVM::ISTORE_3
               JVM::ISUB
               JVM::IUSHR
               JVM::IXOR
               JVM::JSR
               JVM::JSR_W
               JVM::L2I
               JVM::LADD
               JVM::LALOAD
               JVM::LAND
               JVM::LASTORE
               JVM::LCMP
               JVM::LCONST_0
               JVM::LCONST_1
               JVM::LDC
               JVM::LDC_W
               JVM::LDC2_W
               JVM::LDIV
               JVM::LLOAD
               JVM::LLOAD_0
               JVM::LLOAD_1
               JVM::LLOAD_2
               JVM::LLOAD_3
               JVM::LMUL
               JVM::LNEG
               JVM::LOR
               JVM::LREM
               JVM::LRETURN
               JVM::LSHL
               JVM::LSHR
               JVM::LSTORE
               JVM::LSTORE_0
               JVM::LSTORE_1
               JVM::LSTORE_2
               JVM::LSTORE_3
               JVM::LSUB
               JVM::LUSHR
               JVM::LXOR
               JVM::MONITORENTER
               JVM::MONITOREXIT
               JVM::MULTIANEWARRAY
               JVM::NEW
               JVM::NEWARRAY
               JVM::NOP
               JVM::POP
               JVM::POP2
               JVM::PUTFIELD
               JVM::PUTSTATIC
               JVM::RET
               JVM::RETURN
               JVM::SALOAD
               JVM::SASTORE
               JVM::SIPUSH
               JVM::SWAP
               ASSOC-EQUAL LEN NTH ZP SYNTAXP
               QUOTEP FIX NFIX E0-ORDINALP E0-ORD-<)
             (union-eq *acl2-exports*
                       *common-lisp-symbols-from-main-lisp-package*))
   '(PC PROGRAM PUSH POP RETURN REVERSE STEP ++)))

(certify-book "m5" 3)

J & George
|#

(in-package "M5")

(include-book "../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

; -----------------------------------------------------------------------------
; Utilities

(defun push (obj stack) (cons obj stack))
(defun top (stack) (car stack))
(defun pop (stack) (cdr stack))

(defun popn (n stack)
  (if (zp n)
      stack
      (popn (- n 1) (pop stack))))

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

(defun nullrefp (ref)
  (equal ref '(ref -1)))

; Imported from ACL2

(defun reverse (x)
  (if (consp x)
      (append (reverse (cdr x)) (list (car x)))
    nil))

; The following are constants and functions related to fixed integer sizes

(defconst *largest-integer-value* (- (expt 2 31) 1))
(defconst *largest-long-value* (- (expt 2 63) 1))
(defconst *most-negative-integer* (- (expt 2 31)))
(defconst *most-negative-long* (- (expt 2 63)))

; Coerce x to an unsigned integer which will fit in n bits.
(defun u-fix (x n)
  (mod (ifix x) (expt 2 n)))

; Coerce x to a signed integer which will fit in n bits.
(defun s-fix (x n)
  (let ((temp (mod (ifix x) (expt 2 n))))
    (if (< temp (expt 2 (1- n)))
        temp
      (- temp (expt 2 n)))))

(defun byte-fix (x)
  (s-fix x 8))

(defun ubyte-fix (x)
  (u-fix x 8))

(defun short-fix (x)
  (s-fix x 16))

(defun int-fix (x)
  (s-fix x 32))

(defun uint-fix (x)
  (u-fix x 32))

(defun long-fix (x)
  (s-fix x 64))

(defun ulong-fix (x)
  (u-fix x 64))

(defun char-fix (x)
  (u-fix x 16))

(defun 6-bit-fix (x)
  (u-fix x 6))

(defun 5-bit-fix (x)
  (u-fix x 5))

(defun expt2 (n)
  (expt 2 n))

(defun shl (x n)
  (* x (expt2 n)))

(defun shr (x n)
  (floor (* x (expt2 (- n))) 1))

; -----------------------------------------------------------------------------
; States

(defun make-state (thread-table heap class-table)
  (list thread-table heap class-table))
(defun thread-table (s) (nth 0 s))
(defun heap        (s) (nth 1 s))
(defun class-table (s) (nth 2 s))

(defun make-thread (call-stack status rref)
  (list call-stack status rref))

(defun call-stack (th s)
  (nth 0 (binding th (thread-table s))))

(defun status (th s)
  (nth 1 (binding th (thread-table s))))

(defun rref (th s)
  (nth 2 (binding th (thread-table s))))

; -----------------------------------------------------------------------------
; Class Declarations and the Class Table

; The class table of a state is an alist.  Each entry in a class table is
; a "class declaration" and is of the form

;   (class-name super-class-names fields defs)

; Note that the definition below of the Thread class includes a 'run' method,
;  which most applications will override.  The definition is consistent
;  with the default run method provided by the Thread class [O'Reily]

(defun make-class-decl (name superclasses fields sfields cp methods href)
  (list name superclasses fields sfields cp methods href))

(defun class-decl-name (dcl)
  (nth 0 dcl))
(defun class-decl-superclasses (dcl)
  (nth 1 dcl))
(defun class-decl-fields (dcl)
  (nth 2 dcl))
(defun class-decl-sfields (dcl)
  (nth 3 dcl))
(defun class-decl-cp (dcl)
  (nth 4 dcl))
(defun class-decl-methods (dcl)
  (nth 5 dcl))
(defun class-decl-heapref (dcl)
  (nth 6 dcl))

(defun base-class-def ()
   (list (make-class-decl "java.lang.Object"
                          nil
                          '("monitor" "mcount" "wait-set")
                          '()
                          '()
                          '(("<init>" () nil (RETURN)))
                          '(REF -1))
         (make-class-decl "ARRAY"
                          '("java.lang.Object")
                          '(("<array>" . *ARRAY*))
                          '()
                          '()
                          '()
                          '(REF -1))
         (make-class-decl "java.lang.Thread"
                          '("java.lang.Object")
                          '()
                          '()
                          '()
                          '(("run" () nil
                             (RETURN))
                            ("start" () nil ())
                            ("stop" () nil ())
                            ("<init>" ()
                                      nil
                                      (aload_0)
                                      (invokespecial "java.lang.Object" "<init>" 0)
                                      (return)))
                          '(REF -1))
         (make-class-decl "java.lang.String"
                          '("java.lang.Object")
                          '("strcontents")
                          '()
                          '()
                          '(("<init>" ()
                                      nil
                                      (aload_0)
                                      (invokespecial "java.lang.Object" "<init>" 0)
                                      (return)))
                          '(REF -1))
         (make-class-decl "java.lang.Class"
                          '("java.lang.Object")
                          '()
                          '()
                          '()
                          '(("<init>" ()
                                     nil
                                     (aload_0)
                                     (invokespecial "java.lang.Object" "<init>" 0)
                                     (return)))
                          '(REF -1))))

(defun make-class-def (list-of-class-decls)
   (append (base-class-def) list-of-class-decls))

; -----------------------------------------------------------------------------
; A Constant Pool
;
; There is one constant pool per class

; A constant pool is a list of entries.  Each entry is either:
;
;  '(INT n)
;       Where n is a 32-bit number, in the range specified by the JVM spec
;
;  '(STRING (REF -1) "Hello, World!")
;       The 3rd element (a string) is resolved to a heap reference the
;       first time it is used.  Once it is resolved, its reference is placed
;       as the second element (displacing the null ref currently there).

(defun cp-make-int-entry (n)
  (list 'INT n))

(defun cp-make-string-entry (str)
  (list 'STRING '(REF -1) str))

(defun cp-string-resolved? (entry)
  (not (equal (cadr (caddr entry)) -1)))

(defun retrieve-cp (class-name class-table)
  (class-decl-cp (bound? class-name class-table)))

(defun update-ct-string-ref (class idx newval ct)
  (let* ((class-entry (bound? class ct))
         (oldstrval (caddr (nth idx (retrieve-cp class ct))))
         (newstrentry (list 'STRING newval oldstrval))
         (new-cp (update-nth idx
                              newstrentry
                              (class-decl-cp class-entry)))
         (new-class-entry
          (make-class-decl (class-decl-name class-entry)
                           (class-decl-superclasses class-entry)
                           (class-decl-fields class-entry)
                           (class-decl-sfields class-entry)
                           new-cp
                           (class-decl-methods class-entry)
                           (class-decl-heapref class-entry))))
        (bind class (cdr new-class-entry) ct)))

; -----------------------------------------------------------------------------
; Thread Tables
;
; A "thread table" might be used to represent threads in m5.  It consists of
;  a reference, a call stack, a flag to indicate whether its call-stack
;  should be stepped by the scheduler, and a ref to the original object
;  in the heap.
;
; Thread table:
; ((n   . (call-stack flag reverse-ref))
;  (n+1 . (call-stack flag reverse-ref)))
;
; The flags 'SCHEDULED and 'UNSCHEDULED correspond to two of the
; four states threads can be in (according to [O'Reily]).  For our
; model, this will suffice.

(defun make-tt (call-stack)
  (bind 0 (list call-stack 'SCHEDULED nil) nil))

(defun addto-tt (call-stack status heapRef tt)
  (bind (len tt) (list call-stack status heapRef) tt))

(defun mod-thread-scheduling (th sched tt)
  (let* ((thrd (binding th tt))
         (oldcs  (car thrd))
         (oldhr  (caddr thrd))
         (newTH  (list oldcs sched oldhr)))
        (bind th newTH tt)))

(defun schedule-thread (th tt)
  (mod-thread-scheduling th 'SCHEDULED tt))

(defun unschedule-thread (th tt)
  (mod-thread-scheduling th 'UNSCHEDULED tt))

(defun rrefToThread (ref tt)
  (cond ((endp tt) nil)
        ((equal ref (cadddr (car tt))) (caar tt))
        (t (rrefToThread ref (cdr tt)))))

; ----------------------------------------------------------------------------
; Helper function for determining if an object is a 'Thread' object

(defun in-list (item list)
  (cond ((endp list) nil)
        ((equal item (car list)) t)
        (t (in-list item (cdr list)))))

(defun isThreadObject? (class-name class-table)
  (let* ((class (bound? class-name class-table))
        (psupers (class-decl-superclasses class))
        (supers (cons class-name psupers)))
       (or (in-list "java.lang.Thread" supers)
           (in-list "java.lang.ThreadGroup" supers))))

; ----------------------------------------------------------------------------
; Helper functions for locking and unlocking objects

; lock-object and unlock-object will obtain a lock on an instance
;  of an object, using th as the locking id (a thread owns a lock).  If th
;  already has a lock on an object, then the mcount of the object is
;  incremented.  Likewise if you unlock an object with mcount > 0, then
;  the lock will be decremented.  Note:  you must make sure that th can
;  and should get the lock, since this function will blindly go ahead and
;  get the lock

(defun lock-object (th obj-ref heap)
  (let* ((obj-ref-num (cadr obj-ref))
         (instance (binding (cadr obj-ref) heap))
         (obj-fields (binding "java.lang.Object" instance))
         (new-mcount (+ 1 (binding "mcount" obj-fields)))
         (new-obj-fields
            (bind "monitor" th
               (bind "mcount" new-mcount obj-fields)))
         (new-object (bind "java.lang.Object" new-obj-fields instance)))
     (bind obj-ref-num new-object heap)))

(defun unlock-object (th obj-ref heap)
  (let* ((obj-ref-num (cadr obj-ref))
         (instance (binding (cadr obj-ref) heap))
         (obj-fields (binding "java.lang.Object" instance))
         (old-mcount (binding "mcount" obj-fields))
         (new-mcount (ACL2::max 0 (- old-mcount 1)))
         (new-monitor (if (zp new-mcount)
                          0
                          th))
         (new-obj-fields
            (bind "monitor" new-monitor
               (bind "mcount" new-mcount obj-fields)))
         (new-object (bind "java.lang.Object" new-obj-fields instance)))
     (bind obj-ref-num new-object heap)))

; objectLockable? is used to determine if th can unlock instance.  This
;  occurs when either mcount is zero (nobody has a lock), or mcount is
;  greater than zero, but monitor is equal to th.  This means that th
;  already has a lock on the object, and when the object is locked yet again,
;  monitor will remain the same, but mcount will be incremented.
;
; objectUnLockable? determins if a thread can unlock an object (ie if it
;  has a lock on that object)
(defun objectLockable? (instance th)
  (let* ((obj-fields (binding "java.lang.Object" instance))
         (monitor (binding "monitor" obj-fields))
         (mcount (binding "mcount" obj-fields)))
    (or (zp mcount)
        (equal monitor th))))

(defun objectUnLockable? (instance th)
  (let* ((obj-fields (binding "java.lang.Object" instance))
         (monitor (binding "monitor" obj-fields)))
      (equal monitor th)))

; -----------------------------------------------------------------------------
; Frames

(defun make-frame (pc locals stack program sync-flg cur-class)
  (list pc locals stack program sync-flg cur-class))

(defun top-frame (th s) (top (call-stack th s)))

(defun pc      (frame) (nth 0 frame))
(defun locals  (frame) (nth 1 frame))
(defun stack   (frame) (nth 2 frame))
(defun program (frame) (nth 3 frame))
(defun sync-flg (frame) (nth 4 frame))
(defun cur-class (frame) (nth 5 frame))

; -----------------------------------------------------------------------------
; Method Declarations

; The methods component of a class declaration is a list of method definitions.
; A method definition is a list of the form

; (name formals sync-status . program)

; We never build these declarations but just enter list constants for them,

; Note the similarity to our old notion of a program definition.  We
; will use strings to name methods now.

; sync-status is 't' if the method is synchronized, 'nil' if not

; Method definitions will be constructed by expressions such as:
; (Note:  all of the symbols below are understood to be in the pkg "JVM".)

; ("move" (dx dy) nil
;   (load this)
;   (load this)
;   (getfield "Point" "x")
;   (load dx)
;   (add)
;   (putfield "Point" "x")    ; this.x = this.x + dx;
;   (load :this)
;   (load :this)
;   (getfield "Point" "y")
;   (load dy)
;   (add)
;   (putfield "Point" "y")    ; this.y = this.y + dy;
;   (push 1)
;   (xreturn)))               ; return 1;

; Provided this method is defined in the class "Point" it can be invoked by

;   (invokevirtual "Point" "move" 2)

; This assumes that the stack, at the time of invocation, contains an
; reference to an object of type "Point" and two numbers, dx and dy.

; If a method declaration has an empty list for the program (ie- there are
; no bytecodes associated with the method), then the method is considered
; native.  Native methods are normally written in something like C or
; assembly language.  The JVM would normally ensure that the correct number
; and type of arguments are passed to the native method, and would then hand
; over control to C.  In our model, we simply "hardwire" invokevirtual to
; to handle these methods.
;  * Note that a method in Java will never have 0 bytecodes, since even if
;    it has no body, it will consist of at least the (xreturn) bytecode.

; The accessors for methods are:

(defun method-name (m)
  (nth 0 m))
(defun method-formals (m)
  (nth 1 m))
(defun method-sync (m)
  (nth 2 m))
(defun method-program (m)
  (cdddr m))
(defun method-isNative? (m)
  (equal '(NIL)
         (method-program m)))

; The Standard Modify

(defun suppliedp (key args)
  (cond ((endp args) nil)
        ((equal key (car args)) t)
        (t (suppliedp key (cdr args)))))

(defun actual (key args)
  (cond ((endp args) nil)
        ((equal key (car args)) (cadr args))
        (t (actual key (cdr args)))))

(defmacro modify (th s &rest args)
  (list 'make-state
        (cond
         ((or (suppliedp :call-stack args)
              (suppliedp :pc args)
              (suppliedp :locals args)
              (suppliedp :stack args)
              (suppliedp :program args)
              (suppliedp :sync-flg args)
              (suppliedp :cur-class args)
              (suppliedp :status args))
          (list 'bind
                th
                (list 'make-thread
                      (cond
                       ((suppliedp :call-stack args)
                        (actual :call-stack args))
                       ((and (suppliedp :status args)
                             (null (cddr args)))
                        (list 'call-stack th s))
                       (t
                        (list 'push
                              (list 'make-frame
                                    (if (suppliedp :pc args)
                                        (actual :pc args)
                                      (list 'pc (list 'top-frame th s)))
                                    (if (suppliedp :locals args)
                                        (actual :locals args)
                                      (list 'locals (list 'top-frame th s)))
                                    (if (suppliedp :stack args)
                                        (actual :stack args)
                                      (list 'stack (list 'top-frame th s)))
                                    (if (suppliedp :program args)
                                        (actual :program args)
                                      (list 'program (list 'top-frame th s)))
                                    (if (suppliedp :sync-flg args)
                                        (actual :sync-flg args)
                                      (list 'sync-flg (list 'top-frame th s)))
                                    (if (suppliedp :cur-class args)
                                        (actual :cur-class args)
                                      (list 'cur-class
                                            (list 'top-frame th s))))
                              (list 'pop (list 'call-stack th s)))))
                      (if (suppliedp :status args)
                          (actual :status args)
                        (list 'status th s))
                      (list 'rref th s))
                (list 'thread-table s)))
         ((suppliedp :thread-table args)
          (actual :thread-table args))
         (t (list 'thread-table s)))
        (if (suppliedp :heap args)
            (actual :heap args)
          (list 'heap s))
        (if (suppliedp :class-table args)
            (actual :class-table args)
          (list 'class-table s))))

; -----------------------------------------------------------------------------
; Helper functions related to building instances of objects

(defun deref (ref heap)
  (binding (cadr ref) heap))

(defun field-value (class-name field-name instance)
  (binding field-name
           (binding class-name instance)))

(defun build-class-field-bindings (field-names)
  (if (endp field-names)
      nil
    (cons (cons (car field-names) 0)
          (build-class-field-bindings (cdr field-names)))))

(defun build-class-object-field-bindings ()
  '(("monitor" . 0) ("monitor-count" . 0) ("wait-set" . nil)))

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

(defun build-class-data (sfields)
  (cons "java.lang.Class"
        (build-class-field-bindings
         (cons "<name>" sfields))))

(defun build-a-class-instance (sfields class-table)
    (list (build-class-data sfields)
          (build-immediate-instance-data "java.lang.Object" class-table)))


; -----------------------------------------------------------------------------
; Arrays

(defun value-of (obj)
  (cdr obj))

(defun superclasses-of (class ct)
  (class-decl-superclasses (bound? class ct)))

(defun array-content (array)
  (value-of (field-value "ARRAY" "<array>" array)))

(defun array-type (array)
  (nth 0 (array-content array)))

(defun array-bound (array)
  (nth 1 (array-content array)))

(defun array-data (array)
  (nth 2 (array-content array)))

(defun element-at (index array)
  (nth index (array-data array)))

(defun makearray (type bound data class-table)
  (cons (list "ARRAY"
              (cons "<array>" (cons '*array* (list type bound data))))
        (build-an-instance
         (superclasses-of "ARRAY" class-table)
         class-table)))

(defun set-element-at (value index array class-table)
  (makearray (array-type array)
             (array-bound array)
             (update-nth index value (array-data array))
             class-table))

(defun primitive-type (type)
  (cond ((equal type 'T_BYTE) t)
        ((equal type 'T_SHORT) t)
        ((equal type 'T_INT) t)
        ((equal type 'T_LONG) t)
        ((equal type 'T_FLOAT) t)
        ((equal type 'T_DOUBLE) t)
        ((equal type 'T_CHAR) t)
        ((equal type 'T_BOOLEAN) t)
        (t nil)))

(defun atype-to-identifier (atype-num)
  (cond ((equal atype-num 4) 'T_BOOLEAN)
        ((equal atype-num 5) 'T_CHAR)
        ((equal atype-num 6) 'T_FLOAT)
        ((equal atype-num 7) 'T_DOUBLE)
        ((equal atype-num 8) 'T_BYTE)
        ((equal atype-num 9) 'T_SHORT)
        ((equal atype-num 10) 'T_INT)
        ((equal atype-num 11) 'T_LONG)
        (t nil)))

(defun identifier-to-atype (ident)
  (cond ((equal ident 'T_BOOLEAN) 4)
        ((equal ident 'T_CHAR) 5)
        ((equal ident 'T_FLOAT) 6)
        ((equal ident 'T_DOUBLE) 7)
        ((equal ident 'T_BYTE) 8)
        ((equal ident 'T_SHORT) 9)
        ((equal ident 'T_INT) 10)
        ((equal ident 'T_LONG) 11)
        (t nil)))

(defun default-value1 (type)
  (if (primitive-type type)
      0
      nil))

(defun init-array (type count)
  (if (zp count)
      nil
      (cons (default-value1 type) (init-array type (- count 1)))))

; The following measure is due to J
(defun natural-sum (lst)
  (cond ((endp lst) 0)
        (t (+ (nfix (car lst)) (natural-sum (cdr lst))))))

(mutual-recursion

  ; makemultiarray2 :: num, counts, s, ac --> [refs]
  (defun makemultiarray2 (car-counts cdr-counts s ac)
    (declare (xargs :measure (cons (len (cons car-counts cdr-counts))
                                   (natural-sum (cons car-counts cdr-counts)))))
    (if (zp car-counts)
        (mv (heap s) ac)
        (mv-let (new-addr new-heap)
                (makemultiarray cdr-counts s)
                (makemultiarray2 (- car-counts 1)
                                 cdr-counts
                                 (make-state (thread-table s)
                                             new-heap
                                             (class-table s))
                                 (cons (list 'REF new-addr) ac)))))

  ; makemultiarray :: [counts], s --> addr, new-heap
  (defun makemultiarray (counts s)
    (declare (xargs :measure (cons (+ 1 (len counts))
                                   (natural-sum counts))))
    (if (<= (len counts) 1)

        ; "Base case"  Handles initializing the final dimension
        (mv (len (heap s))
            (bind (len (heap s))
                  (makearray 'T_REF
                             (car counts)
                             (init-array 'T_REF (car counts))
                             (class-table s))
                  (heap s)))

        ; "Recursive Case"
        (mv-let (heap-prime lst-of-refs)
                (makemultiarray2 (car counts)
                                 (cdr counts)
                                 s
                                 nil)
                (let* ((obj (makearray 'T_REF
                                       (car counts)
                                       lst-of-refs
                                       (class-table s)))
                       (new-addr (len heap-prime))
                       (new-heap (bind new-addr obj heap-prime)))
                      (mv new-addr new-heap)))))
)

; -----------------------------------------------------------------------------
; Instruction length table -- PCs are now in bytes, not # of instructions

(defun inst-length (inst)
  (case (op-code inst)
    (AALOAD             1)
    (AASTORE            1)
    (ACONST_NULL                1)
    (ALOAD                      2)
    (ALOAD_0            1)
    (ALOAD_1            1)
    (ALOAD_2            1)
    (ALOAD_3            1)
    (ANEWARRAY          3)
    (ARETURN            1)
    (ARRAYLENGTH                1)
    (ASTORE             2)
    (ASTORE_0           1)
    (ASTORE_1           1)
    (ASTORE_2           1)
    (ASTORE_3           1)
    (BALOAD             1)
    (BASTORE            1)
    (BIPUSH             2)
    (CALOAD             1)
    (CASTORE            1)
    (DUP                        1)
    (DUP_X1             1)
    (DUP_X2             1)
    (DUP2               1)
    (DUP2_X1            1)
    (DUP2_X2            1)
    (GETFIELD           3)
    (GETSTATIC          3)
    (GOTO                       3)
    (GOTO_W             5)
    (I2B                        1)
    (I2C                        1)
    (I2L                        1)
    (I2S                        1)
    (IADD                       1)
    (IALOAD             1)
    (IAND                       1)
    (IASTORE            1)
    (ICONST_M1          1)
    (ICONST_0           1)
    (ICONST_1           1)
    (ICONST_2           1)
    (ICONST_3           1)
    (ICONST_4           1)
    (ICONST_5           1)
    (IDIV                       1)
    (IF_ACMPEQ          3)
    (IF_ACMPNE          3)
    (IF_ICMPEQ          3)
    (IF_ICMPGE          3)
    (IF_ICMPGT          3)
    (IF_ICMPLE          3)
    (IF_ICMPLT          3)
    (IF_ICMPNE          3)
    (IFEQ                       3)
    (IFGE                       3)
    (IFGT                       3)
    (IFLE                       3)
    (IFLT                       3)
    (IFNE                       3)
    (IFNONNULL          3)
    (IFNULL             3)
    (IINC                       3)
    (ILOAD                      2)
    (ILOAD_0            1)
    (ILOAD_1            1)
    (ILOAD_2            1)
    (ILOAD_3            1)
    (IMUL                       1)
    (INEG                       1)
    (INSTANCEOF         3)
    (INVOKESPECIAL              3)
    (INVOKESTATIC               3)
    (INVOKEVIRTUAL              3)
    (IOR                        1)
    (IREM                       1)
    (IRETURN            1)
    (ISHL                       1)
    (ISHR                       1)
    (ISTORE             2)
    (ISTORE_0           1)
    (ISTORE_1           1)
    (ISTORE_2           1)
    (ISTORE_3           1)
    (ISUB                       1)
    (IUSHR                      1)
    (IXOR                       1)
    (JSR                        3)
    (JSR_W                      5)
    (L2I                        1)
    (LADD                       1)
    (LALOAD             1)
    (LAND                       1)
    (LASTORE            1)
    (LCMP                       1)
    (LCONST_0           1)
    (LCONST_1           1)
    (LDC                        2)
    (LDC_W                      3)
    (LDC2_W             3)
    (LDIV                       1)
    (LLOAD                      2)
    (LLOAD_0            1)
    (LLOAD_1            1)
    (LLOAD_2            1)
    (LLOAD_3            1)
    (LMUL                       1)
    (LNEG                       1)
    (LOR                        1)
    (LREM                       1)
    (LRETURN            1)
    (LSHL                       1)
    (LSHR                       1)
    (LSTORE             2)
    (LSTORE_0           1)
    (LSTORE_1           1)
    (LSTORE_2           1)
    (LSTORE_3           1)
    (LSUB                       1)
    (LUSHR                      1)
    (LXOR                       1)
    (MONITORENTER               1)
    (MONITOREXIT                1)
    (MULTIANEWARRAY     4)
    (NEW                        3)
    (NEWARRAY           2)
    (NOP                        1)
    (POP                        1)
    (POP2                       1)
    (PUTFIELD           3)
    (PUTSTATIC          3)
    (RET                        2)
    (RETURN             1)
    (SALOAD             1)
    (SASTORE            1)
    (SIPUSH             3)
    (SWAP                       1)
    (t 1)))


; =============================================================================
; JVM INSTRUCTIONS BEGIN HERE
; =============================================================================

; -----------------------------------------------------------------------------
; (AALOAD) Instruction

(defun execute-AALOAD (inst th s)
  (let* ((index (top (stack (top-frame th s))))
         (arrayref (top (pop (stack (top-frame th s)))))
         (array (deref arrayref (heap s))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push (element-at index array)
                             (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (AASTORE) Instruction

(defun execute-AASTORE (inst th s)
  (let* ((value (top (stack (top-frame th s))))
         (index (top (pop (stack (top-frame th s)))))
         (arrayref (top (pop (pop (stack (top-frame th s)))))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (pop (pop (pop (stack (top-frame th s)))))
                :heap (bind (cadr arrayref)
                            (set-element-at value
                                            index
                                            (deref arrayref (heap s))
                                            (class-table s))
                            (heap s)))))

; -----------------------------------------------------------------------------
; (ACONST_NULL) Instruction

(defun execute-ACONST_NULL (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push '(REF -1)
                       (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (ALOAD idx) Instruction - load a reference from the locals

(defun execute-ALOAD (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (nth (arg1 inst)
                            (locals (top-frame th s)))
                       (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (ALOAD_X) Instruction - load a reference from the locals
;                         covers ALOAD_{0, 1, 2, 3}

(defun execute-ALOAD_X (inst th s n)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (nth n (locals (top-frame th s)))
                       (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (ANEWARRAY) Instruction

(defun execute-ANEWARRAY (inst th s)
  (let* ((type 'T_REF)
         (count (top (stack (top-frame th s))))
         (addr (len (heap s)))
         (obj (makearray type
                         count
                         (init-array type count)
                         (class-table s))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push (list 'REF addr)
                             (pop (stack (top-frame th s))))
                :heap (bind addr
                            obj
                            (heap s)))))

; -----------------------------------------------------------------------------
; (ARETURN) Instruction - return a reference to the preceeding frame

(defun execute-ARETURN (inst th s)
  (declare (ignore inst))
  (let* ((val (top (stack (top-frame th s))))
         (obj-ref (nth 0 (locals (top-frame th s))))
         (sync-status (sync-flg (top-frame th s)))
         (class (cur-class (top-frame th s)))
         (ret-ref (class-decl-heapref (bound? class (class-table s))))
         (new-heap (cond ((equal sync-status 'LOCKED)
                          (unlock-object th obj-ref (heap s)))
                         ((equal sync-status 'S_LOCKED)
                          (unlock-object th ret-ref (heap s)))
                         (t (heap s))))
         (s1 (modify th s
                     :call-stack (pop (call-stack th s))
                     :heap new-heap)))
    (modify th s1
            :stack (push val (stack (top-frame th s1))))))

; -----------------------------------------------------------------------------
; (ARRAYLENGTH) Instruction

(defun execute-ARRAYLENGTH (inst th s)
  (let* ((arrayref (top (stack (top-frame th s))))
         (array (deref arrayref (heap s))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push (array-bound array)
                             (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (ASTORE idx) Instruction - store a reference into the locals

(defun execute-ASTORE (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :locals (update-nth (arg1 inst)
                               (top (stack (top-frame th s)))
                               (locals (top-frame th s)))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (ASTORE_X) Instruction - store a reference into the locals
;                          covers ASTORE_{0, 1, 2, 3}

(defun execute-ASTORE_X (inst th s n)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :locals (update-nth n
                               (top (stack (top-frame th s)))
                               (locals (top-frame th s)))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (BALOAD) Instruction

(defun execute-BALOAD (inst th s)
  (let* ((index (top (stack (top-frame th s))))
         (arrayref (top (pop (stack (top-frame th s)))))
         (array (deref arrayref (heap s)))
         (element (if (equal (array-type array)
                             'T_BOOLEAN)
                      (ubyte-fix (element-at index array))
                      (byte-fix (element-at index array)))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push element
                             (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (BASTORE) Instruction

(defun execute-BASTORE (inst th s)
  (let* ((value (top (stack (top-frame th s))))
         (index (top (pop (stack (top-frame th s)))))
         (arrayref (top (pop (pop (stack (top-frame th s))))))
         (element (if (equal (array-type (deref arrayref (heap s)))
                             'T_BYTE)
                      (byte-fix value)
                      (u-fix value 1))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (pop (pop (pop (stack (top-frame th s)))))
                :heap (bind (cadr arrayref)
                            (set-element-at element
                                            index
                                            (deref arrayref (heap s))
                                            (class-table s))
                            (heap s)))))

; -----------------------------------------------------------------------------
; (BIPUSH const) Instruction

(defun execute-BIPUSH (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (byte-fix (arg1 inst))
                       (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (CALOAD) Instruction

(defun execute-CALOAD (inst th s)
  (let* ((index (top (stack (top-frame th s))))
         (arrayref (top (pop (stack (top-frame th s)))))
         (array (deref arrayref (heap s))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push (char-fix (element-at index array))
                             (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (CASTORE) Instruction

(defun execute-CASTORE (inst th s)
  (let* ((value (top (stack (top-frame th s))))
         (index (top (pop (stack (top-frame th s)))))
         (arrayref (top (pop (pop (stack (top-frame th s)))))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (pop (pop (pop (stack (top-frame th s)))))
                :heap (bind (cadr arrayref)
                            (set-element-at (char-fix value)
                                            index
                                            (deref arrayref (heap s))
                                            (class-table s))
                            (heap s)))))

; -----------------------------------------------------------------------------
; (DUP) Instruction

(defun execute-DUP (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (top (stack (top-frame th s)))
                       (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (DUP_X1) Instruction

(defun execute-DUP_X1 (inst th s)
  (let* ((val1 (top (stack (top-frame th s))))
         (val2 (top (pop (stack (top-frame th s)))))
         (stack_prime (pop (pop (stack (top-frame th s))))))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push val1 (push val2 (push val1 stack_prime))))))

; -----------------------------------------------------------------------------
; (DUP_X2) Instruction

(defun execute-DUP_X2 (inst th s)
  (let* ((val1 (top (stack (top-frame th s))))
         (val2 (top (pop (stack (top-frame th s)))))
         (val3 (top (popn 2 (stack (top-frame th s)))))
         (stack_prime (popn 3 (stack (top-frame th s)))))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push val1
                           (push val2
                                 (push val3
                                       (push val1 stack_prime)))))))

; -----------------------------------------------------------------------------
; (DUP2) Instruction

(defun execute-DUP2 (inst th s)
  (let* ((val1 (top (stack (top-frame th s))))
         (val2 (top (pop (stack (top-frame th s)))))
         (stack_prime (pop (pop (stack (top-frame th s))))))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push val1
                           (push val2
                                 (push val1
                                       (push val2 stack_prime)))))))

; -----------------------------------------------------------------------------
; (DUP2_X1) Instruction

(defun execute-DUP2_X1 (inst th s)
  (let* ((val1 (top (stack (top-frame th s))))
         (val2 (top (pop (stack (top-frame th s)))))
         (val3 (top (popn 2 (stack (top-frame th s)))))
         (stack_prime (popn 3 (stack (top-frame th s)))))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push val1
                           (push val2
                                 (push val3
                                       (push val1
                                             (push val2 stack_prime))))))))

; -----------------------------------------------------------------------------
; (DUP2_X2) Instruction

(defun execute-DUP2_X2 (inst th s)
  (let* ((val1 (top (stack (top-frame th s))))
         (val2 (top (pop (stack (top-frame th s)))))
         (val3 (top (popn 2 (stack (top-frame th s)))))
         (val4 (top (popn 3 (stack (top-frame th s)))))
         (stack_prime (popn 4 (stack (top-frame th s)))))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push val1
                       (push val2
                         (push val3
                           (push val4
                             (push val1
                               (push val2 stack_prime)))))))))

; -----------------------------------------------------------------------------
; (GETFIELD "class" "field" ?long-flag?) Instruction

(defun execute-GETFIELD (inst th s)
  (let* ((class-name (arg1 inst))
         (field-name (arg2 inst))
         (long-flag  (arg3 inst))
         (instance (deref (top (stack (top-frame th s))) (heap s)))
         (field-value (field-value class-name field-name instance)))
    (modify th s
            :pc (+ (inst-length inst) (pc (top-frame th s)))
            :stack (if long-flag
                       (push 0 (push field-value
                                     (pop (stack (top-frame th s)))))
                       (push field-value
                             (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (GETSTATIC "class" "field" ?long-flag?) Instruction

(defun static-field-value (class-name field-name s)
  (let* ((class-ref (class-decl-heapref
                     (bound? class-name (class-table s))))
         (instance (deref class-ref (heap s))))
    (field-value "java.lang.Class" field-name instance)))

(defun execute-GETSTATIC (inst th s)
  (let* ((class-name (arg1 inst))
         (field-name (arg2 inst))
         (long-flag (arg3 inst))
         (class-ref (class-decl-heapref
                     (bound? class-name (class-table s))))
         (instance (deref class-ref (heap s)))
         (field-value (field-value "java.lang.Class" field-name instance)))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (if long-flag
                           (push 0 (push field-value (stack (top-frame th s))))
                           (push field-value (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (GOTO pc) Instruction

(defun execute-GOTO (inst th s)
  (modify th s
          :pc (+ (arg1 inst) (pc (top-frame th s)))))

; -----------------------------------------------------------------------------
; (GOTO_W pc) Instruction

(defun execute-GOTO_W (inst th s)
  (modify th s
          :pc (+ (arg1 inst) (pc (top-frame th s)))))

; -----------------------------------------------------------------------------
; (I2B) Instruction - int to byte narrowing conversion

(defun execute-I2B (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (byte-fix (top (stack (top-frame th s))))
                       (pop (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (I2C) Instruction - int to char narrowing conversion

(defun execute-I2C (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (char-fix (top (stack (top-frame th s))))
                       (pop (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (I2L) Instruction - int to long conversion

(defun execute-I2L (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (long-fix (top (stack (top-frame th s))))
                             (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (I2S) Instruction - int to short narrowing conversion

(defun execute-I2S (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (short-fix (top (stack (top-frame th s))))
                       (pop (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (IADD) Instruction

(defun execute-IADD (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (int-fix
                          (+ (top (pop (stack (top-frame th s))))
                             (top (stack (top-frame th s)))))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (IALOAD) Instruction

(defun execute-IALOAD (inst th s)
  (let* ((index (top (stack (top-frame th s))))
         (arrayref (top (pop (stack (top-frame th s)))))
         (array (deref arrayref (heap s))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push (element-at index array)
                             (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (IAND) Instruction

(defun execute-IAND (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (logand (top (pop (stack (top-frame th s))))
                               (top (stack (top-frame th s))))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (IASTORE) Instruction

(defun execute-IASTORE (inst th s)
  (let* ((value (top (stack (top-frame th s))))
         (index (top (pop (stack (top-frame th s)))))
         (arrayref (top (pop (pop (stack (top-frame th s)))))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (pop (pop (pop (stack (top-frame th s)))))
                :heap (bind (cadr arrayref)
                            (set-element-at value
                                            index
                                            (deref arrayref (heap s))
                                            (class-table s))
                            (heap s)))))

; -----------------------------------------------------------------------------
; (ICONST_X) Instruction - push a certain constant onto the stack
;                          covers ICONST_{M1, 0, 1, 2, 3, 4, 5}

(defun execute-ICONST_X (inst th s n)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push n (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (IDIV) Instruction

(defun execute-IDIV (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (int-fix
                            (truncate (top (pop (stack (top-frame th s))))
                                      (top (stack (top-frame th s)))))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (IF_ACMPEQ pc) Instruction

(defun execute-IF_ACMPEQ (inst th s)
  (modify th s
          :pc (if (equal (top (pop (stack (top-frame th s))))
                         (top (stack (top-frame th s))))
                  (+ (arg1 inst) (pc (top-frame th s)))
                (+ (inst-length inst) (pc (top-frame th s))))
          :stack (pop (pop (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (IF_ACMPNE pc) Instruction

(defun execute-IF_ACMPNE (inst th s)
  (modify th s
          :pc (if (equal (top (pop (stack (top-frame th s))))
                         (top (stack (top-frame th s))))
                  (+ (inst-length inst) (pc (top-frame th s)))
                  (+ (arg1 inst) (pc (top-frame th s))))
          :stack (pop (pop (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (IF_ICMPEQ pc) Instruction

(defun execute-IF_ICMPEQ (inst th s)
  (modify th s
          :pc (if (equal (top (pop (stack (top-frame th s))))
                         (top (stack (top-frame th s))))
                  (+ (arg1 inst) (pc (top-frame th s)))
                  (+ (inst-length inst) (pc (top-frame th s))))
          :stack (pop (pop (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (IF_ICMPGE pc) Instruction

(defun execute-IF_ICMPGE (inst th s)
  (modify th s
          :pc (if (>= (top (pop (stack (top-frame th s))))
                      (top (stack (top-frame th s))))
                  (+ (arg1 inst) (pc (top-frame th s)))
                  (+ (inst-length inst) (pc (top-frame th s))))
          :stack (pop (pop (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (IF_ICMPGT pc) Instruction

(defun execute-IF_ICMPGT (inst th s)
  (modify th s
          :pc (if (> (top (pop (stack (top-frame th s))))
                     (top (stack (top-frame th s))))
                  (+ (arg1 inst) (pc (top-frame th s)))
                  (+ (inst-length inst) (pc (top-frame th s))))
          :stack (pop (pop (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (IF_ICMPLT pc) Instruction

(defun execute-IF_ICMPLT (inst th s)
  (modify th s
          :pc (if (< (top (pop (stack (top-frame th s))))
                     (top (stack (top-frame th s))))
                  (+ (arg1 inst) (pc (top-frame th s)))
                  (+ (inst-length inst) (pc (top-frame th s))))
          :stack (pop (pop (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (IF_ICMPLE pc) Instruction

(defun execute-IF_ICMPLE (inst th s)
  (modify th s
          :pc (if (<= (top (pop (stack (top-frame th s))))
                      (top (stack (top-frame th s))))
                  (+ (arg1 inst) (pc (top-frame th s)))
                  (+ (inst-length inst) (pc (top-frame th s))))
          :stack (pop (pop (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (IF_ICMPNE pc) Instruction

(defun execute-IF_ICMPNE (inst th s)
  (modify th s
          :pc (if (equal (top (pop (stack (top-frame th s))))
                         (top (stack (top-frame th s))))
                  (+ (inst-length inst) (pc (top-frame th s)))
                  (+ (arg1 inst) (pc (top-frame th s))))
          :stack (pop (pop (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (IFEQ pc) Instruction

(defun execute-IFEQ (inst th s)
  (modify th s
          :pc (if (equal (top (stack (top-frame th s))) 0)
                  (+ (arg1 inst) (pc (top-frame th s)))
                (+ (inst-length inst) (pc (top-frame th s))))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (IFGE pc) Instruction

(defun execute-IFGE (inst th s)
  (modify th s
          :pc (if (>= (top (stack (top-frame th s))) 0)
                  (+ (arg1 inst) (pc (top-frame th s)))
                (+ (inst-length inst) (pc (top-frame th s))))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (IFGT pc) Instruction

(defun execute-IFGT (inst th s)
  (modify th s
          :pc (if (> (top (stack (top-frame th s))) 0)
                  (+ (arg1 inst) (pc (top-frame th s)))
                (+ (inst-length inst) (pc (top-frame th s))))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (IFLE pc) Instruction

(defun execute-IFLE (inst th s)
  (modify th s
          :pc (if (<= (top (stack (top-frame th s))) 0)
                  (+ (arg1 inst) (pc (top-frame th s)))
                (+ (inst-length inst) (pc (top-frame th s))))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (IFLT pc) Instruction

(defun execute-IFLT (inst th s)
  (modify th s
          :pc (if (< (top (stack (top-frame th s))) 0)
                  (+ (arg1 inst) (pc (top-frame th s)))
                (+ (inst-length inst) (pc (top-frame th s))))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (IFNE pc) Instruction

(defun execute-IFNE (inst th s)
  (modify th s
          :pc (if (equal (top (stack (top-frame th s))) 0)
                  (+ (inst-length inst) (pc (top-frame th s)))
                (+ (arg1 inst) (pc (top-frame th s))))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (IFNONNULL pc) Instruction

(defun execute-IFNONNULL (inst th s)
  (modify th s
          :pc (if (equal (top (stack (top-frame th s))) '(REF -1))
                  (+ (inst-length inst) (pc (top-frame th s)))
                  (+ (arg1 inst) (pc (top-frame th s))))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (IFNULL pc) Instruction

(defun execute-IFNULL (inst th s)
  (modify th s
          :pc (if (equal (top (stack (top-frame th s))) '(REF -1))
                  (+ (arg1 inst) (pc (top-frame th s)))
                  (+ (inst-length inst) (pc (top-frame th s))))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (IINC idx const) Instruction - Increment local variable by a constant

(defun execute-IINC (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :locals (update-nth (arg1 inst)
                               (int-fix
                                  (+ (arg2 inst)
                                     (nth (arg1 inst)
                                          (locals (top-frame th s)))))
                               (locals (top-frame th s)))))

; -----------------------------------------------------------------------------
; (ILOAD idx) Instruction - Push a local onto the stack

(defun execute-ILOAD (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (nth (arg1 inst)
                            (locals (top-frame th s)))
                       (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (ILOAD_X) Instruction - Push a local onto the stack
;                         covers ILOAD_{0, 1, 2, 3}

(defun execute-ILOAD_X (inst th s n)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (nth n (locals (top-frame th s)))
                       (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (IMUL) Instruction

(defun execute-IMUL (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (int-fix
                        (* (top (pop (stack (top-frame th s))))
                           (top (stack (top-frame th s)))))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (INEG) Instruction
;        Because of the way the JVM represents 2's complement ints,
;         the negation of the most negative int is itself

(defun execute-INEG (inst th s)
  (let* ((result (if (equal (top (stack (top-frame th s)))
                            *most-negative-integer*)
                     *most-negative-integer*
                     (- (top (stack (top-frame th s)))))))
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push result (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (INSTANCEOF) Instruction

(defun execute-INSTANCEOF (inst th s)
  (let* ((ref (top (stack (top-frame th s))))
         (obj (deref ref (heap s)))
         (obj-class (caar obj))
         (obj-supers (cons obj-class (class-decl-superclasses
                      (bound? obj-class (class-table s)))))
         (value (if (nullrefp ref)
                    0
                    (if (member-equal (arg1 inst) obj-supers)
                        1
                        0))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push value (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (IOR) Instruction

(defun execute-IOR (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (logior (top (pop (stack (top-frame th s))))
                               (top (stack (top-frame th s))))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (IREM) Instruction

(defun execute-IREM (inst th s)
  (let* ((val1 (top (pop (stack (top-frame th s)))))
         (val2 (top (stack (top-frame th s))))
         (result (- val1 (* (truncate val1 val2) val2))))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push result
                           (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (IRETURN) Instruction - return an int

(defun execute-IRETURN (inst th s)
  (declare (ignore inst))
  (let* ((val (top (stack (top-frame th s))))
         (obj-ref (nth 0 (locals (top-frame th s))))
         (sync-status (sync-flg (top-frame th s)))
         (class (cur-class (top-frame th s)))
         (ret-ref (class-decl-heapref (bound? class (class-table s))))
         (new-heap (cond ((equal sync-status 'LOCKED)
                          (unlock-object th obj-ref (heap s)))
                         ((equal sync-status 'S_LOCKED)
                          (unlock-object th ret-ref (heap s)))
                         (t (heap s))))
         (s1 (modify th s
                     :call-stack (pop (call-stack th s))
                     :heap new-heap)))
    (modify th s1
            :stack (push val (stack (top-frame th s1))))))

; -----------------------------------------------------------------------------
; (ISHL) Instruction

(defun execute-ISHL (inst th s)
  (let* ((val1 (top (pop (stack (top-frame th s)))))
         (val2 (top (stack (top-frame th s))))
         (shiftval (5-bit-fix val2))
         (result (shl val1 shiftval)))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push (int-fix result)
                           (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (ISHR) Instruction

(defun execute-ISHR (inst th s)
  (let* ((val1 (top (pop (stack (top-frame th s)))))
         (val2 (top (stack (top-frame th s))))
         (shiftval (5-bit-fix val2))
         (result (shr val1 shiftval)))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push (int-fix result)
                           (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (ISTORE idx) Instruction - store an int into the locals

(defun execute-ISTORE (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :locals (update-nth (arg1 inst)
                               (top (stack (top-frame th s)))
                               (locals (top-frame th s)))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (ISTORE_X) Instruction - store an int into the locals
;                          covers ISTORE_{0, 1, 2, 3}

(defun execute-ISTORE_X (inst th s n)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :locals (update-nth n
                               (top (stack (top-frame th s)))
                               (locals (top-frame th s)))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (ISUB) Instruction

(defun execute-ISUB (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (int-fix (- (top (pop (stack (top-frame th s))))
                                   (top (stack (top-frame th s)))))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (IUSHR) Instruction

(defun execute-IUSHR (inst th s)
  (let* ((val1 (top (pop (stack (top-frame th s)))))
         (val2 (top (stack (top-frame th s))))
         (shiftval (5-bit-fix val2))
         (result (shr val1 shiftval)))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push (int-fix result)
                           (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (IXOR) Instruction

(defun execute-IXOR (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (logxor (top (pop (stack (top-frame th s))))
                               (top (stack (top-frame th s))))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (JSR) Instruction

(defun execute-JSR (inst th s)
  (modify th s
          :pc (+ (arg1 inst) (pc (top-frame th s)))
          :stack (push (list 'RETURNADDRESS
                             (+ (inst-length inst)
                                (pc (top-frame th s))))
                       (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (JSR_W) Instruction

(defun execute-JSR_W (inst th s)
  (modify th s
          :pc (+ (arg1 inst) (pc (top-frame th s)))
          :stack (push (list 'RETURNADDRESS
                             (+ (inst-length inst)
                                (pc (top-frame th s))))
                       (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (INVOKESPECIAL "class" "name" n) Instruction

(defun class-name-of-ref (ref heap)
  (car (car (deref ref heap))))

(defun bind-formals (n stack)
  (if (zp n)
      nil
    (cons (top stack)
          (bind-formals (- n 1) (pop stack)))))

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

(defun execute-INVOKESPECIAL (inst th s)
  (let* ((method-name (arg2 inst))
         (nformals (arg3 inst))
         (obj-ref (top (popn nformals (stack (top-frame th s)))))
         (instance (deref obj-ref (heap s)))
         (obj-class-name (arg1 inst))
         (closest-method
          (lookup-method method-name
                         obj-class-name
                         (class-table s)))
         (prog (method-program closest-method))
         (s1 (modify th s
                     :pc (+ (inst-length inst) (pc (top-frame th s)))
                     :stack (popn (+ nformals 1)
                                  (stack (top-frame th s)))))
         (tThread (rrefToThread obj-ref (thread-table s))))
    (cond
     ((method-isNative? closest-method)
      (cond ((equal method-name "start")
             (modify tThread s1 :status 'SCHEDULED))
            ((equal method-name "stop")
             (modify tThread s1
                     :status 'UNSCHEDULED))
            (t s)))
     ((and (method-sync closest-method)
           (objectLockable? instance th))
      (modify th s1
              :call-stack
              (push (make-frame 0
                                (reverse
                                 (bind-formals (+ nformals 1)
                                               (stack (top-frame th s))))
                                nil
                                prog
                                'LOCKED
                                (arg1 inst))
                    (call-stack th s1))
              :heap (lock-object th obj-ref (heap s))))
     ((method-sync closest-method)
      s)
     (t
      (modify th s1
              :call-stack
              (push (make-frame 0
                                (reverse
                                 (bind-formals (+ nformals 1)
                                               (stack (top-frame th s))))
                                nil
                                prog
                                'UNLOCKED
                                (arg1 inst))
                    (call-stack th s1)))))))

; -----------------------------------------------------------------------------
; (INVOKESTATIC "class" "name" n) Instruction

(defun execute-INVOKESTATIC (inst th s)
  (let* ((class (arg1 inst))
         (method-name (arg2 inst))
         (nformals (arg3 inst))
         (obj-ref (class-decl-heapref (bound? class (class-table s))))
         (instance (deref obj-ref (heap s)))
         (closest-method
          (lookup-method method-name
                         (arg1 inst)
                         (class-table s)))
         (prog (method-program closest-method))
         (s1 (modify th s
                     :pc (+ (inst-length inst) (pc (top-frame th s)))
                     :stack (popn nformals (stack (top-frame th s))))))
    (cond
     ((and (method-sync closest-method)
           (objectLockable? instance th))
      (modify th s1
              :call-stack
              (push (make-frame 0
                                (reverse
                                 (bind-formals nformals
                                               (stack (top-frame th s))))
                                nil
                                prog
                                'S_LOCKED
                                (arg1 inst))
                    (call-stack th s1))
              :heap (lock-object th obj-ref (heap s))))
     ((method-sync closest-method)
      s)
     (t
      (modify th s1
              :call-stack
              (push (make-frame 0
                                (reverse
                                 (bind-formals nformals
                                               (stack (top-frame th s))))
                                nil
                                prog
                                'UNLOCKED
                                (arg1 inst))
                    (call-stack th s1)))))))

; -----------------------------------------------------------------------------
; (INVOKEVIRTUAL "class" "name" n) Instruction

(defun execute-INVOKEVIRTUAL (inst th s)
  (let* ((method-name (arg2 inst))
         (nformals (arg3 inst))
         (obj-ref (top (popn nformals (stack (top-frame th s)))))
         (instance (deref obj-ref (heap s)))
         (obj-class-name (class-name-of-ref obj-ref (heap s)))
         (closest-method
          (lookup-method method-name
                         obj-class-name
                         (class-table s)))
         (prog (method-program closest-method))
         (s1 (modify th s
                     :pc (+ (inst-length inst) (pc (top-frame th s)))
                     :stack (popn (+ nformals 1)
                                  (stack (top-frame th s)))))
         (tThread (rrefToThread obj-ref (thread-table s))))
    (cond
     ((method-isNative? closest-method)
      (cond ((equal method-name "start")
             (modify tThread s1 :status 'SCHEDULED))
            ((equal method-name "stop")
             (modify tThread s1
                     :status 'UNSCHEDULED))
            (t s)))
     ((and (method-sync closest-method)
           (objectLockable? instance th))
      (modify th s1
              :call-stack
              (push (make-frame 0
                                (reverse
                                 (bind-formals (+ nformals 1)
                                               (stack (top-frame th s))))
                                nil
                                prog
                                'LOCKED
                                (arg1 inst))
                    (call-stack th s1))
              :heap (lock-object th obj-ref (heap s))))
     ((method-sync closest-method)
      s)
     (t
      (modify th s1
              :call-stack
              (push (make-frame 0
                                (reverse
                                 (bind-formals (+ nformals 1)
                                               (stack (top-frame th s))))
                                nil
                                prog
                                'UNLOCKED
                                (arg1 inst))
                    (call-stack th s1)))))))

; -----------------------------------------------------------------------------
; (L2I) Instruction - long to int narrowing conversion

(defun execute-L2I (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (int-fix (top (pop (stack (top-frame th s)))))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (LADD) Instruction - Add to longs from the top of the stack

(defun execute-LADD (inst th s)
  (let* ((val1 (top (pop (stack (top-frame th s)))))
         (val2 (top (popn 3 (stack (top-frame th s))))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push 0
                             (push (long-fix (+ val1 val2))
                                   (popn 4 (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (LALOAD) Instruction

(defun execute-LALOAD (inst th s)
  (let* ((index (top (stack (top-frame th s))))
         (arrayref (top (pop (stack (top-frame th s)))))
         (array (deref arrayref (heap s))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push 0
                             (push (element-at index array)
                                   (pop (pop (stack (top-frame th s)))))))))

; -----------------------------------------------------------------------------
; (LAND) Instruction

(defun execute-LAND (inst th s)
  (let* ((val1 (top (pop (stack (top-frame th s)))))
         (val2 (top (popn 3 (stack (top-frame th s))))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push 0
                             (push (logand val1 val2)
                                   (popn 4 (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (LASTORE) Instruction

(defun execute-LASTORE (inst th s)
  (let* ((value (top (pop (stack (top-frame th s)))))
         (index (top (pop (pop (stack (top-frame th s))))))
         (arrayref (top (popn 3 (stack (top-frame th s))))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (popn 4 (stack (top-frame th s)))
                :heap (bind (cadr arrayref)
                            (set-element-at value
                                            index
                                            (deref arrayref (heap s))
                                            (class-table s))
                            (heap s)))))

; -----------------------------------------------------------------------------
; (LCMP) Instruction - compare two longs
;                      val1 > val2 --> 1
;                      val1 = val2 --> 0
;                      val1 < val2 --> -1

(defun execute-LCMP (inst th s)
  (let* ((val2 (top (pop (stack (top-frame th s)))))
         (val1 (top (popn 3 (stack (top-frame th s)))))
         (result (cond ((> val1 val2) 1)
                       ((< val1 val2) -1)
                       (t 0))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push result
                             (popn 4 (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (LCONST_X) Instruction - push a certain long constant onto the stack
;                          covers LCONST_{0, 1}

(defun execute-LCONST_X (inst th s n)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push n (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (LDC) Instruction

(defun set-instance-field (class-name field-name value instance)
  (bind class-name
        (bind field-name value
              (binding class-name instance))
        instance))

(defun execute-LDC (inst th s)
  (let* ((class (cur-class (top-frame th s)))
         (cp (retrieve-cp class (class-table s)))
         (entry (nth (arg1 inst) cp))
         (value (cadr entry)))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push value (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (LDC2_W) Instruction

(defun execute-LDC2_W (inst th s)
  (let* ((class (cur-class (top-frame th s)))
         (cp (retrieve-cp class (class-table s)))
         (entry (nth (arg1 inst) cp))
         (value (cadr entry)))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push value (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (LDIV) Instruction

(defun execute-LDIV (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push
                         (long-fix
                            (truncate (top (popn 3 (stack (top-frame th s))))
                                      (top (pop (stack (top-frame th s))))))
                       (popn 4 (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (LLOAD idx) Instruction - Push a long local onto the stack

(defun execute-LLOAD (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (nth (arg1 inst)
                                  (locals (top-frame th s)))
                             (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (LLOAD_X) Instruction - Push a long local onto the stack
;                         covers LLOAD_{0, 1, 2, 3}

(defun execute-LLOAD_X (inst th s n)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (nth n (locals (top-frame th s)))
                             (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (LMUL) Instruction

(defun execute-LMUL (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (ulong-fix
                              (* (top (pop (stack (top-frame th s))))
                                 (top (popn 3 (stack (top-frame th s))))))
                             (popn 4 (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (LNEG) Instruction
;        Because of the way the JVM represents 2's complement ints,
;         the negation of the most negative int is itself

(defun execute-LNEG (inst th s)
  (let* ((result (if (equal (top (pop (stack (top-frame th s))))
                            *most-negative-long*)
                     *most-negative-long*
                     (- (top (pop (stack (top-frame th s))))))))
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push result (popn 2 (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (LOR) Instruction

(defun execute-LOR (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (logior (top (pop (stack (top-frame th s))))
                                     (top (popn 3 (stack (top-frame th s)))))
                             (popn 4 (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (LREM) Instruction

(defun execute-LREM (inst th s)
  (let* ((val1 (top (pop (stack (top-frame th s)))))
         (val2 (top (popn 3 (stack (top-frame th s)))))
         (result (- val1 (* (truncate val1 val2) val2))))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push 0
                           (push result
                                 (popn 4 (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (LRETURN) Instruction - return a long

(defun execute-LRETURN (inst th s)
  (declare (ignore inst))
  (let* ((val (top (pop (stack (top-frame th s)))))
         (obj-ref (nth 0 (locals (top-frame th s))))
         (sync-status (sync-flg (top-frame th s)))
         (class (cur-class (top-frame th s)))
         (ret-ref (class-decl-heapref (bound? class (class-table s))))
         (new-heap (cond ((equal sync-status 'LOCKED)
                          (unlock-object th obj-ref (heap s)))
                         ((equal sync-status 'S_LOCKED)
                          (unlock-object th ret-ref (heap s)))
                         (t (heap s))))
         (s1 (modify th s
                     :call-stack (pop (call-stack th s))
                     :heap new-heap)))
    (modify th s1
            :stack (push 0 (push val (stack (top-frame th s1)))))))

; -----------------------------------------------------------------------------
; (LSHL) Instruction

(defun execute-LSHL (inst th s)
  (let* ((val1 (top (popn 2 (stack (top-frame th s)))))
         (val2 (top (stack (top-frame th s))))
         (shiftval (6-bit-fix val2))
         (result (shl val1 shiftval)))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push 0
                           (push (long-fix result)
                                 (popn 3 (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (LSHR) Instruction

(defun execute-LSHR (inst th s)
  (let* ((val1 (top (popn 2 (stack (top-frame th s)))))
         (val2 (top (stack (top-frame th s))))
         (shiftval (6-bit-fix val2))
         (result (shr val1 shiftval)))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push 0
                           (push (long-fix result)
                                 (popn 3 (pop (stack (top-frame th s)))))))))

; -----------------------------------------------------------------------------
; (LSTORE idx) Instruction - store a long into the locals

(defun execute-LSTORE (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :locals (update-nth (arg1 inst)
                               (top (pop (stack (top-frame th s))))
                               (locals (top-frame th s)))
          :stack (popn 2 (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (LSTORE_X) Instruction - store a long into the locals
;                          covers LSTORE_{0, 1, 2, 3}

(defun execute-LSTORE_X (inst th s n)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :locals (update-nth n
                               (top (pop (stack (top-frame th s))))
                               (locals (top-frame th s)))
          :stack (popn 2 (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (LSUB) Instruction

(defun execute-LSUB (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push
                        (ulong-fix (- (top (popn 3 (stack (top-frame th s))))
                                      (top (pop (stack (top-frame th s))))))
                             (popn 4 (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (LUSHR) Instruction

(defun execute-LUSHR (inst th s)
  (let* ((val1 (top (popn 2 (stack (top-frame th s)))))
         (val2 (top (stack (top-frame th s))))
         (shiftval (6-bit-fix val2))
         (result (shr val1 shiftval)))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push 0
                           (push (long-fix result)
                                 (popn 3 (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (LXOR) Instruction

(defun execute-LXOR (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (logxor (top (pop (stack (top-frame th s))))
                                     (top (popn 3 (stack (top-frame th s)))))
                             (popn 4 (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (MONITORENTER) Instruction

(defun execute-MONITORENTER (inst th s)
  (let* ((obj-ref (top (stack (top-frame th s))))
         (instance (deref obj-ref (heap s))))
    (cond
     ((objectLockable? instance th)
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (pop (stack (top-frame th s)))
              :heap (lock-object th obj-ref (heap s))))
     (t s))))

; -----------------------------------------------------------------------------
; (MONITOREXIT) Instruction

(defun execute-MONITOREXIT (inst th s)
  (let* ((obj-ref (top (stack (top-frame th s))))
         (instance (deref obj-ref (heap s))))
    (cond
     ((objectUnLockable? instance th)
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (pop (stack (top-frame th s)))
              :heap (unlock-object th obj-ref (heap s))))
     (t s))))

; -----------------------------------------------------------------------------
; (MULTIANEWARRAY) Instruction

(defun execute-MULTIANEWARRAY (inst th s)
  (let* ((dimentions (arg1 inst))
         (counts (reverse (take dimentions (stack (top-frame th s))))))
        (mv-let (addr new-heap)
                (makemultiarray counts s)
            (modify th s
                    :pc (+ (inst-length inst) (pc (top-frame th s)))
                    :stack (push (list 'REF addr)
                                 (nthcdr dimentions (stack (top-frame th s))))
                    :heap new-heap))))

; -----------------------------------------------------------------------------
; (NEW "class") Instruction

(defun execute-NEW (inst th s)
  (let* ((class-name (arg1 inst))
         (class-table (class-table s))
         (closest-method (lookup-method "run" class-name class-table))
         (prog (method-program closest-method))
         (new-object (build-an-instance
                      (cons class-name
                            (class-decl-superclasses
                             (bound? class-name class-table)))
                      class-table))
         (new-address (len (heap s)))
         (s1 (modify th s
                     :pc (+ (inst-length inst) (pc (top-frame th s)))
                     :stack (push (list 'REF new-address)
                                  (stack (top-frame th s)))
                     :heap (bind new-address new-object (heap s)))))
    (if (isThreadObject? class-name class-table)
        (modify nil s1
                :thread-table
                (addto-tt
                 (push
                  (make-frame 0
                              (list (list 'REF new-address))
                              nil
                              prog
                              'UNLOCKED
                              class-name)
                  nil)
                 'UNSCHEDULED
                 (list 'REF new-address)
                 (thread-table s1)))
      s1)))

; -----------------------------------------------------------------------------
; (NEWARRAY) Instruction

(defun execute-NEWARRAY (inst th s)
  (let* ((type (arg1 inst))
         (count (top (stack (top-frame th s))))
         (addr (len (heap s)))
         (obj (makearray type
                         count
                         (init-array type count)
                         (class-table s))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push (list 'REF addr)
                             (pop (stack (top-frame th s))))
                :heap (bind addr
                            obj
                            (heap s)))))

; -----------------------------------------------------------------------------
; (NOP) Instruction

(defun execute-NOP (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))))

; -----------------------------------------------------------------------------
; (POP) Instruction

(defun execute-POP (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (POP2) Instruction

(defun execute-POP2 (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (popn 2 (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (PUTFIELD "class" "field" ?long-flag?) Instruction

(defun execute-PUTFIELD (inst th s)
  (let* ((class-name (arg1 inst))
         (field-name (arg2 inst))
         (long-flag  (arg3 inst))
         (value (if long-flag
                    (top (pop (stack (top-frame th s))))
                    (top (stack (top-frame th s)))))
         (instance (if long-flag
                       (deref (top (popn 2 (stack (top-frame th s)))) (heap s))
                       (deref (top (pop (stack (top-frame th s)))) (heap s))))
         (address (cadr (if long-flag
                            (top (popn 2 (stack (top-frame th s))))
                            (top (pop (stack (top-frame th s))))))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (if long-flag
                           (popn 3 (stack (top-frame th s)))
                           (pop (pop (stack (top-frame th s)))))
                :heap (bind address
                            (set-instance-field class-name
                                                field-name
                                                value
                                                instance)
                            (heap s)))))

; -----------------------------------------------------------------------------
; (PUTSTATIC "class" "field" ?long-flag?) Instruction

(defun execute-PUTSTATIC (inst th s)
  (let* ((class-name (arg1 inst))
         (field-name (arg2 inst))
         (long-flag (arg3 inst))
         (class-ref (class-decl-heapref
                     (bound? class-name (class-table s))))
         (value (if long-flag
                    (top (pop (stack (top-frame th s))))
                    (top (stack (top-frame th s)))))
         (instance (deref class-ref (heap s))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (if long-flag
                           (popn 2 (stack (top-frame th s)))
                           (pop (stack (top-frame th s))))
                :heap (bind (cadr class-ref)
                            (set-instance-field "java.lang.Class"
                                                field-name
                                                value
                                                instance)
                            (heap s)))))

; -----------------------------------------------------------------------------
; (RET) Instruction

(defun execute-RET (inst th s)
  (let* ((ret-addr (nth (arg1 inst) (locals (top-frame th s))))
         (addr (cadr ret-addr)))
        (modify th s :pc addr)))

; -----------------------------------------------------------------------------
; (RETURN) Instruction - Void Return

(defun execute-RETURN (inst th s)
  (declare (ignore inst))
  (let* ((obj-ref (nth 0 (locals (top-frame th s))))
         (sync-status (sync-flg (top-frame th s)))
         (class (cur-class (top-frame th s)))
         (ret-ref (class-decl-heapref (bound? class (class-table s))))
         (new-heap (cond ((equal sync-status 'LOCKED)
                          (unlock-object th obj-ref (heap s)))
                         ((equal sync-status 'S_LOCKED)
                          (unlock-object th ret-ref (heap s)))
                         (t (heap s)))))
    (modify th s
            :call-stack (pop (call-stack th s))
            :heap new-heap)))

; -----------------------------------------------------------------------------
; (SALOAD) Instruction

(defun execute-SALOAD (inst th s)
  (let* ((index (top (stack (top-frame th s))))
         (arrayref (top (pop (stack (top-frame th s)))))
         (array (deref arrayref (heap s))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push (element-at index array)
                             (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (SASTORE) Instruction

(defun execute-SASTORE (inst th s)
  (let* ((value (top (stack (top-frame th s))))
         (index (top (pop (stack (top-frame th s)))))
         (arrayref (top (pop (pop (stack (top-frame th s)))))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (pop (pop (pop (stack (top-frame th s)))))
                :heap (bind (cadr arrayref)
                            (set-element-at (short-fix value)
                                            index
                                            (deref arrayref (heap s))
                                            (class-table s))
                            (heap s)))))

; -----------------------------------------------------------------------------
; (SIPUSH const) Instruction

(defun execute-SIPUSH (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (short-fix (arg1 inst))
                       (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (SWAP) Instruction

(defun execute-SWAP (inst th s)
  (let* ((val1 (top (stack (top-frame th s))))
         (val2 (top (pop (stack (top-frame th s))))))
      (modify th s
              :pc (+ (inst-length inst) (pc (top-frame th s)))
              :stack (push val2
                           (push val1
                              (pop (pop (stack (top-frame th s)))))))))

; -----------------------------------------------------------------------------
; Putting it all together

(defun index-into-program (byte-offset program)
  (declare (xargs :measure (len program)))
  (if (endp program)
      nil
      (if (zp byte-offset)
          (car program)
          (index-into-program (- byte-offset
                                 (inst-length (car program)))
                              (cdr program)))))

(defun next-inst (th s)
  (index-into-program (pc (top-frame th s))
                      (program (top-frame th s))))

(defun do-inst (inst th s)
  (case (op-code inst)
    (AALOAD         (execute-AALOAD inst th s))
    (AASTORE        (execute-AASTORE inst th s))
    (ACONST_NULL    (execute-ACONST_NULL inst th s))
    (ALOAD          (execute-ALOAD inst th s))
    (ALOAD_0        (execute-ALOAD_X inst th s 0))
    (ALOAD_1        (execute-ALOAD_X inst th s 1))
    (ALOAD_2        (execute-ALOAD_X inst th s 2))
    (ALOAD_3        (execute-ALOAD_X inst th s 3))
    (ANEWARRAY      (execute-ANEWARRAY inst th s))
    (ARETURN        (execute-ARETURN inst th s))
    (ARRAYLENGTH    (execute-ARRAYLENGTH inst th s))
    (ASTORE         (execute-ASTORE inst th s))
    (ASTORE_0       (execute-ASTORE_X inst th s 0))
    (ASTORE_1       (execute-ASTORE_X inst th s 1))
    (ASTORE_2       (execute-ASTORE_X inst th s 2))
    (ASTORE_3       (execute-ASTORE_X inst th s 3))
    (BALOAD         (execute-BALOAD inst th s))
    (BASTORE        (execute-BASTORE inst th s))
    (BIPUSH         (execute-BIPUSH inst th s))
    (CALOAD         (execute-CALOAD inst th s))
    (CASTORE        (execute-CASTORE inst th s))
    (DUP            (execute-DUP inst th s))
    (DUP_X1         (execute-DUP_X1 inst th s))
    (DUP_X2         (execute-DUP_X2 inst th s))
    (DUP2           (execute-DUP2 inst th s))
    (DUP2_X1        (execute-DUP2_X1 inst th s))
    (DUP2_X2        (execute-DUP2_X2 inst th s))
    (GETFIELD       (execute-GETFIELD inst th s))
    (GETSTATIC      (execute-GETSTATIC inst th s))
    (GOTO           (execute-GOTO inst th s))
    (GOTO_W         (execute-GOTO_W inst th s))
    (I2B            (execute-I2B inst th s))
    (I2C            (execute-I2C inst th s))
    (I2L            (execute-I2L inst th s))
    (I2S            (execute-I2S inst th s))
    (IADD           (execute-IADD inst th s))
    (IALOAD         (execute-IALOAD inst th s))
    (IAND           (execute-IAND inst th s))
    (IASTORE        (execute-IASTORE inst th s))
    (ICONST_M1      (execute-ICONST_X inst th s -1))
    (ICONST_0       (execute-ICONST_X inst th s 0))
    (ICONST_1       (execute-ICONST_X inst th s 1))
    (ICONST_2       (execute-ICONST_X inst th s 2))
    (ICONST_3       (execute-ICONST_X inst th s 3))
    (ICONST_4       (execute-ICONST_X inst th s 4))
    (ICONST_5       (execute-ICONST_X inst th s 5))
    (IDIV           (execute-IDIV inst th s))
    (IF_ACMPEQ      (execute-IF_ACMPEQ inst th s))
    (IF_ACMPNE      (execute-IF_ACMPNE inst th s))
    (IF_ICMPEQ      (execute-IF_ICMPEQ inst th s))
    (IF_ICMPGE      (execute-IF_ICMPGE inst th s))
    (IF_ICMPGT      (execute-IF_ICMPGT inst th s))
    (IF_ICMPLE      (execute-IF_ICMPLE inst th s))
    (IF_ICMPLT      (execute-IF_ICMPLT inst th s))
    (IF_ICMPNE      (execute-IF_ICMPNE inst th s))
    (IFEQ           (execute-IFEQ inst th s))
    (IFGE           (execute-IFGE inst th s))
    (IFGT           (execute-IFGT inst th s))
    (IFLE           (execute-IFLE inst th s))
    (IFLT           (execute-IFLT inst th s))
    (IFNE           (execute-IFNE inst th s))
    (IFNONNULL      (execute-IFNONNULL inst th s))
    (IFNULL         (execute-IFNULL inst th s))
    (IINC           (execute-IINC inst th s))
    (ILOAD          (execute-ILOAD inst th s))
    (ILOAD_0        (execute-ILOAD_X inst th s 0))
    (ILOAD_1        (execute-ILOAD_X inst th s 1))
    (ILOAD_2        (execute-ILOAD_X inst th s 2))
    (ILOAD_3        (execute-ILOAD_X inst th s 3))
    (IMUL           (execute-IMUL inst th s))
    (INEG           (execute-INEG inst th s))
    (INSTANCEOF     (execute-INSTANCEOF inst th s))
    (INVOKESPECIAL  (execute-INVOKESPECIAL inst th s))
    (INVOKESTATIC   (execute-INVOKESTATIC inst th s))
    (INVOKEVIRTUAL  (execute-INVOKEVIRTUAL inst th s))
    (IOR            (execute-IOR inst th s))
    (IREM           (execute-IREM inst th s))
    (IRETURN        (execute-IRETURN inst th s))
    (ISHL           (execute-ISHL inst th s))
    (ISHR           (execute-ISHR inst th s))
    (ISTORE         (execute-ISTORE inst th s))
    (ISTORE_0       (execute-ISTORE_X inst th s 0))
    (ISTORE_1       (execute-ISTORE_X inst th s 1))
    (ISTORE_2       (execute-ISTORE_X inst th s 2))
    (ISTORE_3       (execute-ISTORE_X inst th s 3))
    (ISUB           (execute-ISUB inst th s))
    (IUSHR          (execute-IUSHR inst th s))
    (IXOR           (execute-IXOR inst th s))
    (JSR            (execute-JSR inst th s))
    (JSR_W          (execute-JSR_W inst th s))
    (L2I            (execute-L2I inst th s))
    (LADD           (execute-LADD inst th s))
    (LALOAD         (execute-LALOAD inst th s))
    (LAND           (execute-LAND inst th s))
    (LASTORE        (execute-LASTORE inst th s))
    (LCMP           (execute-LCMP inst th s))
    (LCONST_0       (execute-LCONST_X inst th s 0))
    (LCONST_1       (execute-LCONST_X inst th s 1))
    (LDC            (execute-LDC inst th s))
    (LDC_W          (execute-LDC inst th s))
    (LDC2_W         (execute-LDC2_W inst th s))
    (LDIV           (execute-LDIV inst th s))
    (LLOAD          (execute-LLOAD inst th s))
    (LLOAD_0        (execute-LLOAD_X inst th s 0))
    (LLOAD_1        (execute-LLOAD_X inst th s 1))
    (LLOAD_2        (execute-LLOAD_X inst th s 2))
    (LLOAD_3        (execute-LLOAD_X inst th s 3))
    (LMUL           (execute-LMUL inst th s))
    (LNEG           (execute-LNEG inst th s))
    (LOR            (execute-LOR inst th s))
    (LREM           (execute-LREM inst th s))
    (LRETURN        (execute-LRETURN inst th s))
    (LSHL           (execute-LSHL inst th s))
    (LSHR           (execute-LSHR inst th s))
    (LSTORE         (execute-LSTORE inst th s))
    (LSTORE_0       (execute-LSTORE_X inst th s 0))
    (LSTORE_1       (execute-LSTORE_X inst th s 1))
    (LSTORE_2       (execute-LSTORE_X inst th s 2))
    (LSTORE_3       (execute-LSTORE_X inst th s 3))
    (LSUB           (execute-LSUB inst th s))
    (LUSHR          (execute-LUSHR inst th s))
    (LXOR           (execute-LXOR inst th s))
    (MONITORENTER   (execute-MONITORENTER inst th s))
    (MONITOREXIT    (execute-MONITOREXIT inst th s))
    (MULTIANEWARRAY (execute-MULTIANEWARRAY inst th s))
    (NEW            (execute-NEW inst th s))
    (NEWARRAY       (execute-NEWARRAY inst th s))
    (NOP            (execute-NOP inst th s))
    (POP            (execute-POP  inst th s))
    (POP2           (execute-POP2  inst th s))
    (PUTFIELD       (execute-PUTFIELD inst th s))
    (PUTSTATIC      (execute-PUTSTATIC inst th s))
    (RET            (execute-RET inst th s))
    (RETURN         (execute-RETURN inst th s))
    (SALOAD         (execute-SALOAD inst th s))
    (SASTORE        (execute-SASTORE inst th s))
    (SIPUSH         (execute-SIPUSH inst th s))
    (SWAP           (execute-SWAP inst th s))
    (HALT           s)
    (otherwise s)))

(defun step (th s)
  (if (equal (status th s) 'SCHEDULED)
    (do-inst (next-inst th s) th s)
    s))

(defun run (sched s)
  (if (endp sched)
      s
    (run (cdr sched) (step (car sched) s))))

; Begin the simulator
;

(defun ack2 (num n lst)
  (if (zp n)
      lst
      (ack2 num (- n 1) (cons num lst))))

(defun ack0 (n)
  (ack2 0 n nil))

(acl2::set-state-ok t)

(defun sim-loop (s acl2::state)
  (declare (acl2::xargs :mode :program))
  (prog2$
   (acl2::cw "~%>>")                         ;;; Print prompt
   (acl2::mv-let
    (flg cmd acl2::state)
    (acl2::read-object acl2::*standard-oi* acl2::state)  ;;; read next command
    (declare (ignore flg))
    (cond
     ((equal cmd :q) (acl2::value t))        ;;; quit on :q
     ((and (consp cmd)                 ;;; recognize (step i) and (step i j)
           (acl2::eq (car cmd) 'step)        ;;; where i and j are integers
           (true-listp cmd)
           (consp (cdr cmd))
           (integerp (cadr cmd))
           (or (acl2::null (cddr cmd))
               (and (integerp (caddr cmd))
                    (acl2::null (cdddr cmd)))))
      (let ((thread (cadr cmd))
            (n (if (cddr cmd) (caddr cmd) 1)))
        (sim-loop (run (ack2 thread n nil) s) acl2::state)))
     (t (acl2::mv-let (flg val acl2::state)
                      (acl2::simple-translate-and-eval cmd
                                                       (list (cons 's s))
                                                       nil
                                                       "Your command" 'sim
                                                       (acl2::w acl2::state)
                                                       acl2::state
                                                       nil)
                      (prog2$
                       (cond (flg nil)
                             (t (acl2::cw "~x0~%" (cdr val))))
                       (sim-loop s acl2::state))))))))

(defun sim (s acl2::state)
  (declare (acl2::xargs :mode :program))
  (prog2$
   (acl2::cw "~%M5 Simulator.~%~%")
   (sim-loop s acl2::state)))

; A small assembler to resolve labels into relative byte addresses
;
; Labels are symbols in the "LABEL" package.  Examples include:
;      LABEL::JUMP  LABEL::FOR  LABEL::START1
;
; To denote the jump-to point, insert a label before the opcode
;
; '((aconst_null)                       '((aconst_null)
;   (goto LABEL::TARGET)                  (goto 5)
;   (iconst_0)             =====>         (iconst_0)
;   (iconst_2)                            (iconst_2)
;   (LABEL::TARGET ADD)                   (add)
;   (ireturn))                            (ireturn))

(defun isLabel? (sym)
  (and (symbolp sym)
       (equal (symbol-package-name sym) "LABEL")))

(defun isLabeledInst? (inst)
  (isLabel? (car inst)))

(defun gen_label_alist (bytecodes cur_pc label_alist)
  (if (endp bytecodes)
      label_alist
      (let* ((bare_inst (if (isLabeledInst? (car bytecodes))
                            (cdr (car bytecodes))
                            (car bytecodes))))
            (gen_label_alist (cdr bytecodes)
                             (+ cur_pc
                                (inst-length bare_inst))
                             (if (isLabeledInst? (car bytecodes))
                                 (bind (car (car bytecodes))
                                       cur_pc
                                       label_alist)
                                 label_alist)))))

(defun resolve_labels (bytecodes cur_pc label_alist)
  (if (endp bytecodes)
      nil
      (let* ((inst (car bytecodes))
             (bare-inst (if (isLabeledInst? inst)
                            (cdr inst)
                            inst))
             (resolved-inst (if (isLabel? (arg1 bare-inst))
                                (list (op-code bare-inst)
                                      (- (binding (arg1 bare-inst)
                                                  label_alist)
                                         cur_pc))
                                bare-inst)))
            (append (list resolved-inst)
                  (resolve_labels (cdr bytecodes)
                                  (+ cur_pc
                                     (inst-length bare-inst))
                                  label_alist)))))

; resolve_basic_block takes a method and resolves all of the labels
;
; note that the JVM restricts jumps to within the method

(defun resolve_basic_block (bytecodes)
  (resolve_labels bytecodes
                  0
                  (gen_label_alist bytecodes 0 nil)))

; The following functions are used to strip a state down to resolve
;  all of the basic blocks and build up the newly resolved state

; resolving thread tables
;
(defun assemble_frame (frame)
  (make-frame (pc frame)
              (locals frame)
              (stack frame)
              (resolve_basic_block (program frame))
              (sync-flg frame)
              (cur-class frame)))

(defun assemble_call_stack (cs)
  (if (endp cs)
      nil
      (cons (assemble_frame (car cs))
            (assemble_call_stack (cdr cs)))))

(defun assemble_thread (thread)
  (list (assemble_call_stack (car thread))
        (cadr thread)
        (caddr thread)))

(defun assemble_thread_table (tt)
  (if (endp tt)
      nil
      (cons (cons (caar tt)
                  (assemble_thread (cdar tt)))
            (assemble_thread_table (cdr tt)))))

; resolving class tables
;
(defun assemble_method (method)
  (append (list (method-name method)
                (method-formals method)
                (method-sync method))
          (resolve_basic_block (method-program method))))

(defun assemble_methods (methods)
  (if (endp methods)
      nil
      (cons (assemble_method (car methods))
            (assemble_methods (cdr methods)))))

(defun assemble_class (class)
  (make-class-decl (class-decl-name class)
                   (class-decl-superclasses class)
                   (class-decl-fields class)
                   (class-decl-sfields class)
                   (class-decl-cp class)
                   (assemble_methods (class-decl-methods class))
                   (class-decl-heapref class)))

(defun assemble_class_table (ct)
  (if (endp ct)
      nil
      (cons (assemble_class (car ct))
            (assemble_class_table (cdr ct)))))

(defun assemble_state (s)
  (make-state (assemble_thread_table (thread-table s))
              (heap s)
              (assemble_class_table (class-table s))))

; -----------------------------------------------------------------------------
; load_class_library: a utility for populating the heap with Class and
;                     String objects

(defun make-string-obj (class cpentry s idx)
  (let* ((new-object (build-an-instance
                      (cons "java.lang.String"
                            (class-decl-superclasses
                             (bound? "java.lang.String" (class-table s))))
                     (class-table s)))
         (stuffed-obj (set-instance-field "java.lang.String"
                                          "strcontents"
                                          (caddr cpentry)
                                          new-object))
         (new-address (len (heap s))))
        (modify th s
                :heap (bind new-address stuffed-obj (heap s))
                :class-table (update-ct-string-ref
                              class
                              idx
                              (list 'REF new-address)
                              (class-table s)))))


(defun resolve-string-constants (class cp s idx)
  (cond ((endp cp) s)
        ((equal (caar cp) 'STRING)
         (resolve-string-constants class
                                   (cdr cp)
                                   (make-string-obj class (car cp) s idx)
                                   (+ idx 1)))
        (t (resolve-string-constants class (cdr cp) s (+ idx 1)))))


(defun gen_class_obj (class s)
  (let* ((new-state (resolve-string-constants class
                                             (retrieve-cp class (class-table s))
                                             s
                                             0))
         (new-heap (heap new-state))
         (new-ct (class-table new-state))
         (new-object (build-a-class-instance
                      (class-decl-sfields (bound? class new-ct))
                      new-ct))
         (stuffed-obj (set-instance-field "java.lang.Class"
                                          "<name>"
                                          class
                                          new-object))
         (new-address (len new-heap))
         (old-class-ent (bound? class new-ct))
         (new-class-ent
          (make-class-decl (class-decl-name old-class-ent)
                           (class-decl-superclasses old-class-ent)
                           (class-decl-fields old-class-ent)
                           (class-decl-sfields old-class-ent)
                           (class-decl-cp old-class-ent)
                           (class-decl-methods old-class-ent)
                           (list 'REF new-address)))
         (new-class-table (bind class
                                (cdr new-class-ent)
                                new-ct)))
        (make-state (thread-table s)
                    (bind new-address stuffed-obj new-heap)
                    new-class-table)))

(defun ld_class_lib (classes s)
  (if (endp classes)
      s
      (ld_class_lib (cdr classes) (gen_class_obj (car classes) s))))

(defun load_class_library (s)
  (ld_class_lib (strip-cars (class-table s)) s))

; -----------------------------------------------------------------------------
; m5_load: both load and resolve a given state

(defun m5_load (s)
  (load_class_library (assemble_state s)))

