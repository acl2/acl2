; M5.lisp
; J Strother Moore <moore@cs.utexas.edu>
; George Porter <george@cs.utexas.edu>
;
; Fixed arithmetic work by Robert Krug <rkrug@cs.utexas.edu>
; Support for Arrays by Hanbing Liu <hbl@cs.utexas.edu>
; Support for Floating Point by Dmitry Nadezhin <dmitry.nadezhin@gmail.com>
;
; $Id: m5.lisp,v 1.1 2001/07/10 17:37:06 george Exp $

(in-package "M5")
(include-book "rtl/rel11/lib/excps" :dir :system)


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

;; Floating-point command are implemented with a few flaws:
;; 1) float-extended-exponent and double-extended-exponent value sets (JVM spec 2.3.2)
;; are not implemented. So we can trust verification only strictp
;; floating-point methods.
;; 2) JVM spec is a little uncertain about NaN. It says that there is only one
;; NaN value, but programmer can construct and inspect NaN bits by
;; longBitsToDouble and doubleToRawLongBits methods. Hence JVM implementation
;; might be a little different with respect to NaNs. The M5 model chooses some
;; concrete treatment of NaN.

(defconst *mxcsr*
  (rtl::set-flag (rtl::imsk)
   (rtl::set-flag (rtl::dmsk)
    (rtl::set-flag (rtl::zmsk)
     (rtl::set-flag (rtl::omsk)
      (rtl::set-flag (rtl::umsk)
       (rtl::set-flag (rtl::pmsk)
        0)))))))  ; rne

(defun int2fp (x dstf)
  (mv-let (result flags)
          (rtl::sse-round x *mxcsr* dstf)
          (declare (ignore flags))
          result))

(defun fp2fp (x srcf dstf)
  (cond ((rtl::nanp x srcf) (rtl::indef dstf))
        ((rtl::infp x srcf) (rtl::iencode (rtl::sgnf x srcf) dstf))
        ((rtl::zerp x srcf) (rtl::zencode (rtl::sgnf x srcf) dstf))
        (t (mv-let (result flags)
                   (rtl::sse-round (rtl::decode x srcf) *mxcsr* dstf)
                   (declare (ignore flags))
                   result))))

(defun fp2int (x srcf dstw)
  (cond ((rtl::nanp x srcf) 0)
        ((rtl::infp x srcf) (if (= (rtl::sgnf x srcf) 1)
                                (- (expt2 (1- dstw)))
                                (1- (expt2 (1- dstw)))))
        (t (min (max (truncate (rtl::decode x srcf) 1)
                     (- (expt2 (1- dstw))))
                (1- (expt2 (1- dstw)))))))

(defun fpcmp (x y f nan)
  (cond ((or (rtl::nanp x f) (rtl::nanp y f)) nan)
        ((= x y) 0)
        ((rtl::infp x f) (if (= (rtl::sgnf x f) 1) -1 +1))
        ((rtl::infp y f) (if (= (rtl::sgnf y f) 1) +1 -1))
        ((and (rtl::zerp x f) (rtl::zerp y f)) 0)
        ((> (rtl::decode x f) (rtl::decode y f)) +1)
        (t -1)))

(defun fp-binary (op x y f)
  (mv-let (result flags)
          (rtl::sse-binary-spec op x y *mxcsr* f)
          (declare (ignore flags))
          result))

(defun fpadd (x y f)
  (fp-binary 'rtl::add x y f))

(defun fpsub (x y f)
  (fp-binary 'rtl::sub x y f))

(defun fpmul (x y f)
  (fp-binary 'rtl::mul x y f))

(defun fpdiv (x y f)
  (fp-binary 'rtl::div x y f))

(defun fprem (x y f)
  (cond ((or (rtl::nanp x f)
             (rtl::nanp y f)
             (rtl::infp x f)
             (rtl::zerp y f))
         (rtl::indef f))
        ((or (rtl::zerp x f)
             (rtl::infp y f))
         x)
        (t (mv-let (result flags)
                   (rtl::sse-round (- (rtl::decode x f)
                                      (* (truncate (rtl::decode x f)
                                                   (rtl::decode y f))
                                         (rtl::decode y f)))
                                   *mxcsr*
                                   f)
                   (declare (ignore flags))
                   result))))

(defun fpneg (x f)
  (fpsub (rtl::zencode 1 f) x f))

(defun fpsqrt (x f)
  (mv-let (result flags)
          (rtl::sse-sqrt-spec x *mxcsr* f)
          (declare (ignore flags))
          result))

(defun bits2fp (x f)
  (let ((x (u-fix x (+ 1 (rtl::expw f) (rtl::sigw f)))))
       (if (rtl::nanp x f) (rtl::qnanize x f) x)))

; -----------------------------------------------------------------------------
; States

(defun make-state (thread-table heap class-table options)
  (list thread-table heap class-table options))
(defun thread-table (s) (nth 0 s))
(defun heap (s) (nth 1 s))
(defun class-table (s) (nth 2 s))
(defun options (s) (nth 3 s))

(defthm states
  (and (equal (thread-table (make-state tt h c o)) tt)
       (equal (heap (make-state tt h c o)) h)
       (equal (class-table (make-state tt h c o)) c)
       (equal (options (make-state tt h c o)) o)))

(in-theory (disable make-state thread-table heap class-table options))

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

(defconst *java.lang.Object-fake*
  (make-class-decl
    "java/lang/Object"
    '()
    '()
    '()
    '()
    '(("<init>:()V" nil
       (return)))
    '(ref -1)))

(defconst *java.lang.Thread-fake*
  (make-class-decl
    "java/lang/Thread"
    '("java/lang/Object")
    '()
    '()
    '()
    '(("run:()V" nil
       (return))
      ("start:()V" nil
       ())
      ("stop:()V" nil
       ())
      ("<init>:()V" nil
       (aload_0)
       (invokespecial "java/lang/Object" "<init>:()V" 0)
       (return)))
    '(ref -1)))

; Fake java.lang.String with fields like JDK 8
(defconst *java.lang.String-fake8*
  (make-class-decl
    "java/lang/String"
    '("java/lang/Object")
    '("value:[C")
    '()
    '()
    '(("<init>:()V" nil
       (aload_0)
       (invokespecial "java/lang/Object" "<init>:()V" 0)
       (return)))
    '(ref -1)))

; Fake java.lang.String with fields like JDK 9
(defconst *java.lang.String-fake9*
  (make-class-decl
    "java/lang/String"
    '("java/lang/Object")
    '("value:[B" "coder:B")
    '()
    '()
    '(("<init>:()V" nil
       (aload_0)
       (invokespecial "java/lang/Object" "<init>:()V" 0)
       (return)))
    '(ref -1)))

(defconst *java.lang.Class-fake*
  (make-class-decl
    "java/lang/Class"
    '("java/lang/Object")
    '()
    '()
    '()
    '(("<init>:()V" nil
       (aload_0)
       (invokespecial "java/lang/Object" "<init>:()V" 0)
       (return)))
    '(ref -1)))

(defun base-class-def ()
   (list *java.lang.Object-fake*
         *java.lang.Thread-fake*
         *java.lang.String-fake8*
         *java.lang.Class-fake*))

(defconst *default-m5-options*
  'DEFAULT-M5-OPTIONS)

(defund is-big-endian (options)
  (case options
    (UTF16-BIG-ENDIAN 1)
    (UTF16-LITTLE-ENDIAN 0)
    (otherwise 0)))

(defund byte-strings-p (options)
  (case options
    (UTF16-BIG-ENDIAN t)
    (UTF16-LITTLE-ENDIAN t)
    (otherwise nil)))

; -----------------------------------------------------------------------------
; A Constant Pool
;
; There is one constant pool per class

; A constant pool is a list of entries.  Each entry is either:
;
;  '(DOUBLE n)
;       Where n is a 64-bit unsigned number, bit representation of double
;
;  '(FLOAT n)
;       Where n is a 32-bit unsigned number, bit representation of float
;
;  '(INT n)
;       Where n is a 32-bit number, in the range specified by the JVM spec
;
;  '(LONG n)
;       Where n is a 64-bit number, in the range specified by the JVM spec
;
;  '(STRING (REF -1) 72 101 108 108 111 44 32 87 111 114 108 100 33) ; "Hello, World!"
;       Elements from 3rd to the end are UTF16 char codes of a String.
;       They are resolved to a heap reference the first time it is used.
;       Once it is resolved, its reference is placed
;       as the second element (displacing the null ref currently there).

(defun cp-make-double-entry (n)
  (list 'DOUBLE (bits2fp n (rtl::dp))))

(defun cp-make-float-entry (n)
  (list 'FLOAT (bits2fp n (rtl::sp))))

(defun cp-make-int-entry (n)
  (list 'INT (int-fix n)))

(defun cp-make-long-entry (n)
  (list 'LONG (long-fix n)))

(defun cp-make-string-entry (chars)
  (list* 'STRING '(REF -1) chars))

(defun cp-string-resolved? (entry)
  (not (equal (cadr (caddr entry)) -1)))

(defun retrieve-cp (class-name class-table)
  (class-decl-cp (bound? class-name class-table)))

(defun update-ct-string-ref (class idx newval ct)
  (let* ((class-entry (bound? class ct))
         (oldstrval (cddr (nth idx (retrieve-cp class ct))))
         (newstrentry (list* 'STRING newval oldstrval))
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
       (or (in-list "java/lang/Thread" supers)
           (in-list "java/lang/ThreadGroup" supers))))

; ----------------------------------------------------------------------------
; Helper functions for locking and unlocking objects

; lock-object and unlock-object will obtain a lock on an instance
;  of an object, using th as the locking id (a thread owns a lock).  If th
;  already has a lock on an object, then the <mcount> of the object is
;  incremented.  Likewise if you unlock an object with <mcount> > 0, then
;  the lock will be decremented.  Note:  you must make sure that th can
;  and should get the lock, since this function will blindly go ahead and
;  get the lock

(defun lock-object (th obj-ref heap)
  (let* ((obj-ref-num (cadr obj-ref))
         (instance (binding (cadr obj-ref) heap))
         (obj-fields (binding "java/lang/Object" instance))
         (new-mcount (+ 1 (binding "<mcount>" obj-fields)))
         (new-obj-fields
            (bind "<monitor>" th
               (bind "<mcount>" new-mcount obj-fields)))
         (new-object (bind "java/lang/Object" new-obj-fields instance)))
     (bind obj-ref-num new-object heap)))

(defun unlock-object (th obj-ref heap)
  (let* ((obj-ref-num (cadr obj-ref))
         (instance (binding (cadr obj-ref) heap))
         (obj-fields (binding "java/lang/Object" instance))
         (old-mcount (binding "<mcount>" obj-fields))
         (new-mcount (ACL2::max 0 (- old-mcount 1)))
         (new-monitor (if (zp new-mcount)
                          0
                          th))
         (new-obj-fields
            (bind "<monitor>" new-monitor
               (bind "<mcount>" new-mcount obj-fields)))
         (new-object (bind "java/lang/Object" new-obj-fields instance)))
     (bind obj-ref-num new-object heap)))

; objectLockable? is used to determine if th can unlock instance.  This
;  occurs when either <mcount> is zero (nobody has a lock), or <mcount> is
;  greater than zero, but <monitor> is equal to th.  This means that th
;  already has a lock on the object, and when the object is locked yet again,
;  <monitor> will remain the same, but <mcount> will be incremented.
;
; objectUnLockable? determins if a thread can unlock an object (ie if it
;  has a lock on that object)
(defun objectLockable? (instance th)
  (let* ((obj-fields (binding "java/lang/Object" instance))
         (monitor (binding "<monitor>" obj-fields))
         (mcount (binding "<mcount>" obj-fields)))
    (and instance
         (or (zp mcount)
             (equal monitor th)))))

(defun objectUnLockable? (instance th)
  (let* ((obj-fields (binding "java/lang/Object" instance))
         (monitor (binding "<monitor>" obj-fields)))
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
; The class in which the current method is defined is the current class (See JLS 2.6).
(defun cur-class (frame) (nth 5 frame))

(defthm frames
  (and
   (equal (pc (make-frame pc l s prog sync-flg cur-class)) pc)
   (equal (locals (make-frame pc l s prog sync-flg cur-class)) l)
   (equal (stack (make-frame pc l s prog sync-flg cur-class)) s)
   (equal (program (make-frame pc l s prog sync-flg cur-class)) prog)
   (equal (sync-flg (make-frame pc l s prog sync-flg cur-class)) sync-flg)
   (equal (cur-class (make-frame pc l s prog sync-flg cur-class)) cur-class)))

(in-theory
 (disable make-frame pc locals stack program sync-flg cur-class))

; -----------------------------------------------------------------------------
; Method Declarations

; The methods component of a class declaration is a list of method definitions.
; A method definition is a list of the form

; (name-and-type formals sync-status . program)

; We never build these declarations but just enter list constants for them,

; Note the similarity to our old notion of a program definition.  We
; will use strings to name methods now.

; sync-status is 't' if the method is synchronized, 'nil' if not

; Method definitions will be constructed by expressions such as:
; (Note:  all of the symbols below are understood to be in the pkg "JVM".)

; ("move:(II)I" nil
;   (iload this)
;   (iload this)
;   (getfield "Point" "x:I")
;   (iload dx)
;   (iadd)
;   (putfield "Point" "x:I")    ; this.x = this.x + dx;
;   (iload :this)
;   (iload :this)
;   (getfield "Point" "y:I")
;   (iload dy)
;   (add)
;   (putfield "Point" "y:I")    ; this.y = this.y + dy;
;   (push 1)
;   (ireturn)))               ; return 1;

; Provided this method is defined in the class "Point" it can be invoked by

;   (invokevirtual "Point" "move:(II)I" 2)

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

(defun method-name-and-type (m)
  (nth 0 m))
(defun method-sync (m)
  (nth 1 m))
(defun method-program (m)
  (cddr m))
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
          (list 'class-table s))
        (if (suppliedp :options args)
            (actual :options args)
          (list 'options s))))

; -----------------------------------------------------------------------------
; Helper functions related to building instances of objects

(defun deref (ref heap)
  (binding (cadr ref) heap))

(defun field-value (class-name field-name-and-type instance)
  (binding field-name-and-type
           (binding class-name instance)))

(defund field-initial-value (field-name-and-type)
  (if (or (search ":L" field-name-and-type)  ; object instance
          (search ":[" field-name-and-type)) ; array instance
      '(REF -1)
    0))

(defund field-long-or-double (field-name-and-type)
  (or (search ":J" field-name-and-type)
      (search ":D" field-name-and-type)))

(defun build-class-field-bindings (fields)
  (if (endp fields)
      nil
    (cons (cons (car fields) (field-initial-value (car fields)))
          (build-class-field-bindings (cdr fields)))))

(defun build-class-object-field-bindings ()
  '(("<monitor>" . 0) ("<mcount>" . 0)))

(defun build-immediate-instance-data (class-name class-table)
  (cons class-name
      (if (equal class-name "java/lang/Object")
          (build-class-object-field-bindings)
          (build-class-field-bindings
           (class-decl-fields
            (bound? class-name class-table))))))

(defun build-an-instance (class-names class-table)
  (if (endp class-names)
      nil
    (cons (build-immediate-instance-data (car class-names) class-table)
          (build-an-instance (cdr class-names) class-table))))

(defun build-class-data (sfields)
  (cons "java/lang/Class"
        (build-class-field-bindings
         (cons "<name>" sfields))))

(defun build-a-class-instance (sfields class-table)
    (list (build-class-data sfields)
          (build-immediate-instance-data "java/lang/Object" class-table)))


; -----------------------------------------------------------------------------
; Arrays

;(defun value-of (obj)
;  (cdr obj))

;(defun superclasses-of (class ct)
;  (class-decl-superclasses (bound? class ct)))

;(defun array-content (array)
;  (value-of (field-value "ARRAY" "<array>" array)))

(defun array-type (array)
  (car (nth 0 array)))
;  (nth 0 (array-content array)))

(defun array-bound (array)
  (nth 1 array))
;  (nth 1 (array-content array)))

(defun array-data (array)
  (nth 2 array))
;  (nth 2 (array-content array)))

(defun element-at (index array)
  (nth index (array-data array)))

(defun makearray (type bound data class-table)
  (declare (ignore class-table))
  (list (list type) bound data))
;  (cons (list "ARRAY"
;              (cons "<array>" (cons '*array* (list type bound data))))
;        (build-an-instance
;         (superclasses-of "ARRAY" class-table)
;         class-table)))

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

(defun atype-to-type (atype-num)
  (cond ((equal atype-num 4) "[Z")
        ((equal atype-num 5) "[C")
        ((equal atype-num 6) "[F")
        ((equal atype-num 7) "[D")
        ((equal atype-num 8) "[B")
        ((equal atype-num 9) "[S")
        ((equal atype-num 10) "[I")
        ((equal atype-num 11) "[J")
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

; "[C" -> "[[C"
(defund array-type-of (element-type)
  (concatenate 'string "[" element-type))

; "[[C" -> "[C"
(defund element-type (array-type)
  (subseq array-type 1 (length array-type)))

(defund array-initial-value (array-type)
  (case (char array-type 1)
    (#\[ '(ref -1))
    (#\L '(ref -1))
    (otherwise 0)))

(defun init-array (initial-value count)
  (if (zp count)
      nil
      (cons initial-value (init-array initial-value (- count 1)))))

; The following measure is due to J
(defun natural-sum (lst)
  (cond ((endp lst) 0)
        (t (+ (nfix (car lst)) (natural-sum (cdr lst))))))

(include-book "ordinals/lexicographic-ordering" :dir :system)

(mutual-recursion

  ; makemultiarray2 :: num, counts, s, ac --> [refs]
  (defun makemultiarray2 (type car-counts cdr-counts s ac)
    (declare (xargs :measure (acl2::llist
                              (len (cons car-counts cdr-counts))
                              (natural-sum (cons car-counts cdr-counts)))
                    :well-founded-relation acl2::l<))
    (if (zp car-counts)
        (mv (heap s) ac)
        (mv-let (new-addr new-heap)
                (makemultiarray type cdr-counts s)
                (makemultiarray2 type
                                 (- car-counts 1)
                                 cdr-counts
                                 (make-state (thread-table s)
                                             new-heap
                                             (class-table s)
                                             (options s))
                                 (cons (list 'REF new-addr) ac)))))

  ; makemultiarray :: [counts], s --> addr, new-heap
  (defun makemultiarray (type counts s)
    (declare (xargs :measure (acl2::llist (+ 1 (len counts))
                                          (natural-sum counts))
                    :well-founded-relation acl2::l<))
    (if (<= (len counts) 1)

        ; "Base case"  Handles initializing the final dimension
        (mv (len (heap s))
            (bind (len (heap s))
                  (makearray type
                             (car counts)
                             (init-array (array-initial-value type)
                                         (car counts))
                             (class-table s))
                  (heap s)))

        ; "Recursive Case"
        (mv-let (heap-prime lst-of-refs)
                (makemultiarray2 (element-type type)
                                 (car counts)
                                 (cdr counts)
                                 s
                                 nil)
                (let* ((obj (makearray type
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
    (CHECKCAST          3)
    (D2F                1)
    (D2I                1)
    (D2L                1)
    (DADD               1)
    (DALOAD             1)
    (DASTORE            1)
    (DCMPG              1)
    (DCMPL              1)
    (DCONST_0           1)
    (DCONST_1           1)
    (DDIV               1)
    (DLOAD              2)
    (DLOAD_0            1)
    (DLOAD_1            1)
    (DLOAD_2            1)
    (DLOAD_3            1)
    (DMUL               1)
    (DNEG               1)
    (DREM               1)
    (DRETURN            1)
    (DSTORE             2)
    (DSTORE_0           1)
    (DSTORE_1           1)
    (DSTORE_2           1)
    (DSTORE_3           1)
    (DSUB               1)
    (DUP                        1)
    (DUP_X1             1)
    (DUP_X2             1)
    (DUP2               1)
    (DUP2_X1            1)
    (DUP2_X2            1)
    (F2D                1)
    (F2I                1)
    (F2L                1)
    (FADD               1)
    (FALOAD             1)
    (FAND               1)
    (FASTORE            1)
    (FCMPL              1)
    (FCMPG              1)
    (FCONST_0           1)
    (FCONST_1           1)
    (FCONST_2           1)
    (FDIV               1)
    (FLOAD              2)
    (FLOAD_0            1)
    (FLOAD_1            1)
    (FLOAD_2            1)
    (FLOAD_3            1)
    (FMUL               1)
    (FNEG               1)
    (FREM               1)
    (FRETURN            1)
    (FSTORE             2)
    (FSTORE_0           1)
    (FSTORE_1           1)
    (FSTORE_2           1)
    (FSTORE_3           1)
    (FSUB               1)
    (GETFIELD           3)
    (GETSTATIC          3)
    (GOTO                       3)
    (GOTO_W             5)
    (I2B                        1)
    (I2C                        1)
    (I2D                        1)
    (I2F                        1)
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
    (L2D                        1)
    (L2F                        1)
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

; -----------------------------------------------------------------------------
; Instruction helpers

(defun set-instance-field (class-name field-name-and-type value instance)
  (bind class-name
        (bind field-name-and-type value
              (binding class-name instance))
        instance))

(defun bind-formals (n stack)
  (if (zp n)
      nil
    (cons (top stack)
          (bind-formals (- n 1) (pop stack)))))

; Retirns a cons pair (class . method) if method is found or nil otherwise
(defun lookup-methodref-in-superclasses (name-and-type classes class-table)
  (cond ((endp classes) nil)
        (t (let* ((class-name (car classes))
                  (class-decl (bound? class-name class-table))
                  (method (bound? name-and-type (class-decl-methods class-decl))))
             (if method
                 (cons class-name method)
                (lookup-methodref-in-superclasses name-and-type (cdr classes)
                                                 class-table))))))

(defun lookup-methodref (name-and-type class-name class-table)
  (lookup-methodref-in-superclasses name-and-type
                                    (cons class-name
                                          (class-decl-superclasses
                                           (bound? class-name class-table)))
                                    class-table))

(defun lookup-method (name-and-type class-name class-table)
  (cdr (lookup-methodref name-and-type class-name class-table)))

(defun invoke-instance-method (nformals class-name method-name-and-type method-decl
          inst-length th s)
  (let* ((obj-ref (top (popn nformals (stack (top-frame th s)))))
         (instance (deref obj-ref (heap s)))
         (prog (method-program method-decl))
         (s1 (modify th s
                     :pc (+ inst-length (pc (top-frame th s)))
                     :stack (popn (+ nformals 1)
                                  (stack (top-frame th s)))))
         (tThread (rrefToThread obj-ref (thread-table s))))
    (cond
     ((method-isNative? method-decl)
      (cond ((and (equal class-name "java/lang/Thread")
                  (equal method-name-and-type "start:()V")
                  tThread)
             (modify tThread s1 :status 'SCHEDULED))
            ((and (equal class-name "java/lang/Thread")
                  (equal method-name-and-type "stop:()V")
                  tThread)
             (modify tThread s1
                     :status 'UNSCHEDULED))
            (t s)))
     ((and (method-sync method-decl)
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
                                class-name)
                    (call-stack th s1))
              :heap (lock-object th obj-ref (heap s))))
     ((method-sync method-decl)
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
                                class-name)
                    (call-stack th s1)))))))

(defun return-stk (ret-stack th s)
  (let* ((cs (call-stack th s))
         (top-frame (top cs))
         (ret-frame (top (pop cs)))
         (obj-ref (nth 0 (locals top-frame)))
         (sync-status (sync-flg top-frame))
         (class (cur-class top-frame))
         (ret-ref (class-decl-heapref (bound? class (class-table s))))
         (new-heap (cond ((and (equal sync-status 'LOCKED)
                               (deref obj-ref (heap s)))
                          (unlock-object th obj-ref (heap s)))
                         ((and (equal sync-status 'S_LOCKED)
                               (deref ret-ref (heap s)))
                          (unlock-object th ret-ref (heap s)))
                         (t (heap s)))))
    (modify th s
            :call-stack (push (make-frame
                                (pc ret-frame)
                                (locals ret-frame)
                                ret-stack
                                (program ret-frame)
                                (sync-flg ret-frame)
                                (cur-class ret-frame))
                               (pop (pop cs)))
            :heap new-heap)))

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
         (arrayref (top (pop (pop (stack (top-frame th s))))))
         (array (deref arrayref (heap s))))
    (if array
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (pop (pop (pop (stack (top-frame th s)))))
                :heap (bind (cadr arrayref)
                            (set-element-at value index array (class-table s))
                            (heap s)))
       s)))

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
  (let* ((type (arg1 inst))
         (count (top (stack (top-frame th s))))
         (addr (len (heap s)))
         (obj (makearray (array-type-of type)
                         count
                         (init-array '(ref -1) count)
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
  (let* ((cs (call-stack th s))
         (val (top (stack (top cs)))))
    (return-stk (push val (stack (top (pop cs)))) th s)))

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
                             "[Z") ; boolean[]
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
         (array (deref arrayref (heap s)))
         (element (if (equal (array-type (deref arrayref (heap s)))
                             "[B") ; byte[]
                      (byte-fix value)
                      (u-fix value 1))))
    (if array
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (pop (pop (pop (stack (top-frame th s)))))
                :heap (bind (cadr arrayref)
                            (set-element-at element index array (class-table s))
                            (heap s)))
        s)))

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
         (arrayref (top (pop (pop (stack (top-frame th s))))))
         (array (deref arrayref (heap s))))
    (if array
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (pop (pop (pop (stack (top-frame th s)))))
                :heap (bind (cadr arrayref)
                            (set-element-at (char-fix value) index array (class-table s))
                            (heap s)))
        s)))

; -----------------------------------------------------------------------------
; (CHECKCAST) Instruction - check whether object is of given type
; No operation in M5 model.

(defun execute-CHECKCAST (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))))

; -----------------------------------------------------------------------------
; (D2F) Instruction - convert double to float

(defun execute-D2F (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (fp2fp (top (pop (stack (top-frame th s))))
                              (rtl::dp)
                              (rtl::sp))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (D2I) Instruction - convert double to int

(defun execute-D2I (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (fp2int (top (pop (stack (top-frame th s))))
                               (rtl::dp)
                               32)
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (D2L) Instruction - convert double to long

(defun execute-D2L (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (fp2int (top (pop (stack (top-frame th s))))
                                     (rtl::dp)
                                     64)
                             (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (DADD) Instruction - add double

(defun execute-DADD (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push
                         (fpadd (top (popn 3 (stack (top-frame th s))))
                                (top (pop (stack (top-frame th s))))
                                (rtl::dp))
                         (popn 4 (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (DALOAD) Instruction - load double from array

(defun execute-DALOAD (inst th s)
  (let* ((index (top (stack (top-frame th s))))
         (arrayref (top (pop (stack (top-frame th s)))))
         (array (deref arrayref (heap s))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push 0
                             (push (element-at index array)
                                   (pop (pop (stack (top-frame th s)))))))))

; -----------------------------------------------------------------------------
; (DASTORE) Instruction - store into double array

(defun execute-DASTORE (inst th s)
  (let* ((value (top (pop (stack (top-frame th s)))))
         (index (top (pop (pop (stack (top-frame th s))))))
         (arrayref (top (popn 3 (stack (top-frame th s)))))
         (array (deref arrayref (heap s))))
    (if array
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (popn 4 (stack (top-frame th s)))
                :heap (bind (cadr arrayref)
                            (set-element-at value index array (class-table s))
                            (heap s)))
        s)))

; -----------------------------------------------------------------------------
; (DCMPG) Instruction - compare double

(defun execute-DCMPG (inst th s)
  (let* ((val2 (top (pop (stack (top-frame th s)))))
         (val1 (top (popn 3 (stack (top-frame th s)))))
         (result (fpcmp val1 val2 (rtl::dp) +1)))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push result
                             (popn 4 (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (DCMPL) Instruction - compare double

(defun execute-DCMPL (inst th s)
  (let* ((val2 (top (pop (stack (top-frame th s)))))
         (val1 (top (popn 3 (stack (top-frame th s)))))
         (result (fpcmp val1 val2 (rtl::dp) -1)))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push result
                             (popn 4 (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (DCONST_0) Instruction - push double 0.0

(defun execute-DCONST_0 (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push #x0000000000000000 (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (DCONST_1) Instruction - push double 1.0

(defun execute-DCONST_1 (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push #x3ff0000000000000 (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (DDIV) Instruction - divide double

(defun execute-DDIV (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push
                         (fpdiv (top (popn 3 (stack (top-frame th s))))
                                (top (pop (stack (top-frame th s))))
                                (rtl::dp))
                         (popn 4 (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (DLOAD idx) Instruction - load double from local variable

(defun execute-DLOAD (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (nth (arg1 inst)
                                  (locals (top-frame th s)))
                             (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (DLOAD_X) Instruction - load double from local variable
;                         covers DLOAD_{0, 1, 2, 3}

(defun execute-DLOAD_X (inst th s n)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (nth n (locals (top-frame th s)))
                             (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (DMUL) Instruction - multiply double

(defun execute-DMUL (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (fpmul (top (popn 3 (stack (top-frame th s))))
                                    (top (pop (stack (top-frame th s))))
                                    (rtl::dp))
                             (popn 4 (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (DNEG) Instruction - negate double

(defun execute-DNEG (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (fpneg (top (pop (stack (top-frame th s)))) (rtl::dp))
                             (popn 2 (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (DREM) Instruction - remainder double

(defun execute-DREM (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (fprem (top (popn 3 (stack (top-frame th s))))
                                    (top (pop (stack (top-frame th s))))
                                    (rtl::dp))
                             (popn 4 (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (DRETURN) Instruction - return double from method

(defun execute-DRETURN (inst th s)
  (declare (ignore inst))
  (let* ((cs (call-stack th s))
         (val (top (pop (stack (top cs))))))
    (return-stk (push 0 (push val (stack (top (pop cs))))) th s)))

; -----------------------------------------------------------------------------
; (DSTORE idx) Instruction - store double into local variable

(defun execute-DSTORE (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :locals (update-nth (arg1 inst)
                               (top (pop (stack (top-frame th s))))
                               (locals (top-frame th s)))
          :stack (popn 2 (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (DSTORE_X) Instruction - store double long into local variable
;                          covers DSTORE_{0, 1, 2, 3}

(defun execute-DSTORE_X (inst th s n)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :locals (update-nth n
                               (top (pop (stack (top-frame th s))))
                               (locals (top-frame th s)))
          :stack (popn 2 (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (DSUB) Instruction

(defun execute-DSUB (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (fpsub (top (popn 3 (stack (top-frame th s))))
                                    (top (pop (stack (top-frame th s))))
                                    (rtl::dp))
                             (popn 4 (stack (top-frame th s)))))))

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
; (F2D) Instruction - convert float to double

(defun execute-F2D (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (fp2fp (top (stack (top-frame th s)))
                                    (rtl::sp)
                                    (rtl::dp))
                             (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (F2I) Instruction - convert float to long

(defun execute-F2I (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (fp2int (top (stack (top-frame th s)))
                               (rtl::sp)
                               32)
                       (pop (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (F2L) Instruction - convert float to long

(defun execute-F2L (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (fp2int (top (stack (top-frame th s)))
                                     (rtl::sp)
                                     64)
                             (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (FADD) Instruction - add float

(defun execute-FADD (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (fpadd (top (pop (stack (top-frame th s))))
                              (top (stack (top-frame th s)))
                              (rtl::sp))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (FALOAD) Instruction - load float from array

(defun execute-FALOAD (inst th s)
  (let* ((index (top (stack (top-frame th s))))
         (arrayref (top (pop (stack (top-frame th s)))))
         (array (deref arrayref (heap s))))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push (element-at index array)
                             (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (FASTORE) Instruction - store into float array

(defun execute-FASTORE (inst th s)
  (let* ((value (top (stack (top-frame th s))))
         (index (top (pop (stack (top-frame th s)))))
         (arrayref (top (pop (pop (stack (top-frame th s))))))
         (array (deref arrayref (heap s))))
    (if array
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (pop (pop (pop (stack (top-frame th s)))))
                :heap (bind (cadr arrayref)
                            (set-element-at value index array (class-table s))
                            (heap s)))
        s)))

; -----------------------------------------------------------------------------
; (FCMPG) Instruction - compare float

(defun execute-FCMPG (inst th s)
  (let* ((val2 (top (stack (top-frame th s))))
         (val1 (top (pop (stack (top-frame th s)))))
         (result (fpcmp val1 val2 (rtl::dp) +1)))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push result
                             (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (FCMPL) Instruction - compare float

(defun execute-FCMPL (inst th s)
  (let* ((val2 (top (stack (top-frame th s))))
         (val1 (top (pop (stack (top-frame th s)))))
         (result (fpcmp val1 val2 (rtl::dp) -1)))
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (push result
                             (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (FCONST_0) Instruction - push float 0.0

(defun execute-FCONST_0 (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push #x00000000 (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (FCONST_1) Instruction - push float 1.0

(defun execute-FCONST_1 (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push #x3f800000 (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (FCONST_2) Instruction - push float 2.0

(defun execute-FCONST_2 (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push #x40000000 (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (FDIV) Instruction - divide float

(defun execute-FDIV (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (fpdiv (top (pop (stack (top-frame th s))))
                              (top (stack (top-frame th s)))
                              (rtl::sp))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (FLOAD idx) Instruction - load float from local variable

(defun execute-FLOAD (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (nth (arg1 inst)
                            (locals (top-frame th s)))
                       (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (FLOAD_X) Instruction - load float from local variable
;                         covers FLOAD_{0, 1, 2, 3}

(defun execute-FLOAD_X (inst th s n)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (nth n (locals (top-frame th s)))
                       (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (FMUL) Instruction - multiply float

(defun execute-FMUL (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (fpmul (top (pop (stack (top-frame th s))))
                              (top (stack (top-frame th s)))
                              (rtl::sp))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (FNEG) Instruction - negate float

(defun execute-FNEG (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (fpneg (top (stack (top-frame th s)))
                              (rtl::sp))
                       (pop (stack (top-frame th s))))))

; -----------------------------------------------------------------------------
; (FREM) Instruction - remainder float

(defun execute-FREM (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (fprem (top (pop (stack (top-frame th s))))
                              (top (stack (top-frame th s)))
                              (rtl::sp))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (FRETURN) Instruction - return float from method

(defun execute-FRETURN (inst th s)
  (declare (ignore inst))
  (let* ((cs (call-stack th s))
         (val (top (stack (top cs)))))
    (return-stk (push val (stack (top (pop cs)))) th s)))

; -----------------------------------------------------------------------------
; (FSTORE idx) Instruction - store float into local variable

(defun execute-FSTORE (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :locals (update-nth (arg1 inst)
                               (top (stack (top-frame th s)))
                               (locals (top-frame th s)))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (FSTORE_X) Instruction - store float into local variable
;                          covers FSTORE_{0, 1, 2, 3}

(defun execute-FSTORE_X (inst th s n)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :locals (update-nth n
                               (top (stack (top-frame th s)))
                               (locals (top-frame th s)))
          :stack (pop (stack (top-frame th s)))))

; -----------------------------------------------------------------------------
; (FSUB) Instruction - subtract float

(defun execute-FSUB (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (fpsub (top (pop (stack (top-frame th s))))
                              (top (stack (top-frame th s)))
                              (rtl::sp))
                       (pop (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (GETFIELD "class" "field" ?long-flag?) Instruction

(defun execute-GETFIELD (inst th s)
  (let* ((class-name (arg1 inst))
         (field-name-and-type (arg2 inst))
         (long-flag  (or (arg3 inst) (field-long-or-double field-name-and-type)))
         (instance (deref (top (stack (top-frame th s))) (heap s)))
         (field-value (field-value class-name field-name-and-type instance)))
    (modify th s
            :pc (+ (inst-length inst) (pc (top-frame th s)))
            :stack (if long-flag
                       (push 0 (push field-value
                                     (pop (stack (top-frame th s)))))
                       (push field-value
                             (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (GETSTATIC "class" "field" ?long-flag?) Instruction

(defun static-field-value (class-name field-name-and-type s)
  (let* ((class-ref (class-decl-heapref
                     (bound? class-name (class-table s))))
         (instance (deref class-ref (heap s))))
    (field-value "java/lang/Class" field-name-and-type instance)))

(defun execute-GETSTATIC (inst th s)
  (let* ((class-name (arg1 inst))
         (field-name-and-type (arg2 inst))
         (long-flag (or (arg3 inst) (field-long-or-double field-name-and-type)))
         (class-ref (class-decl-heapref
                     (bound? class-name (class-table s))))
         (instance (deref class-ref (heap s)))
         (field-value (field-value "java/lang/Class" field-name-and-type instance)))
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
; (I2D) Instruction - int to double conversion

(defun execute-I2D (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (int2fp (top (stack (top-frame th s)))
                                     (rtl::dp))
                             (pop (stack (top-frame th s)))))))

; -----------------------------------------------------------------------------
; (I2F) Instruction - int to float conversion

(defun execute-I2F (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (int2fp (top (stack (top-frame th s)))
                               (rtl::sp))
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
         (arrayref (top (pop (pop (stack (top-frame th s))))))
         (array (deref arrayref (heap s))))
    (if array
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (pop (pop (pop (stack (top-frame th s)))))
                :heap (bind (cadr arrayref)
                            (set-element-at value index array (class-table s))
                            (heap s)))
        s)))

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
  (let* ((cs (call-stack th s))
         (val (top (stack (top cs)))))
    (return-stk (push val (stack (top (pop cs)))) th s)))

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

(defun iushr (val1 shft)
  (if (< val1 0)
      (+ (shr val1 shft) (shl 1 (- 32 shft)))
    (shr val1 shft)))

(defun execute-IUSHR (inst th s)
  (let* ((val1 (top (pop (stack (top-frame th s)))))
         (val2 (top (stack (top-frame th s))))
         (shiftval (5-bit-fix val2))
         (result (iushr val1 shiftval)))
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

(defun execute-INVOKESPECIAL (inst th s)
  (let* ((method-name-and-type (arg2 inst))
         (nformals (arg3 inst))
         (class-name (arg1 inst))
         (class-decl (bound? class-name (class-table s)))
         (method (bound? method-name-and-type (class-decl-methods class-decl))))
        (invoke-instance-method nformals
                                class-name
                                method-name-and-type
                                method
                                (inst-length inst)
                                th
                                s)))

; -----------------------------------------------------------------------------
; (INVOKESTATIC "class" "name" n) Instruction

(defun execute-INVOKESTATIC (inst th s)
  (let* ((class (arg1 inst))
         (method-name-and-type (arg2 inst))
         (nformals (arg3 inst))
         (class-decl (bound? class (class-table s)))
         (class-ref (class-decl-heapref class-decl))
         (class-instance (deref class-ref (heap s)))
         (method-decl (bound? method-name-and-type (class-decl-methods class-decl)))
         (prog (method-program method-decl))
         (s1 (modify th s
                     :pc (+ (inst-length inst) (pc (top-frame th s)))
                     :stack (popn nformals (stack (top-frame th s))))))
    (cond
     ((method-isNative? method-decl)
      (cond ((and (equal class "java/lang/Double")
                  (equal method-name-and-type "doubleToRawLongBits:(D)J"))
             (modify th s1
                     :stack (push (long-fix (top (stack (top-frame th s))))
                                  (stack (top-frame th s1)))))
            ((and (equal class "java/lang/Float")
                  (equal method-name-and-type "floatToRawIntBits:(F)I"))
             (modify th s1
                     :stack (push (int-fix (top (stack (top-frame th s))))
                                  (stack (top-frame th s1)))))
            ((and (equal class "java/lang/Float")
                  (equal method-name-and-type "intBitsToFloat:(I)F"))
             (modify th s1
                     :stack (push (bits2fp (top (stack (top-frame th s)))
                                           (rtl::sp))
                                  (stack (top-frame th s1)))))
            ((and (equal class "java/lang/Double")
                  (equal method-name-and-type "longBitsToDouble:(J)D"))
             (modify th s1
                     :stack (push (bits2fp (top (stack (top-frame th s)))
                                           (rtl::dp))
                                  (stack (top-frame th s1)))))
            ((and (equal class "java/lang/StrictMath")
                  (equal method-name-and-type "sqrt:(D)D"))
             (modify th s1
                     :stack (push (fpsqrt (top (stack (top-frame th s)))
                                           (rtl::dp))
                                  (stack (top-frame th s1)))))
            ((and (equal class "java/lang/StringUTF16")
                  (equal method-name-and-type "isBigEndian()Z"))
             (modify th s1
                     :stack (push (is-big-endian (options s))
                                  (stack (top-frame th s1)))))
            (t s)))
     ((and (method-sync method-decl)
           (objectLockable? class-instance th))
      (modify th s1
              :call-stack
              (push (make-frame 0
                                (reverse
                                 (bind-formals nformals
                                               (stack (top-frame th s))))
                                nil
                                prog
                                'S_LOCKED
                                class)
                    (call-stack th s1))
              :heap (lock-object th class-ref (heap s))))
     ((method-sync method-decl)
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
                                class)
                    (call-stack th s1)))))))

; -----------------------------------------------------------------------------
; (INVOKEVIRTUAL "class" "name" n) Instruction

(defun class-name-of-ref (ref heap)
  (car (car (deref ref heap))))

(defun execute-INVOKEVIRTUAL (inst th s)
  (let* ((method-name-and-type (arg2 inst))
         (nformals (arg3 inst))
         (obj-ref (top (popn nformals (stack (top-frame th s)))))
         (obj-class-name (class-name-of-ref obj-ref (heap s)))
         (closest-methodref
          (lookup-methodref method-name-and-type
                            obj-class-name
                            (class-table s)))
         (closest-class (car closest-methodref))
         (closest-method (cdr closest-methodref)))
        (invoke-instance-method nformals
                                closest-class
                                method-name-and-type
                                closest-method
                                (inst-length inst)
                                th
                                s)))

; -----------------------------------------------------------------------------
; (L2D) Instruction - long to double conversion

(defun execute-L2D (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push 0
                       (push (int2fp (top (pop (stack (top-frame th s))))
                                     (rtl::dp))
                             (pop (pop (stack (top-frame th s))))))))

; -----------------------------------------------------------------------------
; (L2F) Instruction - long to float narrowing conversion

(defun execute-L2F (inst th s)
  (modify th s
          :pc (+ (inst-length inst) (pc (top-frame th s)))
          :stack (push (int2fp (top (pop (stack (top-frame th s))))
                               (rtl::sp))
                       (pop (pop (stack (top-frame th s)))))))

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
         (arrayref (top (popn 3 (stack (top-frame th s)))))
         (array (deref arrayref (heap s))))
    (if array
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (popn 4 (stack (top-frame th s)))
                :heap (bind (cadr arrayref)
                            (set-element-at value index array (class-table s))
                            (heap s)))
        s)))

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
  (let* ((val1 (top (popn 3 (stack (top-frame th s)))))
         (val2 (top (pop (stack (top-frame th s)))))
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
  (let* ((cs (call-stack th s))
         (val (top (pop (stack (top cs))))))
    (return-stk (push 0 (push val (stack (top (pop cs))))) th s)))

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

(defun lushr (val1 shft)
  (if (< val1 0)
      (+ (shr val1 shft) (shl 1 (- 64 shft)))
    (shr val1 shft)))

(defun execute-LUSHR (inst th s)
  (let* ((val1 (top (popn 2 (stack (top-frame th s)))))
         (val2 (top (stack (top-frame th s))))
         (shiftval (6-bit-fix val2))
         (result (lushr val1 shiftval)))
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
  (let* ((type (arg1 inst))
         (dimentions (arg2 inst))
         (counts (reverse (take dimentions (stack (top-frame th s))))))
        (mv-let (addr new-heap)
                (makemultiarray type counts s)
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
         (closest-methodref (lookup-methodref "run:()V" class-name class-table))
         (closest-class (car closest-methodref))
         (closest-method (cdr closest-methodref))
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
                              closest-class)
                  nil)
                 'UNSCHEDULED
                 (list 'REF new-address)
                 (thread-table s1)))
      s1)))

; -----------------------------------------------------------------------------
; (NEWARRAY) Instruction

(defun execute-NEWARRAY (inst th s)
  (let* ((atype (arg1 inst))
         (count (top (stack (top-frame th s))))
         (addr (len (heap s)))
         (obj (makearray (atype-to-type atype)
                         count
                         (init-array 0 count)
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
         (field-name-and-type (arg2 inst))
         (long-flag (or (arg3 inst) (field-long-or-double field-name-and-type)))
         (value (if long-flag
                    (top (pop (stack (top-frame th s))))
                    (top (stack (top-frame th s)))))
         (instance (if long-flag
                       (deref (top (popn 2 (stack (top-frame th s)))) (heap s))
                       (deref (top (pop (stack (top-frame th s)))) (heap s))))
         (address (cadr (if long-flag
                            (top (popn 2 (stack (top-frame th s))))
                            (top (pop (stack (top-frame th s))))))))
    (if instance
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (if long-flag
                           (popn 3 (stack (top-frame th s)))
                           (pop (pop (stack (top-frame th s)))))
                :heap (bind address
                            (set-instance-field class-name
                                                field-name-and-type
                                                value
                                                instance)
                            (heap s)))
        s)))

; -----------------------------------------------------------------------------
; (PUTSTATIC "class" "field" ?long-flag?) Instruction

(defun execute-PUTSTATIC (inst th s)
  (let* ((class-name (arg1 inst))
         (field-name-and-type (arg2 inst))
         (long-flag (or (arg3 inst) (field-long-or-double field-name-and-type)))
         (class-ref (class-decl-heapref
                     (bound? class-name (class-table s))))
         (value (if long-flag
                    (top (pop (stack (top-frame th s))))
                    (top (stack (top-frame th s)))))
         (instance (deref class-ref (heap s))))
    (if instance
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (if long-flag
                           (popn 2 (stack (top-frame th s)))
                           (pop (stack (top-frame th s))))
                :heap (bind (cadr class-ref)
                            (set-instance-field "java/lang/Class"
                                                field-name-and-type
                                                value
                                                instance)
                            (heap s)))
        s)))

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
  (let ((cs (call-stack th s)))
    (return-stk (stack (top (pop cs))) th s)))

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
         (arrayref (top (pop (pop (stack (top-frame th s))))))
         (array (deref arrayref (heap s))))
    (if array
        (modify th s
                :pc (+ (inst-length inst) (pc (top-frame th s)))
                :stack (pop (pop (pop (stack (top-frame th s)))))
                :heap (bind (cadr arrayref)
                            (set-element-at (short-fix value) index array (class-table s))
                            (heap s)))
        s)))

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
    (CHECKCAST      (execute-CHECKCAST inst th s))
    (D2F            (execute-D2F inst th s))
    (D2I            (execute-D2I inst th s))
    (D2L            (execute-D2L inst th s))
    (DADD           (execute-DADD inst th s))
    (DALOAD         (execute-DALOAD inst th s))
    (DASTORE        (execute-DASTORE inst th s))
    (DCMPG          (execute-DCMPG inst th s))
    (DCMPL          (execute-DCMPL inst th s))
    (DCONST_0       (execute-DCONST_0 inst th s))
    (DCONST_1       (execute-DCONST_1 inst th s))
    (DDIV           (execute-DDIV inst th s))
    (DLOAD          (execute-DLOAD inst th s))
    (DLOAD_0        (execute-DLOAD_X inst th s 0))
    (DLOAD_1        (execute-DLOAD_X inst th s 1))
    (DLOAD_2        (execute-DLOAD_X inst th s 2))
    (DLOAD_3        (execute-DLOAD_X inst th s 3))
    (DMUL           (execute-DMUL inst th s))
    (DNEG           (execute-DNEG inst th s))
    (DREM           (execute-DREM inst th s))
    (DRETURN        (execute-DRETURN inst th s))
    (DSTORE         (execute-DSTORE inst th s))
    (DSTORE_0       (execute-DSTORE_X inst th s 0))
    (DSTORE_1       (execute-DSTORE_X inst th s 1))
    (DSTORE_2       (execute-DSTORE_X inst th s 2))
    (DSTORE_3       (execute-DSTORE_X inst th s 3))
    (DSUB           (execute-DSUB inst th s))
    (DUP            (execute-DUP inst th s))
    (DUP_X1         (execute-DUP_X1 inst th s))
    (DUP_X2         (execute-DUP_X2 inst th s))
    (DUP2           (execute-DUP2 inst th s))
    (DUP2_X1        (execute-DUP2_X1 inst th s))
    (DUP2_X2        (execute-DUP2_X2 inst th s))
    (F2D            (execute-F2D inst th s))
    (F2I            (execute-F2I inst th s))
    (F2L            (execute-F2L inst th s))
    (FADD           (execute-FADD inst th s))
    (FALOAD         (execute-FALOAD inst th s))
    (FASTORE        (execute-FASTORE inst th s))
    (FCMPG          (execute-FCMPG inst th s))
    (FCMPL          (execute-FCMPL inst th s))
    (FCONST_0       (execute-FCONST_0 inst th s))
    (FCONST_1       (execute-FCONST_1 inst th s))
    (FCONST_2       (execute-FCONST_2 inst th s))
    (FDIV           (execute-FDIV inst th s))
    (FLOAD          (execute-FLOAD inst th s))
    (FLOAD_0        (execute-FLOAD_X inst th s 0))
    (FLOAD_1        (execute-FLOAD_X inst th s 1))
    (FLOAD_2        (execute-FLOAD_X inst th s 2))
    (FLOAD_3        (execute-FLOAD_X inst th s 3))
    (FMUL           (execute-FMUL inst th s))
    (FNEG           (execute-FNEG inst th s))
    (FREM           (execute-FREM inst th s))
    (FRETURN        (execute-FRETURN inst th s))
    (FSTORE         (execute-FSTORE inst th s))
    (FSTORE_0       (execute-FSTORE_X inst th s 0))
    (FSTORE_1       (execute-FSTORE_X inst th s 1))
    (FSTORE_2       (execute-FSTORE_X inst th s 2))
    (FSTORE_3       (execute-FSTORE_X inst th s 3))
    (FSUB           (execute-FSUB inst th s))
    (GETFIELD       (execute-GETFIELD inst th s))
    (GETSTATIC      (execute-GETSTATIC inst th s))
    (GOTO           (execute-GOTO inst th s))
    (GOTO_W         (execute-GOTO_W inst th s))
    (I2B            (execute-I2B inst th s))
    (I2C            (execute-I2C inst th s))
    (I2D            (execute-I2D inst th s))
    (I2F            (execute-I2F inst th s))
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
    (L2D            (execute-L2D inst th s))
    (L2F            (execute-L2F inst th s))
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
  (append (list (method-name-and-type method)
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
              (assemble_class_table (class-table s))
              (options s)))

; -----------------------------------------------------------------------------
; Linking.
; Top function of linking is link-class-table.
; It preprocesses a list of class-decls into linked class-table.
;
; The first class-decl in the list must be java/lang/Object .
; All class-decls in the list must have distinct class-names.
; All other class-decls must have nonempty direct superclass name and
; a class-decl of supercalls must precede it in the list.
; If superclass not found link-class-table returns a string with error message
; instead of a class-table.
;
; After superclasses chains are ready the linking preprocessor searches for all
; references of array types in classfiles and builds automatically all
; mentioned array types together with their superclasses chains.
;
; Then link-class-table scans instructions of all methods in the class table
; and resolves fieldrefs in instructions GETFIELD, GETSTATIC, PUTFIELD, PUTSTATIC
; and methodrefs in instructions INVOKESPECIAL, INVOKESTATIC, INVOKEVIRTUAL .
; Only classname in fieldrefs and methodsrefs might be modified, name-and-type
; is kept unchanged. If class-decl with classname contains field or method whose name-and-type is
; exactly name-and-type of fieldref or methodref, it remains unchanged.
; Otherwise it is replaced by a name of closest superclass, where field or
; method is found. If search fails then classname is replaced by a diagnostic
; string.
; Notice that static linking is insufficent for INVOKEVIRTUAL instruction.
; It seraches for overwriting methods in run-time.

(defun classref->type (classref)
  (if (equal (char classref 0) #\[)
      classref
      (concatenate 'string "L" classref ";")))

(defun make-array-type (elem-type count)
  (if (zp count)
      elem-type
      (make-array-type (array-type-of elem-type) (1- count))))

(defun name-and-type->type (name-and-type)
  (subseq name-and-type
          (1+ (position #\: name-and-type))
          (length name-and-type)))

(defun unpack-param-types-loop (params i st j ans)
  (declare (xargs :measure (if (natp j) (nfix (- (length params) j)) 0)))
  (cond ((or (not (natp j)) (>= j (length params)))
         (reverse ans))
        ((and (not st) (equal (char params j) #\[))
         (unpack-param-types-loop params i nil (1+ j) ans))
        ((and (not st) (equal (char params j) #\L))
         (unpack-param-types-loop params i t (1+ j) ans))
        ((or (not st) (equal (char params j) #\;))
         (unpack-param-types-loop params (1+ j) nil (1+ j)
                                  (cons (subseq params i (1+ j)) ans)))
        (t (unpack-param-types-loop params i t (1+ j) ans))))

(defun unpack-param-types (params)
  (unpack-param-types-loop params 0 nil 0 nil))

(defun unpack-method-type (type)
  (let ((pos (position #\) type)))
       (cons (subseq type (1+ pos) (length type))
             (unpack-param-types (subseq type 1 pos)))))

; Functions below collect types from classrefs, fieldsrefs, methodrefs among classtable

(defun collect-type (type types)
  (if (member-equal type types) types (cons type types)))

(defun collect-types-in-list (type-list types)
  (if (endp type-list)
      types
      (collect-types-in-list
        (cdr type-list)
        (collect-type (car type-list) types))))

(defun collect-types-in-classref (classref types)
  (collect-type (classref->type classref) types))

(defun collect-types-in-fieldref (class name-and-type types)
  (collect-type
    (classref->type class)
    (collect-type (name-and-type->type name-and-type)
                  types)))

(defun collect-types-in-methodref (class name-and-type types)
  (collect-type
    (classref->type class)
    (collect-types-in-list
      (unpack-method-type (name-and-type->type name-and-type))
      types)))

(defun collect-types-in-superclasses (superclasses types)
  (if (endp superclasses)
      types
      (collect-types-in-superclasses
        (cdr superclasses)
        (collect-types-in-classref (car superclasses) types))))

(defun collect-types-in-constant-pool (constants types)
  (if (endp constants)
      types
      (collect-types-in-constant-pool
        (cdr constants)
        (let ((const (car constants)))
             (if (equal (car const) 'class)
                 (collect-types-in-classref (cadr const) types)
                 types)))))

(defun collect-types-in-fields (fields types)
  (if (endp fields)
      types
      (collect-types-in-fields
        (cdr fields)
        (collect-type (name-and-type->type (car fields)) types))))

(defun collect-types-in-instr (instr types)
  (case (car instr)
    (ANEWARRAY      (collect-types-in-classref (array-type-of (cadr instr)) types))
    (CHECKCAST      (collect-types-in-classref (cadr instr) types))
    (GETFIELD       (collect-types-in-fieldref (cadr instr) (caddr instr) types))
    (GETSTATIC      (collect-types-in-fieldref (cadr instr) (caddr instr) types))
    (INSTANCEOF     (collect-types-in-classref (cadr instr) types))
    (INVOKESPECIAL  (collect-types-in-methodref (cadr instr) (caddr instr) types))
    (INVOKESTATIC   (collect-types-in-methodref (cadr instr) (caddr instr) types))
    (INVOKEVIRTUAL  (collect-types-in-methodref (cadr instr) (caddr instr) types))
    (MULTINEWARRAY  (collect-types-in-classref (cadr instr) types))
    (NEW            (collect-types-in-classref (cadr instr) types))
    (NEWARRAY       (collect-type (atype-to-type (cadr instr)) types))
    (PUTFIELD       (collect-types-in-fieldref (cadr instr) (caddr instr) types))
    (PUTSTATIC      (collect-types-in-fieldref (cadr instr) (caddr instr) types))
    (otherwise types)))

(defun collect-types-in-program (instrs types)
  (if (endp instrs)
      types
      (collect-types-in-program
        (cdr instrs)
        (collect-types-in-instr
          (let ((instr (car instrs)))
               (if (isLabeledInst? instr) (cdr instr) instr))
          types))))

(defun collect-types-in-methods (methods types)
  (if (endp methods)
      types
      (collect-types-in-methods
        (cdr methods)
        (let ((method (car methods)))
              (collect-types-in-list
                (unpack-method-type (name-and-type->type (method-name-and-type method)))
                (collect-types-in-program
                  (method-program method)
                  types))))))

(defun collect-types-in-classes (classes types)
  (if (endp classes)
      types
      (collect-types-in-classes
        (cdr classes)
        (let ((class (car classes)))
             (collect-types-in-classref
               (class-decl-name class)
               (collect-types-in-superclasses
                 (class-decl-superclasses class)
                 (collect-types-in-constant-pool
                   (class-decl-cp class)
                   (collect-types-in-fields
                      (class-decl-fields class)
                      (collect-types-in-fields
                        (class-decl-sfields class)
                        (collect-types-in-methods
                          (class-decl-methods class)
                          types))))))))))

; arrays is a map form elem-type to its maximal array dimension

(defun collect-arrays-loop (types arrays)
  (if (endp types)
      arrays
      (collect-arrays-loop
        (cdr types)
        (let ((type (car types)))
             (if (equal (char type 0) #\[)
                 (let* ((pos (search "[" type :from-end t))
                        (elem (subseq type (1+ pos) (length type)))
                        (dim (binding elem arrays)))
                       (if (and pos (or (not dim) (>= pos dim)))
                           (bind elem (1+ pos) arrays)
                           arrays))
                 arrays)))))

(defun collect-arrays (list-of-class-decls)
  (collect-arrays-loop (collect-types-in-classes list-of-class-decls nil) nil))

(defun link-superclasses-loop (list-of-class-decls ans)
  (if (endp list-of-class-decls)
      (if (atom ans) ans (reverse ans))
      (let* ((this-cl (car list-of-class-decls))
             (thisclass (class-decl-name this-cl))
             (superclass (car (class-decl-superclasses this-cl)))
             (super-cl (bound? superclass ans)))
            (if (bound? thisclass ans)
                (concatenate 'string "LinkageError: " thisclass) ; Duplicate class
                (if super-cl
                    (link-superclasses-loop
                      (cdr list-of-class-decls)
                      (cons
                        (make-class-decl
                          thisclass
                          (cons superclass
                            (class-decl-superclasses super-cl))
                          (class-decl-fields this-cl)
                          (class-decl-sfields this-cl)
                          (class-decl-cp this-cl)
                          (class-decl-methods this-cl)
                          '(ref -1))
                        ans))
                     (concatenate 'string "NoClassDefFoundError: " superclass))))))

(defun propagate-superclasses-in-arrays (superclasses dim arrays)
  (if (endp superclasses)
       arrays
       (propagate-superclasses-in-arrays
         (cdr superclasses)
         dim
         (let* ((supertype (classref->type (car superclasses)))
                (old-dim (nfix (binding supertype arrays))))
               (bind supertype (max dim old-dim) arrays)))))

(defun propagate-superarrays (class-table arrays)
  (if (endp class-table)
      arrays
      (propagate-superarrays
        (cdr class-table)
        (let* ((class (car class-table))
               (class-name (class-decl-name class))
               (superclasses (class-decl-superclasses class))
               (dim (binding (classref->type class-name)
                             arrays)))
                (if (posp dim)
                    (propagate-superclasses-in-arrays superclasses dim arrays)
                    arrays)))))

(defun append-array-decls (elem-type superelem-type dim class-table)
  (if (posp dim)
      (let ((class-table (if (> dim 1)
                             (append-array-decls elem-type
                                                 superelem-type
                                                 (1- dim)
                                                 class-table)
                             class-table)))
           (cons (make-class-decl
                   (make-array-type elem-type dim)
                   (let ((superclass
                           (cond (superelem-type
                                  (make-array-type superelem-type dim))
                                 ((> dim 1)
                                  (make-array-type "Ljava/lang/Object;" (1- dim)))
                                 (t "java/lang/Object"))))
                        (cons superclass
                              (class-decl-superclasses (bound? superclass class-table))))
                   ()
                   ()
                   ()
                   ()
                   '(ref -1))
                 class-table))
       class-table))

(defun make-arrays-loop (class-table arrays ans)
  (if (endp class-table)
      (reverse ans)
      (make-arrays-loop
        (cdr class-table)
        arrays
        (let* ((class (car class-table))
               (class-name (class-decl-name class))
               (superclass-name (car (class-decl-superclasses class)))
               (elem-type (classref->type class-name))
               (superelem-type (classref->type superclass-name))
               (dim (binding elem-type arrays)))
              (append-array-decls elem-type superelem-type dim (cons class ans))))))

(defun make-basic-array-decls (elems arrays class-table)
  (if (endp elems)
      class-table
      (make-basic-array-decls
        (cdr elems)
        arrays
        (append-array-decls
          (car elems)
          nil
          (binding (car elems) arrays)
          class-table))))

(defun make-arrays (class-table arrays)
  (let ((arrays (propagate-superarrays class-table arrays)))
       (make-arrays-loop
         (cdr class-table)
         arrays
         (make-basic-array-decls
           '("Ljava/lang/Object;" "Z" "B" "C" "S" "I" "J" "F" "D")
           arrays
           (list (car class-table))))))

(defun link-superclasses (list-of-class-decls)
  (let ((first-cl (first list-of-class-decls)))
       (if (equal (class-decl-name first-cl) "java/lang/Object")
           (if (class-decl-superclasses first-cl)
               "ClassFormatError: java/lang/Object"
               (let ((class-table (link-superclasses-loop
                                   (cdr list-of-class-decls)
                                   (list first-cl))))
                    (if (consp class-table)
                         (make-arrays class-table (collect-arrays list-of-class-decls))
                         class-table)))
          "NoClassDefFoundError: java/lang/Object")))

(defun resolve-field-in-superclasses (name-and-type classes class-table)
  (if (endp classes)
       nil
      (let* ((class-name (car classes))
             (class-decl (bound? class-name class-table)))
            (if (member-equal name-and-type (class-decl-fields class-decl))
                class-name
                (resolve-field-in-superclasses
                  name-and-type
                  (cdr classes)
                  class-table)))))

(defun resolve-field (class-name name-and-type class-table)
  (let ((class (bound? class-name class-table)))
       (if class
           (let ((resolved-class
                  (resolve-field-in-superclasses
                    name-and-type
                    (cons class-name (class-decl-superclasses class))
                    class-table)))
                (or resolved-class
                    (concatenate 'string "NoSuchFieldError: "
                               class-name " " name-and-type)))
           (concatenate 'string "NoClassDefFoundError: " class-name))))

(defun resolve-sfield-in-superclasses (name-and-type classes class-table)
  (if (endp classes)
       nil
      (let* ((class-name (car classes))
             (class-decl (bound? class-name class-table)))
            (if (member-equal name-and-type (class-decl-sfields class-decl))
                class-name
                (resolve-sfield-in-superclasses
                  name-and-type
                  (cdr classes)
                  class-table)))))

(defun resolve-sfield (class-name name-and-type class-table)
  (let ((class (bound? class-name class-table)))
       (if class
           (let ((resolved-class
                  (resolve-sfield-in-superclasses
                    name-and-type
                    (cons class-name (class-decl-superclasses class))
                    class-table)))
                (or resolved-class
                    (concatenate 'string "NoSuchFieldError: "
                               class-name " " name-and-type)))
           (concatenate 'string "NoClassDefFoundError: " class-name))))

(defun resolve-method (class-name name-and-type class-table)
  (let ((class (bound? class-name class-table)))
       (if class
           (let ((methodref
                   (lookup-methodref name-and-type class-name class-table)))
                (if methodref
                    (car methodref)
                    (concatenate 'string "NoSuchMethodError: "
                                 class-name " "  name-and-type)))
           (concatenate 'string "NoClassDefFoundError: " class-name))))

(defun link-instr (instr class-table)
  (case (car instr)
    (GETFIELD       (list* 'GETFIELD
                           (resolve-field (cadr instr) (caddr instr) class-table)
                           (caddr instr)
                           (cdddr instr)))
    (GETSTATIC      (list* 'GETSTATIC
                           (resolve-sfield (cadr instr) (caddr instr) class-table)
                           (caddr instr)
                           (cdddr instr)))
    (INVOKESPECIAL  (list* 'INVOKESPECIAL
                           (resolve-method (cadr instr) (caddr instr) class-table)
                           (caddr instr)
                           (cdddr instr)))
    (INVOKESTATIC   (list* 'INVOKESTATIC
                           (resolve-method (cadr instr) (caddr instr) class-table)
                           (caddr instr)
                           (cdddr instr)))
    (INVOKEVIRTUAL  (list* 'INVOKEVIRTUAL
                           (resolve-method (cadr instr) (caddr instr) class-table)
                           (caddr instr)
                           (cdddr instr)))
    (PUTFIELD       (list* 'PUTFIELD
                           (resolve-field (cadr instr) (caddr instr) class-table)
                           (caddr instr)
                           (cdddr instr)))
    (PUTSTATIC      (list* 'PUTSTATIC
                           (resolve-sfield (cadr instr) (caddr instr) class-table)
                           (caddr instr)
                           (cdddr instr)))
    (otherwise instr)))

(defun link-program (instrs class-table)
  (if (endp instrs)
      instrs
      (let ((instr (car instrs)))
           (cons (if (isLabeledInst? instr)
                     (cons (car instr)
                           (link-instr (cdr instr) class-table))
                     (link-instr instr class-table))
                 (link-program (cdr instrs) class-table)))))

(defun link-methods (methods class-table)
  (if (endp methods)
      methods
      (let ((method (car methods)))
           (cons
             (list* (method-name-and-type method)
                    (method-sync method)
                    (link-program (method-program method) class-table))
             (link-methods (cdr methods) class-table)))))

(defun link-class-list-loop (class-decls class-table)
  (if (endp class-decls)
      class-decls
      (let ((class (car class-decls)))
           (cons
             (make-class-decl
               (class-decl-name class)
               (class-decl-superclasses class)
               (class-decl-fields class)
               (class-decl-sfields class)
               (class-decl-cp class)
               (link-methods (class-decl-methods class) class-table)
               '(ref -1))
             (link-class-list-loop (cdr class-decls) class-table)))))

(defun link-class-list (class-table)
  (link-class-list-loop class-table class-table))

(defun link-class-table (list-of-class-decls)
  (link-class-list
    (link-superclasses list-of-class-decls)))

(defun make-class-def (list-of-class-decls)
   (link-class-table
     (append (base-class-def) list-of-class-decls)))

; -----------------------------------------------------------------------------
; load_class_library: a utility for populating the heap with Class and
;                     String objects

(defund chars-to-bytes (chars is-big-endian)
  (if (endp chars)
      nil
      (if (equal is-big-endian 0)
          (cons (byte-fix (car chars))
                (cons (byte-fix (shr (car chars) 8))
                      (chars-to-bytes (cdr chars) is-big-endian)))
          (cons (byte-fix (shr (car chars) 8))
                (cons (byte-fix (car chars))
                      (chars-to-bytes (cdr chars) is-big-endian))))))

(defun make-string-obj (class cpentry s idx)
  (let* ((new-object (build-an-instance
                      (cons "java/lang/String"
                            (class-decl-superclasses
                             (bound? "java/lang/String" (class-table s))))
                     (class-table s)))
         (array-address (len (heap s)))
         (new-address (1+ array-address))
         (chars (cddr cpentry))
         (char-array (if (byte-strings-p (options s))
                         (makearray 'T_BYTE
                                    (* 2 (len chars))
                                    (chars-to-bytes chars
                                                    (is-big-endian (options s)))
                                    (class-table s))
                         (makearray 'T_CHAR
                                    (len chars)
                                    chars
                                    (class-table s))))
         (stuffed-obj (if (byte-strings-p (options s))
                          (set-instance-field
                            "java/lang/String"
                            "value:[B"
                            (list 'REF array-address)
                            (set-instance-field "java/lang/Stirng"
                                                "coder:B"
                                                1
                                                new-object))
                          (set-instance-field "java/lang/String"
                                              "value:[C"
                                              (list 'REF array-address)
                                              new-object)))
         (new-heap (bind new-address
                         stuffed-obj
                         (bind array-address
                               char-array
                               (heap s)))))
        (modify th s
                :heap new-heap
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
         (stuffed-obj (set-instance-field "java/lang/Class"
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
                    new-class-table
                    (options s))))

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

