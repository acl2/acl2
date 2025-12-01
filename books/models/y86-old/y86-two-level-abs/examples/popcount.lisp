(in-package "ACL2")

; Added by Matt K., May 2015.  Improvement observed when certification used
; the :delay strategy:
; 82.62 sec. vs. 118.04 sec.
(value-triple (set-gc-strategy :delay))

(include-book "../y86/y86")
(include-book "../y86/y86-asm")
(include-book "../y86/y86-mem-init")

; popcount.lisp                        Warren A. Hunt, Jr.

(include-book "arithmetic-5/top" :dir :system)
(include-book "centaur/gl/gl"    :dir :system)
; Increase memory for X86 memory.
; Matt K., May 2015: Commenting out next two lines, since above call of
; set-gc-strategy should do the job.
; (include-book "centaur/misc/memory-mgmt-logic" :dir :system)
; (value-triple (set-max-mem (* 6 (expt 2 30))))

(defun gl-int (start by count)
 ;; An aid for writing DEF-GL-THM bindings
 (declare (xargs :guard (and (natp start)
                             (natp by)
                             (natp count))))
 (if (zp count)
     nil
   (cons start
         (gl-int (+ by start) by (1- count)))))

; Some definitions to make the converstion
; from C to Lisp easier to follow.

(defconst *2^32*    (expt 2 32))
(defconst *2^32-1*  (1- *2^32*))
(defconst *2^64*    (expt 2 64))
(defconst *2^64-1*  (1- *2^64*))
(defconst *2^128*   (expt 2 128))
(defconst *2^128-1* (1- *2^128*))
(defconst *2^256*   (expt 2 256))
(defconst *2^256-1* (1- *2^256*))


(defmacro &   (x y) `(logand ,x ,y))
(defmacro >>  (x y) `(ash ,x (- ,y)))
; (defmacro 32* (x y) `(&   (* ,x ,y)   *2^32*)) ; Wrong
; (defmacro 32* (x y) `(&   (* ,x ,y)   (1- *2^32*)))
(defmacro 32* (x y) `(mod (* ,x ,y)      *2^32*))

; Population count (often called "pop-count") definition
; Counts the number (population) of "1"s in an integer

;    v = v - ((v >> 1) & 0x55555555);
;    v = (v & 0x33333333) + ((v >> 2) & 0x33333333);
;    c = ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;

(defun fast-logcount-32 (v)
 (declare (xargs :guard (natp v)))
 (let*
  ((v (- v  (& (>> v 1)   #x55555555)))
   ;v = v - (  (v >> 1) & 0x55555555);

   (v (+ (& v #x33333333)   (& (>> v 2)   #x33333333)))
   ;v =  (v & 0x33333333) + (  (v >> 2) & 0x33333333);

   (c (>> (32* (& (+ v   (>> v 4))  #xF0F0F0F)   #x1010101)    24))
   ;c =           ( (v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;
   )
   c))


#||
(defthm fast-logcount-32-is-logcount-attempt-1
 (implies (and (integerp x)
               (<= 0 x)
               (< x *2^32*))
          (equal (fast-logcount-32 x)
                 (logcount x)))
 :hints (("Goal" :in-theory (e/d () (ash logand)))))

(defthm fast-logcount-32-is-logcount-attempt-2
 (implies (and (integerp x)
               (<= 0 x)
               (< x *2^32*))
          (equal (fast-logcount-32 x)
                 (logcount x)))
 :hints (("Goal" :in-theory (e/d () (ash logand * floor)))))
||#

; So, let's try the GL system.

(def-gl-thm fast-logcount-32-correct
 :hyp (unsigned-byte-p 32 x)
 :concl (equal (fast-logcount-32 x)
               (logcount x))
 :g-bindings `((x (:g-number ,(gl-int 0 1 33)))))

; What about wider words?

; Let's go and have a look at the C program -- and
; consider its verification.

(defun fast-logcount-64 (x)
 (declare (xargs :guard (and (natp x)
                             (< x (expt 2 64)))
                 :guard-hints
                 (("Goal" :in-theory (e/d () (ash logand))))))
 (let ((word0 (logand x *2^32-1*))
       (word1 (ash x -32)))
   (+ (fast-logcount-32 word0)
      (fast-logcount-32 word1))))

(def-gl-thm fast-logcount-64-correct
 :hyp (unsigned-byte-p 64 x)
 :concl (equal (fast-logcount-64 x)
               (logcount x))
 :g-bindings `((x (:g-number ,(gl-int 0 1 65)))))


(defun fast-logcount-128 (x)
 (declare (xargs :guard (and (natp x)
                             (< x (expt 2 128)))
                 :guard-hints
                 (("Goal" :in-theory (e/d () (ash logand))))))
 (let ((word0 (logand x *2^64-1*))
       (word1 (logand (ash x -64))))
   (+ (fast-logcount-64 word0)
      (fast-logcount-64 word1))))

(def-gl-thm fast-logcount-128-correct
 :hyp (unsigned-byte-p 128 x)
 :concl (equal (fast-logcount-128 x)
               (logcount x))
 :g-bindings `((x (:g-number ,(gl-int 0 1 129)))))


(defun fast-logcount-256 (x)
 (declare (xargs :guard (and (natp x)
                             (< x (expt 2 256)))
                 :guard-hints
                 (("Goal" :in-theory (e/d () (ash logand))))))
 (let ((word0 (logand x *2^128-1*))
       (word1 (logand (ash x -128))))
   (+ (fast-logcount-128 word0)
      (fast-logcount-128 word1))))

(def-gl-thm fast-logcount-256-correct
 :hyp (unsigned-byte-p 256 x)
 :concl (equal (fast-logcount-256 x)
               (logcount x))
 :g-bindings `((x (:g-number ,(gl-int 0 1 257)))))


; What about performing using FAST-LOGCOUNT-256 repeatedly so as to
; implement LOGCOUNT?

(defun logcount-by-256-bits (x)
 (declare (xargs :guard (natp x)))
 (if (zp x)
     0
   (+ (fast-logcount-256 (logand x *2^256-1*))
      (logcount-by-256-bits (ash x -256)))))

(defthm lognot-of-negative-is-positive
 (implies (and (integerp x)
               (< x 0))
          (<= 0 (lognot x)))
 :hints (("Goal" :in-theory (e/d (lognot ifix)( )))))

(defun fast-logcount (x)
 (declare (xargs :guard (integerp x)))
 (cond ((zip x) 0)
       ((< x 0)
        (logcount-by-256-bits (lognot x)))
       (t (logcount-by-256-bits x))))

(in-theory (enable nonnegative-integer-quotient-for-gl))

(encapsulate
 ()

 (local
  (defun logcount-floor (x)
    ;;
    (declare (xargs :measure (cond ((zip x) 0)
                                   ((< x 0) (- x))
                                   (t x))
                    :hints (("goal" :in-theory (enable lognot)))))
    (cond
     ((zip x) 0)
     ((< x 0) (logcount-floor (lognot x)))
     ((evenp x)
      (logcount-floor (floor x 2)))
     (t (1+ (logcount-floor (floor x 2)))))))

 ; (dmr-start)

 (local
  (encapsulate
   ()

   (local
    (defthm |(logcount x) --- crock-1|
      (implies (and (not (zip x))
                    (<= 0 x)
                    (integerp (* 1/2 x))
                    )
               (equal (logcount x)
                      (logcount (* 1/2 x))))
      :hints (("goal"
               :in-theory
               (enable nonnegative-integer-quotient-for-gl)))))

    (defthm |(logcount x)|
      (equal (logcount x)
             (logcount-floor x))
      :hints (("goal" :in-theory
               (e/d (nonnegative-integer-quotient-for-gl)
                    (|(floor x 2)|)))))
   ))

 (local
  (in-theory (disable logcount)))

 (local
  (defun logcount-floor-natp (x)
    ;; This function "mimics" LOGCOUNT when X is positive.
    (cond
     ((zp x) 0)
     ((evenp x)
      (logcount-floor-natp (floor x 2)))
     (t (1+ (logcount-floor-natp (floor x 2)))))))

 (local
  (defthm |(logcount-floor x)|
    (implies (and (integerp x)
                  (<= 0 x))
             (equal (logcount-floor x)
                    (logcount-floor-natp x)))))

 ;; From here on, all work is done using LOGCOUNT-FLOOR-NATP.
 (local
  (in-theory (disable logcount-floor)))

 (local
  (encapsulate
   ()

   (local
    (defun ind-hint (x n)
      (if (zp x)
          (+ x n)
        (ind-hint (floor x 2) (+ -1 n)))))

   (local
    (defun ind-hint-n (n)
      (if (and (integerp n)
               (< 0 n))
          (ind-hint-n (+ -1 n))
        42)))

   (local
    (scatter-exponents))

   (local
    (defthm crock-1
      (implies (and (not (zp x))
                    (integerp n)
                    (< 0 n)
                    (integerp (* x (expt 2 (- n)))))
               (integerp (* 1/2 x)))
      :hints (("goal" :induct (ind-hint-n n)))))

   (local
    (gather-exponents))

   (local
    (defthm crock-2
      (implies (and (not (zp x))
                    (integerp n)
                    (< 0 n)
                    (not (integerp (* 1/2 (mod x (expt 2 n))))))
               (not (integerp (* 1/2 x))))))

   (local
    (defthm crock-3
      (implies (and (not (zp x))
                    (integerp n)
                    (< 0 n)
                    (not (integerp (* x (expt 2 (- n)))))
                    (integerp (* 1/2 (mod x (expt 2 n)))))
               (integerp (* 1/2 x)))))

   (defthm split-logcount-floor-natp
     (implies (and (integerp x)
                   (<= 0 x)
                   (integerp n)
                   (< 0 n))
              (equal (+ (logcount-floor-natp (mod   x (expt 2 n)))
                        (logcount-floor-natp (floor x (expt 2 n))))
                     (logcount-floor-natp x)))
     :hints (("goal" :in-theory (disable ; |(floor (floor x y) z)|
                                 |(mod (floor x y) z)|
                                 |(floor x 2)|
                                 crock-1
                                 crock-2
                                 crock-3)
              :induct (ind-hint x n)
              :do-not '(generalize eliminate-destructors fertilize))
             ("subgoal *1/2.1"    :expand ((logcount-floor-natp (mod x (expt 2 n)))
                                           (logcount-floor-natp x)))
             ("subgoal *1/2.1.5"  :in-theory (disable logcount-floor-natp
                                                      |(mod (floor x y) z)|
                                                      |(floor x 2)| ))
             ("subgoal *1/2.1.4"  :in-theory (disable logcount-floor-natp
                                                      |(mod (floor x y) z)|
                                                      |(floor x 2)| ))
             ("subgoal *1/2.1.2'" :in-theory (disable logcount-floor-natp
                                                      |(floor x 2)| ))
             ("subgoal *1/2.1.1"  :in-theory (disable logcount-floor-natp
                                                      |(mod (floor x y) z)|
                                                      |(floor x 2)| ))
             ))
   ))

 ;; Next two lemmas deal with the original input being positive or
 ;; negative.
 (local
  (defthm crock-1
    (implies (and (not (zip x)) (<= 0 x))
             (equal (logcount-by-256-bits x)
                    (logcount-floor-natp x)))
    :hints (("subgoal *1/4'"
             :use ((:instance split-logcount-floor-natp
                              (n 256)))
             :in-theory (disable logcount-floor-natp
                                 logcount-by-256-bits)))))

 (local
  (defthm crock-2
    (implies (and (not (zip x)) (< x 0))
             (equal (logcount-by-256-bits (lognot x))
                    (logcount-floor x)))
    :hints (("goal" :expand ((logcount-floor x))
             :use ((:instance crock-1
                              (x (lognot x))))))))


 (defthm fast-logcount-is-logcount
   (implies (integerp x)
            (equal (fast-logcount x)
                   (logcount x)))
   :otf-flg t)
 )


; Y86 Version of popcount

#||
int popcount_bits ( int v ) {
  v = v - ((v >> 1) & 0x55555555);
  v = (v & 0x33333333) + ((v >> 2) & 0x33333333);
  v = ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;
  return( v );  }
||#

(defconst *popcount-source*
  ;; Register Usage:
  ;;   %eax -- evolving count
  ;;   %ebx -- input argument, which is erased as it is counted
  ;;   %ecx -- tmp
  ;;   %edx -- mask, starts as 1 and is shifted left each iteration
  ;;   %esi -- constant 1
  '(popcount
    ;; Subroutine setup
    (pushl  %ebp)            ;   0: Save superior frame pointer
    (rrmovl %esp %ebp)       ;   2: Set frame pointer
    (pushl  %ebx)            ;   4: Save callee-save register
    (pushl  %esi)            ;   6: Save callee-save register

    (mrmovl 8(%ebp) %ebx)    ;   8: Get <v>
    (xorl   %eax %eax)       ;  14: %eax <- 0
    (irmovl 1 %esi)          ;  16: %edx <- 1
    (rrmovl %esi %edx)       ;  22: %esi <- 1

    loop
    (rrmovl %ebx %ecx)       ;  24: Evolving <v>
    (andl   %edx %ecx)       ;  26: Bit a 1?
    (je     move_mask)       ;  28  Jump if bit is zero

    (xorl   %edx %ebx)       ;  33: Erase bit just counted
    (addl   %esi %eax)       ;  35: Add 1 to the count

    move_mask
    (addl   %edx %edx)       ;  37: Shift mask left
    (andl   %ebx %ebx)       ;  39: Anything left to count?
    (jne    loop)            ;  41: If so, keep counting

    popcount_leave
    (popl   %esi)            ;  46: Restore callee-save register
    (popl   %ebx)            ;  48: Restore callee-save register
    (rrmovl %ebp %esp)       ;  50: Restore stack pointer
    (popl   %ebp)            ;  52: Restore previous frame pointer
    (ret)                    ;  54: Subroutine return
    popcount_end             ;  55:

    ;; Main program

    (pos   80)               ;  80: Align to 16-byte address
    main                     ;  80: "main" program
    (irmovl  stack %esp)     ;  80: Initialize stack pointer (%esp)
    (rrmovl  %esp %ebp)      ;  86: Initialize frame pointer (%ebp)
    (irmovl  1023 %eax)      ;  88: <v>

    (pushl   %eax)           ;  94: Push argument on stack
    call-popcount
    (call    popcount)       ;  96: Call PopCount subroutine
    return-from-popcount


    (popl    %ebx)           ; 101: Restore local stack position
    halt-of-main
    (halt)                   ; 103: Halt
    end-of-code              ; 104: Label for the end of the code

    ;; Stack

    (pos 8192)               ; 8192: Assemble position
    stack                    ; 8192: Thus, "stack" has value 8192
    ))

; Program OK?

(defthm popcount-program-ok
  (y86-prog *popcount-source*))

(defconst *popcount-start-location* 0)
(defconst *popcount-symbol-table*
  (hons-shrink-alist
   (y86-symbol-table *popcount-source*
                     *popcount-start-location*
                     'symbol-table)
   nil))

; The function Y86-ASM assembles a program into a memory image.

(defconst *popcount-binary*
  (reverse (y86-asm *popcount-source*
                    *popcount-start-location*
                    *popcount-symbol-table* nil)))

(defthm x86-32p-create-x86-32
  (x86-32p (create-x86-32))
  :hints (("Goal" :in-theory (e/d (x86-32p memp-aux)
                                  ((x86-32$ap))))))

(in-theory (disable create-x86-32))

(defun-nx popcount-init-x86-32 (n esp eip)

; N is our formal, ESP is the stack pointer just before (call
; popcount), and EIP position of the (call popcount) instruction.
; It's important that addresses from *popcount-binary* don't include
; ESP, and in fact there's sufficient separation to let the stack grow
; a bit to hold callee-save registers.

  (declare (xargs :guard (and (n32p n)
                              (n32p esp)
                              (n32p eip))))
  (init-y86-state
   nil               ; Y86 status
   eip               ; Initial program counter
   `((:esp . ,esp))  ; Initial stack pointer
   nil               ; Initial flags, if NIL, then all zeros
   *popcount-binary* ; Initial memory
   (wm32 esp n (create-x86-32)) ; <n> placed on top of the stack
   ))


(defun poised-at-popcount-n (n x86-32)
  (declare (xargs :guard (n32p n)
                  :stobjs x86-32))
  (let ((esp (rgfi *mr-esp* x86-32)))
    (and (n32p (+ 3 esp))
         ;; call has not yet taken place (next step is the call)
         (equal n (rm32 esp x86-32))

         ;; We check that the stack necessary won't overwrite the
         ;; code.  When we call POPCOUNT, we require five additional
         ;; doublewords (32-bit words): one for the return address
         ;; and four for temporary storage.

         (<= (cdr (assoc-eq 'end-of-code ; just past the return
                            *popcount-symbol-table*))
             (- esp ; subtract max number of bytes to be pushed
                20)))))


(defun mem-segment-p (alist x86-32)

; This function is only appropriate if alist doesn't have duplicates --
; otherwise we are making requirements on shadowed entries.  We know that alist
; doesn't have duplicates if it results from a call of hons-shrink-alist.

  (declare (xargs :stobjs x86-32))
  (cond ((atom alist) t)
        (t (and (consp (car alist))
                (n32p (caar alist))
                (equal (rm08 (caar alist) x86-32)
                       (cdar alist))
                (mem-segment-p (cdr alist) x86-32)))))

(defun poised-at-popcount-base (eip x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (n32p eip)))
  (and (mem-segment-p *popcount-binary* x86-32)
       (equal (eip x86-32) eip)))

(defun poised-at-popcount (n eip x86-32)
  (declare (xargs  :stobjs x86-32
                   :guard (and (n32p n)
                               (n32p eip))))
  (and (poised-at-popcount-base eip x86-32)
       (poised-at-popcount-n n x86-32)))

; Why this next thorem when we already have
; Y86-STEP-PRESERVES-X86-32P?

#||
(skip-proofs
 (defthm x86-32p-y86-step
   (implies (x86-32p x86-32)
            (x86-32p (y86-step x86-32)))
   :hints (("Goal" :in-theory (enable y86-step)))))
||#

(defun reduce-popcount (x86-32)
  (declare (xargs :stobjs x86-32))
  (let ((esp (rgfi *mr-esp* x86-32)))
    (popcount-init-x86-32 (rm32 esp x86-32)
                     esp
                     (cdr (assoc-eq 'call-popcount
                                    *popcount-symbol-table*)))))

(def-gl-thm y86-popcount-correct-reduced-symsim
  :hyp (n32p n)
  :concl (let* ((start-eip (cdr (assoc-eq 'call-popcount
                                          *popcount-symbol-table*)))
                (halt-eip (cdr (assoc-eq 'halt-of-main
                                         *popcount-symbol-table*)))
                (esp 8192)
                (x86-32 (popcount-init-x86-32 n esp start-eip))
                (count 300)
                (x86-32 (y86 x86-32 count)))
           (and (equal (rgfi *mr-eax* x86-32)
                       (logcount n))
                (equal (eip x86-32)
                       halt-eip)))
  :g-bindings
  `((n   (:g-number ,(gl-int 0 1 33))))
  :rule-classes nil)


(def-gl-thm y86-popcount-correct-reduced-symsim-2
  :hyp (and ; (n32p n)
            (n32p esp)
            (<= 128 esp)
            (<= esp 512))
  :concl (let* ((start-eip (cdr (assoc-eq 'call-popcount
                                          *popcount-symbol-table*)))
                (halt-eip (cdr (assoc-eq 'halt-of-main
                                         *popcount-symbol-table*)))
                (n 2047)
                ;; (esp 8192)
                (x86-32 (popcount-init-x86-32 n esp start-eip))
                (count 300)
                (x86-32 (y86 x86-32 count)))
           (and (equal (rgfi *mr-eax* x86-32)
                       (logcount n))
                (equal (eip x86-32)
                       halt-eip)))
  :g-bindings
  `(;; (n   (:g-number ,(gl-int 0 1 33)))
    (esp (:g-number ,(gl-int 33 1 33))))
  :rule-classes nil)
