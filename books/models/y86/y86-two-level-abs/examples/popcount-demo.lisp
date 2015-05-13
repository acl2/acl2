(in-package "ACL2")

; Added by Matt K., May 2015.  Improvement observed when certification used
; the :delay strategy:
; 38.84 sec. vs. 61.13 sec.
; (Maybe we can delete the commented-out set-max-mem below.)
(value-triple (set-gc-strategy :delay))

(include-book "../y86/y86-asm")
(include-book "../y86/y86-mem-init")
(include-book "centaur/gl/gl" :dir :system)

#||
;; [Jared]: trick cert.pl into allocating more memory for this book on our cluster.
(set-max-mem (* 4 (expt 2 30)))
||#

; If popcount-demo.lisp (which, incidentally, is more or less subsumed by
; popcount.lisp) is certified in parallel with popcount.lisp, that could result
; in memory usage that stresses a machine with 8GB of RAM.  So we are tempted
; to add artificial dependency here, and we did at one time.  But now, the
; overall books/Makefile ensures that only one book is certified under
; books/models/y86/ at a time, and that seems sufficient.  To restore the
; previous state of affairs, eliminate the newline below as indicated.
#||
(include-book
 "popcount")
||#

(defthm x86-32p-create-x86-32
  (x86-32p (create-x86-32))
  :hints (("Goal" :in-theory (e/d (x86-32p memp-aux)
				  ((x86-32$ap))))))

(in-theory (disable create-x86-32))

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

    (mrmovl 8(%ebp) %ebx)    ;   8: Get <n>
    (xorl   %eax %eax)       ;  14: %eax <- 0
    (irmovl 1 %esi)          ;  16: %esi <- 1
    (rrmovl %esi %edx)       ;  22: %edx <- 1

    loop
    (rrmovl %ebx %ecx)       ;  24: Evolving <n>
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
    (irmovl  1023 %eax)      ;  88: <n>

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
   nil                          ; Y86 status
   eip                          ; Initial program counter
   `((:esp . ,esp))             ; Initial stack pointer
   nil                          ; Initial flags, if NIL, then all zeros
   *popcount-binary*            ; Initial memory
   (wm32 esp n (create-x86-32)) ; <n> placed on top of the stack
   ))

(def-gl-thm y86-popcount-correct-reduced-symsim-fixed-n-var-esp
  :hyp (and (equal n 1023) ;; Fixing the value of n
	    (natp esp)
	    (< 118 esp)
	    (<= esp (- (expt 2 32) 4)))
  :concl (let* ((start-eip (cdr (assoc-eq 'call-popcount
					  *popcount-symbol-table*)))
		(halt-eip (cdr (assoc-eq 'halt-of-main
					 *popcount-symbol-table*)))
		(x86-32 (popcount-init-x86-32 n esp start-eip))
		(count 300)
		(x86-32 (y86 x86-32 count)))
	   (and (equal (rgfi *mr-eax* x86-32)
		       (logcount n))
		(equal (eip x86-32)
		       halt-eip)))
  :g-bindings
  ;; Note that GL can optimize the following away to construct a symbolic
  ;; object that represents 1023.
  `((n   (:g-number ,(gl-int 0 1 33)))
    (esp (:g-number ,(gl-int 33 1 33))))
  :rule-classes nil)

(def-gl-thm y86-popcount-correct-reduced-symsim-var-n-fixed-esp
  :hyp (and (equal esp 8192) ;; Fixing the value of esp
	    (n32p n))
  :concl (let* ((start-eip (cdr (assoc-eq 'call-popcount
					  *popcount-symbol-table*)))
		(halt-eip (cdr (assoc-eq 'halt-of-main
					 *popcount-symbol-table*)))
		(x86-32 (popcount-init-x86-32 n esp start-eip))
		(count 300)
		(x86-32 (y86 x86-32 count)))
	   (and (equal (rgfi *mr-eax* x86-32)
		       (logcount n))
		(equal (eip x86-32)
		       halt-eip)))
  :g-bindings
  `((n   (:g-number ,(gl-int 0 1 33)))
    ;; Note that GL can optimize the following away to construct a symbolic
    ;; object that represents 8192.
    (esp (:g-number ,(gl-int 33 1 33))))
  :rule-classes nil)

;; (def-gl-thm y86-popcount-correct-reduced-symsim-var-esp-var-n-1
;;   :hyp (and  (natp esp)
;;              (<= 118 esp)
;;              (< esp (expt 2 10))
;;              (n32p n))
;;   :concl (let* ((start-eip (cdr (assoc-eq 'call-popcount
;;                                           *popcount-symbol-table*)))
;;                 (halt-eip (cdr (assoc-eq 'halt-of-main
;;                                          *popcount-symbol-table*)))
;;                 (x86-32 (popcount-init-x86-32 n esp start-eip))
;;                 (count 300)
;;                 (x86-32 (y86 x86-32 count)))
;;            (and (equal (rgfi *mr-eax* x86-32)
;;                        (logcount n))
;;                 (equal (eip x86-32)
;;                        halt-eip)))
;;   :g-bindings
;;   `((n   (:g-number ,(gl-int 0 1 33)))
;;     (esp (:g-number ,(gl-int 33 1 33))))
;;   :rule-classes nil)

;; (def-gl-thm y86-popcount-correct-reduced-symsim-var-esp-var-n-2
;;   :hyp (and  (natp esp)
;;              (<= (expt 2 10) esp)
;;              (< esp (- (expt 2 32) 8))
;;              (n32p n))
;;   :concl (let* ((start-eip (cdr (assoc-eq 'call-popcount
;;                                           *popcount-symbol-table*)))
;;                 (halt-eip (cdr (assoc-eq 'halt-of-main
;;                                          *popcount-symbol-table*)))
;;                 (x86-32 (popcount-init-x86-32 n esp start-eip))
;;                 (count 300)
;;                 (x86-32 (y86 x86-32 count)))
;;            (and (equal (rgfi *mr-eax* x86-32)
;;                        (logcount n))
;;                 (equal (eip x86-32)
;;                        halt-eip)))
;;   :g-bindings
;;   `((n   (:g-number ,(gl-int 0 1 33)))
;;     (esp (:g-number ,(gl-int 33 1 33))))
;;   :rule-classes nil)
