(in-package "ACL2")

(include-book "py86")
(include-book "../y86/y86-asm")
(include-book "py86-mem-init")

(defun fib (n)
  (declare (xargs :guard (natp n)))
  (cond ((zp n) 0)
        ((eql n 1) 1)
        (t (+ (fib (- n 1)) (fib (- n 2))))))

(defconst *fib-source*
  '(fib
    ;; Subroutine setup
    (pushl  %ebp)         ;   0: Save superior frame pointer
    (rrmovl %esp %ebp)    ;   2: Set frame pointer
    (pushl  %ebx)         ;   4: Save callee-save registers on stack
    (pushl  %esi)         ;   6:

    (mrmovl 8(%ebp) %ebx) ;   8: Get <N>

    ;; Zero test

    (xorl   %eax %eax)    ;  14: %eax := 0
    (andl   %ebx %ebx)    ;  16: Set flags
    (jle    fib_leave)    ;  18: Return 0, if <N> <= 0

    ;; One test

    (irmovl 1 %eax)       ;  23: %eax := 1
    (rrmovl %ebx %ecx)    ;  29: %ecx := <N>
    (subl   %eax %ecx)    ;  31: %ecx := <N> - 1
    (je     fib_leave)    ;  33: Return 1, if <N> == 0

    ;; Push (- N 1) on stack for recursive FIB call

    (pushl  %ecx)         ;  38: Push (<N> - 1)
    fib-1
    (call   fib)          ;  40: Recursively call fib(<N> - 1)
    (popl   %ecx)         ;  45: Restore stack pointer
    (rrmovl %eax %esi)    ;  47: Save fib(<N> - 1)

    (irmovl 2 %ecx)       ;  49:
    (subl   %ecx %ebx)    ;  55: <N> - 2

    ;; Push (- N 2) on stack for recursive FIB call

    (pushl  %ebx)         ;  57: Push (<N> - 2)
    fib-2
    (call   fib)          ;  59: Recursively call fib(<N> - 2)
    (popl   %ecx)         ;  64: Restore stack pointer

    (addl   %esi %eax)    ;  66: fib(<N> - 2) + fib(<N> - 1)

    ;; Subroutine leave

    fib_leave
    (popl   %esi)         ;  68: Restore callee-save register
    (popl   %ebx)         ;  70: Restore callee-save register
    (rrmovl %ebp %esp)    ;  72: Restore stack pointer
    (popl   %ebp)         ;  74: Restore previous frame pointer
    (ret)                 ;  76: Subroutine return
    end-of-code

    ;; Main program

    (align   16)          ;  80: Align to 16-byte address
    main                  ;  80: "main" program
    (irmovl  stack %esp)  ;  80: Initialize stack pointer (%esp)
    (rrmovl  %esp %ebp)   ;  86: Initialize frame pointer (%ebp)
    (irmovl  6 %eax)      ;  88: <N>:  fibonacci( <N> )

    (pushl   %eax)        ;  94: Push argument on stack
    call-fib
    (call    fib)         ;  96: Call Fibonacci subroutine
    return-from-fib

    (popl    %ebx)        ; 101: Restore local stack position
    (halt)                ; 103: Halt

      ;; Stack ; ;

    (pos 8192)            ; 8192: Assemble position
    stack                 ; 8192: Thus, "stack" has value 8192
    ))

(defconst *fib-start-location*
  0)

(defconst *fib-symbol-table*
  (y86-symbol-table *fib-source* *fib-start-location* nil))

(defconst *fib-binary*
  (hons-shrink-alist
   (y86-asm *fib-source* *fib-start-location* *fib-symbol-table* 'fib)
   'shrunk-sum-1-to-n))

(defun fib-count (n)

; Return the number of steps taken by y86, starting at a call of FIB and ending
; just after corresponding (ret) in the FIB routine.

  (declare (xargs :guard (natp n)
                  :ruler-extenders :all))
  (1+                   ; (for the call instr)
   (cond ((zp n) 13)    ; 8 (prelude) + 5 (postlude, to fib_leave)
         ((eql n 1) 17) ; 8 + 4 (extra prelude when N = 1) + 5
         (t (+ 13       ; 8 (prelude)
               (fib-count (- n 1))
               5
               (fib-count (- n 2))
               7)))))

(defun fib-init-x86-32 (n esp eip)

; N is our formal, esp is the stack pointer just before (call fib), and eip
; position of the (call fib) instruction.  It's important that addresses from
; *fib-binary* don't include esp, and in fact there's sufficient separation to
; let the stack grow as fib is executed without smashing the fib code.

  (declare (xargs :guard (and (n32p n)
                              (n32p esp)
                              (n32p eip))))
  (init-y86-state nil
                  eip
                  `((:esp . ,esp))
                  nil
                  *fib-binary*
                  (wm32 esp n (create-x86-32)) ; n is on the top of the stack
                  ))

(defun mem-segment-p (alist x86-32)

; This function is only appropriate if alist doesn't have duplicates --
; otherwise we are making requirements on shadowed entries.  We know that alist
; doesn't have duplicates if it results from a call of hons-shrink-alist.

  (declare (xargs :guard (x86-32p x86-32)))
  (cond ((atom alist) t)
        (t (and (consp (car alist))
                (n32p (caar alist))
                (equal (rm08 (caar alist) x86-32)
                       (cdar alist))
                (mem-segment-p (cdr alist) x86-32)))))

(defun fib-stack-max-bytes (n)

; The maximum number of bytes pushed onto the stack by calls of fib

  (declare (xargs :guard (natp n)))
  (* 4    ; convert dwords (computed just below) to bytes
     (+ 1 ; for the dword already at tos (i.e., the parameter of fib)
        (case n
          ((0 1) 4)
          (otherwise (- (* 5 n)
                        1))))))

(defun poised-at-fib-n (n x86-32)
  (declare (xargs :guard (and (n32p n)
                              (x86-32p x86-32))))
  (let ((esp (rgfi *mr-esp* x86-32)))
    (and (n32p (+ 3 esp))
         ;; call has not yet taken place (next step is the call)
         (equal n (rm32 esp x86-32))

         ;; We check that the stack necessary won't overwrite the
         ;; code.  The nesting of calls is at most n, and for each
         ;; stack frame we push four doublewords.

         (<= (cdr (assoc-eq 'end-of-code ; just past the return
                            *fib-symbol-table*))
             (- esp ; subtract max number of bytes to be pushed
                (fib-stack-max-bytes n))))))

(defun poised-at-fib-base (eip x86-32)
  (declare (xargs :guard (and (x86-32p x86-32)
                              (n32p eip))))
  (and (mem-segment-p *fib-binary* x86-32)
       (equal (eip x86-32) eip)))

(defun poised-at-fib (n eip x86-32)
  (declare (xargs :guard (and (n32p n)
                              (n32p eip)
                              (x86-32p x86-32))))
  (and (poised-at-fib-base eip x86-32)
       (poised-at-fib-n n x86-32)))

(defthm x86-32p-y86-step
  (implies (x86-32p x86-32)
           (x86-32p (y86-step x86-32)))
  :hints (("Goal" :in-theory (enable y86-step))))

(defun reduce-fib (x86-32)
  (declare (xargs :guard (x86-32p x86-32)))
  (let ((esp (rgfi *mr-esp* x86-32)))
    (fib-init-x86-32 (rm32 esp x86-32)
                     esp
                     (cdr (assoc-eq 'call-fib
                                    *fib-symbol-table*)))))

; Let's do a sanity check before investing proof effort.
#||
(let* ((n 10)
       (esp 9000)
       (eip (cdr (assoc-eq 'call-fib
                           *fib-symbol-table*)))
       (x86-32 (fib-init-x86-32 n esp eip))
       (count (fib-count n)))
  (list :x86-32p (x86-32p x86-32)
        :initial-eip (eip x86-32)
        :initial-esp (rgfi *mr-esp* x86-32)
        :initial-tos (rm32 (rgfi *mr-esp* x86-32) x86-32)
        :poised (poised-at-fib n eip x86-32)
        (let ((x86-32 (y86 x86-32 count)))
          (list :eax (rgfi *mr-eax* x86-32)
                :final-eip (eip x86-32)
                :functional (fib n)))))
||#

; Start proof of y86-fib-correct-up-to-6-reduced.

(local (include-book "centaur/gl/gl" :dir :system))

(defun disjoint-intervals-p (lower1 upper1 lower2 upper2)

; Test if [lower1,upper1] and [lower2,upper2] are indeed closed intervals with
; natural number bounds such that lower1 <= upper1 and lower2 <= upper2, and
; that these intervals are disjoint.

  (declare (xargs :guard t))
  (and (n32p lower1)
       (n32p upper1)
       (<= lower1 upper1)
       (n32p lower2)
       (n32p upper2)
       (<= lower2 upper2)
       (or (< upper1 lower2)
           (< upper2 lower1))))

(defun f-stack-okp (n esp)
  (declare (xargs :guard (and (n32p n)
                              (n32p esp)
                              (n32p (+ 3 esp)))))
  (let* ((max-bytes (fib-stack-max-bytes n))
         (min-tos (- esp max-bytes))
         (start-of-fib (cdr (assoc-eq 'fib
                                      *fib-symbol-table*)))
         (end-of-fib (cdr (assoc-eq 'end-of-code ; just past the return
                                    *fib-symbol-table*)))
         (start-of-call (cdr (assoc-eq 'call-fib
                                       *fib-symbol-table*)))
         (end-of-call (+ 5 start-of-call)))
    (and (disjoint-intervals-p min-tos esp
                               start-of-fib end-of-fib)
         (disjoint-intervals-p min-tos esp
                               start-of-call end-of-call))))

(local
 (def-gl-thm y86-fib-correct-up-to-3-reduced-symsim

; We can go up to 4 but it takes about 12 to 19 seconds on a fast MacBook Pro.
; !! We can get up to (< n 7) in 5 or 6 seconds and (< n 8) in 15 seconds, by
; let-binding the esp to (cdr (assoc-eq 'stack *fib-symbol-table*)).  But then
; we will need a notion of reduction that allows translating memory addresses,
; so that we correspond 8192 in the reduced state with an arbitrary legal stack
; in the given state.

   :hyp (and (natp n)
             (< n 3)
             (n32p esp)
             (n32p (+ esp 3))
             (f-stack-okp n esp))
   :concl (let* ((eip (cdr (assoc-eq 'call-fib
                                     *fib-symbol-table*)))
                 (x86-32 (fib-init-x86-32 n esp eip))
                 (x86-32 (y86 x86-32 (fib-count n))))
            (and (equal (rgfi *mr-eax* x86-32)
                        (fib n))
                 (equal (eip x86-32)
                        (cdr (assoc-eq 'return-from-fib
                                       *fib-symbol-table*)))))
   :g-bindings
   `((n (:g-number ,(gl-int 0 1 4)))
     (esp (:g-number ,(gl-int 4 1 33))))
   :rule-classes nil))

(defthm y86-fib-correct-up-to-3-reduced
  (let ((eip (cdr (assoc-eq 'call-fib *fib-symbol-table*)))
        (esp (rgfi *mr-esp* x86-32)))
    (implies (and (natp n)
                  (< n 3)
                  (n32p esp)
                  (n32p (+ esp 3))
                  (f-stack-okp n esp)
                  (x86-32p x86-32)

; Perhaps we could drop the following hypothesis, but since it's available and
; could be needed in some other examples (say, because there are restrictions
; on n), we leave it here.

                  (poised-at-fib n eip x86-32))
             (let* ((x86-32 (reduce-fib x86-32))
                    (x86-32 (y86 x86-32 (fib-count n))))
               (and (equal (rgfi *mr-eax* x86-32)
                           (fib n))
                    (equal (eip x86-32)
                           (cdr (assoc-eq 'return-from-fib
                                          *fib-symbol-table*)))))))
  :hints (("Goal"
           :use ((:instance y86-fib-correct-up-to-3-reduced-symsim
                            (esp (rgfi *mr-esp* x86-32))))
           :in-theory (union-theories '(reduce-fib
                                        poised-at-fib
                                        poised-at-fib-n)
                                      (theory 'minimal-theory))))
  :rule-classes nil)

;;; !! Need to define fib-equiv-p in order to eliminate skip-proofs below.
(defstub fib-equiv-p (a b) t)

(skip-proofs
 (defthm fib-equiv-p-is-invariant-step
   (implies (and (x86-32p x86-32-prime)
                 (x86-32p x86-32)
                 (fib-equiv-p x86-32-prime x86-32))
            (fib-equiv-p (y86-step x86-32-prime)
                         (y86-step x86-32)))))

; so by induction:

(defun fib-equiv-p-is-invariant-induction (x y n)
  (if (zp n)
      (list x y)
    (fib-equiv-p-is-invariant-induction (y86-step x)
                                        (y86-step y)
                                        (1- n))))

(skip-proofs
 (defthm fib-equiv-p-implies-same-ms
   (implies (and (x86-32p x)
                 (x86-32p y)
                 (not (equal (ms x) (ms y))))
            (not (fib-equiv-p x y)))))

(defthm fib-equiv-p-is-invariant
  (implies (and (x86-32p x86-32-prime)
                (x86-32p x86-32)
                (fib-equiv-p x86-32-prime x86-32)
                (natp k))
           (fib-equiv-p (y86 x86-32-prime k)
                        (y86 x86-32 k)))
  :hints (("Goal" :in-theory (enable y86)
           :induct (fib-equiv-p-is-invariant-induction
                    x86-32-prime x86-32 k))))

; So rgfi-0-y86-reduce-fib kind of follows from the above, using the following
; to relieve the third hyp above.

(skip-proofs
 (defthm fib-equiv-p-reduce-fib
   (let ((eip (cdr (assoc-eq 'call-fib *fib-symbol-table*))))
     (implies (and (x86-32p x86-32)
                   (poised-at-fib-base eip x86-32))
              (fib-equiv-p (reduce-fib x86-32)
                           x86-32)))))

(skip-proofs
 (defthm fib-equiv-p-implies-same-eax
   (implies (and (x86-32p x86-32)
                 (x86-32p x86-32-prime)
                 (fib-equiv-p x86-32-prime x86-32)
                 (equal (eip x86-32-prime)
                        (cdr (assoc-eq 'return-from-fib *fib-symbol-table*))))
            (equal (rgfi *mr-eax* x86-32)
                   (rgfi *mr-eax* x86-32-prime)))
   :rule-classes nil))

;;; !! Consider not disabling the following in the first place, in
;;; py86-state.lisp.  Otherwise we need 5^2 rules for dealing with these.
;;; (in-theory (enable rgfi !rgfi eip !eip flg !flg memi !memi ms !ms))

(defthm x86-32p-reduce-fib
  (implies (x86-32p x86-32)
           (x86-32p (reduce-fib x86-32)))
  :hints (("Goal" :in-theory (enable init-y86-state
                                     y86-alu-results-store-flgs
                                     m86-reg-updates
                                     x86-32p rgfp))
          ("[1]Goal" :in-theory (enable x86-32p))))

(defthm rgfi-0-y86-reduce-fib
  (implies (and (x86-32p x86-32)
                (natp n)
                (< n 3)
                (n32p (+ (rgfi *mr-esp* x86-32) 3))
                (f-stack-okp n (rgfi *mr-esp* x86-32))
                (let ((eip (cdr (assoc-eq 'call-fib *fib-symbol-table*))))
                  (poised-at-fib n eip x86-32)))
           (equal (rgfi *mr-eax* (y86 (reduce-fib x86-32) (fib-count n)))
                  (rgfi *mr-eax* (y86 x86-32 (fib-count n)))))
  :hints (("Goal"
           :use ((:instance fib-equiv-p-implies-same-eax
                            (x86-32-prime (y86 (reduce-fib x86-32) (fib-count n)))
                            (x86-32 (y86 x86-32 (fib-count n))))
                 (:instance fib-equiv-p-is-invariant
                            (k (fib-count n))
                            (x86-32-prime (reduce-fib x86-32)))
                 (:instance y86-fib-correct-up-to-3-reduced))
           :in-theory (union-theories '(fib-equiv-p-reduce-fib
                                        poised-at-fib
                                        natp-rgfi
                                        (:linear rgfi-less-than-expt-2-32)
                                        x86-32p-reduce-fib
                                        y86-preserves-x86-32p
                                        (:type-prescription fib-count)
                                        natp-compound-recognizer
                                        (assoc-equal)
                                        (natp))
                                      (theory 'minimal-theory)))))

(defthm y86-fib-correct-up-to-3
  (implies (and (x86-32p x86-32)
                (natp n)
                (< n 3)
                (n32p (+ (rgfi *mr-esp* x86-32) 3))
                (f-stack-okp n (rgfi *mr-esp* x86-32))
                (let ((eip (cdr (assoc-eq 'call-fib *fib-symbol-table*))))
                  (poised-at-fib n eip x86-32)))
           (let ((x86-32 (y86 x86-32 (fib-count n))))
             (equal (rgfi *mr-eax* x86-32)
                    (fib n))))
  :hints (("Goal" :use y86-fib-correct-up-to-3-reduced
           :in-theory (union-theories '(rgfi-0-y86-reduce-fib
                                        poised-at-fib
                                        natp-rgfi)
                                      (theory 'minimal-theory)))))
