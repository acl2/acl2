(in-package "ACL2")

; Serial version of Fibonacci

(defun fib (x)
  (declare (xargs :guard (natp x)))
  (cond ((mbe :logic (or (zp x) (<= x 0))
              :exec (<= x 0))
         0)
        ((= x 1)
         1)

        (t
         (let ((a (fib (- x 1)))
               (b (fib (- x 2))))

           (+ a b)))))


; Parallelized version of Fibonacci, using plet

(defun pfib (x)
  (declare (xargs :guard (natp x)))
  (cond ((mbe :logic (or (zp x) (<= x 0))
              :exec (<= x 0))
         0)
        ((= x 1)
         1)

        (t
         (plet
          (declare (granularity (> x 27)))

          ((a (pfib (- x 1)))
           (b (pfib (- x 2))))

          (binary-+ a b)))))


; Parallel version of Fibonacci, using pcall
#|
(defun pfib (x)
  (declare (xargs :guard (natp x)))
  (cond ((mbe :logic (or (zp x) (<= x 0))
              :exec (<= x 0))
         0)
        ((= x 1)
         1)

        (t
         (pcall
          (declare (granularity (> x 27)))

          (binary-+ (pfib (- x 1))
                    (pfib (- x 2)))))))
|#







#|
; Results


ACL2 !>
(princ$ "Testing Fib (47)" *standard-co* state)

(time$ (fib 47))
(time$ (fib 47))
(time$ (fib 47))

(time$ (pfib 47))
(time$ (pfib 47))
(time$ (pfib 47))

(princ$ "Done Testing Fib" *standard-co* state)

Testing Fib (47)<state>
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 326,015 milliseconds (326.015 seconds) to run.
Of that, 325,938 milliseconds (325.938 seconds) were spent in user mode
         79 milliseconds (0.079 seconds) were spent in system mode
 120 bytes of memory allocated.
2971215073
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 325,813 milliseconds (325.813 seconds) to run.
Of that, 325,748 milliseconds (325.748 seconds) were spent in user mode
         79 milliseconds (0.079 seconds) were spent in system mode
 120 bytes of memory allocated.
2971215073
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 325,818 milliseconds (325.818 seconds) to run.
Of that, 325,753 milliseconds (325.753 seconds) were spent in user mode
         79 milliseconds (0.079 seconds) were spent in system mode
 120 bytes of memory allocated.
2971215073
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 85,968 milliseconds (85.968 seconds) to run.
Of that, 342,772 milliseconds (342.772 seconds) were spent in user mode
         429 milliseconds (0.429 seconds) were spent in system mode
24 milliseconds (0.024 seconds) was spent in GC.
 3,496 bytes of memory allocated.
2971215073
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 86,148 milliseconds (86.148 seconds) to run.
Of that, 343,121 milliseconds (343.121 seconds) were spent in user mode
         586 milliseconds (0.586 seconds) were spent in system mode
87 milliseconds (0.087 seconds) was spent in GC.
 336 bytes of memory allocated.
2971215073
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 86,228 milliseconds (86.228 seconds) to run.
Of that, 343,345 milliseconds (343.345 seconds) were spent in user mode
         597 milliseconds (0.597 seconds) were spent in system mode
95 milliseconds (0.095 seconds) was spent in GC.
 336 bytes of memory allocated.
2971215073
ACL2 !>Done Testing Fib<state>
ACL2 !>



|#