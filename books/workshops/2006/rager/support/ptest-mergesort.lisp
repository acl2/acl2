(in-package "SET")

;;;;;;;;;;;;;;;; Tests for ACL2 parallelization paper ;;;;;;;;;;;;;

; We originally needed version 0.91 of the sets library, which includes a tail
; recursive version of split-list.  This version is distributed with ACL2 3.0.
;
; We changed this book to use halve-list instead of split-list in 2012.
;
; This book shouldn't be included in any other book.  Beyond containing silly
; definitions, it is probably unsound (see the definition of mergesort-exec-par
; below).

(include-book "std/osets/top" :dir :system)

(defun integers (n acc)
; Matt K.: Added guard declaration to avoid stack overflow when building
; compiled file for Lisps including Allegro CL and LispWorks.
  (declare (xargs :guard (and (natp n)
                              (true-listp acc))))
  (if (zp n)
      (reverse acc)
    (integers (1- n) (cons n acc))))

(comp t)

(defconst *my-ints*
  (integers 2000000 nil))

; Non parallel version is in effect by default

#|
(skip-proofs
 (defun SET::mergesort-exec (x)
   (declare (xargs :guard t))
   (cond ((endp x) nil)
         ((endp (cdr x)) (SET::insert (car x) nil))
         (t (mv-let (part1 part2)
                    (SET::halve-list x)
                    (SET::union (SET::mergesort-exec part1)
                                 (SET::mergesort-exec part2)))))))
|#

;; (princ$ "Non parallel version is in effect" *standard-co* state)

;; (time$ (prog2$ (SET::mergesort-exec *my-ints*) t))
;; (time$ (prog2$ (SET::mergesort-exec *my-ints*) t))
;; (time$ (prog2$ (SET::mergesort-exec *my-ints*) t))

(skip-proofs
 (defun SET::mergesort-exec-par (x depth)
   (declare (xargs :guard

; This guard is insufficient, so the above skip-proofs is clearly unsound.

                   t))
   (cond ((endp x) nil)
         ((endp (cdr x)) (SET::insert (car x) nil))
         (t (mv-let (part1 part2)
                    (SET::halve-list x)
                    (ACL2::pargs ; was pcall in the paper
                     (declare (granularity (< depth 2)))
                     (SET::union (SET::mergesort-exec-par part1
                                                        (1+ depth))
                                  (SET::mergesort-exec-par part2
                                                        (1+ depth)))))))))

;; (princ$ "Parallel version with depth granularity is in effect" *standard-co* state)
;; (time$ (prog2$ (SET::mergesort-exec-par *my-ints* 0) t))
;; (time$ (prog2$ (SET::mergesort-exec-par *my-ints* 0) t))
;; (time$ (prog2$ (SET::mergesort-exec-par *my-ints* 0) t))

#|

; Results

ACL2 !>
(princ$ "Non parallel version is in effect" *standard-co* state)

(time$ (prog2$ (SET::mergesort-exec *my-ints*) t))
(time$ (prog2$ (SET::mergesort-exec *my-ints*) t))
(time$ (prog2$ (SET::mergesort-exec *my-ints*) t))
Non parallel version is in effect<state>
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 24,771 milliseconds (24.771 seconds) to run.
Of that, 21,701 milliseconds (21.701 seconds) were spent in user mode
         1,545 milliseconds (1.545 seconds) were spent in system mode
         1,525 milliseconds (1.525 seconds) were spent executing other OS processes.
12,627 milliseconds (12.627 seconds) was spent in GC.
 989,668,480 bytes of memory allocated.
T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 24,523 milliseconds (24.523 seconds) to run.
Of that, 21,538 milliseconds (21.538 seconds) were spent in user mode
         1,461 milliseconds (1.461 seconds) were spent in system mode
         1,524 milliseconds (1.524 seconds) were spent executing other OS processes.
12,439 milliseconds (12.439 seconds) was spent in GC.
 989,668,480 bytes of memory allocated.
T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 24,213 milliseconds (24.213 seconds) to run.
Of that, 21,243 milliseconds (21.243 seconds) were spent in user mode
         1,438 milliseconds (1.438 seconds) were spent in system mode
         1,532 milliseconds (1.532 seconds) were spent executing other OS processes.
12,148 milliseconds (12.148 seconds) was spent in GC.
 989,668,480 bytes of memory allocated.
T

; snip: pasted the parallel version

ACL2 !>(princ$ "Parallel version with depth granularity is in effect" *standard-co* state)
(time$ (prog2$ (SET::mergesort-exec-par *my-ints* 0) t))
(time$ (prog2$ (SET::mergesort-exec-par *my-ints* 0) t))
(time$ (prog2$ (SET::mergesort-exec-par *my-ints* 0) t))

Parallel version with depth granularity is in effect<state>
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 23,993 milliseconds (23.993 seconds) to run.
Of that, 30,563 milliseconds (30.563 seconds) were spent in user mode
         1,985 milliseconds (1.985 seconds) were spent in system mode
19,847 milliseconds (19.847 seconds) was spent in GC.
 48,003,464 bytes of memory allocated.
T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 23,929 milliseconds (23.929 seconds) to run.
Of that, 30,469 milliseconds (30.469 seconds) were spent in user mode
         1,987 milliseconds (1.987 seconds) were spent in system mode
19,823 milliseconds (19.823 seconds) was spent in GC.
 48,000,392 bytes of memory allocated.
T
ACL2 !>
(EV-REC (FARGN FORM 1) ALIST W (DECREMENT-BIG-N BIG-N) SAFE-MODE GC-OFF LATCHES HARD-ERROR-RETURNS-NILP) took 23,821 milliseconds (23.821 seconds) to run.
Of that, 30,339 milliseconds (30.339 seconds) were spent in user mode
         1,980 milliseconds (1.980 seconds) were spent in system mode
19,705 milliseconds (19.705 seconds) was spent in GC.
 48,000,392 bytes of memory allocated.
T
ACL2 !>

|#
