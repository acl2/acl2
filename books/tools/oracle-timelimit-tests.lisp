; Oracle Timing
; Copyright (C) 2015 Kestrel Institute (http://www.kestrel.edu)
;
; License: (An MIT license):
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original authors: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "oracle-timelimit")
(set-state-ok t)

(defun fib (n)
  (if (zp n)
      1
    (if (equal n 1)
        1
      (+ (fib (- n 1))
         (fib (- n 2))))))

(defun check-time-and-bytes (time bytes)
  (and (or (and (rationalp time)
                (<= 0 time))
           (er hard? 'oracle-timelimit "Bad time: ~x0~%" time))
       (or (natp bytes)
           (er hard? 'oracle-timelimit "Bad bytes: ~x0~%" bytes))))

(defun test1 (state)
  (b* ((- (cw "Test of basic one-valued form that should succeed, inside a function~%"))
       ((mv successp time bytes ans state) (oracle-timelimit 100 (fib 6)))
       ((unless successp)
        (er hard? 'oracle-timelimit "Failed to execute (fib 6) in 100 seconds?")
        state)
       (- (check-time-and-bytes time bytes))
       ((unless (equal ans (fib 6)))
        (er hard? 'oracle-timelimit "Wrong answer for (fib 6)")
        state))
    state))

(make-event
 (let ((state (test1 state)))
   (value '(value-triple :success))))




(make-event
 (b* ((- (cw "Test of basic one-valued form that should succeed, inside a make-event~%"))
      ((mv successp time bytes ans state) (oracle-timelimit 100 (fib 6)))
      ((unless successp)
       (er soft 'oracle-timelimit "Failed to execute (fib 6) in 100 seconds?"))
      (- (check-time-and-bytes time bytes))
      ((unless (equal ans (fib 6)))
       (er soft 'oracle-timelimit "Wrong answer for (fib 6)")))
   (value '(value-triple :success))))



(defun test2 (state)
 (b* ((- (cw "Test a basic form that should fail, inside a function~%"))
      ((mv successp time bytes ans state) (oracle-timelimit 1/10
                                                            (sleep 3)
                                                            :onfail 43))
      ((when successp)
       (er hard? 'oracle-timelimit "Failed to stop a (sleep 3).")
       state)
      (- (check-time-and-bytes time bytes))
      ((unless (and (<= 1/20 time)
                    (<= time 1)))
       (er hard? 'oracle-timelimit "Time to stop a (sleep 3) seems incorrect: ~x0.~%" time)
       state)
      ((unless (equal ans 43))
       (er hard? 'oracle-timelimit "Wrong answer for timeout.")
       state))
   state))

(make-event
 (let ((state (test2 state)))
   (value '(value-triple :success))))


;; BOZO there are all kinds of problems with failure case at the top level...
#||

;; This works just fine:
(test2 state)

;; But calling this directly produces a crazy error:
(oracle-timelimit 1/10 (sleep 3) :onfail 99)

HARD ACL2 ERROR in GETPROP:  No property was found under symbol
COMMAND-LANDMARK for key GLOBAL-VALUE.  GLOBAL-VAL didn't find a value.
Initialize this symbol in PRIMORDIAL-WORLD-GLOBALS.

BOZO what is going on here?

;; A better test to eventually get working:
(b* (((mv time bytes ans state) (oracle-timelimit 1/10
                                                   (sleep 3)
                                                   :onfail 99))
      ((when time)
       (er hard? 'oracle-timelimit "Failed to stop a (sleep 3).")
       state)
      ((unless (equal ans 99))
       (er hard? 'oracle-timelimit "Wrong answer for timeout.")
       state)
      ((unless (equal bytes nil))
       (er hard? 'oracle-timelimit "Wrong BYTES for timeout.")
       state))
   state)

;; Using it in a Make-event also produces the same crazy error.  After
;; adding tons of debugging output, the core exec function really is
;;
(make-event
 (b* (((mv time bytes ans state) (oracle-timelimit 1/10
                                                   (prog2$ (sleep 3) 17)
                                                   :onfail 43))
      ((when time)
       (er soft 'oracle-timelimit "Failed to stop a (sleep 3)."))
      ((unless (equal ans 43))
       (er soft 'oracle-timelimit "Wrong answer for timeout."))
      ((unless (equal bytes nil))
       (er soft 'oracle-timelimit "Wrong BYTES for timeout.")))
   (value '(value-triple :success))))

||#



(defun test3 (state)
  (b* ((- (cw "Test of basic two-valued form that should succeed, inside a function~%"))
       ((mv successp time bytes ans-a ans-b state)
        (oracle-timelimit 100
                          (mv (fib 6) (fib 7))
                          :ret (mv a b)
                          :onfail (mv 17 43)))
       ((unless successp)
        (er hard? 'oracle-timelimit "Failed to execute (fib 6) and (fib 7) in 100 seconds?")
        state)
       (- (check-time-and-bytes time bytes))
       ((unless (equal ans-a (fib 6)))
        (er hard? 'oracle-timelimit "Wrong answer for (fib 6)")
        state)
       ((unless (equal ans-b (fib 7)))
        (er hard? 'oracle-timelimit "Wrong answer for (fib 7)")
        state))
    state))

(make-event
 (let ((state (test3 state)))
   (value '(value-triple :success))))

(make-event
 (b* ((- (cw "Test of basic two-valued form that should succeed, in a make-event~%"))
      ((mv successp time bytes ans-a ans-b state)
       (oracle-timelimit 100
                         (mv (fib 6) (fib 7))
                         :ret (mv a b)
                         :onfail (mv 17 43)))
      ((unless successp)
       (er soft 'oracle-timelimit "Failed to execute (fib 6) and (fib 7) in 100 seconds?"))
      (- (check-time-and-bytes time bytes))
      ((unless (equal ans-a (fib 6)))
       (er soft 'oracle-timelimit "Wrong answer for (fib 6)"))
      ((unless (equal ans-b (fib 7)))
       (er soft 'oracle-timelimit "Wrong answer for (fib 7)")))
   (value '(value-triple :success))))


(defun test4 (state)
  (b* ((- (cw "Test of basic two-valued form that should timeout, inside a function~%"))
       ((mv successp time bytes ans-a ans-b state)
        (oracle-timelimit 1/10
                          (mv (sleep 3) (fib 7))
                          :ret (mv a b)
                          :onfail (mv 17 43)))
       ((when successp)
        (er hard? 'oracle-timelimit "Slept for 3 seconds in 1/10 of a second?")
        state)
       (- (check-time-and-bytes time bytes))
       ((unless (equal ans-a 17))
        (er hard? 'oracle-timelimit "Wrong answer for ans-a.")
        state)
       ((unless (equal ans-b 43))
        (er hard? 'oracle-timelimit "Wrong answer for ans-b.")
        state))
    state))

#||

;; BOZO this has the same bug. :(

; Test of basic two-valued form that should timeout, in a make-event
(make-event
  (b* (((mv time bytes ans-a ans-b state)
        (oracle-timelimit 1/10
                          (mv (sleep 3) (fib 7))
                          :ret (mv a b)
                          :onfail (mv 17 43)))
       ((when time)
        (er soft 'oracle-timelimit "Slept for 3 seconds in 1/10 of a second?"))
       ((when bytes)
        (er soft 'oracle-timelimit "Bytes aren't NIL?"))
       ((unless (equal ans-a 17))
        (er soft 'oracle-timelimit "Wrong answer for ans-a."))
       ((unless (equal ans-b 43))
        (er soft 'oracle-timelimit "Wrong answer for ans-b.")))
    (value '(value-triple :success))))

||#




(defun test5 (state)
  (declare (xargs :mode :program))
  (b* ((- (cw "Test of a form that should cause an error.  This might not ~
               cause an error on all Lisps and may need some conditionals...~%"))
       ((mv successp time bytes ans state)
        (oracle-timelimit 100
                          (car 3)
                          :onfail 99
                          :suppress-lisp-errors t))
       ((when successp)
        (er hard? 'oracle-timelimit "Somehow succeeded in executing (car 3)?~%")
        state)
       (- (check-time-and-bytes time bytes))
       ((unless (equal ans 99))
        (er hard? 'oracle-timelimit "Wrong answer for simulated error.")
        state))
    state))

(make-event
 (let ((state (test5 state)))
   (value '(value-triple :success))))

(defun test6 (state)
  (declare (xargs :mode :program))
  (b* ((- (cw "Test of a form that should create an insanely big number to cause an error.~%"))
       ((mv successp time bytes ans state)
        (oracle-timelimit 100
                          (ash 1 (ash 1 10000))
                          :onfail 99
                          :suppress-lisp-errors t))
       ((when successp)
        (er hard? 'oracle-timelimit "Somehow created enormous number successfully?")
        state)
       (- (check-time-and-bytes time bytes))
       ((unless (equal ans 99))
        (er hard? 'oracle-timelimit "Wrong answer for simulated error.")
        state))
    state))

(make-event
 (let ((state (test6 state)))
   (value '(value-triple :success))))



(defun stack-overflow (x)
  (declare (xargs :mode :program))
  (if (atom x)
      nil
    (append x
            (stack-overflow x))))

(defun test7 (state)
  (declare (xargs :mode :program))
  (b* ((- (cw "Test of a form that should stack overflow.~%"))
       ((mv successp time bytes ans state)
        (oracle-timelimit 100
                          (stack-overflow '(3))
                          :onfail 99
                          :suppress-lisp-errors t))
       ((when successp)
        (er hard? 'oracle-timelimit "Succeeded in infinite computation?")
        state)
       (- (check-time-and-bytes time bytes))
       ((unless (equal ans 99))
        (er hard? 'oracle-timelimit "Wrong answer for simulated error.")
        state))
    state))

(make-event
 (let ((state (test7 state)))
   (value '(value-triple :success))))




(defun test8 (state)
  (declare (xargs :mode :program))
  (b* ((- (cw "Test of a form that should cause an ACL2-style ER.~%"))
       ((mv successp time bytes ans state)
        (oracle-timelimit 100
                          (er hard? 'test8 "causing an acl2-style ER")
                          :onfail 99
                          :suppress-lisp-errors t))
       ((when successp)
        (er hard? 'oracle-timelimit "Calling ER didn't cause an error?")
        state)
       (- (check-time-and-bytes time bytes))
       ((unless (equal ans 99))
        (er hard? 'oracle-timelimit "Wrong answer for simulated error.")
        state))
    state))

(make-event
 (let ((state (test8 state)))
   (value '(value-triple :success))))


(defun test9 (x state)
  (declare (xargs :mode :logic :verify-guards nil))
  (b* ((- (cw "Test of a form that should cause a guard violation.~%"))
       ((mv successp time bytes ans state)
        (oracle-timelimit 100
                          (car x) ;; guard violation
                          :onfail 99
                          :suppress-lisp-errors t))
       ((when successp)
        (er hard? 'oracle-timelimit "Guard didn't get violated?")
        (value nil))
       (- (check-time-and-bytes time bytes))
       ((unless (equal ans 99))
        (er hard? 'oracle-timelimit "Wrong answer for simulated error.")
        (value nil)))
    (value nil)))

(make-event
 ;; BOZO too bad this doesn't explain what the error was.
 (er-progn (with-guard-checking-error-triple :all (test9 5 state))
           (value '(value-triple :success))))



; Test of a runaway memory scenario

(defun allocate-gobs-of-nonsense (n acc)
  (if (zp n)
      acc
    (allocate-gobs-of-nonsense (- n 1)
                               (cons (make-list 1000) acc))))

;; (time$ (prog2$ (allocate-gobs-of-nonsense 1000 nil) nil)) ;; Allocates about 16 MB.

(defun slowly-allocate-gobs-of-nonsense (n acc)  ;; So this should allocate about 160 MB per second.
  (if (zp n)
      acc
    (progn$ (sleep 1/10)
            (cw "Allocating slice ~x0~%" n)
            (let ((acc (allocate-gobs-of-nonsense 1000 acc)))
              (slowly-allocate-gobs-of-nonsense (- n 1) acc)))))

;; (time$ (prog2$ (slowly-allocate-gobs-of-nonsense 10 nil) nil)) ;; 160 MB, 2 seconds.
;; Aha, probably 2 seconds because it actually takes real time to allocate things.
;; OK, at any rate, we can up it to something like 2 GB like this...
;;
;; (time$ (prog2$ (slowly-allocate-gobs-of-nonsense 120 nil) nil))
;;    23.43 seconds realtime, 11.46 seconds runtime, 1,921,923,872 bytes allocated

(defun test10 (state)
  (b* (((mv successp time bytes ans state)
        (oracle-timelimit 100
                          (slowly-allocate-gobs-of-nonsense 120 nil)
                          ;; Do not use more than 800 MB of memory
                          :maxmem (* 800 1024 1024)))
       ((when successp)
        (er hard? 'oracle-timelimit "Failed to stop insane allocation?")
        state)
       (- (check-time-and-bytes time bytes))
       (- (cw "Stopped with time ~x0, bytes ~x1~%" time bytes))
       ((when ans)
        (er hard? 'oracle-timelimit "Expected answer to be nil.")
        state))
    state))

#+Clozure
(make-event
 (let ((state (time$ (test10 state))))
   (value '(value-triple :success))))
