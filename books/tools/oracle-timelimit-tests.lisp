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


; Test of basic one-valued form that should succeed, inside a function
(defun test1 (state)
  (b* (((mv time bytes ans state) (oracle-timelimit 100 (fib 6)))
       ((unless (and (rationalp time)
                     (<= 0 time)))
        (er hard? 'oracle-timelimit "Failed to execute (fib 6) in 100 seconds?")
        state)
       ((unless (natp bytes))
        (er hard? 'oracle-timelimit "Bytes aren't a natural?")
        state)
       ((unless (equal ans (fib 6)))
        (er hard? 'oracle-timelimit "Wrong answer for (fib 6)")
        state))
    state))

(make-event
 (let ((state (test1 state)))
   (value '(value-triple :success))))



; Test of basic one-valued form that should succeed, inside a make-event
(make-event
 (b* (((mv time bytes ans state) (oracle-timelimit 100 (fib 6)))
      ((unless (and (rationalp time)
                    (<= 0 time)))
       (er soft 'oracle-timelimit "Failed to execute (fib 6) in 100 seconds?"))
      ((unless (natp bytes))
       (er soft 'oracle-timelimit "Bytes aren't a natural?"))
      ((unless (equal ans (fib 6)))
       (er soft 'oracle-timelimit "Wrong answer for (fib 6)")))
   (value '(value-triple :success))))



;; Test a basic form that should fail, inside a function
(defun test2 (state)
 (b* (((mv time bytes ans state) (oracle-timelimit 1/10
                                                   (sleep 3)
                                                   :onfail 43))
      ((when time)
       (er hard? 'oracle-timelimit "Failed to stop a (sleep 3).")
       state)
      ((unless (equal ans 43))
       (er hard? 'oracle-timelimit "Wrong answer for timeout.")
       state)
      ((unless (equal bytes nil))
       (er hard? 'oracle-timelimit "Wrong BYTES for timeout.")
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



; Test of basic two-valued form that should succeed, inside a function
(defun test3 (state)
  (b* (((mv time bytes ans-a ans-b state)
        (oracle-timelimit 100
                          (mv (fib 6) (fib 7))
                          :ret (mv a b)
                          :onfail (mv 17 43)))
       ((unless (and (rationalp time)
                     (<= 0 time)))
        (er hard? 'oracle-timelimit "Failed to execute (fib 6) in 100 seconds?")
        state)
       ((unless (natp bytes))
        (er hard? 'oracle-timelimit "Bytes aren't a natural?")
        state)
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

; Test of basic two-valued form that should succeed, in a make-event
(make-event
 (b* (((mv time bytes ans-a ans-b state)
       (oracle-timelimit 100
                         (mv (fib 6) (fib 7))
                         :ret (mv a b)
                         :onfail (mv 17 43)))
      ((unless (and (rationalp time)
                    (<= 0 time)))
       (er soft 'oracle-timelimit "Failed to execute (fib 6) in 100 seconds?"))
      ((unless (natp bytes))
       (er soft 'oracle-timelimit "Bytes aren't a natural?"))
      ((unless (equal ans-a (fib 6)))
       (er soft 'oracle-timelimit "Wrong answer for (fib 6)"))
      ((unless (equal ans-b (fib 7)))
       (er soft 'oracle-timelimit "Wrong answer for (fib 7)")))
   (value '(value-triple :success))))



; Test of basic two-valued form that should timeout, inside a function
(defun test4 (state)
  (b* (((mv time bytes ans-a ans-b state)
        (oracle-timelimit 1/10
                          (mv (sleep 3) (fib 7))
                          :ret (mv a b)
                          :onfail (mv 17 43)))
       ((when time)
        (er hard? 'oracle-timelimit "Slept for 3 seconds in 1/10 of a second?")
        state)
       ((when bytes)
        (er hard? 'oracle-timelimit "Bytes aren't NIL?")
        state)
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



; Test of a form that should cause an error.  This might not cause an error on
; all Lisps and may need some conditionals...
(defun test5 (state)
  (declare (xargs :mode :program))
  (b* (((mv time bytes ans state)
        (oracle-timelimit 100
                          (car 3)
                          :onfail 99
                          :suppress-lisp-errors t))
       ((when time)
        (er hard? 'oracle-timelimit "Expected no time for simulated error.")
        state)
       ((when bytes)
        (er hard? 'oracle-timelimit "Expected no bytes for simulated error.")
        state)
       ((unless (equal ans 99))
        (er hard? 'oracle-timelimit "Wrong answer for simulated error.")
        state))
    state))

(make-event
 (let ((state (test5 state)))
   (value '(value-triple :success))))

(defun test6 (state)
  (declare (xargs :mode :program))
  (b* (((mv time bytes ans state)
        (oracle-timelimit 100
                          (ash 1 (ash 1 10000))
                          :onfail 99
                          :suppress-lisp-errors t))
       ((when time)
        (er hard? 'oracle-timelimit "Expected no time for simulated error.")
        state)
       ((when bytes)
        (er hard? 'oracle-timelimit "Expected no bytes for simulated error.")
        state)
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
  (b* (((mv time bytes ans state)
        (oracle-timelimit 100
                          (stack-overflow '(3))
                          :onfail 99
                          :suppress-lisp-errors t))
       ((when time)
        (er hard? 'oracle-timelimit "Expected no time for simulated error.")
        state)
       ((when bytes)
        (er hard? 'oracle-timelimit "Expected no bytes for simulated error.")
        state)
       ((unless (equal ans 99))
        (er hard? 'oracle-timelimit "Wrong answer for simulated error.")
        state))
    state))

(make-event
 (let ((state (test7 state)))
   (value '(value-triple :success))))




(defun test8 (state)
  (declare (xargs :mode :program))
  (b* (((mv time bytes ans state)
        (oracle-timelimit 100
                          (er hard? 'test8 "causing an acl2-style ER")
                          :onfail 99
                          :suppress-lisp-errors t))
       ((when time)
        (er hard? 'oracle-timelimit "Expected no time for simulated error.")
        state)
       ((when bytes)
        (er hard? 'oracle-timelimit "Expected no bytes for simulated error.")
        state)
       ((unless (equal ans 99))
        (er hard? 'oracle-timelimit "Wrong answer for simulated error.")
        state))
    state))

(make-event
 (let ((state (test8 state)))
   (value '(value-triple :success))))


(defun test9 (x state)
  (declare (xargs :mode :logic :verify-guards nil))
  (b* (((mv time bytes ans state)
        (oracle-timelimit 100
                          (car x) ;; guard violation
                          :onfail 99
                          :suppress-lisp-errors t))
       ((when time)
        (er hard? 'oracle-timelimit "Expected no time for simulated error, but got ~x0" time)
        state)
       ((when bytes)
        (er hard? 'oracle-timelimit "Expected no bytes for simulated error.")
        state)
       ((unless (equal ans 99))
        (er hard? 'oracle-timelimit "Wrong answer for simulated error.")
        state))
    state))

(make-event
 ;; BOZO too bad this doesn't explain what the error was.
 (let ((state
        (with-guard-checking :all (test9 5 state))))
   (value '(value-triple :success))))
