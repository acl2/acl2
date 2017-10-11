;; Copyright (C) 2015, Julien Schmaltz.
;;
;; License: (An MIT/X11-style license)
;;
;;   Permission is hereby granted, free of charge, to any person obtaining a
;;   copy of this software and associated documentation files (the "Software"),
;;   to deal in the Software without restriction, including without limitation
;;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;;   and/or sell copies of the Software, and to permit persons to whom the
;;   Software is furnished to do so, subject to the following conditions:
;;
;;   The above copyright notice and this permission notice shall be included in
;;   all copies or substantial portions of the Software.
;;
;;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;   DEALINGS IN THE SOFTWARE.
;;
;; Original author: Julien Schmaltz <julien.schmaltz@gmail.com>

(in-package "ACL2")

(include-book "avr8_isa")

; Arithmetic

;(include-book "arithmetic-5/top" :dir :system)

; Abstract Data Type Stuff

(defthm stacks
  (and (equal (atop (apush x s)) x)
       (equal (apop (apush x s)) s)

; These next two are needed because some push expressions evaluate to
; list constants, e.g., (push 1 (push 2 nil)) becomes '(1 2) and '(1
; 2) pattern-matches with (cons x s) but not with (push x s).

       (equal (atop (cons x s)) x)
       (equal (apop (cons x s)) s)))

(in-theory (disable apush atop apop (:executable-counterpart apush)))

(defthm states
  (and (equal (apc     (make-state pc regs flags stack program memory)) pc)
       (equal (regs    (make-state pc regs flags stack program memory)) regs)
       (equal (flags   (make-state pc regs flags stack program memory)) flags)
       (equal (stack   (make-state pc regs flags stack program memory)) stack)
       (equal (prg     (make-state pc regs flags stack program memory)) program)
       (equal (memory  (make-state pc regs flags stack program memory)) memory)
; And we add the rules to handle constant states:

       (equal (apc (cons pc x)) pc)
       (equal (regs (cons pc (cons regs x))) regs)
       (equal (flags (cons pc (cons regs (cons flags x)))) flags)
       (equal (stack (cons pc (cons regs (cons flags (cons stack x))))) stack)
       (equal (prg (cons pc (cons locals (cons flags (cons stack (cons program x))))))
              program)
       (equal (memory (cons pc (cons locals (cons flags (cons stack (cons program (cons memory x)))))))
              memory)))


(in-theory (disable make-state apc regs stack flags prg
                    (:executable-counterpart make-state)))

; Step Stuff

(defthm step-opener
  (implies (consp (next-inst s))
           (equal (avr-step s)
                  (do-inst (next-inst s) s))))

(in-theory (disable avr-step))

; Schedules and Run

(defthm run-append
  (equal (run (append a b) s)
         (run b (run a s))))
  
(defthm run-opener
  (and (equal (run nil s) s)
       (equal (run (cons th sched) s)
              (run sched (avr-step s)))))

(in-theory (disable run))

; Nth and update-nth

(defthm nth-add1!
  (implies (natp n)
           (equal (nth (+ 1 n) list)
                  (nth n (cdr list)))))

(defthm update-nth-update-nth-1
  (implies (and (natp i) (natp j) (not (equal i j)))
           (equal (update-nth i v (update-nth j w list))
                  (update-nth j w (update-nth i v list))))
  :rule-classes ((:rewrite :loop-stopper ((i j update-nth)))))

(defthm update-nth-update-nth-2
  (equal (update-nth i v (update-nth i w list))
         (update-nth i v list)))


