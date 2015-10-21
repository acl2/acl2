; Copyright (C) 2001 J Strother Moore

; This book is free software; you can redistribute it and/or
; modify it under the terms of the GNU General Public License as
; published by the Free Software Foundation; either version 2 of
; the License, or (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public
; License along with this book; if not, write to the Free
; Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139,
; USA.

#|
; Certification Instructions.

(include-book "m5")

(certify-book "utilities" 1)

J Moore
|#

(in-package "M5")

; Here we develop the general theory for proving things about the
; M5 bytecode.

; Arithmetic

(include-book "arithmetic/top-with-meta" :dir :system)

; We prove a few things about int arithmetic.  We ought to prove
; many more, but I just put enough here to get the factorial
; proof to go through.

(include-book "ihs/quotient-remainder-lemmas" :dir :system)

(defun intp (x)
  (and (integerp x)
       (<= (- (expt 2 31)) x)
       (< x (expt 2 31))))

(defthm int-lemma0
  (implies (intp x)
           (integerp x))
  :rule-classes (:rewrite :forward-chaining))

(defthm int-lemma1
  (intp (int-fix x)))

(local (in-theory (cons 'zp (disable mod))))

(defthm int-lemma2
  (implies (and (intp x)
                (not (zp x)))
           (equal (int-fix (+ -1 x))
                  (+ -1 x))))

(defthm int-lemma3
  (implies (and (intp x)
                (not (zp x)))
           (intp (+ -1 x))))

(defthm int-lemma4a
  (implies (and (integerp x)
                (integerp y))
           (equal (int-fix (* x (int-fix y)))
                  (int-fix (* x y)))))

(defthm int-lemma5a
  (implies (and (integerp x)
                (integerp y))
           (equal (int-fix (+ x (int-fix y)))
                  (int-fix (+ x y)))))

; This is a special case of the above.  I need a more general
; handling of this, but this will do for the moment.

(defthm int-lemma5a1
  (implies (and (integerp x1)
                (integerp x2)
                (integerp y))
           (equal (int-fix (+ x1 x2 (int-fix y)))
                  (int-fix (+ x1 x2 y))))
  :hints (("Goal" :use (:instance int-lemma5a (x (+ x1 x2))))))

(defthm int-lemma6
  (implies (intp x)
           (equal (int-fix x) x)))

(in-theory (disable intp int-fix))

(defthm int-lemma4b
  (implies (and (integerp x)
                (integerp y))
           (equal (int-fix (* (int-fix y) x))
                  (int-fix (* y x)))))

(defthm int-lemma5b
  (implies (and (integerp x)
                (integerp y))
           (equal (int-fix (+ (int-fix y) x))
                  (int-fix (+ y x)))))

; Structures

(defthm states
  (and (equal (thread-table (make-state tt h c)) tt)
       (equal (heap (make-state tt h c)) h)
       (equal (class-table (make-state tt h c)) c)))

(in-theory (disable make-state thread-table heap class-table))

(defthm frames
  (and
   (equal (pc (make-frame pc l s prog sync-flg cur-class))
          pc)
   (equal (locals (make-frame pc l s prog sync-flg cur-class))
          l)
   (equal (stack (make-frame pc l s prog sync-flg cur-class))
          s)
   (equal (program (make-frame pc l s prog sync-flg cur-class))
          prog)
   (equal (sync-flg (make-frame pc l s prog sync-flg cur-class))
          sync-flg)
   (equal (cur-class (make-frame pc l s prog sync-flg cur-class))
          cur-class)))

(in-theory
 (disable make-frame pc locals stack program sync-flg cur-class))

(defthm stacks
  (and (equal (top (push x s)) x)
       (equal (pop (push x s)) s)))

(in-theory (disable push top pop))

; Mappings

(defthm assoc-equal-bind
  (equal (assoc-equal key1 (bind key2 val alist))
         (if (equal key1 key2)
             (cons key1 val)
           (assoc-equal key1 alist))))

(defthm bind-bind
  (equal (bind x v (bind x w a))
         (bind x v a)))

; Semi-Ground Terms

(defthm bind-formals-opener
  (implies (and (integerp n)
                (<= 0 n))
           (equal (bind-formals (+ 1 n) stack)
                  (cons (top stack)
                        (bind-formals n (pop stack))))))

(defthm nth-opener
  (and (equal (nth 0 lst) (car lst))
       (implies (and (integerp n)
                     (<= 0 n))
                (equal (nth (+ 1 n) lst)
                       (nth n (cdr lst))))))

(in-theory (disable nth))

(defthm popn-opener
  (implies (and (integerp n)
                (<= 0 n))
           (equal (popn (+ 1 n) stack)
                  (popn n (pop stack)))))

(defun repeat (th n)
  (if (zp n)
      nil
    (cons th (repeat th (- n 1)))))

(defthm repeat-opener
  (implies (and (integerp n)
                (<= 0 n))
           (equal (repeat th (+ 1 n))
                  (cons th (repeat th n)))))

; The nil conjunct below is needed because we will disable run.

(defthm run-opener
  (and (equal (run nil s) s)
       (equal (run (cons th sched) s)
              (run sched (step th s))))
  :hints (("Goal" :in-theory (disable step))))

;(in-theory (enable top pop push lookup-method lookup-class-method))

; Step Stuff

(defthm step-opener
  (implies (consp (next-inst th s))
           (equal (step th s)
                  (if (equal (status th s) 'SCHEDULED)
                      (do-inst (next-inst th s) th s)
                    s)))
  :hints (("Goal" :in-theory (disable do-inst))))

(in-theory (disable step))

; Clocks



(defthm run-append
  (equal (run (append sched1 sched2) s)
         (run sched2 (run sched1 s))))

(in-theory (disable run))

