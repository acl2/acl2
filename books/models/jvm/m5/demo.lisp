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

; This book proves the correctness of a recursive static method
; for factorial on M5.

(in-package "M5")
(include-book "jvm-fact-setup")

(defthm fact-is-correct
  (implies (poised-to-invoke-fact th s n)
           (equal
            (run (fact-sched th n) s)
            (modify th s
             :pc (+ 3 (pc (top-frame th s)))
             :stack (push (int-fix (! n))
                          (pop (stack (top-frame th s)))))))
  :hints (("Goal"
           :induct (induction-hint th s n))))

(in-theory (disable fact-sched))

(defthm weak-version-of-fact-is-correct
  (implies (poised-to-invoke-fact th s n)
           (equal (top
                   (stack
                    (top-frame
                     th
                     (run (fact-sched th n) s))))
                  (int-fix (! n)))))

; Symbolic Computation and Use of fact as a Subroutine

(defthm symbolic-computation
  (implies
   (intp (+ 1 k))
   (equal
    (nth 3
         (locals
          (top-frame 0
           (run (append (repeat 0 4)
                        (fact-sched 0 (+ 1 k))
                        (repeat 0 2))
                (make-state
                 (make-tt
                  (push
                   (make-frame 0
                               (list v0 v1 v2 k)
                               stk
                               '((iconst_2)
                                 (iload_3)
                                 (iconst_1)
                                 (iadd)
                                 (invokestatic 1) ; Demo.fact:(I)I
                                 (imul)
                                 (istore_3))
                               'unlocked
                               "Test")
                   nil))
                 *demo-heap*
                 (cons
                  (make-class-decl
                   "Test"
                   '("java/lang/Object")
                   ()
                   ()
                   '(nil
                     (methodref "Demo" "fact:(I)I" 1)) ; 1
                   ()
                   '(ref -1))
                  *demo-class-table*)
                 *default-m5-options*)))))
    (int-fix (* 2 (! (+ 1 k)))))))

; In the steps below we demonstrate the key steps in the
; simplification above, to check the claims made in the paper.

(defun alpha (pc locals stk)
  (make-state
   (make-tt
    (push (make-frame pc
                      locals
                      stk
                      '((iconst_2)
                        (iload_3)
                        (iconst_1)
                        (iadd)
                        (invokestatic 2) ; Demo.fact:(I)I
                        (imul)
                        (istore_3))
                      'UNLOCKED
                      "Demo")
          nil))
   *demo-heap*
   *demo-class-table*
   *default-m5-options*))

(defthm symbolic-computation-step1
  (implies
   (intp (+ 1 k))
   (equal (run (append (repeat 0 4)
                       (fact-sched 0 (+ 1 k))
                       (repeat 0 2))
               (alpha 0 (list v0 v1 v2 k) stk))
          (run (repeat 0 2)
               (run (fact-sched 0 (+ 1 k))
                    (run (repeat 0 4)
                         (alpha 0 (list v0 v1 v2 k) stk)))))))

(defthm symbolic-computation-step2
  (implies
   (intp (+ 1 k))
   (equal (run (repeat 0 4)
               (alpha 0 (list v0 v1 v2 k) stk))
          (alpha 4 (list v0 v1 v2 k)
                 (push (+ 1 k) (push 2 stk))))))

(defthm symbolic-computation-step3
  (implies
   (intp (+ 1 k))
   (equal (run (fact-sched 0 (+ 1 k))
               (alpha 4 (list v0 v1 v2 k)
                      (push (+ 1 k) (push 2 stk))))
          (alpha 7 (list v0 v1 v2 k)
                 (push (int-fix (! (+ 1 k)))
                       (push 2 stk))))))


(defthm symbolic-computation-step4
  (implies
   (intp (+ 1 k))
   (equal (run (repeat 0 2)
               (alpha 7 (list v0 v1 v2 k)
                      (push (int-fix (! (+ 1 k)))
                            (push 2 stk))))
          (alpha 9 (list v0 v1 v2
                         (int-fix
                          (* 2 (! (+ 1 k))))) stk))))

