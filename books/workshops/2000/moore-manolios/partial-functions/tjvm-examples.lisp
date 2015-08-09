;  Copyright (C) 2000 Panagiotis Manolios and J Strother Moore

;  This program is free software; you can redistribute it and/or modify
;  it under the terms of the GNU General Public License as published by
;  the Free Software Foundation; either version 2 of the License, or
;  (at your option) any later version.

;  This program is distributed in the hope that it will be useful,
;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;  GNU General Public License for more details.

;  You should have received a copy of the GNU General Public License
;  along with this program; if not, write to the Free Software
;  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;  Written by Panagiotis Manolios who can be reached as follows.

;  Email: pete@cs.utexas.edu, moore@cs.utexas.edu

;  Postal Mail:
;  Department of Computer Science
;  The University of Texas at Austin
;  Austin, TX 78701 USA

; (include-book "/v/hank/v104/text/tjvm/examples")
; (certify-book "tjvm-examples" 1)
(in-package "TJVM")

(include-book "defpun")

(defmacro defpun (&rest rest) (cons 'acl2::defpun rest))

(defun haltedp (s) (equal s (step s)))

(defpun stepw (s)
  (if (haltedp s)
      s
    (stepw (step s))))

(defun == (a b)(equal (stepw a) (stepw b)))

(defequiv ==)

(in-theory (disable step-opener))

(defthm stepw-step
  (equal (stepw s) (stepw (step s)))
  :rule-classes nil)

; This event is here only so we can exhibit it in the paper.

(defthm ==-step
  (== (make-state call-stack heap class-table)
      (step (make-state call-stack heap class-table)))
  :rule-classes nil)

(defthm ==-stepper
  (implies (and (consp (NTH (PC (TOP call-stack))
                            (PROGRAM (TOP call-stack))))
                (not (equal (car (NTH (PC (TOP call-stack))
                                      (PROGRAM (TOP call-stack))))
                            'invokestatic)))
           (== (make-state
                call-stack
                heap
                class-table)
               (step (make-state
                      call-stack
                      heap
                      class-table))))
  :hints (("Goal" :in-theory (disable step))))

(defthm general-==-stepper
  (implies (equal call-stack call-stack) ; not an abbreviation rule!
           (== (make-state call-stack
                           heap
                           class-table)
               (step (make-state call-stack
                                 heap
                                 class-table)))))
(defun stepn (s n)
  (if (zp n)
      s
    (stepn (step s) (- n 1))))

(defthm ==-stepn
  (== (stepn s n) s))

(defthm ==-Y
  (implies (== (stepn s1 n)
               (stepn s2 m))
           (== s1 s2))
  :rule-classes nil)

(in-theory (disable general-==-stepper ==))
(in-theory (enable step))

(defun next-instruction (call-stack)
  (nth (pc (top call-stack))
       (program (top call-stack))))

; A consequence of this setup is that for every primitive instruction
; except for invokestatic we have a theorem like:

(defthm ==-load
  (implies (and (equal (next-instruction call-stack)
                       `(load ,var)))
           (== (make-state call-stack
                           heap
                           class-table)
               (make-state
                (push (make-frame (+ 1 (pc (top call-stack)))
                                  (locals (top call-stack))
                                  (push (binding var (locals (top call-stack)))
                                        (stack (top call-stack)))
                                  (program (top call-stack)))
                      (pop call-stack))
                heap
                class-table)))
  :rule-classes nil)

; Ok, that completes the general work.  Now let's deal with fact.

(defun fact-==-hint (call-stack heap table n)
  (if (zp n)
      (list call-stack heap table)
    (fact-==-hint
      (push (make-frame 6
                        (list (cons 'n (top (stack (top call-stack)))))
                        (push (- (top (stack (top call-stack))) 1)
                              (push (top (stack (top call-stack)))
                                    nil))
                        (method-program (\bf_fact)))
            (push (make-frame (+ 1 (pc (top call-stack)))
                              (locals (top call-stack))
                              (pop (stack (top call-stack)))
                              (program (top call-stack)))
                  (pop call-stack)))
      heap
      table
     (- n 1))))

(defun Math-class-loadedp (class-table)
  (equal (assoc-equal "Math" class-table)
         (\bfMath-class)))

; The following lemma is proved just so we can prove the next
; theorem without any hints.  The hintless version is shown in the paper.

(defthm ==-invokestatic-fact-lemma
  (implies (and (equal (next-instruction call-stack)
                       '(invokestatic "Math" "fact" 1))
                (Math-class-loadedp class-table)
                (equal n (top (stack (top call-stack))))
                (natp n))
           (== (make-state call-stack
                           heap
                           class-table)
               (make-state
                (push (make-frame (+ 1 (pc (top call-stack)))
                                  (locals (top call-stack))
                                  (push (fact n)
                                        (pop (stack (top call-stack))))
                                  (program (top call-stack)))
                      (pop call-stack))
                heap
                class-table)))
  :hints (("Goal" :in-theory (enable general-==-stepper top-frame)
           :restrict ((general-==-STEPPER
                       ((call-stack call-stack)
                        (heap heap)
                        (class-table class-table))))
           :induct (fact-==-hint call-stack heap class-table n))))

(defthm ==-invokestatic-fact
  (implies (and (equal (next-instruction call-stack)
                       '(invokestatic "Math" "fact" 1))
                (Math-class-loadedp class-table)
                (equal n (top (stack (top call-stack))))
                (natp n))
           (== (make-state call-stack
                           heap
                           class-table)
               (make-state
                (push (make-frame (+ 1 (pc (top call-stack)))
                                  (locals (top call-stack))
                                  (push (fact n)
                                        (pop (stack (top call-stack))))
                                  (program (top call-stack)))
                      (pop call-stack))
                heap
                class-table))))


