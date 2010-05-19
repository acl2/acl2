; Arithmetic-3 Library
; Copyright (C) 2004 Robert Krug <rkrug@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; remove-weak-inequalities.lisp
;;;
;;;
;;; This book contains four rules to remove ``weak'' inequalities
;;; from the goal.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(table acl2-defaults-table :state-ok t)

(include-book "building-blocks")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun present-in-goal (term goal)
  
  ;; Present-in-goal is 'positive if term appears as a literal
  ;; of goal, and 'negative if term appears negated.  It is NIL
  ;; otherwise.  Note that due to ACL2's internal representation
  ;; of a goal in disjunctive normal form, the hypotheses of a
  ;; goal appear internally in the opposite form that the user
  ;; sees.  Thus, a hypothesis such as (<= x y) will appear
  ;; as (< y x) in the clause, while (< x y) will appear as
  ;; (not (< x y)).
  
  (cond ((endp goal)
         nil)
        ((equal term (car goal))
         'positive)
        ((and (eq (fn-symb (car goal)) 'NOT)
              (equal term (fargn (car goal) 1)))
         'negative)
        (t
         (present-in-goal term (cdr goal)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Strict-inequalities

(defun remove-weak-inequalities-one-fn (x y mfc state)

  ;; We remove the second inequality in each thm below.

  ;; (thm (implies (and (< x y) (<= x y)) (equal a b)))
  ;; (thm (implies (and (< (+ 1 x) y) (<= x y)) (equal a b)))
  ;; (thm (implies (and (<= (+ 1 x) y) (<= x y)) (equal a b)))
  
  (if (eq (present-in-goal `(< ,y ,x) (mfc-clause mfc))
          'positive)
      (let ((contradictionp (mfc-ap `(< ,y ,x) mfc state)))
        (if (equal (length (access poly contradictionp :parents))
                   1)
            t
          nil))
    nil))

(defthm remove-weak-inequalities-one
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (syntaxp (remove-weak-inequalities-one-fn x y mfc state))
                  (<= x y))
             (<= x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; ``Regular'' ineaualities

(defun remove-weak-inequalities-two-fn (x y mfc state)

  ;; We remove the second inequality in each thm below.

  ;; (thm (implies (and (< (+ 1 x) y) (< x y)) (equal a b)))
  ;; (thm (implies (and (<= (+ 1 x) y) (< x y)) (equal a b)))
  
  (if (eq (present-in-goal `(< ,x ,y) (mfc-clause mfc))
          'negative)
      (let ((contradictionp (mfc-ap `(NOT (< ,x ,y)) mfc state)))
        (if (equal (length (access poly contradictionp :parents))
                   1)
            t
          nil))
    nil))

(defthm remove-weak-inequalities-two
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (syntaxp (remove-weak-inequalities-two-fn x y mfc state))
                  (< x y))
             (< x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Type three.
;;; involves division

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Type four.
;;; made of two others
