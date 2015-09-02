; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

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
