; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; remove-weak-inequalities.lisp
;;;
;;; This book contains a couple of rules to remove ``weak''
;;; inequalities from the goal in order to reduce clutter.  We could
;;; probably be more aggressive and remove more than we do, but I have
;;; not thought much about just how far to go.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

(table acl2-defaults-table :state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Weak-inequalities

(defun remove-weak-inequalities-fn (x y mfc state)
  (declare (xargs :guard t))

  ;; We remove the second inequality in each thm below.

  ;; (thm (implies (and (< x y) (<= x y)) (equal a b)))
  ;; (thm (implies (and (< (+ 1 x) y) (<= x y)) (equal a b)))
  ;; (thm (implies (and (<= (+ 1 x) y) (<= x y)) (equal a b)))

  ;; We do so by asking if linear arithmetic can prove the inequality
  ;; using ony one other inequality.  The ``other''-ness is ensured by
  ;; linear arithmetic use of parent-trees to prevent tail-biting
  ;; (search for ``tail-biting'' in ACL2's sources).  The one-ness is
  ;; ensured by the use of len below.  We use present-in-hyps to
  ;; restrict this rules operation to removing inequalities from the
  ;; current goal.  It would be useless to use this during
  ;; backchaining --- linear arithmetic is already used for that ---
  ;; and too expensive to try this while expanding function
  ;; defintions.

  ;; I restrict this function to the case where only one other
  ;; inequality out of worries that otherwise I could remove too
  ;;; much from the clause.  I should think this through more
  ;;; carefully, but this is certainly safe even if not optimal.

  (if (eq (present-in-hyps `(< ,y ,x) (mfc-clause mfc))
          'positive)
      (let ((contradictionp (mfc-ap `(< ,y ,x) mfc state)))
        (if (and (consp contradictionp)
		 (consp (car contradictionp))
		 (consp (caar contradictionp))
		 (consp (cdaar contradictionp))
		 (equal (len (access poly contradictionp :parents))
			1))
            t
          nil))
    nil))

(defthm remove-weak-inequalities
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (syntaxp (remove-weak-inequalities-fn x y mfc state))
                  (<= x y))
             (<= x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; strict inequalities

(defun remove-strict-inequalities-fn (x y mfc state)
  (declare (xargs :guard t))

  ;; We remove the second inequality in each thm below.

  ;; (thm (implies (and (< (+ 1 x) y) (< x y)) (equal a b)))
  ;; (thm (implies (and (<= (+ 1 x) y) (< x y)) (equal a b)))

  (if (eq (present-in-hyps `(< ,x ,y) (mfc-clause mfc))
          'negative)
      (let ((contradictionp (mfc-ap `(NOT (< ,x ,y)) mfc state)))
        (if (and (consp contradictionp)  ; for the guard.
		 (consp (car contradictionp))
		 (consp (caar contradictionp))
		 (consp (cdaar contradictionp))
		 (equal (len (access poly contradictionp :parents))
			1))
            t
          nil))
    nil))

(defthm remove-strict-inequalities
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (syntaxp (remove-strict-inequalities-fn x y mfc state))
                  (< x y))
             (< x y)))
