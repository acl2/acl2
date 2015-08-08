(in-package "ACL2")

#|
Exercize 13.1

The expression (INST-in-order i j MT) is true if and only if  the
instruction represented by i precedes the one represented by
j in program order.  Using the MAETT representation, we can define it
as follows, because the MAETT records instructions in program order in
a list.

(defun {member-in-order} (i j lst)
  (member-equal j (cdr (member-equal i lst))))

(defun {INST-in-order-p} (i j MT)
  (member-in-order i j (MT-trace lst)))

We want to prove that (INST-in-order-p i j MT) defines a partial
order between i and j given that MT is fixed.
This requires a proof of the asymmetry and transitivity of
member-in-order:

(defthm member-in-order-asymmetry
    (implies (and (member-in-order i j lst))
             (not (member-in-order j i lst))))

(defthm member-in-order-transitivity
    (implies (and (member-in-order i j lst)
                  (member-in-order j k lst))
             (member-in-order i k lst)))

If possible, prove the above.  If the above are not provable, add
additional hypotheses and prove the resulting theorems.
|#

; The definition of member-in-order
(defun member-in-order (i j lst)
  (member-equal j (cdr (member-equal i lst))))

#|
; This is the definition of INST-in-order-p
This is how we defined the program order between instruction i and j.
This definition is not necessary to complete the exercise.
(defun INST-in-order-p (i j MT)
  (member-in-order i j (MT-trace lst)))
|#

#|
Following theorems do not hold.  Counter examples are:
i = 1, j = 2, k = 3 and lst = (2 3 1 2).

(defthm  member-in-order-asymmetry
    (implies (member-in-order i j lst)
	     (not (member-in-order j i lst))))

(defthm member-in-order-transitivity
    (implies (and (member-in-order i j lst)
		  (member-in-order j k lst))
	     (member-in-order i k lst)))

|#


;; Third argument, lst, to member-in-order must be a unique list
(defun uniq-lst-p (lst)
  (if (endp lst) t
      (and (not (member-equal (car lst) (cdr lst)))
	   (uniq-lst-p (cdr lst)))))

;; We introduce a recursive definition of member-in-order as
;; a definition rule, and disable the original member-in-order
;; function.
(defthm member-in-order*
    (equal (member-in-order i j lst)
	   (if (endp lst)
	       nil
	       (if (equal i (car lst))
		   (member-equal j (cdr lst))
		   (member-in-order i j (cdr lst)))))
  :rule-classes :definition)

(in-theory (disable member-in-order))


;; ACL2 can prove the following theorems easily.
(defthm  member-in-order-asymmetry
    (implies (and (uniq-lst-p lst)
		  (member-in-order i j lst))
	     (not (member-in-order j i lst))))

(defthm member-in-order-transitivity
    (implies (and (uniq-lst-p lst)
		  (member-in-order i j lst)
		  (member-in-order j k lst))
	     (member-in-order i k lst)))

