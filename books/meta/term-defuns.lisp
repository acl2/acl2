; ACL2 books on arithmetic metafunctions
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  John Cowles and Matt Kaufmann
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")

(set-verify-guards-eagerness 2)

; Jared removed this rule because (1) it's slow, and (2) there's an identical rule
; that is built into ACL2, TRUE-LISTP-APPEND.

;; (defthm append-true-listp-type-prescription
;;   (implies (true-listp y)
;;            (true-listp (append x y)))
;;   :rule-classes :type-prescription)

(defun memb (a x)
  (if (consp x)
      (or (equal a (car x))
          (memb a (cdr x)))
    nil))

(defun del (x y)
  (if (consp y)
      (if (equal x (car y))
	  (cdr y)
	(cons (car y) (del x (cdr y))))
    y))

(defthm true-listp-del
  (implies (true-listp x)
           (true-listp (del a x)))
  :rule-classes :type-prescription)

(defun subbagp (x y)
  (if (consp x)
      (if (memb (car x) y)
	  (subbagp (cdr x) (del (car x) y))
	nil)
    t))

(defun bagdiff (x y)
  (if (consp y)
      (if (memb (car y) x)
	  (bagdiff (del (car y) x) (cdr y))
	(bagdiff x (cdr y)))
    x))

(defthm true-listp-bagdiff
  (implies (true-listp x)
           (true-listp (bagdiff x y)))
  :rule-classes :type-prescription)

(defun bagint (x y)
  (if (consp x)
      (if (memb (car x) y)
	  (cons (car x)
		(bagint (cdr x) (del (car x) y)))
	(bagint (cdr x) y))
    nil))

(defun
  term-list-to-type-term ( unary-op-name lst )
  (declare (xargs :guard (and (symbolp unary-op-name)
			      (true-listp lst) )))
  (cond ((null lst)
	 ''t)
	((null (cdr lst))
	 (list unary-op-name (car lst)))
	(t
	 (list 'if
	       (list unary-op-name (car lst))
	       (term-list-to-type-term unary-op-name (cdr lst))
	       ''nil))))

(defun
  binary-op_fringe (binary-op-name x)
  (declare (xargs :guard (and (symbolp binary-op-name)
			      (not (eq binary-op-name 'quote))
			      (pseudo-termp x))))
  (if (and (consp x)
	   (eq (car x) binary-op-name))
      (append (binary-op_fringe binary-op-name (cadr x))
	      (binary-op_fringe binary-op-name (caddr x)))
      (cons x nil)))

(defun binary-op_tree (binary-op-name constant-name fix-name lst)
  (declare (xargs :guard (and (symbolp binary-op-name)
			      (atom constant-name)
			      (true-listp lst))))
  (if (endp lst)
      (list 'quote constant-name)
      (if (endp (cdr lst))
	  (list fix-name (car lst))
	  (if (endp (cddr lst))
	      (list binary-op-name (car lst) (cadr lst))
	      (list binary-op-name (car lst)
		    (binary-op_tree binary-op-name constant-name fix-name
                                    (cdr lst)))))))

(defun binary-op_tree-simple (binary-op-name constant-name lst)
  (declare (xargs :guard (and (symbolp binary-op-name)
			      (atom constant-name)
			      (true-listp lst))))
  (if (endp lst)
      (list 'quote constant-name)
    (if (endp (cdr lst))
        (car lst)
      (list binary-op-name (car lst)
            (binary-op_tree-simple binary-op-name constant-name
                                   (cdr lst))))))

(defun
  remove-duplicates-memb (lst)
  (if (consp lst)
      (if (memb (car lst)(cdr lst))
	  (remove-duplicates-memb (cdr lst))
	  (cons (car lst)
		(remove-duplicates-memb (cdr lst))))
      nil))

(defun fringe-occur (binop arg term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp binop)
                              (not (eq binop 'quote)))))
  (cond
   ((and (consp term)
         (eq (car term) binop))
    (or (fringe-occur binop arg (cadr term))
        (fringe-occur binop arg (caddr term))))
   (t (equal arg term))))
