; ACL2 books on arithmetic metafunctions
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  John Cowles and Matt Kaufmann
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.



(in-package "ACL2")

(include-book "term-defuns")
(include-book "pseudo-termp-lemmas")

(defthm delete-non-member
  (implies (not (memb x y))
           (equal (del x y) y)))

(defthm member-delete
     (implies (memb x (del u v))
	      (memb x v)))

(defthm delete-commutativity
     (equal (del x (del y z))
	    (del y (del x z))))

(defthm subbagp-delete
     (implies (subbagp x (del u y))
	      (subbagp x y)))

(defthm subbagp-cdr1
     (implies (and (subbagp x y)
                   (consp x))
	      (subbagp (cdr x) y)))

(defthm subbagp-cdr2
     (implies (and (subbagp x (cdr y))
                   (consp y))
	      (subbagp x y)))

(defthm subbagp-bagint1
     (subbagp (bagint x y) x))

(defthm subbagp-bagint2
     (subbagp (bagint x y) y))

(defthm memb-append
  (equal (memb a (append x y))
         (or (memb a x)
             (memb a y))))

(defthm binary-op_tree-opener
  (and (implies (not (consp lst))
                (equal (binary-op_tree binary-op-name constant-name fix-name lst)
                       (list 'quote constant-name)))
       (equal (binary-op_tree binary-op-name constant-name fix-name (cons x lst))
              (cond
               ((not (consp lst))
                (list fix-name x))
               ((and (consp lst)
                     (not (consp (cdr lst))))
                (list binary-op-name x (car lst)))
               (t (list binary-op-name x
                        (binary-op_tree binary-op-name constant-name fix-name
                                        lst)))))))

(defthm binary-op_tree-simple-opener
  (and (implies (not (consp lst))
                (equal (binary-op_tree-simple binary-op-name constant-name lst)
                       (list 'quote constant-name)))
       (equal (binary-op_tree-simple binary-op-name constant-name (cons x lst))
              (cond
               ((not (consp lst))
                x)
               (t (list binary-op-name x
                        (binary-op_tree-simple binary-op-name constant-name
                                               lst)))))))

(defthm fringe-occur-same-as-occur-in-fringe
  (equal (fringe-occur binop arg term)
         (memb arg (binary-op_fringe binop term))))


(defthm pseudo-termp-term-list-to-type-term
  (implies (and (pseudo-term-listp x)
		(symbolp unary-op-name))
           (pseudo-termp (term-list-to-type-term unary-op-name x))))

(defthm pseudo-term-listp-del
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (del a x))))

(defthm pseudo-term-listp-bagdiff
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (bagdiff x y))))

(defthm pseudo-term-listp-bagint
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (bagint x y))))

(defthm pseudo-term-listp-binary-op_fringe
  (implies (and (symbolp binary-op-name)
		(not (equal binary-op-name 'quote))
		(pseudo-termp x))
           (pseudo-term-listp (binary-op_fringe binary-op-name x))))

(defthm psuedo-termp-binary-op_tree
  (implies (and (pseudo-term-listp l)
		(symbolp binary-op-name)
                (symbolp fix-name)
                (not (equal binary-op-name 'quote))
		(atom constant-name))
           (pseudo-termp (binary-op_tree binary-op-name constant-name fix-name l)))
  :rule-classes
  (:rewrite
   (:forward-chaining
    :trigger-terms
    ((binary-op_tree binary-op-name constant-name fix-name l)))))

(defthm
  pseudo-term-listp-remove-duplicates-memb
  (implies (pseudo-term-listp lst)
	   (pseudo-term-listp (remove-duplicates-memb lst))))
